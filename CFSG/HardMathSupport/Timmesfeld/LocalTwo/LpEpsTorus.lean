module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LpEpsLift

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open Matrix

namespace Torus

variable {K : Type*} [Field K] {n : ℕ}

@[expose] def diagGL (c : Fin n → Kˣ) : GL (Fin n) K where
  val := diagonal fun i => (c i : K)
  inv := diagonal fun i => ((c i)⁻¹ : Kˣ)
  val_inv := by
    rw [diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  inv_val := by
    rw [diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [h]

theorem coe_diagGL (c : Fin n → Kˣ) :
    ((diagGL c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = diagonal fun i => (c i : K) := rfl

@[expose] def diagHom : (Fin n → Kˣ) →* GL (Fin n) K where
  toFun := fun c => (diagGL c : GL (Fin n) K)
  map_one' := by
    ext i j
    simp only [coe_diagGL, Pi.one_apply, Units.val_one]
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  map_mul' c c' := by
    ext i j
    simp only [coe_diagGL, Units.val_mul, Pi.mul_apply, diagonal_mul_diagonal]

theorem diagHom_apply (c : Fin n → Kˣ) : (diagHom c : GL (Fin n) K) = diagGL c := rfl

theorem det_diagGL (c : Fin n → Kˣ) :
    ((diagGL c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = ∏ i, (c i : K) := by
  rw [coe_diagGL, det_diagonal]

@[expose] def swapGL (a b : Fin n) : GL (Fin n) K :=
  ⟨Matrix.swap K a b, Matrix.swap K a b, Matrix.swap_mul_self a b, Matrix.swap_mul_self a b⟩

theorem coe_swapGL (a b : Fin n) :
    ((swapGL a b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.swap K a b := rfl

theorem swapGL_mul_self (a b : Fin n) : (swapGL a b : GL (Fin n) K) * swapGL a b = 1 :=
  Units.ext (Matrix.swap_mul_self a b)

theorem swapGL_inv (a b : Fin n) : (swapGL a b : GL (Fin n) K)⁻¹ = swapGL a b :=
  inv_eq_of_mul_eq_one_right (swapGL_mul_self a b)

theorem swapGL_conj_diag (a b : Fin n) (c : Fin n → Kˣ) :
    (swapGL a b : GL (Fin n) K) * diagHom c * swapGL a b = diagHom (c ∘ Equiv.swap a b) := by
  apply Units.ext
  have h1 : Matrix.swap K a b = (Equiv.swap a b).toPEquiv.toMatrix := rfl
  rw [Units.val_mul, Units.val_mul, coe_swapGL, diagHom_apply, coe_diagGL, h1,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_submatrix,
    Function.id_comp, Function.comp_id, Equiv.symm_swap, Matrix.submatrix_diagonal_equiv]
  rfl

@[expose] def signVec (b : Fin n) : Fin n → Kˣ := Function.update 1 b (-1)

@[expose] def sgnSwap (a b : Fin n) : GL (Fin n) K := swapGL a b * diagHom (signVec b)

theorem swapGL_comm_diag {a b : Fin n} (v : Fin n → Kˣ) (hv : v ∘ Equiv.swap a b = v) :
    (swapGL a b : GL (Fin n) K) * diagHom v = diagHom v * swapGL a b := by
  have h := swapGL_conj_diag (K := K) a b v
  rw [hv] at h
  calc (swapGL a b : GL (Fin n) K) * diagHom v = (swapGL a b * diagHom v * swapGL a b) *
        (swapGL a b)⁻¹ := by rw [mul_inv_cancel_right]
    _ = diagHom v * swapGL a b := by rw [h, swapGL_inv]

theorem sgnSwap_conj_diag (a b : Fin n) (c : Fin n → Kˣ) :
    (sgnSwap a b : GL (Fin n) K) * diagHom c * (sgnSwap a b)⁻¹ = diagHom (c ∘ Equiv.swap a b) := by
  have e : (sgnSwap a b : GL (Fin n) K) * diagHom c * (sgnSwap a b)⁻¹ =
      swapGL a b * (diagHom (signVec b) * diagHom c * (diagHom (signVec b))⁻¹) * (swapGL a b)⁻¹ := by
    rw [sgnSwap, _root_.mul_inv_rev]; simp only [mul_assoc]
  have hc : signVec b * c * (signVec b)⁻¹ = c := by
    rw [mul_comm (signVec b) c, mul_assoc, mul_inv_cancel, mul_one]
  rw [e, ← map_inv, ← map_mul, ← map_mul, hc, swapGL_inv, swapGL_conj_diag]

theorem sgnSwap_mul_self (a b : Fin n) :
    (sgnSwap a b : GL (Fin n) K) * sgnSwap a b = diagHom (signVec a * signVec b) := by
  have e : (sgnSwap a b : GL (Fin n) K) * sgnSwap a b =
      (swapGL a b * diagHom (signVec b) * swapGL a b) * diagHom (signVec b) := by
    rw [sgnSwap]; simp only [mul_assoc]
  rw [e, swapGL_conj_diag, ← map_mul]
  congr 1
  funext i
  simp only [Function.comp_apply, Pi.mul_apply, signVec, Function.update_apply, Equiv.swap_apply_def,
    Pi.one_apply]
  split_ifs <;> simp_all

theorem signVec_mul_self (b : Fin n) : signVec (K := K) b * signVec b = 1 := by
  funext i
  simp only [Pi.mul_apply, signVec, Function.update_apply, Pi.one_apply]
  split_ifs <;> simp

theorem sgnSwap_pow_four (a b : Fin n) : (sgnSwap a b : GL (Fin n) K) ^ 4 = 1 := by
  have h2 : (sgnSwap a b : GL (Fin n) K) ^ 4 = (sgnSwap a b * sgnSwap a b) * (sgnSwap a b * sgnSwap a b) := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
  rw [h2, sgnSwap_mul_self, ← map_mul]
  have : signVec (K := K) a * signVec b * (signVec a * signVec b) = 1 := by
    calc signVec (K := K) a * signVec b * (signVec a * signVec b) = (signVec a * signVec a) * (signVec b * signVec b) := by
          rw [mul_mul_mul_comm]
      _ = 1 := by rw [signVec_mul_self, signVec_mul_self, mul_one]
  rw [this, map_one]

theorem det_sgnSwap {a b : Fin n} (hab : a ≠ b) :
    ((sgnSwap a b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
  rw [sgnSwap, Units.val_mul, det_mul, coe_swapGL, diagHom_apply, det_diagGL]
  have h1 : (Matrix.swap K a b).det = -1 := by
    rw [Matrix.swap, Matrix.det_permutation, Equiv.Perm.sign_swap hab]
    simp
  have h2 : ∏ i, ((signVec (K := K) b i : Kˣ) : K) = -1 := by
    rw [Finset.prod_eq_single_of_mem b (Finset.mem_univ b)]
    · simp [signVec]
    · intro i _ hi
      simp [signVec, Function.update_of_ne hi]
  rw [h1, h2]
  simp

theorem sgnSwap_apply_ne (a b : Fin n) :
    ((sgnSwap a b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b ≠ 0 := by
  rw [sgnSwap, Units.val_mul, coe_swapGL, diagHom_apply, coe_diagGL]
  have : (Matrix.swap K a b * diagonal fun i => (signVec (K := K) b i : K)) a b = ((signVec (K := K) b b : Kˣ) : K) := by
    rw [Matrix.swap_mul_apply_left]
    simp [diagonal_apply_eq]
  rw [this]
  simp [signVec]

theorem commute_sgnSwap_diag {a b : Fin n} {v : Fin n → Kˣ} (hv : v ∘ Equiv.swap a b = v) :
    Commute (sgnSwap a b : GL (Fin n) K) (diagHom v) := by
  have h := sgnSwap_conj_diag (K := K) a b v
  rw [hv] at h
  exact mul_inv_eq_iff_eq_mul.1 h

theorem commute_swapGL_swapGL {a b c d : Fin n} (h : [a, b, c, d].Nodup) :
    Commute (swapGL a b : GL (Fin n) K) (swapGL c d) := by
  have hc : Commute (Equiv.swap a b) (Equiv.swap c d) :=
    (Equiv.Perm.disjoint_swap_swap h).commute
  apply Units.ext
  simp only [Units.val_mul, coe_swapGL, Matrix.swap]
  rw [← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul, hc.eq]

theorem commute_sgnSwap_sgnSwap {a b c d : Fin n} (h : [a, b, c, d].Nodup) :
    Commute (sgnSwap a b : GL (Fin n) K) (sgnSwap c d) := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at h
  obtain ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩ := h
  have hca : c ≠ a := fun h => hac h.symm
  have hda : d ≠ a := fun h => had h.symm
  have hcb : c ≠ b := fun h => hbc h.symm
  have hdb : d ≠ b := fun h => hbd h.symm
  have h1 : Commute (swapGL a b : GL (Fin n) K) (swapGL c d) :=
    commute_swapGL_swapGL (by simp [hab, hac, had, hbc, hbd, hcd])
  have hvd : signVec (K := K) d ∘ Equiv.swap a b = signVec d := by
    funext i
    simp only [Function.comp_apply, signVec, Function.update_apply, Equiv.swap_apply_def]
    split_ifs <;> simp_all
  have hvb : signVec (K := K) b ∘ Equiv.swap c d = signVec b := by
    funext i
    simp only [Function.comp_apply, signVec, Function.update_apply, Equiv.swap_apply_def]
    split_ifs <;> simp_all
  have h2 : Commute (swapGL a b : GL (Fin n) K) (diagHom (signVec d)) :=
    swapGL_comm_diag _ hvd
  have h3 : Commute (diagHom (signVec b) : GL (Fin n) K) (swapGL c d) :=
    (swapGL_comm_diag _ hvb).symm
  have h4 : Commute (diagHom (signVec b) : GL (Fin n) K) (diagHom (signVec d)) :=
    Commute.all _ _ |>.map diagHom
  rw [sgnSwap, sgnSwap]
  exact (h1.mul_right h2).mul_left ((h3.mul_right h4))

@[expose] def tvec (ζ : Kˣ) (i j : Fin n) : Fin n → Kˣ :=
  Function.update (Function.update 1 i ζ) j ζ⁻¹

theorem tvec_apply_i (ζ : Kˣ) {i j : Fin n} (hij : i ≠ j) : tvec ζ i j i = ζ := by
  simp [tvec, Function.update_of_ne hij]

theorem tvec_apply_j (ζ : Kˣ) (i j : Fin n) : tvec ζ i j j = ζ⁻¹ := by
  simp [tvec]

theorem tvec_apply_of_ne (ζ : Kˣ) {i j m : Fin n} (hi : m ≠ i) (hj : m ≠ j) : tvec ζ i j m = 1 := by
  simp [tvec, Function.update_of_ne hi, Function.update_of_ne hj]

theorem tvec_comp_swap_self (ζ : Kˣ) {i j : Fin n} (hij : i ≠ j) :
    tvec ζ i j ∘ Equiv.swap i j = (tvec ζ i j)⁻¹ := by
  funext m
  by_cases hmi : m = i
  · subst hmi
    simp [Equiv.swap_apply_left, tvec_apply_j, tvec_apply_i ζ hij]
  · by_cases hmj : m = j
    · subst hmj
      simp [Equiv.swap_apply_right, tvec_apply_i ζ hij, tvec_apply_j]
    · simp [Equiv.swap_apply_of_ne_of_ne hmi hmj, tvec_apply_of_ne ζ hmi hmj]

theorem tvec_comp_swap_other (ζ : Kˣ) {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    tvec ζ i k ∘ Equiv.swap i j = (tvec ζ i j)⁻¹ * tvec ζ i k := by
  funext m
  by_cases hmi : m = i
  · subst hmi
    simp [Equiv.swap_apply_left, tvec_apply_of_ne ζ hij.symm hjk,
      tvec_apply_i ζ hij, tvec_apply_i ζ hik]
  · by_cases hmj : m = j
    · subst hmj
      simp [Equiv.swap_apply_right, tvec_apply_i ζ hik, tvec_apply_j, tvec_apply_of_ne ζ hij.symm hjk]
    · by_cases hmk : m = k
      · subst hmk
        simp [Equiv.swap_apply_of_ne_of_ne hmi hmj, tvec_apply_j, tvec_apply_of_ne ζ hmi hmj]
      · simp [Equiv.swap_apply_of_ne_of_ne hmi hmj, tvec_apply_of_ne ζ hmi hmk,
          tvec_apply_of_ne ζ hmi hmj]

theorem tvec_comp_swap_disj (ζ : Kˣ) {i j a b : Fin n} (hai : a ≠ i) (haj : a ≠ j) (hbi : b ≠ i)
    (hbj : b ≠ j) : tvec ζ i j ∘ Equiv.swap a b = tvec ζ i j := by
  funext m
  by_cases hma : m = a
  · subst hma
    simp [Equiv.swap_apply_left, tvec_apply_of_ne ζ hai haj, tvec_apply_of_ne ζ hbi hbj]
  · by_cases hmb : m = b
    · subst hmb
      simp [Equiv.swap_apply_right, tvec_apply_of_ne ζ hai haj, tvec_apply_of_ne ζ hbi hbj]
    · simp [Equiv.swap_apply_of_ne_of_ne hma hmb]

theorem tvec_pow {ζ : Kˣ} {p : ℕ} (hζ : ζ ^ p = 1) (i j : Fin n) : tvec ζ i j ^ p = 1 := by
  funext m
  simp only [Pi.pow_apply, Pi.one_apply, tvec, Function.update_apply]
  split_ifs <;> simp [hζ, inv_pow]

@[expose] def pt (hn : 7 ≤ n) (i : ℕ) (hi : i < 7) : Fin n := ⟨i, lt_of_lt_of_le hi hn⟩

@[expose] def ptk (hn : 7 ≤ n) (k : Fin 4) : Fin n := ⟨k.val + 3, by omega⟩

@[expose] def Xg (ζ : Kˣ) (hn : 7 ≤ n) (k : Fin 4) : GL (Fin n) K :=
  diagHom (tvec ζ (pt hn 2 (by norm_num)) (ptk hn k))

@[expose] def Swg (hn : 7 ≤ n) (k : Fin 4) : GL (Fin n) K :=
  sgnSwap (pt hn 2 (by norm_num)) (ptk hn k)

@[expose] def Tg (hn : 7 ≤ n) : GL (Fin n) K :=
  sgnSwap (pt hn 0 (by norm_num)) (pt hn 1 (by norm_num))

section Facts

variable (ζ : Kˣ) (hn : 7 ≤ n)

theorem pt_ne_ptk (i : ℕ) (hi : i < 7) (hi3 : i < 3) (k : Fin 4) : pt hn i hi ≠ ptk hn k := by
  simp only [pt, ptk, ne_eq, Fin.mk.injEq]; omega

theorem ptk_ne_ptk {j k : Fin 4} (h : j ≠ k) : ptk hn j ≠ ptk hn k := by
  simp only [ptk, ne_eq, Fin.mk.injEq]; omega

theorem pt_ne_pt (i j : ℕ) (hi : i < 7) (hj : j < 7) (h : i ≠ j) : pt hn i hi ≠ pt hn j hj := by
  simp only [pt, ne_eq, Fin.mk.injEq]; exact h

theorem Xg_comm (i j : Fin 4) : Commute (Xg ζ hn i : GL (Fin n) K) (Xg ζ hn j) :=
  (Commute.all _ _).map diagHom

theorem Xg_pow {p : ℕ} (hζ : ζ ^ p = 1) (k : Fin 4) : (Xg ζ hn k : GL (Fin n) K) ^ p = 1 := by
  rw [Xg, ← map_pow, tvec_pow hζ, map_one]

theorem Swg_self (k : Fin 4) :
    (Swg hn k : GL (Fin n) K) * Xg ζ hn k * (Swg hn k)⁻¹ = (Xg ζ hn k)⁻¹ := by
  rw [Swg, Xg, sgnSwap_conj_diag, tvec_comp_swap_self ζ (pt_ne_ptk hn 2 (by norm_num) (by norm_num) k),
    map_inv]

theorem Swg_other {j k : Fin 4} (hjk : j ≠ k) :
    (Swg hn k : GL (Fin n) K) * Xg ζ hn j * (Swg hn k)⁻¹ = (Xg ζ hn k)⁻¹ * Xg ζ hn j := by
  rw [Swg, Xg, Xg, sgnSwap_conj_diag,
    tvec_comp_swap_other ζ (pt_ne_ptk hn 2 (by norm_num) (by norm_num) k)
      (pt_ne_ptk hn 2 (by norm_num) (by norm_num) j) (ptk_ne_ptk hn hjk.symm), map_mul, map_inv]

theorem Tg_pow_four : (Tg hn : GL (Fin n) K) ^ 4 = 1 := sgnSwap_pow_four _ _

theorem Tg_comm_X (k : Fin 4) : Commute (Tg hn : GL (Fin n) K) (Xg ζ hn k) := by
  refine commute_sgnSwap_diag ?_
  refine tvec_comp_swap_disj ζ ?_ ?_ ?_ ?_
  · exact pt_ne_pt hn 0 2 (by norm_num) (by norm_num) (by norm_num)
  · exact pt_ne_ptk hn 0 (by norm_num) (by norm_num) k
  · exact pt_ne_pt hn 1 2 (by norm_num) (by norm_num) (by norm_num)
  · exact pt_ne_ptk hn 1 (by norm_num) (by norm_num) k

theorem Tg_comm_S (k : Fin 4) : Commute (Tg hn : GL (Fin n) K) (Swg hn k) := by
  refine commute_sgnSwap_sgnSwap ?_
  have h01 := pt_ne_pt hn 0 1 (by norm_num) (by norm_num) (by norm_num)
  have h02 := pt_ne_pt hn 0 2 (by norm_num) (by norm_num) (by norm_num)
  have h12 := pt_ne_pt hn 1 2 (by norm_num) (by norm_num) (by norm_num)
  have h0k := pt_ne_ptk hn 0 (by norm_num) (by norm_num) k
  have h1k := pt_ne_ptk hn 1 (by norm_num) (by norm_num) k
  have h2k := pt_ne_ptk hn 2 (by norm_num) (by norm_num) k
  simp [h01, h02, h12, h0k, h1k, h2k]

theorem det_Xg (k : Fin 4) :
    ((Xg ζ hn k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
  rw [Xg, diagHom_apply, det_diagGL]
  have hne := pt_ne_ptk hn 2 (by norm_num) (by norm_num) k
  rw [Finset.prod_eq_mul (pt hn 2 (by norm_num)) (ptk hn k) hne]
  · rw [tvec_apply_i ζ hne, tvec_apply_j]; simp
  · intro m _ hm
    rw [tvec_apply_of_ne ζ (fun h => hm.1 h) (fun h => hm.2 h)]; simp
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro h; exact absurd (Finset.mem_univ _) h

theorem det_Swg (k : Fin 4) :
    ((Swg hn k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 :=
  det_sgnSwap (pt_ne_ptk hn 2 (by norm_num) (by norm_num) k)

theorem det_Tg : ((Tg hn : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 :=
  det_sgnSwap (pt_ne_pt hn 0 1 (by norm_num) (by norm_num) (by norm_num))

theorem Tg_entry :
    ((Tg hn : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) (pt hn 0 (by norm_num))
      (pt hn 1 (by norm_num)) ≠ 0 :=
  sgnSwap_apply_ne _ _

theorem diagHom_injective : Function.Injective (diagHom : (Fin n → Kˣ) →* GL (Fin n) K) := by
  intro v w h
  funext i
  have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) i i) h
  exact Units.ext (by simpa [diagHom_apply, coe_diagGL] using this)

theorem closure_Xg_diag {g : GL (Fin n) K} (hg : g ∈ Subgroup.closure (Set.range (Xg ζ hn))) :
    ∃ v : Fin n → Kˣ, g = diagHom v ∧ v (pt hn 0 (by norm_num)) = 1 := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    refine ⟨_, rfl, ?_⟩
    exact tvec_apply_of_ne ζ (pt_ne_pt hn 0 2 (by norm_num) (by norm_num) (by norm_num))
      (pt_ne_ptk hn 0 (by norm_num) (by norm_num) k)
  | one => exact ⟨1, (map_one _).symm, rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨v, rfl, hv⟩ := hx
    obtain ⟨w, rfl, hw⟩ := hy
    exact ⟨v * w, (map_mul _ _ _).symm, by simp [hv, hw]⟩
  | inv x _ hx =>
    obtain ⟨v, rfl, hv⟩ := hx
    exact ⟨v⁻¹, (map_inv _ _).symm, by simp [hv]⟩

theorem card_closure_Xg [Finite K] {p : ℕ} [Fact p.Prime] (hζ : IsPrimitiveRoot ζ p) :
    p ^ 4 ≤ Nat.card (Subgroup.closure (Set.range (Xg ζ hn)) : Subgroup (GL (Fin n) K)) := by
  classical
  set V : Fin 4 → (Fin n → Kˣ) := fun k => tvec ζ (pt hn 2 (by norm_num)) (ptk hn k) with hV
  set U : Subgroup (Fin n → Kˣ) := Subgroup.closure (Set.range V) with hU
  have hmap : U.map (diagHom : (Fin n → Kˣ) →* GL (Fin n) K) =
      Subgroup.closure (Set.range (Xg ζ hn)) := by
    rw [hU, MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have hcard : Nat.card U = Nat.card (Subgroup.closure (Set.range (Xg ζ hn)) :
      Subgroup (GL (Fin n) K)) := by
    rw [← hmap, Subgroup.card_map_of_injective diagHom_injective]
  rw [← hcard]
  have hev : ∀ (m : Fin 4 → ℕ) (k : Fin 4), (∏ k', V k' ^ m k') (ptk hn k) = ζ⁻¹ ^ m k := by
    intro m k
    rw [Finset.prod_apply, Finset.prod_eq_single k]
    · simp [hV, Pi.pow_apply, tvec_apply_j]
    · intro k' _ hk'
      simp [hV, Pi.pow_apply, tvec_apply_of_ne ζ
        (pt_ne_ptk hn 2 (by norm_num) (by norm_num) k).symm (ptk_ne_ptk hn hk'.symm)]
    · intro h; exact absurd (Finset.mem_univ _) h
  let Φ : (Fin 4 → ZMod p) → U := fun a =>
    ⟨∏ k, V k ^ (a k).val, Subgroup.prod_mem U fun k _ =>
      pow_mem (Subgroup.subset_closure (Set.mem_range_self k)) _⟩
  have hΦ : Function.Injective Φ := by
    intro a b hab
    funext k
    have h1 := congrArg (fun u : U => (u : Fin n → Kˣ) (ptk hn k)) hab
    simp only [Φ] at h1
    rw [hev (fun k => (a k).val) k, hev (fun k => (b k).val) k] at h1
    have hζ' : IsPrimitiveRoot ζ⁻¹ p := hζ.inv
    have := hζ'.pow_inj (ZMod.val_lt (a k)) (ZMod.val_lt (b k)) h1
    exact ZMod.val_injective p this
  have := Nat.card_le_card_of_injective Φ hΦ
  simpa [Nat.card_eq_fintype_card] using this

end Facts


open Subgroup in
theorem lowerDataOfModel {p n : ℕ} [Fact p.Prime] {K : Type*} [Field K] [Finite K]
    {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) (hn : 7 ≤ n) {M S : Type*} [Group M] [Group S]
    (ι : M →* GL (Fin n) K) (hι : Function.Injective ι) (π : M →* S)
    (hπ : ∀ g : M, π g = 1 → ∃ c : Kˣ, ι g = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    (memX : ∀ k, Xg ζ hn k ∈ ι.range) (memS : ∀ k, Swg hn k ∈ ι.range)
    (memT : (Tg hn : GL (Fin n) K) ∈ ι.range) : Nonempty (LowerData p S) := by
  classical
  choose x hx using fun k => MonoidHom.mem_range.1 (memX k)
  choose s hs using fun k => MonoidHom.mem_range.1 (memS k)
  obtain ⟨t, ht⟩ := MonoidHom.mem_range.1 memT
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hcomm : ∀ i j, Commute (x i) (x j) := fun i j => hι (by
    rw [map_mul, map_mul, hx, hx]; exact Xg_comm ζ hn i j)
  have hpow : ∀ i, x i ^ p = 1 := fun i => hι (by
    rw [map_pow, hx, map_one]; exact Xg_pow ζ hn hζp i)
  have hself : ∀ k, s k * x k * (s k)⁻¹ = (x k)⁻¹ := fun k => hι (by
    rw [map_mul, map_mul, map_inv, map_inv, hs, hx]; exact Swg_self ζ hn k)
  have hother : ∀ j k, j ≠ k → s k * x j * (s k)⁻¹ = (x k)⁻¹ * x j := fun j k hjk => hι (by
    rw [map_mul, map_mul, map_inv, map_mul, map_inv, hs, hx, hx]; exact Swg_other ζ hn hjk)
  have htcomm : ∀ i, Commute t (x i) := fun i => hι (by
    rw [map_mul, map_mul, ht, hx]; exact Tg_comm_X ζ hn i)
  have htsw : ∀ k, Commute t (s k) := fun k => hι (by
    rw [map_mul, map_mul, ht, hs]; exact Tg_comm_S hn k)
  have ht4 : t ^ 4 = 1 := hι (by rw [map_pow, ht, map_one]; exact Tg_pow_four hn)
  have htne : π t ≠ 1 := by
    intro h
    obtain ⟨c, hc⟩ := hπ t h
    rw [ht] at hc
    have := Tg_entry (K := K) hn
    rw [hc] at this
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, pt] at this
  refine ⟨?_⟩
  refine
    { X := fun k => π (x k)
      Sw := fun k => π (s k)
      T := π t
      comm := fun i j => (hcomm i j).map π
      pow := fun i => by rw [← map_pow, hpow, map_one]
      sw_self := fun k => by rw [← map_mul, ← map_inv, ← map_mul, hself, map_inv]
      sw_other := fun j k hjk => by
        rw [← map_mul, ← map_inv, ← map_mul, hother j k hjk, map_mul, map_inv]
      T_ne := htne
      T_two := ⟨2, by rw [← map_pow]; simp only [show (2 : ℕ) ^ 2 = 4 from rfl]; rw [ht4, map_one]⟩
      T_comm := fun i => (htcomm i).map π
      T_sw := fun k => (htsw k).map π
      card := ?_ }
  have hmapx : (closure (Set.range x)).map ι = closure (Set.range (Xg ζ hn)) := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    have : (ι ∘ x) = Xg ζ hn := funext hx
    rw [this]
  have hinj : ∀ g ∈ closure (Set.range x), π g = 1 → g = 1 := by
    intro g hg hπg
    obtain ⟨c, hc⟩ := hπ g hπg
    have hg' : ι g ∈ closure (Set.range (Xg ζ hn)) := by
      rw [← hmapx]; exact Subgroup.mem_map_of_mem _ hg
    obtain ⟨v, hv, hv0⟩ := closure_Xg_diag ζ hn hg'
    apply hι
    rw [map_one]
    have h1 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)
      (pt hn 0 (by norm_num)) (pt hn 0 (by norm_num))) (hc.symm.trans hv)
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagHom_apply,
      coe_diagGL, Matrix.diagonal_apply_eq] at h1
    have hc1 : c = 1 := Units.ext (by rw [h1, hv0])
    rw [hc, hc1, map_one]
  have hcard1 : Nat.card (closure (Set.range x)) =
      Nat.card (closure (Set.range (Xg ζ hn)) : Subgroup (GL (Fin n) K)) := by
    rw [← hmapx, Subgroup.card_map_of_injective hι]
  have hinj' : Function.Injective (π.domRestrict (closure (Set.range x))) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    exact Subtype.ext (hinj g g.2 hg)
  have hmapπ : (closure (Set.range x)).map π = closure (Set.range fun k => π (x k)) := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have hcard2 : Nat.card (closure (Set.range fun k => π (x k))) =
      Nat.card (closure (Set.range x)) := by
    rw [← hmapπ, ← MonoidHom.domRestrict_range]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv).symm
  show p ^ 4 ≤ Nat.card (closure (Set.range fun k => π (x k)))
  rw [hcard2, hcard1]
  exact card_closure_Xg ζ hn hζ

end Torus

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
