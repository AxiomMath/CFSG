module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinearBlocks
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb

open Matrix
open scoped commutatorElement

section CentralizerTwo

variable {K : Type*} [Field K]

theorem cross_eq_zero_aux {ι : Type*} (u v w : ι → K) (k : ι) (hk : w k ≠ 0)
    (hu : ∀ i j, u i * w j = u j * w i) (hv : ∀ i j, v i * w j = v j * w i) (i j : ι) :
    u i * v j = u j * v i := by
  apply mul_right_cancel₀ hk
  calc u i * v j * w k = (u i * w k) * v j := by ring
    _ = (u k * w i) * v j := by rw [hu i k]
    _ = u k * (v j * w i) := by ring
    _ = u k * (v i * w j) := by rw [hv j i]
    _ = (u k * w j) * v i := by ring
    _ = (u j * w k) * v i := by rw [hu j k]
    _ = u j * v i * w k := by ring

private def trVec (a : Matrix (Fin 2) (Fin 2) K) : Fin 3 → K :=
  ![a 0 1, a 1 0, a 0 0 - a 1 1]

private theorem trVec_cross_of_commute {y a : Matrix (Fin 2) (Fin 2) K} (h : y * a = a * y)
    (i j : Fin 3) : trVec a i * trVec y j = trVec a j * trVec y i := by
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10
  have p01 : a 0 1 * y 1 0 = a 1 0 * y 0 1 := by linear_combination -h00
  have p02 : a 0 1 * (y 0 0 - y 1 1) = (a 0 0 - a 1 1) * y 0 1 := by linear_combination h01
  have p12 : a 1 0 * (y 0 0 - y 1 1) = (a 0 0 - a 1 1) * y 1 0 := by linear_combination -h10
  fin_cases i <;> fin_cases j <;> simp [trVec]
  · linear_combination p01
  · linear_combination p02
  · linear_combination -p01
  · linear_combination p12
  · linear_combination -p02
  · linear_combination -p12

theorem commute_of_commute_of_not_scalar {y a b : Matrix (Fin 2) (Fin 2) K}
    (hy : ∀ c : K, y ≠ c • (1 : Matrix (Fin 2) (Fin 2) K)) (ha : y * a = a * y)
    (hb : y * b = b * y) : a * b = b * a := by
  have hw : ∃ k, trVec y k ≠ 0 := by
    by_contra hno
    push Not at hno
    have h0 := hno 0
    have h1 := hno 1
    have h2 := hno 2
    simp only [trVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h0 h1 h2
    refine hy (y 0 0) ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h0, h1]
    linear_combination -h2
  obtain ⟨k, hk⟩ := hw
  have hc := cross_eq_zero_aux (trVec a) (trVec b) (trVec y) k hk
    (fun i j => trVec_cross_of_commute ha i j) (fun i j => trVec_cross_of_commute hb i j)
  have c01 := hc 0 1
  have c02 := hc 0 2
  have c12 := hc 1 2
  simp only [trVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at c01 c02 c12
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination c01
  · linear_combination -c02
  · linear_combination c12
  · linear_combination -c01

theorem sl2_central_of_perfect_hom {G : Type*} [Group G] (f : G →* Matrix (Fin 2) (Fin 2) K)
    {V : Subgroup G} (hV : ⁅V, V⁆ = V) {y : Matrix (Fin 2) (Fin 2) K}
    (hy : ∀ v ∈ V, y * f v = f v * y) (hne : ∃ v ∈ V, f v ≠ 1) :
    ∃ c : K, y = c • (1 : Matrix (Fin 2) (Fin 2) K) := by
  by_contra hno
  push Not at hno
  obtain ⟨v, hv, hfv⟩ := hne
  apply hfv
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, f a * f b = f b * f a := fun a ha b hb =>
    commute_of_commute_of_not_scalar hno (hy a ha) (hy b hb)
  have hker : V ≤ (f.toHomUnits).ker := by
    rw [← hV, Subgroup.commutator_le]
    intro a ha b hb
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def]
    have : f.toHomUnits a * f.toHomUnits b = f.toHomUnits b * f.toHomUnits a :=
      Units.ext (by simpa using hcomm a ha b hb)
    simp [mul_assoc, this]
  have h1 := MonoidHom.mem_ker.mp (hker hv)
  simpa using congrArg Units.val h1

end CentralizerTwo

section Embedding

variable {K : Type*} [Field K] {n : ℕ}

@[expose] def embedMat (A : Matrix (Fin n) (Fin 2) K) (B : Matrix (Fin 2) (Fin n) K)
    (g : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin n) (Fin n) K :=
  1 + A * (g - 1) * B

variable {A : Matrix (Fin n) (Fin 2) K} {B : Matrix (Fin 2) (Fin n) K}

theorem embedMat_one : embedMat A B 1 = 1 := by simp [embedMat]

theorem embedMat_mul (hBA : B * A = 1) (g h : Matrix (Fin 2) (Fin 2) K) :
    embedMat A B (g * h) = embedMat A B g * embedMat A B h := by
  have key : A * (g - 1) * B * (A * (h - 1) * B) = A * ((g - 1) * (h - 1)) * B := by
    calc A * (g - 1) * B * (A * (h - 1) * B) = A * (g - 1) * (B * A) * (h - 1) * B := by
          simp only [Matrix.mul_assoc]
      _ = A * ((g - 1) * (h - 1)) * B := by rw [hBA]; simp only [Matrix.mul_assoc, Matrix.mul_one]
  have e : A * (g * h - 1) * B = A * (g - 1) * B + A * (h - 1) * B +
      A * (g - 1) * B * (A * (h - 1) * B) := by
    rw [key]
    have : g * h - 1 = (g - 1) + (h - 1) + (g - 1) * (h - 1) := by noncomm_ring
    rw [this]
    simp only [Matrix.mul_add, Matrix.add_mul]
  simp only [embedMat]
  rw [e]
  noncomm_ring

theorem det_embedMat (hBA : B * A = 1) (g : Matrix (Fin 2) (Fin 2) K) :
    (embedMat A B g).det = g.det := by
  have h1 : embedMat A B g = 1 + A * ((g - 1) * B) := by
    simp [embedMat, Matrix.mul_assoc]
  rw [h1, Matrix.det_one_add_mul_comm, Matrix.mul_assoc (g - 1) B A, hBA, Matrix.mul_one]
  simp

@[expose] noncomputable def embedHom (hBA : B * A = 1) :
    SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin n) K where
  toFun g := ⟨embedMat A B g, by rw [det_embedMat hBA, g.2]⟩
  map_one' := Subtype.ext embedMat_one
  map_mul' g h := Subtype.ext (embedMat_mul hBA g h)

theorem coe_embedHom (hBA : B * A = 1) (g : SpecialLinearGroup (Fin 2) K) :
    (embedHom hBA g : Matrix (Fin n) (Fin n) K) = embedMat A B g :=
  rfl

theorem embedHom_injective (hBA : B * A = 1) : Function.Injective (embedHom hBA) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : embedMat A B (g : Matrix (Fin 2) (Fin 2) K) = 1 := by
    have := congrArg (fun x : SpecialLinearGroup (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) hg
    rwa [coe_embedHom, Matrix.SpecialLinearGroup.coe_one] at this
  have h2 : A * ((g : Matrix (Fin 2) (Fin 2) K) - 1) * B = 0 := by
    simpa [embedMat] using h1
  have h3 : (g : Matrix (Fin 2) (Fin 2) K) - 1 = 0 := by
    have := congrArg (fun X => B * X * A) h2
    simpa [Matrix.mul_assoc, ← Matrix.mul_assoc B A, hBA] using this
  exact Subtype.ext (by simpa [sub_eq_zero] using h3)

theorem exists_sl2_centralizer_of_dual [Finite K] (hK : 4 ≤ Nat.card K) (hn : 3 ≤ n)
    (hBA : B * A = 1) {t : SpecialLinearGroup (Fin n) K}
    (htA : (t : Matrix (Fin n) (Fin n) K) * A = A) (hBt : B * (t : Matrix (Fin n) (Fin n) K) = B) :
    ∃ W : Subgroup (SpecialLinearGroup (Fin n) K),
      W ≤ Subgroup.centralizer {t} ∧ ⁅W, W⁆ = W ∧ W ≠ ⊥ ∧
        W ⊓ Subgroup.center (SpecialLinearGroup (Fin n) K) = ⊥ := by
  have hinj := embedHom_injective hBA
  refine ⟨(embedHom hBA).range, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨g, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    refine Subtype.ext ?_
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_embedHom, embedMat]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc t.1, htA, Matrix.mul_assoc _ B, hBt]
  · have hperf : commutator (SpecialLinearGroup (Fin 2) K) = ⊤ := by
      have : Group.IsPerfect (SpecialLinearGroup (Fin 2) K) := by
        classical
        have : Fintype K := Fintype.ofFinite K
        refine CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := 2) le_rfl (Or.inr ?_)
        obtain ⟨T, -, hT⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K))
          (n := 4) (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hK)
        exact ⟨T, hT⟩
      exact Group.isPerfect_def.mp this
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def, hperf]
  · intro hbot
    let g0 : SpecialLinearGroup (Fin 2) K := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
    have hmem : embedHom hBA g0 ∈ (embedHom hBA).range := ⟨g0, rfl⟩
    rw [hbot, Subgroup.mem_bot, ← map_one (embedHom hBA)] at hmem
    have h0 := congrArg (fun g : SpecialLinearGroup (Fin 2) K =>
      (g : Matrix (Fin 2) (Fin 2) K) 0 1) (hinj hmem)
    simp [g0] at h0
  · rw [eq_bot_iff]
    rintro x ⟨⟨g, rfl⟩, hxc⟩
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hxc
    have hfin : Module.finrank K (Fin 2 → K) < Module.finrank K (Fin n → K) := by
      simp only [Module.finrank_fin_fun]
      omega
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (LinearMap.ker_ne_bot_of_finrank_lt (f := B.mulVecLin) hfin)
    have hBw : B *ᵥ w = 0 := hw
    have h1 : (embedHom hBA g : Matrix (Fin n) (Fin n) K) *ᵥ w = w := by
      simp [coe_embedHom, embedMat, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hBw]
    rw [← hr, scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec,
      Matrix.one_mulVec] at h1
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra hno
      push Not at hno
      exact hw0 (funext hno)
    have hr1 : r = 1 := by
      have := congrFun h1 i
      simp only [Pi.smul_apply, smul_eq_mul] at this
      exact mul_right_cancel₀ hi (by rw [this, one_mul])
    subst hr1
    rw [Subgroup.mem_bot]
    refine Subtype.ext ?_
    rw [← hr]
    simp

theorem exists_sl2_centralizer [Finite K] {p : ℕ} (hp : (p : K) ≠ 0) (hK : 4 ≤ Nat.card K)
    (hn : 3 ≤ n) {t : SpecialLinearGroup (Fin n) K} (htp : t ^ p = 1) {a b : Fin n → K}
    (ha : (t : Matrix (Fin n) (Fin n) K) *ᵥ a = a) (hb : (t : Matrix (Fin n) (Fin n) K) *ᵥ b = b)
    (hab : LinearIndependent K ![a, b]) :
    ∃ W : Subgroup (SpecialLinearGroup (Fin n) K),
      W ≤ Subgroup.centralizer {t} ∧ ⁅W, W⁆ = W ∧ W ≠ ⊥ ∧
        W ⊓ Subgroup.center (SpecialLinearGroup (Fin n) K) = ⊥ := by
  set T : Matrix (Fin n) (Fin n) K := (t : Matrix (Fin n) (Fin n) K) with hT
  have hTp : T ^ p = 1 := by
    rw [hT, ← Matrix.SpecialLinearGroup.coe_pow, htp, Matrix.SpecialLinearGroup.coe_one]
  let A : Matrix (Fin n) (Fin 2) K := Matrix.of fun i j => ![a, b] j i
  have hAmul : ∀ x : Fin 2 → K, A *ᵥ x = x 0 • a + x 1 • b := by
    intro x
    ext i
    simp [A, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  have hTA : T * A = A := by
    ext i j
    fin_cases j
    · simpa [A, Matrix.mulVec, dotProduct, Matrix.mul_apply] using congrFun ha i
    · simpa [A, Matrix.mulVec, dotProduct, Matrix.mul_apply] using congrFun hb i
  have hAinj : LinearMap.ker A.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have hx' : A *ᵥ x = 0 := hx
    rw [hAmul] at hx'
    have := (Fintype.linearIndependent_iff.mp hab) x (by
      simpa [Fin.sum_univ_two] using hx')
    ext i
    exact this i
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective A.mulVecLin hAinj
  set B0 : Matrix (Fin 2) (Fin n) K := LinearMap.toMatrix' g with hB0
  have hB0A : B0 * A = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_one, hB0, Matrix.toLin'_toMatrix']
    exact hg
  set E : Matrix (Fin n) (Fin n) K := (p⁻¹ : K) • ∑ i ∈ Finset.range p, T ^ i with hE
  have hTiA : ∀ i : ℕ, T ^ i * A = A := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ', Matrix.mul_assoc, ih, hTA]
  have hEA : E * A = A := by
    rw [hE, Matrix.smul_mul, Matrix.sum_mul]
    simp only [hTiA, Finset.sum_const, Finset.card_range]
    rw [← Nat.cast_smul_eq_nsmul K p A, smul_smul, inv_mul_cancel₀ hp, one_smul]
  have hET : E * T = E := by
    have h0 : (∑ i ∈ Finset.range p, T ^ i) * (T - 1) = 0 := by
      rw [geom_sum_mul, hTp, sub_self]
    rw [hE, Matrix.smul_mul]
    congr 1
    have := h0
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
    exact this
  refine exists_sl2_centralizer_of_dual (A := A) (B := B0 * E) hK hn (t := t) ?_ ?_ ?_
  · rw [Matrix.mul_assoc, hEA, hB0A]
  · exact hTA
  · rw [Matrix.mul_assoc, hET]

end Embedding

section DetBlocks

open CFSG.AGLEmbedding

variable {K : Type*} [Field K] {n : ℕ} {m : ℕ} {c : ℕ → ℕ}

theorem cuts_le_of_mono (hmono : ∀ i < m, c i < c (i + 1)) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ m) : c i ≤ c j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (ih (by omega)).trans (hmono j (by omega)).le

theorem cuts_le_n (hmono : ∀ i < m, c i < c (i + 1)) (hcm : c m = n) {i : ℕ} (hi : i ≤ m) :
    c i ≤ n :=
  hcm ▸ cuts_le_of_mono hmono hi le_rfl

theorem exists_lt_cut (hc0 : c 0 = 0) (hcm : c m = n) (i : Fin n) :
    ∃ a, a < m ∧ (i : ℕ) < c (a + 1) := by
  rcases m with _ | a
  · exfalso
    have := i.2
    omega
  · exact ⟨a, by omega, by rw [hcm]; exact i.2⟩

noncomputable def cutIdx (hc0 : c 0 = 0) (hcm : c m = n) (i : Fin n) : Fin m :=
  ⟨Nat.find (exists_lt_cut hc0 hcm i), (Nat.find_spec (exists_lt_cut hc0 hcm i)).1⟩

theorem cutIdx_eq_iff (hmono : ∀ i < m, c i < c (i + 1)) (hc0 : c 0 = 0) (hcm : c m = n)
    (i : Fin n) (a : Fin m) :
    cutIdx hc0 hcm i = a ↔ c a ≤ i ∧ (i : ℕ) < c (a + 1) := by
  have hspec := Nat.find_spec (exists_lt_cut hc0 hcm i)
  have hmin := fun {a' : ℕ} (h : a' < Nat.find (exists_lt_cut hc0 hcm i)) =>
    Nat.find_min (exists_lt_cut hc0 hcm i) h
  have hid : (cutIdx hc0 hcm i : ℕ) = Nat.find (exists_lt_cut hc0 hcm i) := rfl
  rw [Fin.ext_iff, hid]
  constructor
  · intro h
    rw [h] at hspec hmin
    refine ⟨?_, hspec.2⟩
    rcases Nat.eq_zero_or_pos (a : ℕ) with h0 | hpos
    · rw [h0, hc0]; exact Nat.zero_le _
    · have := hmin (a' := (a : ℕ) - 1) (by omega)
      have h2 : (a : ℕ) - 1 + 1 = a := by omega
      rw [h2] at this
      by_contra hlt
      exact this ⟨by omega, by omega⟩
  · rintro ⟨h1, h2⟩
    have hle : Nat.find (exists_lt_cut hc0 hcm i) ≤ a :=
      Nat.find_min' (exists_lt_cut hc0 hcm i) ⟨a.2, h2⟩
    refine le_antisymm hle ?_
    by_contra hlt
    push Not at hlt
    have := cuts_le_of_mono hmono (i := Nat.find (exists_lt_cut hc0 hcm i) + 1) (j := a)
      (by omega) (by omega)
    have h3 := hspec.2
    omega

noncomputable def cutBlockEquiv (hmono : ∀ i < m, c i < c (i + 1)) (hc0 : c 0 = 0)
    (hcm : c m = n) (a : Fin m) :
    Fin (c (a + 1) - c a) ≃ {i : Fin n // cutIdx hc0 hcm i = a} where
  toFun j :=
    ⟨⟨c a + j, by have := cuts_le_n hmono hcm (i := a + 1) (by omega); omega⟩,
      (cutIdx_eq_iff hmono hc0 hcm _ a).2 ⟨by simp, by have := j.2; simp; omega⟩⟩
  invFun i :=
    ⟨(i.1 : ℕ) - c a, by
      have := ((cutIdx_eq_iff hmono hc0 hcm _ a).1 i.2); omega⟩
  left_inv j := by
    apply Fin.ext
    simp
  right_inv i := by
    apply Subtype.ext
    apply Fin.ext
    have := ((cutIdx_eq_iff hmono hc0 hcm _ a).1 i.2)
    simp
    omega

theorem det_eq_prod_cutBlock_det_of_cuts {M : Matrix (Fin n) (Fin n) K}
    (hmono : ∀ i < m, c i < c (i + 1)) (hc0 : c 0 = 0) (hcm : c m = n)
    (hM : ∀ i, 0 < i → i < m → ∀ k l : Fin n, (l : ℕ) < c i → c i ≤ (k : ℕ) → M k l = 0) :
    M.det = ∏ a : Fin m,
      (cutBlock M (c a) (c (a + 1)) (cuts_le_n hmono hcm (Nat.succ_le_of_lt a.2))).det := by
  have htri : M.BlockTriangular (cutIdx hc0 hcm) := by
    intro k l hlk
    have hk := (cutIdx_eq_iff hmono hc0 hcm k (cutIdx hc0 hcm k)).1 rfl
    have hl := (cutIdx_eq_iff hmono hc0 hcm l (cutIdx hc0 hcm l)).1 rfl
    have hlk' : (cutIdx hc0 hcm l : ℕ) < cutIdx hc0 hcm k := hlk
    refine hM (cutIdx hc0 hcm k) (by omega) (cutIdx hc0 hcm k).2 k l ?_ hk.1
    exact lt_of_lt_of_le hl.2 (cuts_le_of_mono hmono (by omega) (cutIdx hc0 hcm k).2.le)
  rw [htri.det_fintype]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Matrix.det_submatrix_equiv_self (cutBlockEquiv hmono hc0 hcm a)]
  rfl

open CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.AGLEmbedding.ToralCensus in
theorem det_eq_prod_cutBlock_det {I : Set ℕ} {x : SpecialLinearGroup (Fin n) K}
    (hx : x ∈ flagStabilizer n K I) (hc0 : c 0 = 0) (hcm : c m = n)
    (hcons : ∀ i < m, IsConsecutiveCut n I (c i) (c (i + 1))) :
    (x : Matrix (Fin n) (Fin n) K).det = ∏ a : Fin m,
      (cutBlock (x : Matrix (Fin n) (Fin n) K) (c a) (c (a + 1)) (hcons a a.2).2.1).det := by
  have hmono : ∀ i < m, c i < c (i + 1) := fun i hi => (hcons i hi).1
  refine det_eq_prod_cutBlock_det_of_cuts hmono hc0 hcm ?_
  intro i hi0 him k l hl hk
  have hci : c i ≠ 0 := by
    have h1 := cuts_le_of_mono hmono (i := 1) (j := i) hi0 him.le
    have h2 := hmono 0 (by omega)
    omega
  exact apply_eq_zero_of_mem_flagStabilizer
    (Or.inr ((hcons i him).2.2.1.resolve_left hci)) hx hl hk

end DetBlocks

section Enumeration

open CFSG.AGLEmbedding

noncomputable def nextCut (n : ℕ) (I : Set ℕ) (a : ℕ) : ℕ := by
  classical
  exact if h : ∃ b, a < b ∧ b ≤ n ∧ (b = n ∨ b ∈ I) then Nat.find h else n

theorem nextCut_spec {n : ℕ} (I : Set ℕ) {a : ℕ} (ha : a < n) :
    a < nextCut n I a ∧ nextCut n I a ≤ n ∧ (nextCut n I a = n ∨ nextCut n I a ∈ I) ∧
      ∀ b, a < b → b ≤ n → (b = n ∨ b ∈ I) → nextCut n I a ≤ b := by
  classical
  have h : ∃ b, a < b ∧ b ≤ n ∧ (b = n ∨ b ∈ I) := ⟨n, ha, le_rfl, Or.inl rfl⟩
  have e : nextCut n I a = Nat.find h := by
    simp [nextCut, h]
  rw [e]
  exact ⟨(Nat.find_spec h).1, (Nat.find_spec h).2.1, (Nat.find_spec h).2.2,
    fun b hb hbn hbc => Nat.find_min' h ⟨hb, hbn, hbc⟩⟩

theorem nextCut_le (n : ℕ) (I : Set ℕ) (a : ℕ) : nextCut n I a ≤ n := by
  classical
  by_cases h : ∃ b, a < b ∧ b ≤ n ∧ (b = n ∨ b ∈ I)
  · have e : nextCut n I a = Nat.find h := by
      simp [nextCut, h]
    rw [e]
    exact (Nat.find_spec h).2.1
  · have e : nextCut n I a = n := by
      simp [nextCut, h]
    rw [e]

noncomputable def cutSeq (n : ℕ) (I : Set ℕ) (i : ℕ) : ℕ := (nextCut n I)^[i] 0

theorem cutSeq_zero (n : ℕ) (I : Set ℕ) : cutSeq n I 0 = 0 := by simp [cutSeq]

theorem cutSeq_succ (n : ℕ) (I : Set ℕ) (i : ℕ) :
    cutSeq n I (i + 1) = nextCut n I (cutSeq n I i) := by
  simp only [cutSeq, Function.iterate_succ_apply']

theorem cutSeq_le (n : ℕ) (I : Set ℕ) (i : ℕ) : cutSeq n I i ≤ n := by
  cases i with
  | zero => exact Nat.zero_le _
  | succ i => rw [cutSeq_succ]; exact nextCut_le n I _

theorem min_le_cutSeq (n : ℕ) (I : Set ℕ) (i : ℕ) : min i n ≤ cutSeq n I i := by
  induction i with
  | zero => simp [cutSeq_zero]
  | succ i ih =>
    rw [cutSeq_succ]
    by_cases hlt : cutSeq n I i < n
    · have := (nextCut_spec I hlt).1
      omega
    · have : cutSeq n I i = n := le_antisymm (cutSeq_le n I i) (not_lt.mp hlt)
      rw [this] at ih ⊢
      have h2 : nextCut n I n = n := by
        classical
        simp [nextCut]
        intro b hb1 hb2
        omega
      rw [h2]
      omega

theorem exists_cuts_enum (n : ℕ) (I : Set ℕ) :
    ∃ (m : ℕ) (c : ℕ → ℕ), c 0 = 0 ∧ c m = n ∧
      (∀ i < m, IsConsecutiveCut n I (c i) (c (i + 1))) ∧
      ∀ a b, IsConsecutiveCut n I a b → ∃ i < m, c i = a ∧ c (i + 1) = b := by
  classical
  have hex : ∃ i, cutSeq n I i = n := ⟨n, le_antisymm (cutSeq_le n I n)
    (by simpa using min_le_cutSeq n I n)⟩
  set m := Nat.find hex with hm
  have hcm : cutSeq n I m = n := Nat.find_spec hex
  have hlt : ∀ i < m, cutSeq n I i < n := fun i hi =>
    lt_of_le_of_ne (cutSeq_le n I i) (Nat.find_min hex hi)
  refine ⟨m, cutSeq n I, cutSeq_zero n I, hcm, ?_, ?_⟩
  · intro i hi
    have hspec := nextCut_spec I (hlt i hi)
    rw [← cutSeq_succ] at hspec
    refine ⟨hspec.1, hspec.2.1, ?_, hspec.2.2.1, fun c' hc' ⟨h1, h2⟩ => ?_⟩
    · rcases i with _ | i
      · exact Or.inl rfl
      · refine Or.inr ?_
        have := (nextCut_spec I (hlt i (by omega))).2.2.1
        rw [← cutSeq_succ] at this
        exact this.resolve_left (hlt (i + 1) hi).ne
    · have := hspec.2.2.2 c' h1 (by omega) (Or.inr hc')
      omega
  · rintro a b ⟨hab, hbn, ha, hb, hno⟩
    have hex2 : ∃ j, ¬ cutSeq n I j ≤ a := ⟨m, by rw [hcm]; omega⟩
    set j0 := Nat.find hex2 with hj0
    have hj0m : j0 ≤ m := Nat.find_min' hex2 (by rw [hcm]; omega)
    have hj0pos : 0 < j0 := by
      rcases Nat.eq_zero_or_pos j0 with h0 | h0
      · exfalso
        have := Nat.find_spec hex2
        rw [← hj0, h0, cutSeq_zero] at this
        exact this (Nat.zero_le _)
      · exact h0
    obtain ⟨i, hi⟩ : ∃ i, j0 = i + 1 := ⟨j0 - 1, by omega⟩
    have him : i < m := by omega
    have hci : cutSeq n I i ≤ a := by
      have := Nat.find_min hex2 (m := i) (by omega)
      exact not_not.mp this
    have hci1 : a < cutSeq n I (i + 1) := by
      have := Nat.find_spec hex2
      rw [← hj0, hi] at this
      exact not_le.mp this
    have hspec := nextCut_spec I (hlt i him)
    rw [← cutSeq_succ] at hspec
    have hca : cutSeq n I i = a := by
      refine le_antisymm hci (not_lt.mp fun hlt' => ?_)
      have := hspec.2.2.2 a hlt' (by omega) (by
        rcases ha with h0 | hI
        · omega
        · exact Or.inr hI)
      omega
    refine ⟨i, him, hca, ?_⟩
    have h1 := hspec.2.2.2 b (by omega) hbn hb
    rw [hca] at hspec
    by_contra hne
    have hlt2 : cutSeq n I (i + 1) < b := lt_of_le_of_ne h1 hne
    rcases hspec.2.2.1 with h | h
    · omega
    · exact hno _ h ⟨hspec.1, hlt2⟩
end Enumeration

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb
