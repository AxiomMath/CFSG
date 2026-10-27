module

public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverLarge

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour CFSG.LocalAnalysis.ComponentInitial.LinearCover
open Matrix

namespace L3Core

section SL

variable {F : Type} [Field F]

theorem coe_hei (a b c : F) :
    ((wMat c * xMat a * yMat b : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, a, c + a * b; 0, 1, b; 0, 0, 1] := by
  change wM c * xM a * yM b = _
  simp only [wM, xM, yM, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [add_comm]

theorem sl_hei_inj {a b c a' b' c' : F}
    (h : (wMat c * xMat a * yMat b : SpecialLinearGroup (Fin 3) F) =
      wMat c' * xMat a' * yMat b') : a = a' ∧ b = b' ∧ c = c' := by
  have h' := congrArg (fun g : SpecialLinearGroup (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) h
  simp only [coe_hei] at h'
  have h01 := congrFun (congrFun h' 0) 1
  have h12 := congrFun (congrFun h' 1) 2
  have h02 := congrFun (congrFun h' 0) 2
  simp at h01 h12 h02
  subst h01 h12
  exact ⟨rfl, rfl, by simpa using h02⟩

variable [CharP F 2]

theorem sl_hei_mul (a b c a' b' c' : F) :
    (wMat c * xMat a * yMat b) * (wMat c' * xMat a' * yMat b') =
      wMat (c + c' + a' * b) * xMat (a + a') * yMat (b + b') := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  apply Subtype.ext
  change wM c * xM a * yM b * (wM c' * xM a' * yM b') = wM _ * xM _ * yM _
  simp only [wM, xM, yM, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  all_goals first | exact add_comm _ _ | linear_combination (-(a' * b)) * h2

omit [CharP F 2] in
theorem mem_unitriangular_hei (a b c : F) :
    wMat c * xMat a * yMat b ∈ unitriangular 3 F :=
  mul_mem (mul_mem (wMat_mem_unitriangular c) (xMat_mem_unitriangular a))
    (yMat_mem_unitriangular b)

end SL

section Projective

variable {F : Type} [Field F]

@[expose] def hei (a b c : F) : projectiveSL 3 F := wP c * xP a * yP b

theorem hei_eq_proj (a b c : F) : hei a b c = proj 3 F (wMat c * xMat a * yMat b) := by
  simp only [hei, wP, xP, yP, map_mul]

theorem hei_inj {a b c a' b' c' : F} (h : hei a b c = hei a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  rw [hei_eq_proj, hei_eq_proj] at h
  exact sl_hei_inj (proj_injOn_unitriangular 3 (mem_unitriangular_hei a b c)
    (mem_unitriangular_hei a' b' c') h)

theorem hei_congr {a b c a' b' c' : F} (ha : a = a') (hb : b = b') (hc : c = c') :
    hei a b c = hei a' b' c' := by
  subst ha hb hc
  rfl

theorem hei_zero : hei (0 : F) 0 0 = 1 := by
  rw [hei, (xP_eq_one_iff (0 : F)).mpr rfl, (yP_eq_one_iff (0 : F)).mpr rfl,
    (wP_eq_one_iff (0 : F)).mpr rfl, mul_one, mul_one]

theorem hei_zero_zero (c : F) : hei 0 0 c = wP c := by
  rw [hei, (xP_eq_one_iff (0 : F)).mpr rfl, (yP_eq_one_iff (0 : F)).mpr rfl, mul_one, mul_one]

theorem hei_zero_c (a b : F) : hei a b 0 = xP a * yP b := by
  rw [hei, (wP_eq_one_iff (0 : F)).mpr rfl, one_mul]

theorem hei_eq_wP_mul (a b c : F) : hei a b c = wP c * hei a b 0 := by
  rw [hei_zero_c, hei, mul_assoc]

theorem hei_mem (a b c : F) : hei a b c ∈ projUnitriangular 3 F :=
  Subgroup.mem_map_of_mem _ (mem_unitriangular_hei a b c)

theorem exists_hei {s : projectiveSL 3 F} (hs : s ∈ projUnitriangular 3 F) [CharP F 2] :
    ∃ a b c : F, s = hei a b c := by
  obtain ⟨a, b, c, h⟩ := (projRoots (K := F)).mem_S s hs
  exact ⟨a, b, c, h⟩

variable [CharP F 2]

theorem hei_mul (a b c a' b' c' : F) :
    hei a b c * hei a' b' c' = hei (a + a') (b + b') (c + c' + a' * b) := by
  simp only [hei_eq_proj, ← map_mul, sl_hei_mul]

theorem hei_sq (a b c : F) : hei a b c * hei a b c = hei 0 0 (a * b) := by
  rw [hei_mul]
  refine hei_congr (CharTwo.add_self_eq_zero a) (CharTwo.add_self_eq_zero b) ?_
  rw [add_assoc, ← add_assoc c, CharTwo.add_self_eq_zero, zero_add, mul_comm]

theorem hei_inv (a b c : F) : (hei a b c)⁻¹ = hei a b (c + a * b) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [hei_mul, ← hei_zero]
  refine hei_congr (CharTwo.add_self_eq_zero a) (CharTwo.add_self_eq_zero b) ?_
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination (c + a * b) * h2

theorem hei_conj_y (a b c b' : F) :
    hei 0 b' 0 * hei a b c * (hei 0 b' 0)⁻¹ * (hei a b c)⁻¹ = hei 0 0 (a * b') := by
  rw [hei_inv, hei_inv, hei_mul, hei_mul, hei_mul]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  refine hei_congr ?_ ?_ ?_
  · linear_combination a * h2
  · linear_combination (b + b') * h2
  · linear_combination (c + a * b' + a * b) * h2

@[expose] def invDiag (s : Fin 3 → F) : Fin 3 → F := fun i => (s i)⁻¹

omit [CharP F 2] in
theorem invDiag_prod {s : Fin 3 → F} (hs : s 0 * s 1 * s 2 = 1) :
    invDiag s 0 * invDiag s 1 * invDiag s 2 = 1 := by
  simp only [invDiag]
  rw [← mul_inv, ← mul_inv, hs, inv_one]

omit [CharP F 2] in
theorem diagSL_mul_invDiag {s : Fin 3 → F} (hs : s 0 * s 1 * s 2 = 1) :
    diagSL s hs * diagSL (invDiag s) (invDiag_prod hs) = 1 := by
  apply Subtype.ext
  change diagonal s * diagonal (invDiag s) = 1
  rw [diagonal_mul_diagonal]
  have : (fun i => s i * invDiag s i) = fun _ => (1 : F) :=
    funext fun i => mul_inv_cancel₀ (diag_ne_zero hs i)
  rw [this, diagonal_one]

omit [CharP F 2] in
theorem torus_conj_hei (s : Fin 3 → F) (hs : s 0 * s 1 * s 2 = 1) (a b c : F) :
    proj 3 F (diagSL s hs) * hei a b c * (proj 3 F (diagSL s hs))⁻¹ =
      hei (s 0 * (s 1)⁻¹ * a) (s 1 * (s 2)⁻¹ * b) (s 0 * (s 2)⁻¹ * c) := by
  have e : proj 3 F (diagSL s hs) * hei a b c * (proj 3 F (diagSL s hs))⁻¹ =
      (proj 3 F (diagSL s hs) * wP c * (proj 3 F (diagSL s hs))⁻¹) *
      (proj 3 F (diagSL s hs) * xP a * (proj 3 F (diagSL s hs))⁻¹) *
      (proj 3 F (diagSL s hs) * yP b * (proj 3 F (diagSL s hs))⁻¹) := by
    unfold hei
    group
  rw [e, projDiag_conj_wP, projDiag_conj_xP, projDiag_conj_yP]
  rfl

theorem torus_mem_normalizer (s : Fin 3 → F) (hs : s 0 * s 1 * s 2 = 1) :
    proj 3 F (diagSL s hs) ∈ Subgroup.normalizer
      ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) := by
  have key : ∀ (s : Fin 3 → F) (hs : s 0 * s 1 * s 2 = 1) (g : projectiveSL 3 F),
      g ∈ projUnitriangular 3 F →
        proj 3 F (diagSL s hs) * g * (proj 3 F (diagSL s hs))⁻¹ ∈ projUnitriangular 3 F := by
    intro s hs g hg
    obtain ⟨a, b, c, rfl⟩ := exists_hei hg
    rw [torus_conj_hei]
    exact hei_mem _ _ _
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨key s hs g, fun hg => ?_⟩
  have hinv : (proj 3 F (diagSL s hs))⁻¹ = proj 3 F (diagSL (invDiag s) (invDiag_prod hs)) := by
    rw [inv_eq_iff_mul_eq_one, ← map_mul, diagSL_mul_invDiag, map_one]
  have h2 := key (invDiag s) (invDiag_prod hs) _ hg
  rw [← hinv, inv_inv] at h2
  have e : (proj 3 F (diagSL s hs))⁻¹ * (proj 3 F (diagSL s hs) * g *
      (proj 3 F (diagSL s hs))⁻¹) * proj 3 F (diagSL s hs) = g := by
    group
  rwa [e] at h2

theorem isElemAbelian_of_a_zero {R₀ : Subgroup (projectiveSL 3 F)}
    (h0 : ∀ r ∈ R₀, ∃ b c : F, r = hei 0 b c) : IsElemAbelian 2 R₀ := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨b, c, hx'⟩ := h0 x x.2
    obtain ⟨b', c', hy'⟩ := h0 y y.2
    apply Subtype.ext
    show (x : projectiveSL 3 F) * y = y * x
    rw [hx', hy', hei_mul, hei_mul]
    exact hei_congr (add_comm _ _) (add_comm _ _) (by rw [zero_mul, zero_mul, add_comm c])
  · obtain ⟨b, c, hx'⟩ := h0 x hx
    rw [hx', sq, hei_sq, zero_mul]
    exact hei_zero

theorem isElemAbelian_of_b_zero {R₀ : Subgroup (projectiveSL 3 F)}
    (h0 : ∀ r ∈ R₀, ∃ a c : F, r = hei a 0 c) : IsElemAbelian 2 R₀ := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, c, hx'⟩ := h0 x x.2
    obtain ⟨a', c', hy'⟩ := h0 y y.2
    apply Subtype.ext
    show (x : projectiveSL 3 F) * y = y * x
    rw [hx', hy', hei_mul, hei_mul]
    exact hei_congr (add_comm _ _) (add_comm _ _) (by rw [mul_zero, mul_zero, add_comm c])
  · obtain ⟨a, c, hx'⟩ := h0 x hx
    rw [hx', sq, hei_sq, mul_zero]
    exact hei_zero

theorem card_le_sq_of_isElemAbelian [Finite F] {A₀ : Subgroup (projectiveSL 3 F)}
    (hA : A₀ ≤ projUnitriangular 3 F) (hE : IsElemAbelian 2 A₀) :
    Nat.card A₀ ≤ Nat.card F ^ 2 := by
  have hex : ∀ x : A₀, ∃ p : F × F × F, (x : projectiveSL 3 F) = hei p.1 p.2.1 p.2.2 := fun x => by
    obtain ⟨a, b, c, h⟩ := exists_hei (hA x.2)
    exact ⟨(a, b, c), h⟩
  choose p hp using hex
  have hsq : ∀ x : A₀, (p x).1 * (p x).2.1 = 0 := fun x => by
    have h := hE.2 (x : projectiveSL 3 F) x.2
    rw [sq, hp x, hei_sq] at h
    exact (hei_inj (h.trans hei_zero.symm)).2.2
  have hcomm : ∀ x y : A₀, (p x).1 * (p y).2.1 = (p y).1 * (p x).2.1 := fun x y => by
    have h : (x : projectiveSL 3 F) * y = y * x := congrArg Subtype.val (hE.1.is_comm.comm x y)
    rw [hp x, hp y, hei_mul, hei_mul] at h
    have := (hei_inj h).2.2
    linear_combination (-1 : F) * this
  have hdich : (∀ x : A₀, (p x).1 = 0) ∨ (∀ x : A₀, (p x).2.1 = 0) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hcon
    have hxb : (p x).2.1 = 0 := (mul_eq_zero.mp (hsq x)).resolve_left hx
    have hya : (p y).1 = 0 := (mul_eq_zero.mp (hsq y)).resolve_right hy
    have h := hcomm x y
    rw [hxb, hya, zero_mul] at h
    exact (mul_eq_zero.mp h).elim hx hy
  have hinj : Function.Injective (fun x : A₀ => ((p x).1 + (p x).2.1, (p x).2.2)) := by
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    apply Subtype.ext
    rw [hp x, hp y]
    rcases hdich with h | h
    · rw [h x, h y, zero_add, zero_add] at h1
      exact hei_congr (by rw [h x, h y]) h1 h2
    · rw [h x, h y, add_zero, add_zero] at h1
      exact hei_congr h1 (by rw [h x, h y]) h2
  calc Nat.card A₀ ≤ Nat.card (F × F) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card F ^ 2 := by rw [Nat.card_prod, sq]

theorem eq_projUnitriangular_of_normalized [Finite F] (h8 : 8 ≤ Nat.card F)
    {R₀ : Subgroup (projectiveSL 3 F)} (hRU : R₀ ≤ projUnitriangular 3 F)
    (hU : ∀ g ∈ projUnitriangular 3 F, ∀ r ∈ R₀, g * r * g⁻¹ ∈ R₀)
    (hT : ∀ (s : Fin 3 → F) (hs : s 0 * s 1 * s 2 = 1), ∀ r ∈ R₀,
      proj 3 F (diagSL s hs) * r * (proj 3 F (diagSL s hs))⁻¹ ∈ R₀)
    (hnot : ¬ IsElemAbelian 2 R₀) : R₀ = projUnitriangular 3 F := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨a₁, b₁, c₁, ha₁, h₁⟩ : ∃ a b c : F, a ≠ 0 ∧ hei a b c ∈ R₀ := by
    by_contra hcon
    push Not at hcon
    refine hnot (isElemAbelian_of_a_zero fun r hr => ?_)
    obtain ⟨a, b, c, rfl⟩ := exists_hei (hRU hr)
    have ha : a = 0 := by
      by_contra ha
      exact hcon a b c ha hr
    exact ⟨b, c, by rw [ha]⟩
  obtain ⟨a₂, b₂, c₂, hb₂, h₂'⟩ : ∃ a b c : F, b ≠ 0 ∧ hei a b c ∈ R₀ := by
    by_contra hcon
    push Not at hcon
    refine hnot (isElemAbelian_of_b_zero fun r hr => ?_)
    obtain ⟨a, b, c, rfl⟩ := exists_hei (hRU hr)
    have hb : b = 0 := by
      by_contra hb
      exact hcon a b c hb hr
    exact ⟨a, c, by rw [hb]⟩
  have hZ : ∀ z : F, wP z ∈ R₀ := by
    intro z
    have h := R₀.mul_mem (hU (hei 0 (a₁⁻¹ * z) 0) (hei_mem _ _ _) _ h₁) (R₀.inv_mem h₁)
    rw [hei_conj_y, mul_inv_cancel_left₀ ha₁, hei_zero_zero] at h
    exact h
  have hW : ∀ x y z : F, hei x y z ∈ R₀ ↔ hei x y 0 ∈ R₀ := by
    intro x y z
    rw [hei_eq_wP_mul x y z]
    constructor
    · intro h
      have := R₀.mul_mem (R₀.inv_mem (hZ z)) h
      simpa using this
    · intro h
      exact R₀.mul_mem (hZ z) h
  have hadd : ∀ a b a' b' : F, hei a b 0 ∈ R₀ → hei a' b' 0 ∈ R₀ →
      hei (a + a') (b + b') 0 ∈ R₀ := by
    intro a b a' b' h h'
    have := R₀.mul_mem h h'
    rw [hei_mul] at this
    exact (hW _ _ _).mp this
  have hscale : ∀ u : F, u ≠ 0 → ∀ a b : F, hei a b 0 ∈ R₀ → hei (u * a) (u * b) 0 ∈ R₀ := by
    intro u hu a b h
    have hs : (![u, 1, u⁻¹] : Fin 3 → F) 0 * (![u, 1, u⁻¹] : Fin 3 → F) 1 *
        (![u, 1, u⁻¹] : Fin 3 → F) 2 = 1 := by
      simp [hu]
    have := hT ![u, 1, u⁻¹] hs _ h
    rw [torus_conj_hei] at this
    simpa using this
  have hshear : ∀ v : F, v ≠ 0 → ∀ a b : F, hei a b 0 ∈ R₀ → hei (v⁻¹ * a) (v * v * b) 0 ∈ R₀ := by
    intro v hv a b h
    have hs : (![1, v, v⁻¹] : Fin 3 → F) 0 * (![1, v, v⁻¹] : Fin 3 → F) 1 *
        (![1, v, v⁻¹] : Fin 3 → F) 2 = 1 := by
      simp [hv]
    have := hT ![1, v, v⁻¹] hs _ h
    rw [torus_conj_hei] at this
    simpa using this
  obtain ⟨v, hv0, hv3⟩ : ∃ v : F, v ≠ 0 ∧ v ^ 3 ≠ 1 := by
    obtain ⟨t, ht⟩ := exists_units_pow_three_ne_one h8
    refine ⟨t, t.ne_zero, fun h => ht (Units.ext ?_)⟩
    simpa using h
  have hv3' : 1 + v ^ 3 ≠ 0 := fun h => hv3 (by linear_combination h - h2)
  have hvv : v⁻¹ * v = 1 := inv_mul_cancel₀ hv0
  have hm₁ : hei a₁ b₁ 0 ∈ R₀ := (hW _ _ _).mp h₁
  have hm₂ : hei a₂ b₂ 0 ∈ R₀ := (hW _ _ _).mp h₂'
  have hx : ∀ a : F, hei a 0 0 ∈ R₀ := by
    obtain ⟨a₀, ha₀, h₀⟩ : ∃ a₀ : F, a₀ ≠ 0 ∧ hei a₀ 0 0 ∈ R₀ := by
      have h3 := hadd _ _ _ _ (hshear v hv0 a₁ b₁ hm₁) (hscale (v * v) (mul_ne_zero hv0 hv0) a₁ b₁ hm₁)
      refine ⟨v⁻¹ * a₁ + v * v * a₁, ?_, ?_⟩
      · intro h0
        have h4 : v⁻¹ * a₁ * (1 + v ^ 3) = 0 := by
          have : v⁻¹ * a₁ * (1 + v ^ 3) = v⁻¹ * a₁ + v * v * a₁ := by
            linear_combination (a₁ * v ^ 2) * hvv
          rw [this, h0]
        exact hv3' ((mul_eq_zero.mp h4).resolve_left (mul_ne_zero (inv_ne_zero hv0) ha₁))
      · have e : v * v * b₁ + v * v * b₁ = 0 := by linear_combination (v * v * b₁) * h2
        rw [e] at h3
        exact h3
    intro a
    by_cases ha : a = 0
    · rw [ha, hei_zero]
      exact R₀.one_mem
    · have := hscale (a * a₀⁻¹) (mul_ne_zero ha (inv_ne_zero ha₀)) a₀ 0 h₀
      rwa [inv_mul_cancel_right₀ ha₀, mul_zero] at this
  have hy : ∀ b : F, hei 0 b 0 ∈ R₀ := by
    obtain ⟨b₀, hb₀, h₀⟩ : ∃ b₀ : F, b₀ ≠ 0 ∧ hei 0 b₀ 0 ∈ R₀ := by
      have h3 := hadd _ _ _ _ (hshear v hv0 a₂ b₂ hm₂) (hscale v⁻¹ (inv_ne_zero hv0) a₂ b₂ hm₂)
      refine ⟨v * v * b₂ + v⁻¹ * b₂, ?_, ?_⟩
      · intro h0
        have h4 : v⁻¹ * b₂ * (1 + v ^ 3) = 0 := by
          have : v⁻¹ * b₂ * (1 + v ^ 3) = v * v * b₂ + v⁻¹ * b₂ := by
            linear_combination (b₂ * v ^ 2) * hvv
          rw [this, h0]
        exact hv3' ((mul_eq_zero.mp h4).resolve_left (mul_ne_zero (inv_ne_zero hv0) hb₂))
      · have e : v⁻¹ * a₂ + v⁻¹ * a₂ = 0 := by linear_combination (v⁻¹ * a₂) * h2
        rw [e] at h3
        exact h3
    intro b
    by_cases hb : b = 0
    · rw [hb, hei_zero]
      exact R₀.one_mem
    · have := hscale (b * b₀⁻¹) (mul_ne_zero hb (inv_ne_zero hb₀)) 0 b₀ h₀
      rwa [inv_mul_cancel_right₀ hb₀, mul_zero] at this
  refine le_antisymm hRU (fun g hg => ?_)
  obtain ⟨a, b, c, rfl⟩ := exists_hei hg
  refine (hW a b c).mpr ?_
  have := hadd a 0 0 b (hx a) (hy b)
  rwa [add_zero, zero_add] at this

end Projective

end L3Core

end CFSG.QuasithinUnique.Lin2
