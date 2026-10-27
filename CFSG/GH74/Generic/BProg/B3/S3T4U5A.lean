module

public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveUnitaryLocalComponent
public import CFSG.GH74.Generic.BProg.B3.S3T4L5A

public section

namespace CFSG.GH74.Generic.BProg.B3

open Module CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.LocalAnalysis.ComponentInitial.OddProjectivePair

namespace S3T4

section Abstract

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem le_of_forall_sub_mem' (htwo : (2 : K) ≠ 0) {A A' : Submodule K V} {r : ℕ}
    (b : Basis (Fin r) K A) (S : Set (V →ₗ[K] V)) (hsign : ∀ i, ∃ g ∈ S, g (b i) = -(b i : V))
    (h : ∀ g ∈ S, ∀ x, g x - x ∈ A') : A ≤ A' := by
  have hbi : ∀ i, (b i : V) ∈ A' := by
    intro i
    obtain ⟨g, hg, hgi⟩ := hsign i
    have h1 := h g hg (b i)
    rw [hgi] at h1
    have h2 : -(b i : V) - b i = (-2 : K) • (b i : V) := by
      rw [show (-2 : K) = -(1 + 1) by norm_num, neg_smul, add_smul, one_smul]
      abel
    rw [h2] at h1
    have h3 := A'.smul_mem (-2 : K)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ (neg_ne_zero.2 htwo), one_smul] at h3
  intro a ha
  have h1 : (⟨a, ha⟩ : A) = ∑ i, b.repr ⟨a, ha⟩ i • b i := (b.sum_repr _).symm
  have h2 := congrArg Subtype.val h1
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
  rw [h2]
  exact A'.sum_mem fun i _ => A'.smul_mem _ (hbi i)

theorem eq_zero_of_forall_fix' (htwo : (2 : K) ≠ 0) {A : Submodule K V} {r : ℕ}
    (b : Basis (Fin r) K A) (S : Set (V →ₗ[K] V))
    (hsign : ∀ i, ∃ g ∈ S, ∃ d : Fin r → K, d i = -1 ∧ ∀ k, g (b k) = d k • (b k : V))
    {a : V} (ha : a ∈ A) (h : ∀ g ∈ S, g a = a) : a = 0 := by
  set c := b.repr ⟨a, ha⟩ with hcdef
  have hsum : a = ∑ k, c k • (b k : V) := by
    have h1 : (⟨a, ha⟩ : A) = ∑ k, c k • b k := (b.sum_repr _).symm
    have h2 := congrArg Subtype.val h1
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using h2
  have hc : ∀ i, c i = 0 := by
    intro i
    obtain ⟨g, hg, d, hdi, hgd⟩ := hsign i
    have h1 := h g hg
    rw [hsum, map_sum] at h1
    simp only [map_smul, hgd, smul_smul] at h1
    have h2 : (∑ k, (c k * d k) • b k : A) = ∑ k, c k • b k := by
      apply Subtype.ext
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using h1
    have h3 := congrArg (fun x => b.repr x i) h2
    simp only [b.repr_sum_self] at h3
    rw [hdi] at h3
    have h4 : (2 : K) * c i = 0 := by linear_combination -h3
    exact (mul_eq_zero.1 h4).resolve_left htwo
  rw [hsum]
  exact Finset.sum_eq_zero fun k _ => by rw [hc k, zero_smul]

theorem le_of_summand_eq' (htwo : (2 : K) ≠ 0) {A₁ W₁ A₂ W₂ : Submodule K V}
    (h₂ : IsCompl A₂ W₂) {r₁ r₂ : ℕ} (b₁ : Basis (Fin r₁) K A₁) (b₂ : Basis (Fin r₂) K A₂)
    (S : Set (V →ₗ[K] V)) (hS₁W : ∀ g ∈ S, ∀ w ∈ W₁, g w = w)
    (hS₂ : ∀ g ∈ S, (∀ w ∈ W₂, g w = w) ∧ ∀ a ∈ A₂, g a ∈ A₂)
    (hsign₁ : ∀ i, ∃ g ∈ S, g (b₁ i) = -(b₁ i : V))
    (hsign₂ : ∀ i, ∃ g ∈ S, ∃ d : Fin r₂ → K, d i = -1 ∧ ∀ k, g (b₂ k) = d k • (b₂ k : V)) :
    A₁ ≤ A₂ ∧ W₁ ≤ W₂ := by
  constructor
  · refine le_of_forall_sub_mem' htwo b₁ S hsign₁ fun g hg x => ?_
    obtain ⟨hgW, hgA⟩ := hS₂ g hg
    obtain ⟨a, ha, w, hw, rfl⟩ :=
      Submodule.mem_sup.1 (h₂.sup_eq_top ▸ Submodule.mem_top : x ∈ A₂ ⊔ W₂)
    rw [map_add, hgW w hw, add_sub_add_right_eq_sub]
    exact A₂.sub_mem (hgA a ha) ha
  · intro x hx
    obtain ⟨a, ha, w, hw, rfl⟩ :=
      Submodule.mem_sup.1 (h₂.sup_eq_top ▸ Submodule.mem_top : x ∈ A₂ ⊔ W₂)
    have ha0 : a = 0 := by
      refine eq_zero_of_forall_fix' htwo b₂ S hsign₂ ha fun g hg => ?_
      have h1 := hS₁W g hg _ hx
      rw [map_add, (hS₂ g hg).1 w hw] at h1
      exact add_right_cancel h1
    rw [ha0, zero_add]
    exact hw

theorem mul_eq_smul_of_eigen {A W : Submodule K V} (hc : IsCompl A W) {T₁ T₂ : V →ₗ[K] V}
    {c₁ c₂ : K} (hA₁ : ∀ a ∈ A, T₁ a = c₁ • a) (hW₁ : ∀ w ∈ W, T₁ w = -(c₁ • w))
    (hA₂ : ∀ a ∈ A, T₂ a = c₂ • a) (hW₂ : ∀ w ∈ W, T₂ w = -(c₂ • w)) :
    T₁ * T₂ = (c₁ * c₂) • 1 := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨a, ha, w, hw, rfl⟩ :=
    Submodule.mem_sup.1 (hc.sup_eq_top ▸ Submodule.mem_top : x ∈ A ⊔ W)
  rw [Module.End.mul_apply, map_add, hA₂ a ha, hW₂ w hw, map_add, map_neg, map_smul, map_smul,
    hA₁ a ha, hW₁ w hw, LinearMap.smul_apply, Module.End.one_apply, smul_add, smul_smul,
    smul_neg, neg_neg, smul_smul, mul_comm c₂ c₁]

end Abstract

section Unitary

variable {p f : ℕ} {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]
  {h : UnitaryFieldData p f E} {B : V →ₛₗ[h.bar] V →ₗ[E] E}

omit [AddCommGroup V] [Module E V] in
theorem bar_signs (h : UnitaryFieldData p f E) {r : ℕ} (i j k : Fin r) :
    h.bar (signs i j k) = signs i j k := by
  simp only [signs]
  split_ifs <;> simp

theorem exists_sign_mem_summand [FiniteDimensional E V] (hB : B.IsSymm) {A W : Submodule E V}
    (hc : IsCompl A W) (horth : ∀ a ∈ A, ∀ w ∈ W, B a w = 0)
    (hsepA : (B.domRestrict₁₂ A A).SeparatingLeft) (hA2 : 2 ≤ finrank E A) :
    ∃ b : Basis (Fin (finrank E A)) E A, ∀ i, ∃ g ∈ summandUnitarySet B A W,
      ∃ d : Fin (finrank E A) → E, d i = -1 ∧ ∀ k, unitaryOp g (b k) = d k • (b k : V) := by
  have hAs : (B.domRestrict₁₂ A A).IsSymm := ⟨fun x y => hB.eq x y⟩
  obtain ⟨b, hb⟩ := h.exists_orthonormal_basis (M := A) hAs hsepA
  refine ⟨b, fun i => ?_⟩
  obtain ⟨j, hj⟩ := exists_fin_ne hA2 i
  set d : Fin (finrank E A) → E := signs i j with hd
  set D : Module.End E A := Matrix.toLin b b (Matrix.diagonal d) with hD
  have hDb : ∀ k, D (b k) = d k • b k := by
    intro k
    rw [hD, Matrix.toLin_self]
    simp [Matrix.diagonal_apply]
  have hDD' : D * D = 1 := b.ext fun k => by
    rw [Module.End.mul_apply, hDb, map_smul, hDb, smul_smul, hd, signs_mul_self, one_smul,
      Module.End.one_apply]
  have hDD : Function.Involutive D := fun x => by
    rw [← Module.End.mul_apply, hDD', Module.End.one_apply]
  set gA : LinearMap.GeneralLinearGroup E A :=
    LinearMap.GeneralLinearGroup.ofLinearEquiv (LinearEquiv.ofInvolutive D hDD) with hgAdef
  have hgA_apply : ∀ x, ((gA : LinearMap.GeneralLinearGroup E A) : Module.End E A) x = D x :=
    fun x => rfl
  have hgA : gA ∈ sesqSpecialUnitaryGroup (B.domRestrict₁₂ A A) := by
    rw [mem_sesqSpecialUnitaryGroup]
    refine ⟨?_, ?_⟩
    · rw [mem_sesqUnitaryGroup]
      have hext : ((B.domRestrict₁₂ A A).comp (gA : A →ₗ[E] A)).compl₂ (gA : A →ₗ[E] A) =
          B.domRestrict₁₂ A A := by
        refine LinearMap.ext_basis b b fun k l => ?_
        rw [LinearMap.compl₂_apply, LinearMap.comp_apply, hgA_apply, hgA_apply, hDb, hDb,
          LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, smul_eq_mul, hb, hd, bar_signs]
        by_cases hkl : k = l
        · subst hkl
          simp only [ite_true, mul_one]
          exact signs_mul_self i j k
        · simp only [hkl, ite_false, mul_zero]
      intro x y
      have := LinearMap.congr_fun₂ hext x y
      rwa [LinearMap.compl₂_apply, LinearMap.comp_apply] at this
    · change LinearMap.det D = 1
      rw [hD, LinearMap.det_toLin, Matrix.det_diagonal, hd, prod_signs]
  obtain ⟨hmem, hS⟩ := glConj_symm_summandGL_mem hB hc horth hgA
  refine ⟨⟨_, hmem⟩, hS, d, signs_left hj.symm, fun k => ?_⟩
  change ((glConj (Submodule.prodEquivOfIsCompl A W hc).symm (summandGL E A W gA) :
    LinearMap.GeneralLinearGroup E V) : Module.End E V) (b k) = _
  rw [glConj_apply, LinearEquiv.symm_symm, show (Submodule.prodEquivOfIsCompl A W hc).symm (b k) =
      (b k, 0) from Submodule.prodEquivOfIsCompl_symm_apply_left A W hc (b k), summandGL_apply,
    Submodule.coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, add_zero, hgA_apply, hDb,
    Submodule.coe_smul]

theorem mul_eq_smul_of_summand_eq (hp : p ≠ 2) [FiniteDimensional E V] (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) {T₁ T₂ : sesqUnitaryGroup B} {l₁ l₂ : E} (hl₁ : l₁ ≠ 0)
    (hl₂ : l₂ ≠ 0) (hAA₁ : unitaryOp T₁ * unitaryOp T₁ = (l₁ ^ 2) • 1)
    (hAA₂ : unitaryOp T₂ * unitaryOp T₂ = (l₂ ^ 2) • 1) (hN₁ : h.norm l₁ = 1)
    (hN₂ : h.norm l₂ = 1) (hm₁ : 2 ≤ finrank E (eigenPlus l₁ (unitaryOp T₁)))
    (hm₂ : 2 ≤ finrank E (eigenPlus l₂ (unitaryOp T₂)))
    (heq : summandUnitarySet B (eigenPlus l₁ (unitaryOp T₁)) (eigenMinus l₁ (unitaryOp T₁)) =
      summandUnitarySet B (eigenPlus l₂ (unitaryOp T₂)) (eigenMinus l₂ (unitaryOp T₂))) :
    unitaryOp T₁ * unitaryOp T₂ = (l₁ * l₂) • 1 := by
  have := h.finite
  have h2 := two_ne_zero_of_odd h hp
  obtain ⟨horth₁, hsep₁, -, -⟩ := exists_split_centralizer_equiv hp hB hBl hl₁ hAA₁ hN₁
  obtain ⟨horth₂, hsep₂, -, -⟩ := exists_split_centralizer_equiv hp hB hBl hl₂ hAA₂ hN₂
  have hc₁ : IsCompl (eigenPlus l₁ (unitaryOp T₁)) (eigenMinus l₁ (unitaryOp T₁)) :=
    isCompl_ker_sub_one_ker_add_one h2 (invSMulOp_mul_self hl₁ hAA₁)
  have hc₂ : IsCompl (eigenPlus l₂ (unitaryOp T₂)) (eigenMinus l₂ (unitaryOp T₂)) :=
    isCompl_ker_sub_one_ker_add_one h2 (invSMulOp_mul_self hl₂ hAA₂)
  obtain ⟨b₁, hb₁⟩ := exists_sign_mem_summand hB hc₁ horth₁ hsep₁ hm₁
  obtain ⟨b₂, hb₂⟩ := exists_sign_mem_summand hB hc₂ horth₂ hsep₂ hm₂
  set S : Set (V →ₗ[E] V) := unitaryOp '' summandUnitarySet B (eigenPlus l₁ (unitaryOp T₁))
    (eigenMinus l₁ (unitaryOp T₁)) with hSdef
  have hS₁ : ∀ g ∈ S, (∀ w ∈ eigenMinus l₁ (unitaryOp T₁), g w = w) ∧
      ∀ a ∈ eigenPlus l₁ (unitaryOp T₁), g a ∈ eigenPlus l₁ (unitaryOp T₁) := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨hg.1, hg.2.1⟩
  have hS₂ : ∀ g ∈ S, (∀ w ∈ eigenMinus l₂ (unitaryOp T₂), g w = w) ∧
      ∀ a ∈ eigenPlus l₂ (unitaryOp T₂), g a ∈ eigenPlus l₂ (unitaryOp T₂) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [heq] at hg
    exact ⟨hg.1, hg.2.1⟩
  have hsign : ∀ {A : Submodule E V} {r : ℕ} (b : Basis (Fin r) E A),
      (∀ i, ∃ g ∈ summandUnitarySet B (eigenPlus l₁ (unitaryOp T₁))
        (eigenMinus l₁ (unitaryOp T₁)), ∃ d : Fin r → E, d i = -1 ∧
          ∀ k, unitaryOp g (b k) = d k • (b k : V)) →
      ∀ i, ∃ g ∈ S, ∃ d : Fin r → E, d i = -1 ∧ ∀ k, g (b k) = d k • (b k : V) := by
    intro A r b hb i
    obtain ⟨g, hg, d, hdi, hgd⟩ := hb i
    exact ⟨_, ⟨g, hg, rfl⟩, d, hdi, hgd⟩
  have hsign₁ := hsign b₁ hb₁
  have hsign₂ := hsign b₂ (by rw [heq]; exact hb₂)
  have hneg : ∀ {A : Submodule E V} {r : ℕ} (b : Basis (Fin r) E A),
      (∀ i, ∃ g ∈ S, ∃ d : Fin r → E, d i = -1 ∧ ∀ k, g (b k) = d k • (b k : V)) →
      ∀ i, ∃ g ∈ S, g (b i) = -(b i : V) := by
    intro A r b hb i
    obtain ⟨g, hg, d, hdi, hgd⟩ := hb i
    exact ⟨g, hg, by rw [hgd, hdi, neg_one_smul]⟩
  obtain ⟨hA12, hW12⟩ := le_of_summand_eq' h2 hc₂ b₁ b₂ S (fun g hg => (hS₁ g hg).1) hS₂
    (hneg b₁ hsign₁) hsign₂
  obtain ⟨hA21, hW21⟩ := le_of_summand_eq' h2 hc₁ b₂ b₁ S (fun g hg => (hS₂ g hg).1) hS₁
    (hneg b₂ hsign₂) hsign₁
  have hA := le_antisymm hA12 hA21
  have hW := le_antisymm hW12 hW21
  have hplus : ∀ {l : E} {T : Module.End E V}, l ≠ 0 → ∀ a ∈ eigenPlus l T, T a = l • a := by
    intro l T hl a ha
    rw [eigenPlus_eq_ker hl, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, sub_eq_zero] at ha
    exact ha
  have hminus : ∀ {l : E} {T : Module.End E V}, l ≠ 0 → ∀ w ∈ eigenMinus l T,
      T w = -(l • w) := by
    intro l T hl w hw
    rw [eigenMinus_eq_ker hl, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply, add_eq_zero_iff_eq_neg] at hw
    exact hw
  refine mul_eq_smul_of_eigen hc₁ (hplus hl₁) (hminus hl₁) (fun a ha => hplus hl₂ a ?_)
    (fun w hw => hminus hl₂ w ?_)
  · rw [← hA]; exact ha
  · rw [← hW]; exact hw

end Unitary

end S3T4

end CFSG.GH74.Generic.BProg.B3
