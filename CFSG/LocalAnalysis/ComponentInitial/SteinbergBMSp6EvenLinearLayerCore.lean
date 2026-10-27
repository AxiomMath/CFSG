module

public import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelSelector
public import CFSG.YGroups.Y443.EvenPresentation

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SteinbergBM

open Subgroup LinearFlag GL3TwoFixedModel
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.YGroups.Y443 (z2Hom z2_cases z2Hom_ofAdd_one)

variable {Y : Type} [Group Y] {D : Subgroup Y} [D.Normal]

theorem conjNormal_mem_inner {a : Y} (ha : a ∈ D) : MulAut.conjNormal a ∈ inner D :=
  ⟨⟨a, ha⟩, MulEquiv.ext fun d => Subtype.ext (by
    change (⟨a, ha⟩ : D) * d * (⟨a, ha⟩ : D)⁻¹ = (MulAut.conjNormal a d : Y)
    rw [MulAut.conjNormal_apply]
    rfl)⟩

theorem orderOf_conjNormal {a : Y} (ha : orderOf a = 2) (hact : ∃ d ∈ D, a * d * a⁻¹ ≠ d) :
    orderOf (MulAut.conjNormal (H := D) a) = 2 := by
  refine orderOf_eq_prime ?_ fun h => ?_
  · rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  · obtain ⟨d, hd, hne⟩ := hact
    apply hne
    have h1 := congrArg (fun φ : MulAut D => ((φ ⟨d, hd⟩ : D) : Y)) h
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    exact h1

theorem subgroupOf_le_autFixed {a : Y} {S : Subgroup Y} (hSa : S ≤ centralizer {a}) :
    S.subgroupOf D ≤ autFixed (MulAut.conjNormal (H := D) a) := fun s hs => by
  rw [mem_autFixed]
  apply Subtype.ext
  rw [MulAut.conjNormal_apply]
  have h := mem_centralizer_singleton_iff.1 (hSa (mem_subgroupOf.1 hs))
  rw [← h, mul_inv_cancel_right]

theorem subgroupOf_normal_autFixed {a : Y} {S : Subgroup Y} (hSa : S ≤ centralizer {a})
    (hSn : (S.subgroupOf (centralizer {a})).Normal) :
    ((S.subgroupOf D).subgroupOf (autFixed (MulAut.conjNormal (H := D) a))).Normal := by
  constructor
  intro s hs g
  rw [mem_subgroupOf, mem_subgroupOf] at hs ⊢
  have hg : ((g : D) : Y) ∈ centralizer {a} := by
    have h1 := mem_autFixed.1 g.2
    rw [mem_centralizer_singleton_iff]
    have h2 := congrArg Subtype.val h1
    rw [MulAut.conjNormal_apply] at h2
    calc ((g : D) : Y) * a = a * ((g : D) : Y) * a⁻¹ * a := by rw [h2]
      _ = a * ((g : D) : Y) := by rw [inv_mul_cancel_right]
  have hs' : ((s : D) : Y) ∈ centralizer {a} := hSa hs
  have := hSn.conj_mem ⟨_, hs'⟩ (mem_subgroupOf.2 hs) ⟨_, hg⟩
  rw [mem_subgroupOf] at this
  exact this

theorem map_autFixed_conjNormal (a : Y) :
    (autFixed (MulAut.conjNormal (H := D) a)).map D.subtype = D ⊓ centralizer {a} := by
  ext y
  constructor
  · rintro ⟨d, hd, rfl⟩
    refine ⟨d.2, ?_⟩
    change (d : Y) ∈ centralizer {a}
    rw [mem_centralizer_singleton_iff]
    have h2 := congrArg Subtype.val (mem_autFixed.1 hd)
    rw [MulAut.conjNormal_apply] at h2
    calc (d : Y) * a = a * (d : Y) * a⁻¹ * a := by rw [h2]
      _ = a * (d : Y) := by rw [inv_mul_cancel_right]
  · rintro ⟨hyD, hya⟩
    refine ⟨⟨y, hyD⟩, ?_, rfl⟩
    change (⟨y, hyD⟩ : D) ∈ autFixed _
    rw [mem_autFixed]
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, ← mem_centralizer_singleton_iff.1 hya, mul_inv_cancel_right]

theorem even_linear_simple_layer_core [Finite Y] [IsSimpleGroup D] {a : Y}
    (ha : orderOf a = 2) (hact : ∃ d ∈ D, a * d * a⁻¹ ≠ d) {S : Subgroup Y} (hSD : S ≤ D)
    (hSa : S ≤ centralizer {a}) (hSn : (S.subgroupOf (centralizer {a})).Normal)
    [IsSimpleGroup S] (hSnab : ∃ x y : S, x * y ≠ y * x) (κ : S ≃* GL (Fin 3) (ZMod 2))
    {n f : ℕ} (hn : 2 ≤ n) (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = 2 ^ f)
    (η : D ≃* projectiveSL n K) :
    n = 3 ∧ f = 2 ∧ S = D ⊓ centralizer {a} ∧ Nat.card D = 20160 ∧
      ordProj[2] (Nat.card D) = 64 ∧ MulAut.conjNormal (H := D) a ∉ inner D ∧ a ∉ D ∧
      ∃ (hn3 : n = 3) (_ : CharP K 2) (σ : K ≃+* K), (∀ c, σ c = c ^ 2) ∧
        Function.Injective (binaryEmbed K hn3) ∧
        (binaryEmbed K hn3).range = autFixed (fieldAut n K σ) ∧
        ∃ (B : GL (Fin n) K) (e : ℕ), e ≤ 1 ∧
          (∀ d : D, (conjAut n K B * dualAut n K ^ e) (η (MulAut.conjNormal a d)) =
            fieldAut n K σ ((conjAut n K B * dualAut n K ^ e) (η d))) ∧
          ∀ s : S, (conjAut n K B * dualAut n K ^ e) (η ⟨s, hSD s.2⟩) =
            binaryEmbed K hn3 (κ s) := by
  set e' : S.subgroupOf D ≃* S := subgroupOfEquivOfLe hSD with he'
  have : IsSimpleGroup (S.subgroupOf D) := e'.isSimpleGroup
  have hS'nab : ∃ x y : S.subgroupOf D, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hSnab
    refine ⟨e'.symm x, e'.symm y, fun h => hxy ?_⟩
    have := congrArg e' h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
  obtain ⟨h3, h2, hfix, hout, hcard, hord, hn3, hchar, σ, hσ, hinj, hrange, B, e, he, hint, hlab⟩ :=
    even_projective_linear_involution_normal_GL3_two_fixed_model_selector hn hf hK η
      (orderOf_conjNormal ha hact) (subgroupOf_le_autFixed hSa)
      (subgroupOf_normal_autFixed hSa hSn) hS'nab (e'.trans κ)
  refine ⟨h3, h2, ?_, hcard, hord, hout, fun haD => hout (conjNormal_mem_inner haD), hn3,
    hchar, σ, hσ, hinj, hrange, B, e, he, hint, fun s => ?_⟩
  · have h1 := congrArg (Subgroup.map D.subtype) hfix
    rw [map_autFixed_conjNormal, subgroupOf_map_subtype, inf_eq_left.2 hSD] at h1
    exact h1
  · have h := hlab (e'.symm s)
    rw [MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at h
    exact h

@[expose] def fieldInvolHom {n : ℕ} {K : Type} [Field K] (σ : K ≃+* K)
    (hσ : ∀ c, σ (σ c) = c) : Multiplicative (ZMod 2) →* MulAut (projectiveSL n K) :=
  z2Hom (fieldAut n K σ) (by
    rw [← map_mul]
    have h : σ * σ = 1 := RingEquiv.ext hσ
    rw [h, map_one])

theorem fieldInvolHom_ofAdd_one {n : ℕ} {K : Type} [Field K] (σ : K ≃+* K)
    (hσ : ∀ c, σ (σ c) = c) :
    fieldInvolHom (n := n) σ hσ (Multiplicative.ofAdd 1) = fieldAut n K σ :=
  z2Hom_ofAdd_one _ _

theorem exists_layer_semidirect_equiv {a : Y} (ha : orderOf a = 2) (haD : a ∉ D) {n : ℕ}
    {K : Type} [Field K] (χ : D ≃* projectiveSL n K) (σ : K ≃+* K) (hσ : ∀ c, σ (σ c) = c)
    (hχ : ∀ d : D, χ (MulAut.conjNormal a d) = fieldAut n K σ (χ d)) :
    ∃ ψ : ↥(D ⊔ zpowers a) ≃*
        projectiveSL n K ⋊[fieldInvolHom σ hσ] Multiplicative (ZMod 2),
      (∀ d : D, ψ ⟨d, le_sup_left (a := D) d.2⟩ = SemidirectProduct.inl (χ d)) ∧
        ψ ⟨a, le_sup_right (a := D) (mem_zpowers a)⟩ =
          SemidirectProduct.inr (Multiplicative.ofAdd 1) := by
  set M := D ⊔ zpowers a with hM
  set a' : M := ⟨a, le_sup_right (a := D) (mem_zpowers a)⟩ with ha'
  have ha'2 : a' * a' = 1 := by
    apply Subtype.ext
    change a * a = 1
    rw [← pow_two, ← ha, pow_orderOf_eq_one]
  set f₁ : projectiveSL n K →* M := (inclusion (le_sup_left (a := D))).comp χ.symm.toMonoidHom
    with hf₁
  have hf₁v : ∀ p, ((f₁ p : M) : Y) = (χ.symm p : Y) := fun _ => rfl
  have hcompat : ∀ g : Multiplicative (ZMod 2),
      f₁.comp (fieldInvolHom (n := n) σ hσ g).toMonoidHom =
        (MulAut.conj (z2Hom a' ha'2 g)).toMonoidHom.comp f₁ := by
    intro g
    refine MonoidHom.ext fun p => Subtype.ext ?_
    rcases z2_cases g with rfl | rfl
    · simp
    · rw [fieldInvolHom_ofAdd_one, z2Hom_ofAdd_one]
      change (χ.symm (fieldAut n K σ p) : Y) = a * (χ.symm p : Y) * a⁻¹
      have h := hχ (χ.symm p)
      rw [MulEquiv.apply_symm_apply] at h
      rw [← h, MulEquiv.symm_apply_apply, MulAut.conjNormal_apply]
  set ψ' := SemidirectProduct.lift f₁ (z2Hom a' ha'2) hcompat with hψ'
  have hinj : Function.Injective ψ' := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [← SemidirectProduct.inl_left_mul_inr_right x, map_mul, SemidirectProduct.lift_inl,
      SemidirectProduct.lift_inr] at hx
    rcases z2_cases x.right with h | h
    · rw [h, map_one, mul_one] at hx
      have h1 : x.left = 1 := by
        have := congrArg (fun m : M => (m : Y)) hx
        simp only [hf₁v, OneMemClass.coe_one] at this
        have h2 : χ.symm x.left = 1 := Subtype.ext this
        rw [← map_one χ.symm] at h2
        exact χ.symm.injective h2
      exact SemidirectProduct.ext h1 h
    · rw [h, z2Hom_ofAdd_one] at hx
      exfalso
      apply haD
      have h1 : a' = (f₁ x.left)⁻¹ := eq_inv_of_mul_eq_one_right hx
      have h2 := congrArg (fun m : M => (m : Y)) h1
      simp only [InvMemClass.coe_inv, hf₁v] at h2
      change a = _ at h2
      rw [h2]
      exact D.inv_mem (χ.symm x.left).2
  have hsurj : Function.Surjective ψ' := by
    have hle : M ≤ ψ'.range.map M.subtype := by
      refine sup_le (fun d hd => ⟨ψ' (SemidirectProduct.inl (χ ⟨d, hd⟩)), ⟨_, rfl⟩, ?_⟩)
        (zpowers_le.2 ?_)
      · rw [SemidirectProduct.lift_inl]
        change (χ.symm (χ ⟨d, hd⟩) : Y) = d
        rw [MulEquiv.symm_apply_apply]
      · refine ⟨ψ' (SemidirectProduct.inr (Multiplicative.ofAdd 1)), ⟨_, rfl⟩, ?_⟩
        rw [SemidirectProduct.lift_inr, z2Hom_ofAdd_one]
        rfl
    intro m
    obtain ⟨m', ⟨x, rfl⟩, hm'⟩ := hle m.2
    exact ⟨x, Subtype.ext hm'⟩
  refine ⟨(MulEquiv.ofBijective ψ' ⟨hinj, hsurj⟩).symm, fun d => ?_, ?_⟩
  · rw [MulEquiv.symm_apply_eq]
    change _ = ψ' (SemidirectProduct.inl (χ d))
    rw [SemidirectProduct.lift_inl]
    apply Subtype.ext
    change (d : Y) = (χ.symm (χ d) : Y)
    rw [MulEquiv.symm_apply_apply]
  · rw [MulEquiv.symm_apply_eq]
    change _ = ψ' (SemidirectProduct.inr (Multiplicative.ofAdd 1))
    rw [SemidirectProduct.lift_inr, z2Hom_ofAdd_one]

end CFSG.LocalAnalysis.ComponentInitial.SteinbergBM
