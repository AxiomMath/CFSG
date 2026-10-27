module

public import CFSG.ClassicalInvolution.Q3.TA3FrameBase
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Sp4Fix
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvShape

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3.Q3T.MFS QuaternionGroup
open scoped MatrixGroups

@[expose] def LayerExcludesQ8 (X : Type) [Group X] (t : X) : Prop :=
  ∀ φ : QuaternionGroup 2 →* X, Function.Injective φ →
    (∀ x, φ x ∈ Subgroup.centralizer ({t} : Set X)) →
    (∀ K : Subgroup X, IsComponentOf K (Subgroup.centralizer ({t} : Set X)) →
      ∀ x, ∀ k ∈ K, φ x * k = k * φ x) → False

section Transport

variable {X X' : Type} [Group X] [Group X']

theorem map_centralizer (e : X ≃* X') (t : X) :
    (Subgroup.centralizer ({e t} : Set X')).map e.symm.toMonoidHom =
      Subgroup.centralizer ({t} : Set X) := by
  ext x
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, e.injective.eq_iff]

theorem isComponentOf_map (e : X ≃* X') {t : X} {K : Subgroup X'}
    (hK : IsComponentOf K (Subgroup.centralizer ({e t} : Set X'))) :
    IsComponentOf (K.map e.symm.toMonoidHom) (Subgroup.centralizer ({t} : Set X)) := by
  refine ⟨?_, ?_, ComponentClassification.Components.quasisimple_of_equiv
    (K.equivMapOfInjective _ e.symm.injective).symm hK.2.2⟩
  · rw [← map_centralizer e t]
    exact Subgroup.map_mono hK.1
  · rw [← map_centralizer e t]
    exact ComponentClassification.Components.chain_map _ hK.2.1

theorem LayerExcludesQ8.of_mulEquiv (e : X ≃* X') {t : X} (h : LayerExcludesQ8 X' (e t)) :
    LayerExcludesQ8 X t := by
  intro φ hφ hC hK
  refine h (e.toMonoidHom.comp φ) (e.injective.comp hφ) (fun x => ?_) (fun K' hK' x k hk => ?_)
  · have := Subgroup.mem_centralizer_singleton_iff.mp (hC x)
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
    rw [← map_mul, ← map_mul, this]
  · have h1 := hK _ (isComponentOf_map e hK') x (e.symm k)
      (Subgroup.mem_map_equiv.mpr (by rwa [MulEquiv.symm_symm, MulEquiv.apply_symm_apply]))
    have h2 := congrArg e h1
    simp only [map_mul, MulEquiv.apply_symm_apply] at h2
    exact h2

end Transport

section Member

variable {Y : Type} [Group Y] [Finite Y] {z : Y} {L T : Subgroup Y}

omit [Finite Y] in
theorem map_centralizer_subtype {z' : T} :
    (Subgroup.centralizer ({z'} : Set T)).map T.subtype =
      T ⊓ Subgroup.centralizer ({(z' : Y)} : Set Y) := by
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨w.2, ?_⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hw
  · intro hy
    obtain ⟨hyT, hyc⟩ := Subgroup.mem_inf.mp hy
    refine ⟨⟨y, hyT⟩, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hyc
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext hyc

theorem false_of_layerExcludesQ8 [T.Normal] (hL : IsClassicalMember3 L z) (hTL : T ⊔ L = ⊤)
    (h3 : memberIndex L T = 3) (h : LayerExcludesQ8 T ⟨z, mem_of_member hL hTL h3⟩) : False := by
  obtain ⟨φ, hφ, hφLT⟩ := exists_q8 hL hTL h3
  let φ' : QuaternionGroup 2 →* T := φ.codRestrict T fun x => (hφLT x).2
  refine h φ' (fun x y hxy => hφ (congrArg Subtype.val hxy)) (fun x => ?_)
    (fun K' hK' x k hk => ?_)
  · rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hL.le_centralizer (hφLT x).1)
  · have hK : IsComponentOf (K'.map T.subtype) (T ⊓ Subgroup.centralizer ({z} : Set Y)) := by
      refine ⟨?_, ?_, ComponentClassification.Components.quasisimple_of_equiv
        (K'.equivMapOfInjective _ T.subtype_injective).symm hK'.2.2⟩
      · rw [← map_centralizer_subtype (z' := ⟨z, mem_of_member hL hTL h3⟩)]
        exact Subgroup.map_mono hK'.1
      · rw [← map_centralizer_subtype (z' := ⟨z, mem_of_member hL hTL h3⟩)]
        exact ComponentClassification.Components.chain_map _ hK'.2.1
    exact Subtype.ext (commute_of_isComponentOf hL hK _ (hφLT x).1 _ ⟨k, hk, rfl⟩)

end Member

section Criteria

variable {X : Type} [Group X]

theorem isComponentOf_of_normal {C K : Subgroup X} (hKC : K ≤ C) (hn : (K.subgroupOf C).Normal)
    (hq : CFSG.Open.IsQuasisimple K) : IsComponentOf K C :=
  ⟨hKC, IsSubnormal.step hKC hn (IsSubnormal.refl C), hq⟩

theorem isQuasisimple_of_equiv_sl2 {K : Subgroup X} {F : Type} [Field F] [Finite F]
    (h4 : 4 ≤ Nat.card F) (e : K ≃* SL(2, F)) : CFSG.Open.IsQuasisimple K := by
  obtain ⟨hp, hs, -⟩ := GH74.GLS.IVK.GHInv.isQuasisimple_sl2 h4
  exact ComponentClassification.Components.quasisimple_of_equiv e ⟨hp.commutator_eq_top, hs⟩

theorem commute_of_mem_sup {g : X} {K₁ K₂ : Subgroup X} (h₁ : ∀ k ∈ K₁, g * k = k * g)
    (h₂ : ∀ k ∈ K₂, g * k = k * g) : ∀ h ∈ K₁ ⊔ K₂, g * h = h * g := by
  have hle : K₁ ⊔ K₂ ≤ Subgroup.centralizer ({g} : Set X) :=
    sup_le (fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr (h₁ k hk).symm)
      (fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr (h₂ k hk).symm)
  exact fun h hh => (Subgroup.mem_centralizer_singleton_iff.mp (hle hh)).symm

theorem layerExcludesQ8_of_cent {t : X} {K : Subgroup X}
    (hK : IsComponentOf K (Subgroup.centralizer ({t} : Set X)))
    (hab : ∀ a ∈ Subgroup.centralizer ({t} : Set X), ∀ b ∈ Subgroup.centralizer ({t} : Set X),
      (∀ k ∈ K, a * k = k * a) → (∀ k ∈ K, b * k = k * b) → a ^ 2 ≠ 1 → b ^ 2 ≠ 1 →
        a * b = b * a) : LayerExcludesQ8 X t := by
  intro φ hφ hC hK'
  have hsq : ∀ q : QuaternionGroup 2, q ^ 2 ≠ 1 → φ q ^ 2 ≠ 1 := fun q hq h =>
    hq (hφ (by rw [map_pow, h, map_one]))
  have hc := hab _ (hC (a 1)) _ (hC (xa 0)) (hK' K hK (a 1)) (hK' K hK (xa 0))
    (hsq _ (by decide)) (hsq _ (by decide))
  rw [← map_mul, ← map_mul] at hc
  exact absurd (hφ hc) (by decide)

theorem layerExcludesQ8_of_noQ8Fix (hZ : Subgroup.center X = ⊥) {t : X} {H : Subgroup X}
    (hH : ∀ g ∈ Subgroup.centralizer ({t} : Set X),
      (∀ K, IsComponentOf K (Subgroup.centralizer ({t} : Set X)) → ∀ k ∈ K, g * k = k * g) →
        ∀ h ∈ H, g * h = h * g)
    (hfix : NoQ8Fix X H) : LayerExcludesQ8 X t := by
  intro φ hφ hC hK
  refine hfix (MulAut.conj.comp φ) (fun x y hxy => hφ ?_) fun q h hh => ?_
  · have h1 : (φ y)⁻¹ * φ x ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun α : MulAut X => α g) hxy
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulAut.conj_apply] at this
      calc g * ((φ y)⁻¹ * φ x) = (φ y)⁻¹ * (φ y * g * (φ y)⁻¹) * φ x := by group
        _ = (φ y)⁻¹ * (φ x * g * (φ x)⁻¹) * φ x := by rw [this]
        _ = (φ y)⁻¹ * φ x * g := by group
    rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact h1.symm
  · show φ q * h * (φ q)⁻¹ = h
    rw [hH _ (hC q) (fun K hK' k hk => hK K hK' q k hk) h hh, mul_inv_cancel_right]

theorem layerExcludesQ8_of_sl2Pair [Finite X] (hF : TwoSubgroupsFourGenerated X) {t : X}
    {K₁ K₂ H₁ H₂ : Subgroup X}
    (hK₁ : IsComponentOf K₁ (Subgroup.centralizer ({t} : Set X)))
    (hK₂ : IsComponentOf K₂ (Subgroup.centralizer ({t} : Set X))) (h₁ : H₁ ≤ K₁) (h₂ : H₂ ≤ K₂)
    (hc : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a) {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁]
    [Finite F₂] (hF₁ : Odd (Nat.card F₁)) (hF₂ : Odd (Nat.card F₂)) (e₁ : H₁ ≃* SL(2, F₁))
    (e₂ : H₂ ≃* SL(2, F₂)) : LayerExcludesQ8 X t := by
  intro φ hφ _ hK
  obtain ⟨ψ₁, hψ₁, hψ₁H, -⟩ := exists_q8_of_mulEquiv_sl2 hF₁ H₁ e₁
  obtain ⟨ψ₂, hψ₂, hψ₂H, -⟩ := exists_q8_of_mulEquiv_sl2 hF₂ H₂ e₂
  have hgen : GH74.Gen4 (X ⧸ (⊥ : Subgroup X)) := GH74.Gen4.quotient ⊥ hF
  refine GH74.Filter.Lie.not_gen4_quotient_of_Q8_cube ⊥ bot_le ![φ, ψ₁, ψ₂] ?_ ?_ hgen
  · intro i
    fin_cases i
    exacts [hφ, hψ₁, hψ₂]
  · have c01 : ∀ x y, Commute (φ x) (ψ₁ y) := fun x y => hK K₁ hK₁ x _ (h₁ (hψ₁H y))
    have c02 : ∀ x y, Commute (φ x) (ψ₂ y) := fun x y => hK K₂ hK₂ x _ (h₂ (hψ₂H y))
    have c12 : ∀ x y, Commute (ψ₁ x) (ψ₂ y) := fun x y => hc _ (hψ₁H x) _ (hψ₂H y)
    intro i j hij x y
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    exacts [c01 x y, c02 x y, (c01 y x).symm, c12 x y, (c02 y x).symm, (c12 y x).symm]

end Criteria

end CFSG.ClassicalInvolution.Q3.TA3.Frame
