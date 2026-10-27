module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamCore
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2Defs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddExc

public noncomputable section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
  CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LieType.Ree (ReeTag)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

@[expose] def Cl24ExcInnerDiag (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 → Nat.card K = p ^ f →
    ∀ (α : MulAut (adjointGroup τ K)) (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ),
      (∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
        (h : ModGL τ K) * (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹) → orderOf α = 2 →
      ∀ L : Subgroup (fixedSubgroup α), IsComponent L → Cl24Q p (fun f' => f' = f) L

theorem cl24_exp_eq_two_mul {K : Type} [Finite K] {p f e : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p ^ f) (hKe : Nat.card K = (p ^ e) ^ 2) : f = 2 * e :=
  Nat.pow_right_injective hp.two_le
    (show p ^ f = p ^ (2 * e) by rw [← hK, hKe, ← pow_mul, mul_comm])

section


variable {K : Type} [Field K] [Finite K]

theorem cl24_odd_field
    {t : StatedLieTag} {τ : Tag}
    (htτ : t = .G2 ∧ τ = .G2 ∨ t = .F4 ∧ τ = .F4 ∨ t = .E6 ∧ τ = .E6 ∨ t = .E7 ∧ τ = .E7 ∨
      t = .E8 ∧ τ = .E8) {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hKe : Nat.card K = (p ^ e) ^ 2) (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ (p ^ e))
    {α : MulAut (adjointGroup τ K)} {g : adjointGroup τ K} {a : Fin τ.rank → Kˣ}
    (hαg : ∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
      Units.map (entrywiseHom δ.toRingHom) (h : ModGL τ K) * (rootDiagUnit τ a)⁻¹ *
        (g : ModGL τ K)⁻¹)
    (hα : α ^ 2 = 1) {X : Type} [Group X] (Ψ : X ≃* fixedSubgroup α) {L : Subgroup X}
    (hL : IsComponent L) : Cl24Q p (fun f' => f' = e) L := by
  obtain ⟨E⟩ := odd_field_component_equiv hp hp2 he hKe δ hδ hαg hα Ψ hL
  have hk := card_fixSubfield_of_sq_pow hp he hKe δ hδ
  have h3 := three_le_pow_of_odd_prime hp hp2 he
  have hadm : StatedLieAdmissible t 0 p e := by
    rcases htτ with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact ⟨hp, he, rfl, h3⟩
    all_goals exact ⟨hp, he, rfl⟩
  exact ⟨t, 0, e, rfl, hadm, lieModel_centralQuotient_of_mulEquiv_adjointGroup htτ hadm hk E⟩

theorem cl24_odd_F4_E8_G2_explicit
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E8 ∨ τ = .G2) (hinner : Cl24ExcInnerDiag τ)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : τ = .G2 → p ≠ 3) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (β : MulAut (adjointGroup τ K)) (hβ : orderOf β = 2)
    {X : Type} [Group X] (Ψ : X ≃* fixedSubgroup β) {L : Subgroup X} (hL : IsComponent L) :
    Cl24Q p (fun f' => f' = f ∨ f = 2 * f') L := by
  have hβ2 : β ^ 2 = 1 := hβ ▸ pow_orderOf_eq_one β
  have hchar := ringChar_eq_of_card hp hf hK
  have hKodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hτ' : τ = .F4 ∨ τ = .E8 ∨ (τ = .G2 ∧ ringChar K ≠ 3) := by
    rcases hτ with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨h, hchar ▸ hp3 h⟩)
  rcases odd_F4_E8_G2_involution_inner_or_quadratic hτ' hKodd hβ2 with ⟨g, a, hβg⟩ |
    ⟨q, e, hq, he, hKe, δ, hδ, g, a, hβg⟩
  · exact (cl24_of_component_equiv Ψ (hinner K p f hp hp2 hK β g a hβg hβ) hL).mono
      fun _ h => Or.inl h
  · have hqp : q = p := by
      have h : q ∣ p ^ f := by
        rw [← hK, hKe]
        exact dvd_pow (dvd_pow_self q (by omega)) two_ne_zero
      exact (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h)
    subst hqp
    have htτ : (StatedLieTag.F4 = .F4 ∧ τ = .F4 ∨ StatedLieTag.E8 = .E8 ∧ τ = .E8) ∨
        τ = .G2 := by
      rcases hτ with h | h | h
      · exact Or.inl (Or.inl ⟨rfl, h⟩)
      · exact Or.inl (Or.inr ⟨rfl, h⟩)
      · exact Or.inr h
    have hf2 := cl24_exp_eq_two_mul hp hK hKe
    rcases htτ with (⟨-, rfl⟩ | ⟨-, rfl⟩) | rfl
    · exact (cl24_odd_field (t := .F4) (Or.inr (Or.inl ⟨rfl, rfl⟩)) hq hp2 he hKe
        δ hδ hβg hβ2 Ψ hL).mono fun _ h => Or.inr (by omega)
    · exact (cl24_odd_field (t := .E8)
        (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))) hq hp2 he hKe δ hδ hβg hβ2 Ψ hL).mono
        fun _ h => Or.inr (by omega)
    · exact (cl24_odd_field (t := .G2) (Or.inl ⟨rfl, rfl⟩) hq hp2 he hKe δ hδ
        hβg hβ2 Ψ hL).mono fun _ h => Or.inr (by omega)

theorem cl24_family_of_explicit
    {t : StatedLieTag} {τ : Tag} (ht : t ∈ chevalleyExceptionalTags)
    (hmodel : ∀ (J : Type) [Group J] (p f : ℕ), ChevalleyExceptionalModel J t p f →
      UntwistedChevalleyModel J τ (p ^ f))
    (hexp : ∀ (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
      Nat.card K = p ^ f → ∀ β : MulAut (adjointGroup τ K), orderOf β = 2 →
        ∀ (X : Type) [Group X], (X ≃* fixedSubgroup β) → ∀ L : Subgroup X, IsComponent L →
          Cl24Q p (fun f' => f' = f ∨ f = 2 * f') L) :
    Cl24OddFamily t := by
  intro J _ n p f hp hp2 hadm hm α hα Kc hKc
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ
    (hmodel J p f (GH74.chevalleyExceptionalModel_of_lieModel ht hm))
  have hβ : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  exact Or.inl ((hexp F p f hp hp2 hadm.2.1 hF _ hβ _ (fixedSubgroupCongrEquiv e α) Kc
    hKc).mono fun _ h => by unfold Cl24FieldRel; omega)

end

end CFSG.OddStandard.SmallF3.HypA2Leaves
