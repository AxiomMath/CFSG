module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieRoot
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiTwoAAutomorphisms
public import CFSG.LieType.Chevalley.ExactG2FiniteOrder
public import CFSG.Quasithin.EmptyFaithfulMultiple.G2TwoUnitary
public import CFSG.Timmesfeld.Orders.Classical
import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog

section Small

theorem not_kOrder_6048 : ¬ KOrder 6048 := by
  rintro (h | h | ⟨p, -, hp7, hp⟩)
  · omega
  · omega
  · have hp23 : p < 23 := by
      by_contra hc
      push Not at hc
      have : 23 * (23 * 23 - 1) ≤ p * (p * p - 1) :=
        Nat.mul_le_mul hc (Nat.sub_le_sub_right (Nat.mul_le_mul hc hc) 1)
      omega
    interval_cases p <;> omega

theorem card_psu_three_three {M : Type} [Group M]
    (hM : CFSG.Assembly.LowTwoRank.StatedClassicalModel M .PSU 3 3 1) : Nat.card M = 6048 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three hM

theorem g2Two_derived
    {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2) :
    IsSimpleGroup ↥(commutator ↥(adjointGroup .G2 k)) ∧
      Nat.card ↥(commutator ↥(adjointGroup .G2 k)) = 6048 := by
  have hLie := CFSG.Quasithin.EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds k hk
  rcases hLie with ⟨-, hM⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · obtain ⟨-, hsimple⟩ := CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 3 1 hM
    have hcard := card_psu_three_three hM
    have hDM : (commutator ↥(adjointGroup .G2 k)).map (adjointGroup .G2 k).subtype =
        ⁅adjointGroup .G2 k, adjointGroup .G2 k⁆ := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    let eD : ↥(commutator ↥(adjointGroup .G2 k)) ≃*
        ↥⁅adjointGroup .G2 k, adjointGroup .G2 k⁆ :=
      ((commutator ↥(adjointGroup .G2 k)).equivMapOfInjective _
        (adjointGroup .G2 k).subtype_injective).trans (MulEquiv.subgroupCongr hDM)
    have := hsimple
    exact ⟨eD.isSimpleGroup, by rw [Nat.card_congr eD.toEquiv, hcard]⟩
  all_goals exact absurd h0 (by norm_num)

end Small

section Components

theorem isSimpleGroup_adjointGroup_g2
    {k : Type} [Field k] [Finite k] (hk : 3 ≤ Nat.card k) :
    IsSimpleGroup ↥(adjointGroup .G2 k) := by
  have hq := CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card k hk
  have hZ : Subgroup.center ↥(adjointGroup .G2 k) = ⊥ := center_adjointGroup_eq_bot
  exact CFSG.LieType.Simplicity.isSimpleGroup_of_mulEquiv hq
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm

theorem g2_not_hasKComponent
    {k : Type} [Field k] [Finite k] {m : ℕ} (hm : 1 ≤ m)
    (hk : Nat.card k = 2 ^ m) : ¬ HasKComponent ↥(adjointGroup .G2 k) := by
  rcases Nat.lt_or_ge 1 m with hm2 | hm1
  ·
    have hsimple : IsSimpleGroup ↥(adjointGroup .G2 k) := by
      refine isSimpleGroup_adjointGroup_g2 ?_
      rw [hk]
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    obtain ⟨-, h2, -⟩ := exact_G2_finite_order k (q := 2 ^ m) hk
    refine not_hasKComponent_of_isSimpleGroup (b := 2 * m)
      (m := ((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1)) (by omega)
      (Nat.odd_mul.mpr ⟨CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_sub_one hm (by norm_num),
        CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_sub_one hm (by norm_num)⟩) ?_
    rw [h2]
    ring
  ·
    have hm1' : m = 1 := le_antisymm hm1 hm
    have hk2 : Nat.card k = 2 := by rw [hk, hm1', pow_one]
    obtain ⟨hDsimple, hDcard⟩ := g2Two_derived hk2
    have := hDsimple
    exact not_hasKComponent_of_commutator_simple (by rw [hDcard]; exact not_kOrder_6048)

end Components

theorem g2Even_core
    {Γ : Type} [Group Γ] {f : ℕ} (hf2 : 2 ≤ f)
    (hmodel : ChevalleyExceptionalModel Γ .G2 2 f) (a : MulAut Γ) (ha : a * a = 1)
    (h0 : HasKComponent ↥(fixSubgroup a)) : False := by
  obtain ⟨-, F, _, _, hF, ⟨e₀⟩⟩ := hmodel
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := by
    have : Fintype F := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hF])
  have hZ : Subgroup.center ↥(adjointGroup .G2 F) = ⊥ := center_adjointGroup_eq_bot
  let e : Γ ≃* ↥(adjointGroup .G2 F) :=
    e₀.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
  obtain ⟨α, hαdef⟩ : ∃ α : MulAut ↥(adjointGroup .G2 F), α = MulAut.congr e a := ⟨_, rfl⟩
  have hαα : α * α = 1 := by rw [hαdef, ← map_mul, ha, map_one]
  have h1 : HasKComponent ↥(fixSubgroup α) := by
    rw [hαdef]
    exact hasKComponent_fixSubgroup_of_intertwine e a _
      (mulAut_congr_apply_self e a) h0
  by_cases hα1 : α = 1
  ·
    rw [hα1] at h1
    exact g2_not_hasKComponent (m := f) (by omega) hF (hasKComponent_of_fixSubgroup_one h1)
  have hα2 : orderOf α = 2 := orderOf_eq_prime (by rwa [pow_two]) hα1
  rcases even_G2_involution_inner_or_canonical_field hf2 F hF α hα2 with hin | ⟨hev, hδ⟩
  ·
    exact not_hasKComponent_fix_of_inner hZ
      (fun y hy B => rootWeightDatum_involution_centralizer_component_free
        (RootWeightDatum.ordinary (K := F) .G2) y hy B) hαα hα1 hin h1
  ·
    obtain ⟨m, hm⟩ := hev
    have hm1 : 1 ≤ m := by omega
    obtain ⟨φ₀, hφ₀, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
        Nat.prime_two (by omega) hF
    have hσ : ∀ c, (φ₀ ^ m) c = c ^ 2 ^ m :=
      CFSG.LocalAnalysis.ComponentInitial.ringAut_pow_apply_of_sq hφ₀ m
    obtain ⟨β, ψ, hβ, hψ, -⟩ := hδ (φ₀ ^ m).toRingHom fun c => by
      rw [show f / 2 = m by omega]
      exact hσ c
    have hβδ : β = entrywiseAdjointAut .G2 (φ₀ ^ m) :=
      MulEquiv.ext fun u => Subtype.ext (by rw [hβ u, coe_entrywiseAdjointAut])
    have hK2 : Nat.card F = 2 ^ (2 * m) := by rw [hF, show f = 2 * m by omega]
    obtain ⟨-, hk, -, hFix, -⟩ := even_G2_canonical_field_full_centralizer hm1 F hK2 (φ₀ ^ m) hσ
    have hint : ∀ y, β (ψ y) = ψ (α y) := fun y => by
      rw [← hψ, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
    have h2 : HasKComponent ↥(fixSubgroup β) :=
      hasKComponent_fixSubgroup_of_intertwine ψ α β hint h1
    rw [hβδ] at h2
    have e₁ : ↥(adjointGroup .G2 (fixSubfield (φ₀ ^ m))) ≃*
        ↥(fixedFieldImage .G2 (φ₀ ^ m)) :=
      (adjointGroup .G2 (fixSubfield (φ₀ ^ m))).equivMapOfInjective _ (baseChangeGL_injective _)
    have e₂ : ↥(fixSubgroup (entrywiseAdjointAut .G2 (φ₀ ^ m))) ≃*
        ↥(adjointGroup .G2 (fixSubfield (φ₀ ^ m))) :=
      (((fixSubgroup (entrywiseAdjointAut .G2 (φ₀ ^ m))).equivMapOfInjective
        (adjointGroup .G2 F).subtype (adjointGroup .G2 F).subtype_injective).trans
        (MulEquiv.subgroupCongr hFix)).trans e₁.symm
    have : Finite (fixSubfield (φ₀ ^ m)) := Subtype.finite
    exact g2_not_hasKComponent hm1 hk (h2.of_mulEquiv e₂)

theorem tabIdentFor_g2Even
    : TabIdentFor @Ident.FamG2Even := by
  intro G _ _ X K t hs hX
  obtain ⟨-, f, hf2, hmodel⟩ := hX
  exact (g2Even_core hf2 hmodel (hs.conjAut : MulAut ↥X) hs.conjAut_mul_self
    hs.hasKComponent_fix).elim

end CFSG.QuasithinUnique.Id2519
