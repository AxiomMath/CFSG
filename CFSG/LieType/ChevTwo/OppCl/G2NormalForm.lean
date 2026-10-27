module

public import CFSG.LieType.ChevTwo.OppositeFixedExcTri
public import CFSG.RankThree.PartTwo.KFacts.K71D4G2Group
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAutomorphisms
public import CFSG.LieType.Chevalley.OddF4CosetDescent

set_option linter.unusedSectionVars false

public section

namespace CFSG.LieType.ChevTwo.Semi

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartTwo.KFacts
  CFSG.ComponentClassification.UnbalancedCatalog

section Cert

variable
    {K : Type} [Field K] [Finite K]

theorem uniqueNormalFormOn_G2 {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) :
    UniqueNormalFormOn (graphFixedRootGroup TwistTag.D4 K (RingHom.id K)) := by
  have hf1 : 1 ≤ f := by omega
  haveI : CharP K 2 := charP_two_of_card_two_pow hK
  have hchar : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨hΓ, -, -, -, ⟨Ψ, hΨ, -, -⟩, hbase⟩ :=
    even_D4_pure_graph_fixed_group_exact_G2 (K := K) hchar
  rw [← hΓ]
  obtain ⟨hNF, -⟩ := even_G2_exact_automorphism_normal_form hf K hK
  intro α
  let αG : MulAut (adjointGroup Tag.G2 K) := (Ψ.symm.trans α).trans Ψ
  obtain ⟨⟨gG, σ⟩, hgσ, huniq⟩ := hNF αG
  have hmem : ∀ (σ : K ≃+* K) (h : ModGL TwistTag.D4.tag K),
      h ∈ twistedFixedGroup TwistTag.D4 K (RingHom.id K) →
        Units.map (entrywiseHom σ.toRingHom) h ∈ twistedFixedGroup TwistTag.D4 K (RingHom.id K) := by
    intro σ h hh
    rw [units_map_entrywiseHom_eq_baseChangeGL]
    exact (hbase K σ.toRingHom).1 h hh
  have hcomp : ∀ (σ : K ≃+* K) (h : twistedFixedGroup TwistTag.D4 K (RingHom.id K)),
      (Ψ ⟨Units.map (entrywiseHom σ.toRingHom) (h : ModGL TwistTag.D4.tag K), hmem σ h h.2⟩ :
        ModGL Tag.G2 K) = Units.map (entrywiseHom σ.toRingHom) (Ψ h : ModGL Tag.G2 K) := by
    intro σ h
    have h1 := (hbase K σ.toRingHom).2 h
      ⟨Units.map (entrywiseHom σ.toRingHom) (h : ModGL TwistTag.D4.tag K), hmem σ h h.2⟩
      (units_map_entrywiseHom_eq_baseChangeGL σ.toRingHom (h : ModGL TwistTag.D4.tag K))
    rw [hΨ, h1, hΨ h, units_map_entrywiseHom_eq_baseChangeGL]
  have key : ∀ (g : twistedFixedGroup TwistTag.D4 K (RingHom.id K)) (σ' : K ≃+* K),
      (∀ h : twistedFixedGroup TwistTag.D4 K (RingHom.id K),
        ((α h : twistedFixedGroup TwistTag.D4 K (RingHom.id K)) : ModGL TwistTag.D4.tag K) =
          (g : ModGL TwistTag.D4.tag K) *
            Units.map (entrywiseHom (σ' : K →+* K)) (h : ModGL TwistTag.D4.tag K) *
              (g : ModGL TwistTag.D4.tag K)⁻¹) ↔
      (∀ x : adjointGroup Tag.G2 K, (αG x : ModGL Tag.G2 K) = (Ψ g : ModGL Tag.G2 K) *
        Units.map (entrywiseHom σ'.toRingHom) (x : ModGL Tag.G2 K) * (Ψ g : ModGL Tag.G2 K)⁻¹) := by
    intro g σ'
    constructor
    · intro H x
      have e1 := H (Ψ.symm x)
      have e2 : α (Ψ.symm x) = g * ⟨Units.map (entrywiseHom σ'.toRingHom)
          ((Ψ.symm x : twistedFixedGroup TwistTag.D4 K (RingHom.id K)) : ModGL TwistTag.D4.tag K),
            hmem σ' _ (Ψ.symm x).2⟩ * g⁻¹ := Subtype.ext e1
      have e3 : αG x = Ψ g * Ψ ⟨Units.map (entrywiseHom σ'.toRingHom)
          ((Ψ.symm x : twistedFixedGroup TwistTag.D4 K (RingHom.id K)) : ModGL TwistTag.D4.tag K),
            hmem σ' _ (Ψ.symm x).2⟩ * (Ψ g)⁻¹ := by
        change Ψ (α (Ψ.symm x)) = _
        rw [e2, map_mul, map_mul, map_inv]
      rw [e3]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hcomp σ' (Ψ.symm x), MulEquiv.apply_symm_apply]
    · intro H h
      have e1 := H (Ψ h)
      have e3 : Ψ (α h) = Ψ (g * ⟨Units.map (entrywiseHom σ'.toRingHom)
          (h : ModGL TwistTag.D4.tag K), hmem σ' _ h.2⟩ * g⁻¹) := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
        rw [hcomp σ' h, ← e1]
        change (Ψ (α h) : ModGL Tag.G2 K) = (Ψ (α (Ψ.symm (Ψ h))) : ModGL Tag.G2 K)
        rw [MulEquiv.symm_apply_apply]
      have e4 := Ψ.injective e3
      have e5 := congrArg (fun y : twistedFixedGroup TwistTag.D4 K (RingHom.id K) =>
        (y : ModGL TwistTag.D4.tag K)) e4
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, RingEquiv.toRingHom_eq_coe] using e5
  refine ⟨(Ψ.symm gG, σ), (key _ _).2 (fun x => ?_), fun p hp => ?_⟩
  · simpa only [MulEquiv.apply_symm_apply] using hgσ x
  · have h1 := huniq (Ψ p.1, p.2) ((key p.1 p.2).1 hp)
    have h2 : Ψ p.1 = gG := (Prod.mk.inj h1).1
    have h3 : p.2 = σ := (Prod.mk.inj h1).2
    exact Prod.ext (Ψ.injective (by rw [h2, MulEquiv.apply_symm_apply])) h3

end Cert

end CFSG.LieType.ChevTwo.Semi
