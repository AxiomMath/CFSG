module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2SwapOverlap
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotNeighbourLevi

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint
open CFSG.Quasithin (perfectCore perfectCore_le)
open scoped commutatorElement Pointwise

section E7Step

variable {τ : Tag} {K : Type} [Field K]

theorem canonicalRep_conj_pinnedX_of_charTwo [CharP K 2] (w : WeylGroup τ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (c : K) :
    canonicalRep (coxeterSystem τ) K w * pinnedX τ K γ c * (canonicalRep (coxeterSystem τ) K w)⁻¹ =
      pinnedX τ K (w • γ) c := by
  obtain ⟨ε, hε, hεc⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w hγ
  have hε1 : ε = 1 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have : (ε - 1) * (ε - 1) = 0 := by linear_combination hε + (1 - ε) * h2
    exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
  rw [hεc, hε1, one_mul]

variable (K) in
@[expose] noncomputable def canonicalRepElt (w : WeylGroup τ) : adjointGroup τ K :=
  ⟨canonicalRep (coxeterSystem τ) K w, canonicalRep_mem_adjointGroup _ K w⟩

theorem map_conj_canonicalRep_rootPairSL2 [CharP K 2] (w : WeylGroup τ) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) :
    (rootPairSL2 τ K γ).map (MulAut.conj (canonicalRepElt K w)).toMonoidHom =
      rootPairSL2 τ K (w • γ) := by
  rw [map_rootPairSL2_eq_of_forall _ γ (a := fun c => EPilot.pinnedElt τ (w • γ) c)
    (b := fun c => EPilot.pinnedElt τ (-(w • γ)) c) (fun c => ?_) (fun c => ?_),
    ← rootPairSL2_eq_closure]
  · apply Subtype.ext
    exact canonicalRep_conj_pinnedX_of_charTwo w hγ c
  · apply Subtype.ext
    change canonicalRep (coxeterSystem τ) K w * pinnedX τ K (-γ) c *
      (canonicalRep (coxeterSystem τ) K w)⁻¹ = pinnedX τ K (-(w • γ)) c
    rw [canonicalRep_conj_pinnedX_of_charTwo w (IsRoot.neg hγ) c, smul_neg]

theorem map_conj_canonicalRep_perpLevi (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (w : WeylGroup τ) :
    (EPilot.perpLevi τ K).map (MulAut.conj (canonicalRepElt K w)).toMonoidHom =
      (rootSpan τ K (EPilot.rootPerp τ (w • highRoot τ))).subgroupOf (adjointGroup τ K) := by
  rw [EPilot.perpLevi, CFSG.LieType.Chevalley.map_conj_subgroupOf
    (EPilot.rootSpan_le_adjointGroup' _) (canonicalRepElt K w)]
  congr 1
  exact EPilot.map_conj_rootSpan_perpRoots hτ w

theorem isSimpleGroup_rootSpan_rootPerp_E7 [Finite K] [CharP K 2] {β : Fin (Tag.rank .E7) → ℤ}
    (hβ : IsRoot .E7 β) :
    IsSimpleGroup ((rootSpan .E7 K (EPilot.rootPerp .E7 β)).subgroupOf (adjointGroup .E7 K)) ∧
      center ((rootSpan .E7 K (EPilot.rootPerp .E7 β)).subgroupOf (adjointGroup .E7 K)) = ⊥ := by
  obtain ⟨w, hw⟩ := EPilot.exists_smul_highRoot_eq (Or.inr (Or.inl rfl)) hβ
  have h := map_conj_canonicalRep_perpLevi (K := K) (Or.inr (Or.inl rfl)) w
  rw [hw] at h
  rw [← h]
  have e : EPilot.perpLevi .E7 K ≃* (EPilot.perpLevi .E7 K).map
      (MulAut.conj (canonicalRepElt K w)).toMonoidHom :=
    (EPilot.perpLevi .E7 K).equivMapOfInjective _ (MulAut.conj _).injective
  have := E7Pilot.isSimpleGroup_perpLevi_E7 (K := K)
  exact ⟨e.symm.isSimpleGroup, F4Pilot.center_eq_bot_congr e E7Pilot.center_perpLevi_E7_eq_bot⟩

theorem perfectCore_centralizer_rootPairSL2_E7_of_descent [Finite K] [CharP K 2]
    (hdesc : E6Pilot.PerpLeviFrobDescent .E7 K) {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β)
    {Z : Subgroup (adjointGroup .E7 K)} (hZJ : Z ≤ rootPairSL2 .E7 K β) (hcyc : IsCyclic Z)
    (hZ : Nat.card Z = Nat.card K + 1) :
    perfectCore (centralizer (Z : Set (adjointGroup .E7 K))) =
      (rootSpan .E7 K (EPilot.rootPerp .E7 β)).subgroupOf (adjointGroup .E7 K) := by
  have : Finite (adjointGroup .E7 K) := by
    have : Finite (ModGL Tag.E7 K) := finite_modGL
    infer_instance
  obtain ⟨w, hw⟩ := EPilot.exists_smul_highRoot_eq (Or.inr (Or.inl rfl)) hβ
  set n := canonicalRepElt K w with hn
  have hJ : (rootPairSL2 .E7 K (highRoot .E7)).map (MulAut.conj n).toMonoidHom =
      rootPairSL2 .E7 K β := by
    rw [hn, map_conj_canonicalRep_rootPairSL2 w (isRoot_highRoot _), hw]
  set Z' := Z.map (MulAut.conj n⁻¹).toMonoidHom with hZ'def
  have hZ'J : Z' ≤ (EPilot.highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K) := by
    have h1 : Z' ≤ (rootPairSL2 .E7 K β).map (MulAut.conj n⁻¹).toMonoidHom := map_mono hZJ
    rw [← hJ, map_conj_inv_map_conj_self] at h1
    exact h1
  have hcyc' : IsCyclic Z' := by
    have e : Z ≃* Z' := Z.equivMapOfInjective _ (MulAut.conj n⁻¹).injective
    exact isCyclic_of_surjective e e.surjective
  have hZ' : Nat.card Z' = Nat.card K + 1 := by
    rw [hZ'def, Subgroup.card_map_of_injective (MulAut.conj n⁻¹).injective, hZ]
  obtain ⟨hcen, -, hZD⟩ :=
    E6Pilot.centralizer_nonsplit_of_descent (Or.inr (Or.inl rfl)) hdesc hZ'J hcyc' hZ'
  have hP : ⁅EPilot.perpLevi .E7 K, EPilot.perpLevi .E7 K⁆ = EPilot.perpLevi .E7 K :=
    isPerfect_iff.mp E7Pilot.isQuasisimple_perpLevi_E7.1
  have hcore' : perfectCore (centralizer (Z' : Set (adjointGroup .E7 K))) =
      EPilot.perpLevi .E7 K := by
    rw [hcen]
    exact F4Pilot.perfectCore_sup_eq_of_le_centralizer
      (F4Pilot.le_centralizer_self_of_isCyclic hcyc') hZD hP
  have hZeq : Z'.map (MulAut.conj n).toMonoidHom = Z := map_conj_map_conj_inv_self n Z
  have hcenconj : (centralizer (Z' : Set (adjointGroup .E7 K))).map (MulAut.conj n).toMonoidHom =
      centralizer (Z : Set (adjointGroup .E7 K)) := by
    rw [F4Pilot.map_centralizer_mulEquiv, hZeq]
  rw [← hcenconj, ← CFSG.Quasithin.map_perfectCore, hcore', hn,
    map_conj_canonicalRep_perpLevi (Or.inr (Or.inl rfl)) w, hw]

end E7Step

section Levi

theorem symmetrizedCartan_E8_e7Node (i j : Fin (Tag.rank .E7)) :
    Tag.symmetrizedCartan .E8 (e7Node i) (e7Node j) = Tag.symmetrizedCartan .E7 i j := by
  simp only [Tag.symmetrizedCartan, Tag.symmetrizer, one_mul]
  exact cartan_E8_e7Node i j

theorem iform_e7Embed (a b : Fin (Tag.rank .E7) → ℤ) :
    iform (e7Embed a) (e7Embed b) = iform a b := by
  simp only [iform]
  rw [sum_E8_eq]
  simp only [e7Embed_highNode, zero_mul, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_E8_eq, e7Embed_highNode, mul_zero, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [e7Embed_e7Node, e7Embed_e7Node, symmetrizedCartan_E8_e7Node]

theorem image_e7Embed_rootPerp (β : Fin (Tag.rank .E7) → ℤ) :
    e7Embed '' EPilot.rootPerp .E7 β = orthRoots (highRoot .E8) ∩ orthRoots (e7Embed β) := by
  ext δ'
  constructor
  · rintro ⟨δ, ⟨hδ, h0⟩, rfl⟩
    refine ⟨⟨isRoot_e7Embed hδ, ?_⟩, ⟨isRoot_e7Embed hδ, ?_⟩⟩
    · rw [EPilot.iform_highRoot (Or.inr (Or.inr rfl)), e7Embed_highNode]
    · rw [iform_e7Embed, iform_comm, h0]
  · rintro ⟨⟨hδ', h1⟩, ⟨-, h2⟩⟩
    rw [EPilot.iform_highRoot (Or.inr (Or.inr rfl))] at h1
    refine ⟨e8Restrict δ', ⟨isRoot_e8Restrict hδ' h1, ?_⟩, e7Embed_e8Restrict h1⟩
    rw [← iform_e7Embed, e7Embed_e8Restrict h1, iform_comm, h2]

variable {K : Type} [Field K] [Finite K] [CharP K 2]

variable (K) in
@[expose] noncomputable def e7LeviEmbed : adjointGroup .E7 K →* adjointGroup .E8 K :=
  (e7Levi K).subtype.comp (e7LeviEquiv K).symm.toMonoidHom

theorem e7LeviEmbed_injective : Function.Injective (e7LeviEmbed K) :=
  (e7Levi K).subtype_injective.comp (e7LeviEquiv K).symm.injective

theorem e7LeviEmbed_pinnedElt {δ : Fin (Tag.rank .E7) → ℤ} (hδ : IsRoot .E7 δ) (c : K) :
    e7LeviEmbed K (EPilot.pinnedElt .E7 δ c) = EPilot.pinnedElt .E8 (e7Embed δ) c :=
  Subtype.ext (coe_e7LeviEquiv_symm_pinnedX hδ c)

theorem map_e7LeviEmbed_rootSpan {S : Set (Fin (Tag.rank .E7) → ℤ)}
    (hS : ∀ δ ∈ S, IsRoot .E7 δ) :
    ((rootSpan .E7 K S).subgroupOf (adjointGroup .E7 K)).map (e7LeviEmbed K) =
      (rootSpan .E8 K (e7Embed '' S)).subgroupOf (adjointGroup .E8 K) := by
  rw [F4Pilot.rootSpan_subgroupOf_eq_closure, F4Pilot.rootSpan_subgroupOf_eq_closure,
    MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨h, ⟨δ, hδ, c, hc⟩, rfl⟩
    have hh : h = EPilot.pinnedElt .E7 δ c := Subtype.ext hc.symm
    refine ⟨e7Embed δ, ⟨δ, hδ, rfl⟩, c, ?_⟩
    rw [hh, e7LeviEmbed_pinnedElt (hS δ hδ) c]
  · rintro ⟨_, ⟨δ, hδ, rfl⟩, c, hc⟩
    refine ⟨EPilot.pinnedElt .E7 δ c, ⟨δ, hδ, c, rfl⟩, ?_⟩
    rw [e7LeviEmbed_pinnedElt (hS δ hδ) c]
    exact Subtype.ext hc

theorem map_e7LeviEmbed_rootPairSL2 {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) :
    (rootPairSL2 .E7 K β).map (e7LeviEmbed K) = rootPairSL2 .E8 K (e7Embed β) := by
  rw [map_rootPairSL2_eq_of_forall (e7LeviEmbed K) β
    (a := fun c => EPilot.pinnedElt .E8 (e7Embed β) c)
    (b := fun c => EPilot.pinnedElt .E8 (-(e7Embed β)) c) (e7LeviEmbed_pinnedElt hβ) (fun c => ?_),
    ← rootPairSL2_eq_closure]
  rw [e7LeviEmbed_pinnedElt (IsRoot.neg hβ), e7Embed_neg]

theorem e8TwoLeviOverlapInput_of_descent (hdesc : E6Pilot.PerpLeviFrobDescent .E7 K) :
    E8TwoLeviOverlapInput K := by
  intro γ hγ A' hA'J hcyc hA'
  have : Finite (adjointGroup .E8 K) := by
    have : Finite (ModGL Tag.E8 K) := finite_modGL
    infer_instance
  have : Finite (adjointGroup .E7 K) := by
    have : Finite (ModGL Tag.E7 K) := finite_modGL
    infer_instance
  have h0 : γ (highNode .E8) = 0 := by
    have := hγ.2
    rwa [EPilot.iform_highRoot (Or.inr (Or.inr rfl))] at this
  set β := e8Restrict γ with hβdef
  have hβ : IsRoot .E7 β := isRoot_e8Restrict hγ.1 h0
  have hγβ : e7Embed β = γ := e7Embed_e8Restrict h0
  have hJ : (rootPairSL2 .E7 K β).map (e7LeviEmbed K) = rootPairSL2 .E8 K γ := by
    rw [map_e7LeviEmbed_rootPairSL2 hβ, hγβ]
  set Z := A'.comap (e7LeviEmbed K) with hZdef
  have hA'range : A' ≤ (e7LeviEmbed K).range := by
    have h1 : A' ≤ rootPairSL2 .E8 K γ := hA'J
    rw [← hJ] at h1
    exact h1.trans (map_le_range _ _)
  have hZA' : Z.map (e7LeviEmbed K) = A' := map_comap_eq_self hA'range
  have hZJ : Z ≤ rootPairSL2 .E7 K β := by
    rw [← map_le_map_iff_of_injective e7LeviEmbed_injective, hZA', hJ]
    exact hA'J
  have eZ : Z ≃* A' := (Z.equivMapOfInjective _ e7LeviEmbed_injective).trans
    (MulEquiv.subgroupCongr hZA')
  have hcycZ : IsCyclic Z := isCyclic_of_surjective eZ.symm eZ.symm.surjective
  have hZ : Nat.card Z = Nat.card K + 1 := by rw [Nat.card_congr eZ.toEquiv, hA']
  have hinter : e7Levi K ⊓ centralizer (A' : Set (adjointGroup .E8 K)) =
      (centralizer (Z : Set (adjointGroup .E7 K))).map (e7LeviEmbed K) := by
    have h := F4Pilot.inf_centralizer_map_symm (L := e7Levi K) (e7LeviEquiv K) Z
    rw [Subgroup.map_map, Subgroup.map_map] at h
    rw [← hZA']
    exact h
  have hcore := perfectCore_centralizer_rootPairSL2_E7_of_descent hdesc hβ hZJ hcycZ hZ
  have hspan : ((rootSpan .E7 K (EPilot.rootPerp .E7 β)).subgroupOf (adjointGroup .E7 K)).map
      (e7LeviEmbed K) = (rootSpan .E8 K (orthRoots (highRoot .E8) ∩ orthRoots γ)).subgroupOf
        (adjointGroup .E8 K) := by
    rw [map_e7LeviEmbed_rootSpan (fun δ hδ => hδ.1), image_e7Embed_rootPerp, hγβ]
  obtain ⟨hS, hZS⟩ := isSimpleGroup_rootSpan_rootPerp_E7 (K := K) hβ
  have eS : (rootSpan .E7 K (EPilot.rootPerp .E7 β)).subgroupOf (adjointGroup .E7 K) ≃*
      ((rootSpan .E7 K (EPilot.rootPerp .E7 β)).subgroupOf (adjointGroup .E7 K)).map
        (e7LeviEmbed K) := Subgroup.equivMapOfInjective _ _ e7LeviEmbed_injective
  refine ⟨?_, ?_, ?_⟩
  · rw [hinter, ← CFSG.Quasithin.map_perfectCore, hcore, hspan]
  · rw [← hspan]
    exact eS.symm.isSimpleGroup
  · rw [← hspan]
    exact F4Pilot.center_eq_bot_congr eS hZS

theorem e8TwoOverlapInput_of_descent (hdesc : E6Pilot.PerpLeviFrobDescent .E7 K) :
    E8TwoOverlapInput K :=
  e8TwoOverlapInput_of_levi (e8TwoLeviOverlapInput_of_descent hdesc)

end Levi

section Final

@[expose] def E7TwoPerpLeviDescentInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 →
    E6Pilot.PerpLeviFrobDescent .E7 K

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem e8TwoInput_of_fieldRow_of_descent (hcat : E7CatalogueClauses)
    (hdesc : E7TwoPerpLeviDescentInput) (hF : E8TwoFieldRowInput) : E8TwoInput :=
  e8TwoInput_of_fieldRow hcat (fun K _ hK => by
    have : Finite K := Nat.finite_of_card_ne_zero (by omega)
    have := F4Pilot.charP_two_of_natCard_eq_two_pow (show Nat.card K = 2 ^ 1 by rw [hK]; rfl)
    exact e8TwoOverlapInput_of_descent (hdesc K hK)) hF

end Final

end CFSG.SeitzReduction.E8Pilot
