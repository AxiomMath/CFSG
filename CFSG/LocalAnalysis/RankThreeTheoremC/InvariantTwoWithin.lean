module

public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem isSylowOf_of_invariantTwoMaximalWithin {p : ℕ} (hp : p.Prime) {A M X T : Subgroup G}
    (hA : IsPGroup p A) (hXM : X ≤ M) (hX : Nat.Coprime p (Nat.card X))
    (hAX : A ≤ normalizer (X : Set G)) (hT : invariantTwoMaximalWithin A M T) (hTX : T ≤ X) :
    CFSG.ABGLocalTools.IsSylowOf 2 T X := by
  let action := ambientSubgroupActionHom A X hAX
  have hTint : IsPGroup 2 (T.subgroupOf X) :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTX).symm
  have hTinv : ∀ a : A, (T.subgroupOf X).map (action a).toMonoidHom = T.subgroupOf X :=
    (ambient_subgroup_action_invariant_iff A X T hAX hTX).mpr hT.2.2.1
  have hmax : ∀ larger : Subgroup X, IsPGroup 2 larger →
      (∀ a : A, larger.map (action a).toMonoidHom = larger) →
      T.subgroupOf X ≤ larger → larger = T.subgroupOf X := by
    intro larger hlp hfix hle
    have himgInv := (ambient_subgroup_action_image_invariant_iff A X hAX larger).mp hfix
    have himgLe : T ≤ larger.map X.subtype := by
      have h := Subgroup.map_mono (f := X.subtype) hle
      rwa [Subgroup.map_subgroupOf_eq_of_le hTX] at h
    have heq := hT.2.2.2 (larger.map X.subtype) ((Subgroup.map_subtype_le larger).trans hXM)
      (hlp.map X.subtype) himgInv himgLe
    apply Subgroup.map_injective X.subtype_injective
    rwa [Subgroup.map_subgroupOf_eq_of_le hTX]
  obtain ⟨S, hS⟩ := coprime_maximal_invariant_prime_subgroup_is_sylow action p hp hA hX 2
    Nat.prime_two (T.subgroupOf X) hTint hTinv hmax
  exact ⟨S, by rw [hS, Subgroup.map_subgroupOf_eq_of_le hTX]⟩

@[expose] def GL83InvariantTwoWithin (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M D : Subgroup G), ExtremalObstruction p P M D →
    ¬ (P : Subgroup G) ≤ normalizer (D : Set G) → IsMulCommutative D →
      ∀ z ∈ D, z ≠ 1 → z ∈ centralizer (P : Set G) → z ^ p = 1 →
        normalizer ((zpowers z : Subgroup G) : Set G) ≤ M →
        ∀ T : Subgroup G, invariantTwoMaximalWithin D M T →
          T ≤ CFSG.ABGTheoremB.pPrimeCoreIn p M ⊔
            CFSG.ABGTheoremB.pPrimeCoreIn p (normalizer ((zpowers z : Subgroup G) : Set G))

theorem gl83InvariantTwoSylow_of_within (hS : Setting G) (hR : TransitivityReduction G)
    (h : GL83InvariantTwoWithin G) : GL83InvariantTwoSylow G := by
  intro p hp P M D hext hPD hab z hzD hz1 hzc hzp T hT
  have hprime := sigmaA_prime p hp
  have : Fact p.Prime := ⟨hprime⟩
  have hN₀M := hR p hp P M D hext hPD z hzD hz1 hzc hzp
  have hTX := h p hp P M D hext hPD hab z hzD hz1 hzc hzp hN₀M T hT
  have hDP : D ≤ (P : Subgroup G) := hext.obstruction.2.1
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hp hext.obstruction.1).1
  have hDN₀ : D ≤ normalizer ((zpowers z : Subgroup G) : Set G) := by
    refine le_trans ?_ (centralizer_le_normalizer _)
    refine le_centralizer_iff.mp (zpowers_le.mpr (mem_centralizer_iff.mpr fun d hd => ?_))
    exact congrArg Subtype.val (hab.is_comm.comm ⟨d, hd⟩ ⟨z, hzD⟩)
  have hXM : CFSG.ABGTheoremB.pPrimeCoreIn p M ⊔ CFSG.ABGTheoremB.pPrimeCoreIn p
      (normalizer ((zpowers z : Subgroup G) : Set G)) ≤ M :=
    sup_le (CFSG.ABGTheoremB.pPrimeCoreIn_le p M)
      ((CFSG.ABGTheoremB.pPrimeCoreIn_le p _).trans hN₀M)
  exact isSylowOf_of_invariantTwoMaximalWithin hprime (P.isPGroup'.to_le hDP) hXM
    (coprime_card_pPrimeCoreIn_sup hN₀M)
    (le_normalizer_pPrimeCoreIn_sup (hDP.trans hPM) hDN₀) hT hTX

end CFSG.LocalAnalysis.RankThreeTheoremC
