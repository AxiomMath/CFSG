module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeKFacts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem isKGroup_component (hK : CFSG.Open.IsKProper G) {N : Subgroup G} (hN : N ≠ ⊤) {p : ℕ}
    (L : Subgroup (N ⧸ primeComplementCore (G := N) p)) : IsKGroup L :=
  CFSG.KCore.KGroupNonab.kGroupAllSimple CFSG.Assembly.inCatalog_isoInvariant
    CFSG.Assembly.inCatalog_containsAbelianSimple
    (catalogSimpleSections_iff_isKGroup.mp
      (((catalogSimpleSections_of_isKProper hK N hN).quotient _).subgroup L))

theorem primeComplementCore_component_eq_bot {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hcore : primeComplementCore (G := X) p = ⊥) {L : Subgroup X} (hL : IsComponentOf L ⊤) :
    primeComplementCore (G := L) p = ⊥ :=
  cfsg_subnormal_primeComplementCore_eq_bot p L hL.2.1 hcore

theorem false_of_sevenFive (hS : Setting G) (h75 : KFactSevenFive) {p : ℕ}
    {N : Subgroup G} {L : Subgroup (N ⧸ primeComplementCore (G := N) p)}
    {i : TauCeti.CFSGIndex}
    (hi : (7 ≤ p ∧ ∃ hn, i = .alternating (2 * p) hn) ∨
      (5 ≤ p ∧ ∃ hn, i = .alternating (3 * p) hn) ∨ (p = 5 ∧ i = .sporadic .Fi22))
    (hLs : IsSimpleGroup L) (e : Nonempty (L ≃* i.Group)) : False := by
  set O := primeComplementCore (G := N) p
  set π := QuotientGroup.mk' O
  set Y : Subgroup N := L.comap π
  set ρ : Y →* L := π.subgroupComap L
  have hρ : Function.Surjective ρ :=
    π.subgroupComap_surjective_of_surjective L (QuotientGroup.mk'_surjective O)
  let eY : Y ≃* Y.map N.subtype := Y.equivMapOfInjective N.subtype N.subtype_injective
  exact h75 G hS.rank p i hi (e.some.isSimpleGroup_congr.mp hLs) (Y.map N.subtype)
    ((e.some.toMonoidHom.comp ρ).comp eY.symm.toMonoidHom)
    ((e.some.surjective.comp hρ).comp eY.symm.surjective)

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
