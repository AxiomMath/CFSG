module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitSchur
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1EndForm
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Defs
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCore

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup Assembly.LowTwoRank

theorem isMType_of_mulEquiv {A B : Type} [Group A] [Group B] {p : ℕ} (e : A ≃* B)
    (h : IsMType p A) : IsMType p B := by
  obtain ⟨hq, ⟨τ, n, k, hL⟩, hev, hc⟩ := h
  obtain ⟨eZ⟩ := FooteLit.nonempty_quotient_fusionZStar_equiv e
  have hcard : Nat.card ↥(Open.fusionZStar B) = Nat.card ↥(Open.fusionZStar A) := by
    rw [← FooteLit.fusionZStar_map_mulEquiv e,
      Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
  refine ⟨isTwoQuasisimple_of_mulEquiv e hq, ⟨τ, n, k, GSThmB.OddQuot.lieModel_of_equiv eZ hL⟩,
    hcard ▸ hev, fun n k => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [hcard]
    exact (hc n k).1 (GSThmB.OddQuot.lieModel_of_equiv eZ.symm h)
  · rw [hcard]
    exact (hc n k).2 (GSThmB.OddQuot.lieModel_of_equiv eZ.symm h)

theorem isMTypeSchur_of_isMType (hGA : TBLit.GriessMultipliersOdd) {H : Type} [Group H]
    {p : ℕ} (hp2 : p ≠ 2) (h : IsMType p H) : IsMTypeSchur p H := by
  obtain ⟨hq, ⟨τ, n, k, hL⟩, hev, hc⟩ := h
  refine .inl ⟨hq, ⟨τ, n, k, hL⟩, hev, fun n r hn _ hm => ?_⟩
  rcases hm with hm | hm
  · rw [(hc n r).1 hm, factorization_card_griessHopfMultiplier_psl hGA hp2 (by omega) hm]
  · rw [(hc n r).2 hm, factorization_card_griessHopfMultiplier_psu hGA hp2 (by omega)
      (even_two_mul n) hm]

theorem intrinsic_of_isPComponent {G : Type} [Group G] [Finite G] {zz : G}
    {J : Subgroup ↥(centralizer ({zz} : Set G))} (hJ : IsPComponent 2 J)
    (hzzJ : (⟨zz, mem_centralizer_singleton_iff.mpr rfl⟩ : ↥(centralizer ({zz} : Set G))) ∈ J)
    {p : ℕ} (hM : IsMType p ↥J) :
    IsTwoComponentIn (J.map (centralizer ({zz} : Set G)).subtype) (centralizer {zz}) ∧
      zz ∈ J.map (centralizer ({zz} : Set G)).subtype ∧
      IsMType p ↥(J.map (centralizer ({zz} : Set G)).subtype) := by
  have hJ'C : J.map (centralizer ({zz} : Set G)).subtype ≤ centralizer ({zz} : Set G) :=
    map_subtype_le J
  have hsub : (J.map (centralizer ({zz} : Set G)).subtype).subgroupOf
      (centralizer ({zz} : Set G)) = J :=
    comap_map_eq_self_of_injective (centralizer ({zz} : Set G)).subtype_injective J
  exact ⟨(isTwoComponentIn_iff hJ'C).mpr (by rw [hsub]; exact hJ),
    ⟨⟨zz, mem_centralizer_singleton_iff.mpr rfl⟩, hzzJ, rfl⟩,
    isMType_of_mulEquiv (J.equivMapOfInjective _ (centralizer ({zz} : Set G)).subtype_injective)
      hM⟩

theorem harris82TheoremOneKProper_of (hGA : TBLit.GriessMultipliersOdd)
    (hT1 : Harris82Theorem1KProper) : Harris82TheoremOneKProper := by
  intro G _ _ _ hnonab hK hcat zz hzz J hJ hzzJ p hp hp2 hM
  obtain ⟨hJ', hzzJ', hM'⟩ := intrinsic_of_isPComponent hJ hzzJ hM
  exact not_isMTypeSchur_of_kProper hT1 hnonab hK hcat hzz hJ' hzzJ' hp hp2
    (isMTypeSchur_of_isMType hGA hp2 hM')

end CFSG.ComponentClassification.HarrisLit
