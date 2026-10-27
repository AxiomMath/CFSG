module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Single
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Cover59

public section

namespace CFSG.ComponentClassification.GrSLit.KSw

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {X : Type} [Group X] [Finite X]

theorem exists_target (hMax : MaximalTwoComponentInput)
    (hS : SchreierFor Blueprint.Catalog) (hbase : L34BaseSetting X) {a r : X} {J : Subgroup X}
    (ha : orderOf a = 2) (hr : orderOf r = 2) (har : a * r = r * a)
    (hJa : J ≤ centralizer ({a} : Set X))
    (hJc : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set X))))
    (hmax : GSWeakMaximalComponent J) (hL34 : IsL34Type (J ⧸ Open.fusionZStar J))
    (hrK : r ∈ coreActionKernel J) :
    ∃ L : Subgroup X, L ≤ centralizer ({r} : Set X) ∧
      IsPComponent 2 (L.subgroupOf (centralizer ({r} : Set X))) ∧
      centralizer ({r} : Set X) ≤ normalizer (L : Set X) ∧
      IsL34Type (L ⧸ Open.fusionZStar L) ∧ GSWeakMaximalComponent L ∧
      gsFixedLayer J r ≤ L ∧ gsFixedLayer J r ⊔ oddIn L = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hsimple, hnab, hK, -, hUo, -, -, -⟩ := id hbase
  have : IsSimpleGroup X := hsimple
  have hrZ : r ∉ center X := GSLit.not_mem_center_of_orderOf_eq_two hnab hr
  obtain ⟨hTab, hTpc, hTE, -, -, ⟨φ⟩⟩ := GrS5.gsFixedLayer_facts hS hK ha hr har hrZ hJa hJc hrK
  have haCr : a ∈ centralizer ({r} : Set X) := mem_centralizer_singleton_iff.mpr har
  obtain ⟨L, hLr, hLc, hTK, -⟩ :=
    UnbalancedCorr.exists_orbit_component ha haCr hTab hTpc hTE
  have hW : GSWeakCorr a J r L := ⟨ha, hr, har, hJa, hJc, hLr, hLc,
    (mem_coreActionKernel.mp hrK).1, (mem_coreActionKernel.mp hrK).2, hTK⟩
  have hR : GSWeakReach J L := Relation.ReflTransGen.single ⟨a, r, hW⟩
  have hmaxL : GSWeakMaximalComponent L := hmax.of_weakReach hR
  obtain ⟨e⟩ := hmax.2 L hR
  have hL34L : IsL34Type (L ⧸ Open.fusionZStar L) := LieType.CurtisTits.lieModel_of_mulEquiv e hL34
  have hgs : GSMaximalSetting X r L := ⟨hsimple, hnab, hK, hUo, hr, hLr, hLc, hmaxL,
    GrS5.three_le_pRank_of_l34 hL34L, Sol78.not_psp4_of_l34 hL34L, Or.inl ⟨hL34L, hbase⟩⟩
  have hCN : centralizer ({r} : Set X) ≤ normalizer (L : Set X) :=
    GrS4.centralizer_le_normalizer_of_gsMaximalSetting hMax hgs
  have hLa : conjugate L a = L := by
    have haN := hCN haCr
    ext y
    rw [mem_conjugate_iff]
    exact ((mem_normalizer_iff.mp haN) y).symm
  have hTL : gsFixedLayer J r ≤ L := by
    have h := hTK
    rwa [hLa, sup_idem] at h
  obtain ⟨eT⟩ := nonempty_fusionZStar_equiv_of_quotient_equiv φ
  have hL34T : IsL34Type (gsFixedLayer J r ⧸ Open.fusionZStar (gsFixedLayer J r)) :=
    LieType.CurtisTits.lieModel_of_mulEquiv eT.symm hL34
  have hsup : gsFixedLayer J r ⊔ oddIn L = L := GrS5.sup_oddIn_eq_of_le_of_isL34Type hTL hL34T
    hL34L (UnbalancedCorr.commutator_eq_of_isPComponent hLr hLc)
  exact ⟨L, hLr, hLc, hCN, hL34L, hmaxL, hTL, hsup⟩

end CFSG.ComponentClassification.GrSLit.KSw
