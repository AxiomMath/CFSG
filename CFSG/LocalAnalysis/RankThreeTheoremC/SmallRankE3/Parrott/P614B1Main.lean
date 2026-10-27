module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614B1Thompson
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614B1Rank
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.L62Situation
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Fail614Stage
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.U0

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

theorem pieceDelta4_holds : PieceDelta4 := by
  intro hT hNC hQ G _ _ P M x z hS hU0 _ hsit hx hz hnα
  obtain ⟨S, x', z', hD, -, hx', -⟩ := l62Data_of_situation hS hU0 hsit hx hz
  have hXC := P614B1.l62_hasNormalPComplement_centralizer hT hNC hQ hD hnα
  have hmap : (centralizer ({x'} : Set ↥M)).map M.subtype = M ⊓ centralizer ({x} : Set G) := by
    ext g
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine mem_inf.mpr ⟨c.2, mem_centralizer_singleton_iff.mpr ?_⟩
      rw [← hx']
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc)
    · intro hg
      obtain ⟨hgM, hgx⟩ := mem_inf.mp hg
      refine ⟨⟨g, hgM⟩, mem_centralizer_singleton_iff.mpr (Subtype.ext ?_), rfl⟩
      show g * x' = x' * g
      rw [hx']
      exact mem_centralizer_singleton_iff.mp hgx
  have hMC : CFSG.HasNormalPComplement 3 ↥(M ⊓ centralizer ({x} : Set G)) := by
    rw [← hmap]
    exact CFSG.RankThree.Coprime.hasNormalPComplement_map M.subtype hXC
  exact P614B1.hasNormalPComplement_centralizer_of_inf hS hU0 hsit hx hz hMC

theorem pieceCaseDelta_holds : PieceCaseDelta := by
  intro k292 hT hNC hQ G _ _ hS hD1 P M hsit x z hx hz _
  by_cases hα : HasPrimeConstraint (G := M) 3
  · exact fail614NormalizerRank_of_alpha hS hsit hα hx hz
  intro T hTmax
  have hU0 : FullCoreLocal G := fullCoreLocal_of_theoremD1_situation_three hS hD1 hsit
  obtain ⟨S, x', z', hD, -, hx', -⟩ := l62Data_of_situation hS hU0 hsit hx hz
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal
  have hpl := SmallRankPlane.of_situation hS hsit hx hz
  have hBP : zpowers x ⊔ zpowers z ≤ (P : Subgroup G) := hpl.isIsolatedPlane.1
  have hBC : zpowers x ⊔ zpowers z ≤ centralizer ({x} : Set G) :=
    sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp hz.centralizes x hx.mem).symm))
  have hBPx : zpowers x ⊔ zpowers z ≤ (P : Subgroup G) ⊓ centralizer ({x} : Set G) :=
    le_inf hBP hBC
  have hPxCB := P614B1.sylowCentralizer_le_centralizer_plane (x := x) hz
  have hPxM : (P : Subgroup G) ⊓ centralizer ({x} : Set G) ≤ M := inf_le_left.trans hPM
  have hCX : centralizer ({x'} : Set ↥M) = (M ⊓ centralizer ({x} : Set G)).subgroupOf M := by
    ext g
    rw [mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff,
      ← hx']
    exact ⟨fun h => ⟨g.2, congrArg Subtype.val h⟩, fun h => Subtype.ext h.2⟩
  have hPxX : CFSG.ABGLocalTools.IsSylowOf 3
      (((P : Subgroup G) ⊓ centralizer ({x} : Set G)).subgroupOf M)
      (centralizer ({x'} : Set ↥M)) := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h1 : CFSG.ABGLocalTools.IsSylowOf 3 ((P : Subgroup G) ⊓ centralizer ({x} : Set G))
        (centralizer ({x} : Set G)) :=
      CFSG.ABGLocalTools.isSylowOf_iff.mpr
        ⟨inf_le_right, P.isPGroup'.to_le inf_le_left, hx.sylow_centralizer⟩
    have h2 := h1.of_le (le_inf hPxM inf_le_right) inf_le_right
    rw [hCX, ← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff M,
      Subgroup.map_subgroupOf_eq_of_le hPxM, Subgroup.map_subgroupOf_eq_of_le inf_le_left]
    exact h2
  have hΩ : ∀ q ∈ ((P : Subgroup G) ⊓ centralizer ({x} : Set G)).subgroupOf M, q ^ 3 = 1 →
      q ∈ (zpowers x ⊔ zpowers z).subgroupOf M := by
    intro q hq hq3
    exact hpl.mem_of_mem_centralizer _ (hPxCB hq) (by simpa using congrArg Subtype.val hq3)
  have hk := P614B1.l62_caseDelta_rank k292 hNC hQ hD hα hPxX (fun q hq => hBPx hq)
    (P614B1.isElemAbelian_subgroupOf M hpl.isElemAbelian) hΩ
    (P614B1.isMaxTwoInvariantIn_subgroupOf (hBP.trans hPM) hTmax)
  have hmap : (normalizer ((T.subgroupOf M : Subgroup ↥M) : Set ↥M)).map M.subtype =
      M ⊓ normalizer (T : Set G) := by
    rw [CFSG.RankThree.Coprime.map_subtype_normalizer, Subgroup.map_subgroupOf_eq_of_le hTmax.1.1]
  calc CFSG.Open.pRank 3 (P : Subgroup G) = 3 := hP3
    _ ≤ CFSG.Open.pRank 3 (normalizer ((T.subgroupOf M : Subgroup ↥M) : Set ↥M)) := hk
    _ ≤ CFSG.Open.pRank 3 ((normalizer ((T.subgroupOf M : Subgroup ↥M) : Set ↥M)).map
          M.subtype) :=
        CFSG.SectionRank.pRank_le_map (by norm_num) M.subtype M.subtype_injective _
    _ = CFSG.Open.pRank 3 (M ⊓ normalizer (T : Set G)) := by rw [hmap]

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
