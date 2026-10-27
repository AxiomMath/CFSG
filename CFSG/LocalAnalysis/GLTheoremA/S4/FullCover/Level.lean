module

public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.CoverToCatalog
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.CatalogToCover
public import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma49ii
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.UniquenessMaximal

theorem fullCoverLevel_eq_kLevel {p : ℕ} (hM : ListedMultiplierBound p)
    (hH : HatOddMultiplierBound) (hp : p.Prime) (hp2 : p ≠ 2) {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.Open.IsQuasisimple Q) (hZ : IsPGroup p (Subgroup.center Q)) :
    fullCoverLevel p Q = kLevel p (Q ⧸ Subgroup.center Q) := by
  have e1 : K1Cover p Q ↔ IsChevSimple p (Q ⧸ Subgroup.center Q) :=
    ⟨fun h => h.2, fun h => ⟨hQ, h⟩⟩
  have e2 : K2Cover p Q ↔ catalogIs (Q ⧸ Subgroup.center Q) (k2 p) :=
    ⟨k2Cover_imp_catalogIs p, catalogIs_imp_k2Cover hM hH hQ hZ⟩
  have e3 : K3Cover p Q ↔ catalogIs (Q ⧸ Subgroup.center Q) (k3 p) :=
    ⟨k3Cover_imp_catalogIs, catalogIs_imp_k3Cover hM hH hQ hZ⟩
  unfold fullCoverLevel kLevel
  by_cases h1 : K1Cover p Q
  · rw [if_pos h1, if_pos (e1.1 h1)]
  rw [if_neg h1, if_neg (mt e1.2 h1)]
  by_cases h2 : K2Cover p Q
  · rw [if_pos h2, if_pos (e2.1 h2)]
  rw [if_neg h2, if_neg (mt e2.2 h2)]
  by_cases h3 : K3Cover p Q
  · rw [if_pos h3, if_pos (e3.1 h3)]
  rw [if_neg h3, if_neg (mt e3.2 h3)]

variable {G : Type} [Group G] [Finite G]

theorem fullCoverLevel_pQuot_eq {p : ℕ} (hM : ListedMultiplierBound p)
    (hH : HatOddMultiplierBound) (hp : p.Prime) (hp2 : p ≠ 2) {X L : Subgroup G}
    (hL : GLAPComponent p X L) :
    fullCoverLevel p (PQuot p L) = kLevel p (PSimple p L) :=
  fullCoverLevel_eq_kLevel hM hH hp hp2 (isQuasisimple_pQuot_of_glaPComponent hp hL)
    (I2611.isPGroup_center_pQuot' hp L)

theorem lemma49_of_levelCoincidence {p : ℕ} (hM : ListedMultiplierBound p)
    (hH : HatOddMultiplierBound) (hp : p.Prime) (hp2 : p ≠ 2) (h183 : Input18_3_4)
    (hKP : CFSG.Open.IsKProper G) (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (h1412 : I1412UsedAt G p)
    (h1122 : I1122IsoAt G p) (hLB : LBalanceAt G p) : Lemma49At G p := by
  intro t t' hrel
  obtain ⟨h1, h2⟩ := lemma49_legacySimple hp h183 hKP hsimple hnonab h1412 h1122 hLB t t' hrel
  refine ⟨?_, h2⟩
  rw [fullCoverLevel_pQuot_eq hM hH hp hp2 hrel.1.2.2,
    fullCoverLevel_pQuot_eq hM hH hp hp2 hrel.2.1.2.2]
  exact min_le_min_left 4 h1

end CFSG.LocalAnalysis.GLTheoremA
