module

import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.LocalVocabulary

public section

namespace GL83.I243.CoverList

theorem card_le_torsion_center {L : Type} [Group L] [Finite L] {p : ℕ} {E : Subgroup L}
    (hE : CFSG.Open.IsElemAbelian p E) (hZ : E ≤ Subgroup.center L) :
    Nat.card E ≤ Nat.card {z : Subgroup.center L // z ^ p = 1} := by
  refine Nat.card_le_card_of_injective
    (fun x => ⟨⟨x.1, hZ x.2⟩, Subtype.ext (hE.2 x.1 x.2)⟩) ?_
  intro x y hxy
  exact Subtype.ext (congrArg (fun w : {z : Subgroup.center L // z ^ p = 1} => (w.1 : L)) hxy)

theorem pRank_center_le_two_of_torsion {K : Type} [Group K] [Finite K] {p : ℕ} (hp : 1 < p)
    (h : Nat.card {z : Subgroup.center K // z ^ p = 1} ≤ p ^ 2) :
    CFSG.Open.pRank p (Subgroup.center K) ≤ 2 :=
  CFSG.SectionRank.pRank_le hp fun _ hEZ hE => (card_le_torsion_center hE hEZ).trans h

theorem pRank_center_le_two_of_dvd {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hZ : Nat.card (Subgroup.center K) ∣ 12) :
    CFSG.Open.pRank p (Subgroup.center K) ≤ 2 := by
  obtain ⟨E, hEZ, -, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (Subgroup.center K)
  have hd : p ^ CFSG.Open.pRank p (Subgroup.center K) ∣ Nat.card (Subgroup.center K) := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_le hEZ
  by_contra h3
  push Not at h3
  have h12 : p ^ 3 ∣ 12 := (pow_dvd_pow p h3).trans (hd.trans hZ)
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hle := Nat.le_of_dvd (by norm_num) h12
  have h27 : 3 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hp3 3
  omega

end GL83.I243.CoverList
