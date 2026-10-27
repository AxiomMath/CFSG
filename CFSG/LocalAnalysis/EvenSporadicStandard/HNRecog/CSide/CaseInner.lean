module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.SetupModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.DictFix

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open Subgroup CFSG.RankThree.Literature.FSmith CFSG.EvenSporadicStandard.HNRecog
open scoped commutatorElement

variable {C : Type} [Group C] {Q : Subgroup C} [hQn : Q.Normal]
  [Module (ZMod 2) (Additive (Abelianization Q))]

theorem CSideSetup.card_comm_of_inner [Finite C]
    (hC : WeakHyp C Q) (S : CSideSetup C Q) {t : C} (htL : t ∈ commutator C)
    (ht2 : (t : C ⧸ Q) ^ 2 = 1) (ht1 : (t : C ⧸ Q) ≠ 1) :
    Nat.card {q : C // q ∈ Q ∧ ⁅q, t⁆ ∈ centerOf Q} = 2 ^ 5 := by
  haveI : Finite Q := hC.finite_Q
  let l : ↥(commutator C) := ⟨t, htL⟩
  let g := S.θ l
  have hg1 : g ≠ 1 := by
    intro h
    have htQ : t ∈ Q := (S.ker l).mp (by simpa [g, l] using h)
    exact ht1 ((QuotientGroup.eq_one_iff t).mpr htQ)
  have hg2 : g ^ 2 = 1 := by
    have ht2q : (QuotientGroup.mk (t ^ 2) : C ⧸ Q) = 1 := by
      rw [QuotientGroup.mk_pow, ht2]
    have hQ : ((l ^ 2 : ↥(commutator C)) : C) ∈ Q := by
      have hcoe : ((l ^ 2 : ↥(commutator C)) : C) = t ^ 2 := by
        simp [l]
      rw [hcoe, ← QuotientGroup.eq_one_iff]
      exact ht2q
    calc g ^ 2 = S.θ (l ^ 2) := (map_pow S.θ l 2).symm
      _ = 1 := (S.ker (l ^ 2)).mpr hQ
  have hinvol : Nat.card {v : Additive (Abelianization Q) // S.σ g v = v} = 16 :=
    (S.model hC).invol g hg1 hg2
  have hfix : Nat.card {v : Additive (Abelianization Q) //
      conjLinEquiv hQn t v = v} = 16 := by
    rw [S.rho_eq htL]
    simpa [g, l] using hinvol
  rw [cSide_card_comm_eq hC.isExtraspecialPGroup t, hfix]
  norm_num

end CFSG.EvenSporadicStandard.HNRecog.CSide
