module

public import CFSG.ClassicalInvolution.Q3.Q3TWWOddP
public import CFSG.ClassicalInvolution.Q3.Q3TWWPairStmt

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TW

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3Z

theorem weakCT3OddMapPair_of_collapse (hC : B3Collapse) {N : ℕ} (hN : 3 ≤ N) :
    WeakCT3OddMapPair N := by
  intro G _ U hcomm hpair hsp
  obtain ⟨e⟩ := nonempty_ringEquiv_galoisField_three
  have hadm : StatedLieAdmissible .POmegaOdd N 3 1 := ⟨Nat.prime_three, le_rfl, hN, by norm_num⟩
  have hF : Nat.card (GaloisField 3 1) = 3 ^ 1 :=
    natCard_galoisField_three.trans (pow_one 3).symm
  have hcomm' : ∀ i j : Fin N, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a :=
    fun i j hij a ha b hb => hcomm i j hij a ha b hb
  obtain ⟨fr⟩ := exists_oddFramePair_of_ringEquiv e hN U hcomm'
    (fun k hk g hg i => hC k hk g hg i) hpair hsp
  exact weakCT_odd_subgroup_of_oddFramePair hadm hF
    (CFSG.ComponentClassification.CatLeafProof.isQuasisimple_statedSp_two
      (by rw [natCard_galoisField_three])) U hcomm' fr

end CFSG.ClassicalInvolution.Q3.Q3TW
