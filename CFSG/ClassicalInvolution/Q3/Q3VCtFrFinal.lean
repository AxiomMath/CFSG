module

public import CFSG.ClassicalInvolution.Q3.Q3VCtFrMain
public import CFSG.ClassicalInvolution.Q3.Q3ZPres

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V

open CFSG.ClassicalInvolution.Q3.Q3Z
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

theorem exists_spFrame3 (hC : V6Collapse) {n : ℕ} (hn : 3 ≤ n) {X : Type} [Group X]
    (U : Fin n → Subgroup X)
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin n, i.val + 1 = j.val → j.val + 1 < n →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j))
    (hsp : ∀ i j : Fin n, i.val + 1 = n → j.val + 2 = n →
      ∃ W, SymplecticBlockStandardPair (GaloisField 3 1) W (U i) (U j)) :
    Nonempty (SpFrame3 n U) := by
  obtain ⟨e⟩ := nonempty_ringEquiv_galoisField_three
  exact exists_spFrame_of_ringEquiv e hn U hcomm (fun k hk g hg i => hC k hk g hg i) hpair hsp

theorem exists_spFrame3_of_check (hVC : V6CollapseCheck) {n : ℕ} (hn : 3 ≤ n) {X : Type}
    [Group X] (U : Fin n → Subgroup X)
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin n, i.val + 1 = j.val → j.val + 1 < n →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j))
    (hsp : ∀ i j : Fin n, i.val + 1 = n → j.val + 2 = n →
      ∃ W, SymplecticBlockStandardPair (GaloisField 3 1) W (U i) (U j)) :
    Nonempty (SpFrame3 n U) :=
  exists_spFrame3 (v6Collapse_of_check hVC) hn U hcomm hpair hsp

end CFSG.ClassicalInvolution.Q3.Q3V
