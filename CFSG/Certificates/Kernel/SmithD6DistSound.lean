module

public import Certificates.Data.Kernel.SmithD6.DistK
public import CFSG.Certificates.Kernel.SmithD6UwSound
import CFSG.Certificates.Kernel.SmithD6WtSound

public section

namespace CFSG.KD.SmithD6

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KC.PkTree

theorem d6DistGo_sound (B0 : Array Nat) : ∀ (Bs Ps : List (Array Nat)) (v : Nat),
    d6DistGo B0 Bs Ps v = true → ∀ k < Bs.length,
      kcDist (kcMeetA B0 (Bs.getD k #[]) (Ps.getD k #[])) = pkGet JU.uwK 2 (v + k)
  | [], _, _, _, k, hk => absurd hk (by simp)
  | B :: Bs, [], v, h, _, _ => by
    have e : d6DistGo B0 (B :: Bs) [] v = false := rfl
    rw [e] at h
    exact absurd h (by decide)
  | B :: Bs, P :: Ps, v, h, k, hk => by
    have e : d6DistGo B0 (B :: Bs) (P :: Ps) v =
        bAnd(Nat.beq (kcDist (kcMeetA B0 B P)) (pkGet JU.uwK 2 v),
          strictKB (Nat.succ v) (d6DistGo B0 Bs Ps)) := rfl
    rw [e, strictKB_eq] at h
    obtain ⟨h1, h2⟩ := band_true h
    rcases k with _ | k
    · rw [List.getD_cons_zero, List.getD_cons_zero, Nat.add_zero]
      exact Nat.eq_of_beq_eq_true h1
    · rw [List.getD_cons_succ, List.getD_cons_succ, show v + (k + 1) = Nat.succ v + k by omega]
      exact d6DistGo_sound B0 Bs Ps (Nat.succ v) h2 k (by simpa using hk)

theorem d6DistOK_sound {c : Nat} (h : d6DistOK c = true) : ∀ k < (J.pbC.getD c []).length,
    kcDist (kcMeetA (d6PB 0) ((J.pbC.getD c []).getD k #[]) ((J.ppC.getD c []).getD k #[])) =
      pkGet JU.uwK 2 (2048 * c + k) := by
  unfold d6DistOK at h
  rw [nthA_eq, nthA_eq] at h
  exact d6DistGo_sound _ _ _ _ h

end CFSG.KD.SmithD6

end
