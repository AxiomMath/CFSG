module

public import Certificates.Data.Kernel.D4WordPos
public import CFSG.Certificates.Kernel.B3S3KSound
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42Check
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.D4Local

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K
open CFSG.RankThree.PartTwo.Sec4.Item434D42 CFSG.RankThree.PartTwo.KFacts.K426
open CFSG.Monster.B.Co2.Native (compA)

theorem evalWA_pos {m n w ng : ℕ} (hw : szOK n w = true) {gs : Array (Array ℕ)} {G : ℕ → ℕ}
    (hb : BindA n w gs ng G) (hG : ∀ k < ng, permB n w (G k) = true) :
    ∀ ws : List (Fin m × Bool), (∀ x ∈ ws, x.2 = true ∧ x.1.val < ng) →
      evalWA n gs ws = unpack n w (wordPos n w G ws) ∧ permB n w (wordPos n w G ws) = true
  | [], _ => ⟨CFSG.KC.BfsPin.idA_eq hw, permB_id hw⟩
  | x :: ws, h => by
    obtain ⟨ih1, ih2⟩ := evalWA_pos hw hb hG ws fun y hy => h y (List.mem_cons_of_mem _ hy)
    obtain ⟨hx2, hx1⟩ := h x List.mem_cons_self
    have e : evalWA n gs (x :: ws) = compA n gs[x.1.val]! (evalWA n gs ws) := by
      simp [evalWA, hx2]
    have ew : wordPos n w G (x :: ws) = pcomp n w (mask w) (G x.1.val) (wordPos n w G ws) := rfl
    rw [e, ih1, hb.2 _ hx1, comp_unpack' hw (hG _ hx1) ih2, ew]
    exact ⟨rfl, permB_of_pp ((pp_of_permB hw (hG _ hx1)).mul (pp_of_permB hw ih2))⟩

theorem uFlag_unpack {n w X u : ℕ} (hw : szOK n w = true) (hX : permB n w X = true)
    (hu : permB n w u = true) :
    uFlag n (unpack n w X) (unpack n w u) = uFlagK n w X (pw n w X 2) u := by
  unfold uFlag uFlagK
  rw [eqA_id hw hu, powEq_id hw hu 3, eqA_unpack' hw hu hX, pow_unpack' hw hX 2,
    eqA_unpack' hw hu (permB_ppow hw hX 2)]
  simp only [Orb.bAnd_eq, Bool.and_assoc]
  rfl

end CFSG.KC.D4Local
