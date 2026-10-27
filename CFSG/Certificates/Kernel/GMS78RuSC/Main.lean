module

public import Certificates.Data.Kernel.GMS78RuSCent
import CFSG.Certificates.Kernel.GMS78RuSC.Mul
import CFSG.Certificates.Kernel.GMS78RuSC.Cent
import CFSG.Certificates.Kernel.GMS78RuSC.Core
import CFSG.Certificates.Kernel.GMS78RuP.Basic

public section

namespace CFSG.KC.GMS.SC

open CFSG.KLie.CT CFSG.KC.Loop

private theorem sRowP_eq (GT : List (List Nat)) (DPR : List Nat) (LIN DM DO IDX : Nat)
    (C : List Nat) (p : Nat) :
    sRowP GT DPR LIN DM DO IDX C p = rowF (mul17K GT DPR LIN DM DO) IDX C p := by
  unfold sRowP rowF
  beta_reduce
  rw [P117.strictN_eq, P117.strictN_eq]
  beta_reduce
  rw [czPack9_eq]
  rw [listRec_map (fun q => fget IDX (sMulRow LIN DM DO (sGamRow GT (Nat.land p 255))
    (neGet 0 DPR (Nat.land (Nat.shiftRight p 10) 7)) (Nat.land p 255)
    (Nat.mul 2 (Nat.land (Nat.shiftRight p 8) 3)) (Nat.land (Nat.shiftRight p 10) 7) q) 9) C]
  congr 1
  apply List.map_congr_left
  intro q _
  rw [mul17K_eq_row]

private theorem sRows_eq (GT : List (List Nat)) (DPR : List Nat) (LIN DM DO IDX : Nat)
    (C : List Nat) :
    sRows GT DPR LIN DM DO IDX C = C.map (rowF (mul17K GT DPR LIN DM DO) IDX C) := by
  unfold sRows
  have key : ∀ L : List Nat, List.rec (motive := fun _ => List Nat) []
      (fun p _ ih => List.cons (sRowP GT DPR LIN DM DO IDX C p) ih) L =
      L.map (rowF (mul17K GT DPR LIN DM DO) IDX C) := by
    intro L
    induction L with
    | nil => rfl
    | cons p L ih =>
      dsimp only
      rw [ih, sRowP_eq, List.map_cons]
  exact key C

theorem kAll17_sound (GT : List (List Nat)) (DPR : List Nat) (LIN DM DO u k : Nat)
    (h : kAll17 GT DPR LIN DM DO u k = true) :
    kKey17 (mul17K GT DPR LIN DM DO) u k = true ∧ kClo17 (mul17K GT DPR LIN DM DO) u k = true := by
  unfold kAll17 at h
  rw [neStrictB_eq, neStrictB_eq] at h
  beta_reduce at h
  have hm : CommTests (mul17K GT DPR LIN DM DO) DPR DM u := fun p hp =>
    comm_tests GT DPR LIN DM DO p u hp
  rw [sCent17_eq _ DPR DM u hm, sKeyL_filter] at h
  unfold kKey17 kClo17
  rw [P117.sFilter_eq]
  generalize hF : (List.range 8192).filter (fun p => Nat.beq (mul17K GT DPR LIN DM DO p u)
    (mul17K GT DPR LIN DM DO u p)) = F at h ⊢
  have hnd : F.Nodup := hF ▸ (List.nodup_range.filter _)
  generalize kNeedZ u k = b at h ⊢
  cases b
  · dsimp only at h ⊢
    exact ⟨h, rfl⟩
  · dsimp only at h ⊢
    obtain ⟨hK, h3⟩ := P117.andB_iff.1 h
    obtain ⟨h4, h5⟩ := P117.andB_iff.1 h3
    have hlen : F.length = 256 := by
      rw [← neLen_eq]
      exact Nat.eq_of_beq_eq_true h4
    unfold sZxR at h5
    beta_reduce at h5
    rw [sRows_eq] at h5
    obtain ⟨hc, hz'⟩ := zx_core _ F hnd hlen u _ h5
    refine ⟨?_, hc⟩
    rw [P117.andB_iff]
    refine ⟨hK, P117.andB_iff.2 ⟨h4, ?_⟩⟩
    rw [hz']
    exact Nat.beq_refl _

end CFSG.KC.GMS.SC

end
