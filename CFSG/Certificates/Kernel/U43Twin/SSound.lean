module

public import Certificates.Data.Kernel.U43Twin.Psi
public import Certificates.Data.U43TwinCheck
public import CFSG.Certificates.Kernel.U43Pk.CoverSound
import CFSG.Certificates.Kernel.PackSetSound

public section

namespace CFSG.KS.U43Twin

open CFSG.KD.U43Pk CFSG.KD.U43Twin CFSG.KS.U43Pk CFSG.KC.Enum CFSG.KC.Pack
open CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check Certificates.U43Twin

theorem commK_spec {X Y : ℕ} (hX : Dig X) (hY : Dig Y) (h : commK X Y = true) :
    commC (dec X) (dec Y) = true := by
  unfold commK at h
  rw [strictB_eq] at h
  unfold commC
  rw [mulRaw_dec hX hY, mulRaw_dec hY hX, eqZ_dec (mulK_dig hX hY) (mulK_dig hY hX)]
  exact h

theorem invertC_dec {P : ℕ} (hP : rawValidK P = true) (hH : rawValidK (conjTK P) = true)
    (hZ : isZK (mulK P (conjTK P)) = true) : invertC (dec P) = true := by
  have hd := (rawValidK_spec hP).2.1
  unfold invertC
  rw [conjT_dec hd, rawValid_dec hP, rawValid_dec hH, mulRaw_dec hd (conjTK_dig _ hd),
    isZ_dec (mulK_lt _ _), hZ]
  rfl

theorem psiRowK_spec {L H : ℕ → ℕ} {M : ℕ → ℕ → ℕ} {P Q a : ℕ} (h : psiRowK L H M P Q a = true) :
    rawValidK (L a) = true ∧ rawValidK (H a) = true ∧ commK (L a) P = true ∧
      commK (L a) Q = true ∧ ∀ b < 24,
        Nat.beq (nrmK (L (M a b))) (nrmK (mulK (L a) (L b))) = true ∧ commK (L a) (H b) = true := by
  unfold psiRowK at h
  rw [strictB_eq] at h
  obtain ⟨h1, h⟩ := bAnd_spec h
  obtain ⟨h2, h⟩ := bAnd_spec h
  obtain ⟨h3, h⟩ := bAnd_spec h
  obtain ⟨h4, h⟩ := bAnd_spec h
  refine ⟨h1, h2, h3, h4, fun b hb => ?_⟩
  have e := allBlk_spec h b hb
  rw [Nat.add_eq, Nat.zero_add] at e
  exact bAnd_spec e

end CFSG.KS.U43Twin

end
