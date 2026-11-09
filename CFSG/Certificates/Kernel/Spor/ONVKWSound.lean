module

public import Certificates.Data.Kernel.Spor.ONVKW
public import CFSG.Certificates.Kernel.Spor.ONLineKWSound
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.Loops

public section

set_option exponentiation.threshold 600

namespace CFSG.KS.ONW

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON

theorem ptsV_spec {X Y : Nat → Nat} {pre : Nat → Nat → Nat → Bool} {lo : Nat}
    {fin : Nat → Nat → Bool} :
    ∀ (k xx xy : Nat), ptsV X Y pre lo fin k xx xy = true →
      (∀ i < k, pre (lo + i) (X (lo + i)) (Y (lo + i)) = true) ∧
      fin (encF k (fun i => X (lo + i)) + 2 ^ (512 * k) * xx)
        (encF k (fun i => Y (lo + i)) + 2 ^ (512 * k) * xy) = true
  | 0, xx, xy, h => by
    refine ⟨fun i hi => absurd hi (Nat.not_lt_zero i), ?_⟩
    change fin xx xy = true at h
    have e : ∀ f : Nat → Nat, encF 0 f = 0 := fun f => by
      rw [enc_congr 0 f (fun _ => 0) (fun i hi => absurd hi (Nat.not_lt_zero i)), enc_zero]
    rw [e, e, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.one_mul, Nat.zero_add, Nat.zero_add]
    exact h
  | k + 1, xx, xy, h => by
    change (strictB (Nat.add lo k) fun h => strictB (X h) fun x => strictB (Y h) fun y =>
      bAnd(pre h x y,
        strictB (Nat.add x (Nat.shiftLeft xx 512)) fun xx' =>
        strictB (Nat.add y (Nat.shiftLeft xy 512)) fun xy' =>
          ptsV X Y pre lo fin k xx' xy')) = true at h
    simp only [PackFld.strictB_eqP] at h
    obtain ⟨hp, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨ih1, ih2⟩ := ptsV_spec k _ _ h
    refine ⟨fun i hi => ?_, ?_⟩
    · rcases Nat.lt_or_ge i k with hik | hik
      · exact ih1 i hik
      · have : i = k := by omega
        subst this
        exact hp
    · have e : ∀ (f : Nat → Nat) (x : Nat), encF k f + 2 ^ (512 * k) * Nat.add (f k) (Nat.shiftLeft x 512) =
          encF (k + 1) f + 2 ^ (512 * (k + 1)) * x := by
        intro f x
        rw [enc_top, PackFld.shl_eq, Nat.add_eq, show 512 * (k + 1) = 512 * k + 512 by omega,
          Nat.pow_add]
        simp only [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm x]
        omega
      have e1 := e (fun i => X (lo + i)) xx
      have e2 := e (fun i => Y (lo + i)) xy
      simp only [Nat.add_eq] at e1 e2 ih2
      rw [e1, e2] at ih2
      exact ih2

theorem enc_lo {cnt : Nat} {f : Nat → Nat} (hf : Bd cnt f) :
    Nat.land (encF cnt f) (encF cnt (fun _ => mask 256)) = encF cnt (fun i => vP (f i)) := by
  have := enc_sel lo_eq.1 cnt f hf
  rw [Nat.shiftRight_zero] at this
  change (encF cnt f &&& encF cnt (fun _ => mask 256)) = _
  rw [this]
  simp only [Nat.shiftRight_zero]
  rfl

theorem enc_hi {cnt : Nat} {f : Nat → Nat} (hf : Bd cnt f) :
    Nat.land (Nat.shiftRight (encF cnt f) 256) (encF cnt (fun _ => mask 256)) =
      encF cnt (fun i => vM (f i)) := by
  have := enc_sel lo_eq.2 cnt f hf
  change (encF cnt f >>> 256) &&& encF cnt (fun _ => mask 256) = _
  rw [this]
  exact enc_congr cnt _ _ fun i hi => field_hi (hf i hi)

theorem mv_eq_mvL (L : List Nat) (x : Nat) : mv L x = mvL L (vP x >>> 0) (vM x >>> 0) 0 0 := by
  simp only [mv, PackFld.strictN_eqP, Nat.shiftRight_zero]

theorem finE_spec {L : List Nat} {cnt : Nat} {fX fY : Nat → Nat} (hX : Bd cnt fX)
    (hY : Bd cnt fY) (hc : ∀ i < cnt, canon (fX i) = true)
    (h : finE L cnt (encF cnt fX) (encF cnt fY) = true) : ∀ i < cnt, mv L (fX i) = fY i := by
  unfold finE at h
  simp only [PackFld.strictB_eqP, rep_eq] at h
  rw [enc_lo hX, enc_hi hX, enc_lo hY, enc_hi hY] at h
  have bP : ∀ {f : Nat → Nat}, Bd cnt (fun i => vP (f i)) := fun _ _ => lt512_of_lt256 (vP_lt _)
  have bM : ∀ {f : Nat → Nat}, Bd cnt f → Bd cnt (fun i => vM (f i)) :=
    fun hf i hi => lt512_of_lt256 (vM_lt (hf i hi))
  have hd : ∀ i < cnt, vP (fX i) &&& vM (fX i) = 0 := fun i hi => (canon_bits (hc i hi)).1
  have b0 : Bd cnt (fun _ => 0) := fun _ _ => Nat.two_pow_pos 512
  have s := wmvL_spec bP (bM hX) bP (bM hY) hd L 0 _ _ b0 b0 (by rw [enc_zero]; exact h)
  intro i hi
  rw [mv_eq_mvL, s i hi, vmk_vP_vM]

theorem finP_spec {L : List Nat} {cnt : Nat} {fX fY : Nat → Nat} (hX : Bd cnt fX)
    (hY : Bd cnt fY) (hc : ∀ i < cnt, canon (fX i) = true)
    (h : finP L cnt (encF cnt fX) (encF cnt fY) = true) :
    ∀ i < cnt, pmEq (fY i) (mv L (fX i)) = true := by
  unfold finP at h
  simp only [PackFld.strictB_eqP, rep_eq] at h
  rw [enc_lo hX, enc_hi hX, enc_lo hY, enc_hi hY] at h
  have bP : ∀ {f : Nat → Nat}, Bd cnt (fun i => vP (f i)) := fun _ _ => lt512_of_lt256 (vP_lt _)
  have bM : ∀ {f : Nat → Nat}, Bd cnt f → Bd cnt (fun i => vM (f i)) :=
    fun hf i hi => lt512_of_lt256 (vM_lt (hf i hi))
  have hd : ∀ i < cnt, vP (fX i) &&& vM (fX i) = 0 := fun i hi => (canon_bits (hc i hi)).1
  have b0 : Bd cnt (fun _ => 0) := fun _ _ => Nat.two_pow_pos 512
  obtain ⟨ap, am, hap, ham, fA, sA⟩ :=
    wmvLT_spec bP (bM hX) hd L 0 _ _ b0 b0 (by rw [enc_zero]; exact h)
  have pA := pmW_spec bP (bM hY) hap ham fA
  intro i hi
  rw [mv_eq_mvL, sA i hi]
  rcases pA i hi with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1, e2, vmk_vP_vM]
    exact pmEq_self _
  · rw [e1, e2]
    exact pmEq_neg _

theorem sigRangeW_imp {KS K : Nat → Nat} {LT : List Nat} {lo cnt : Nat}
    (h : sigRangeW KS K LT lo cnt = true) : sigRange KS K LT lo cnt = true := by
  obtain ⟨h1, h2⟩ := ptsV_spec cnt 0 0 h
  simp only [Nat.mul_zero, Nat.add_zero] at h2
  have hc : ∀ i < cnt, canon (key K (lo + i)) = true ∧ canon (key KS (lo + i)) = true :=
    fun i hi => (bAnd_iff _ _).1 (h1 i hi)
  have hf := finE_spec (fun i _ => key_lt K _) (fun i _ => key_lt KS _) (fun i hi => (hc i hi).1) h2
  refine allBlk_of fun l hl => ?_
  unfold sigAt
  simp only [PackFld.strictB_eqP]
  rw [(hc l hl).2, hf l hl]
  simp [Nat.beq_refl]

end CFSG.KS.ONW

end
