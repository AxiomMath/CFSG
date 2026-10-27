module

public import Certificates.Data.Kernel.Spor.MulHCay
public import CFSG.Certificates.Kernel.Spor.MulHSound
public import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KS.MulHCay

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH

theorem pcomp_assoc_c {n w p q r : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hr : canonK n w (mask w) (n * w) r = true) :
    pcomp n w (mask w) (pcomp n w (mask w) p q) r =
      pcomp n w (mask w) p (pcomp n w (mask w) q r) := by
  obtain ⟨hn, hw, -, -⟩ := PF.canon_facts hp
  obtain ⟨-, -, -, hrr⟩ := PF.canon_facts hr
  have hn32 : n < 2 ^ 32 := by omega
  have hw0 := PF.w_pos hw
  refine PF.eq_of_fields hw0 (PF.pcomp_shr _ _ hn32 hw0) (PF.pcomp_shr _ _ hn32 hw0) fun i hi => ?_
  rw [PF.pg_pcomp hn32 hi, PF.pg_pcomp hn32 (hrr i hi), PF.pg_pcomp hn32 hi,
    PF.pg_pcomp hn32 hi]

theorem pcomp_id_c {n w p : Nat} (hp : canonK n w (mask w) (n * w) p = true) :
    pcomp n w (mask w) p (pidn n w) = p ∧ pcomp n w (mask w) (pidn n w) p = p := by
  obtain ⟨hn, hw, hp0, hpr⟩ := PF.canon_facts hp
  have hn32 : n < 2 ^ 32 := by omega
  have hw0 := PF.w_pos hw
  refine ⟨PF.eq_of_fields hw0 (PF.pcomp_shr _ _ hn32 hw0) hp0 fun i hi => ?_,
    PF.eq_of_fields hw0 (PF.pcomp_shr _ _ hn32 hw0) hp0 fun i hi => ?_⟩
  · rw [PF.pg_pcomp hn32 hi, PF.pg_pidn hn hw hi]
  · rw [PF.pg_pcomp hn32 hi, PF.pg_pidn hn hw (hpr i hi)]

theorem powPK_succ (n w m p e : Nat) : powPK n w m p (e + 1) = pcomp n w m p (powPK n w m p e) :=
  rfl

theorem cayPtK_spec {cnt k i j : Nat} {PL POS M : Nat → Nat} (hj : j < cnt)
    (h : cayPtK cnt k PL POS M (cnt * i + j) = true) :
    r32 M (cnt * i + j) < cnt ∧ (j = 0 → r32 M (cnt * i + j) = i) ∧
      (j ≠ 0 → r32 M (cnt * i + j) =
        r32 POS (r32 M (cnt * i + parOf PL j) * k + labOf PL j)) := by
  have hc : 0 < cnt := by omega
  have e1 : Nat.div (cnt * i + j) cnt = i := by
    change (cnt * i + j) / cnt = i
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hc, Nat.div_eq_of_lt hj, Nat.zero_add]
  have e2 : Nat.mod (cnt * i + j) cnt = j := by
    change (cnt * i + j) % cnt = j
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  unfold cayPtK at h
  rw [CFSG.KS.Raw.Orb.strictB_eq, e1, CFSG.KS.Raw.Orb.strictB_eq, e2,
    CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, CFSG.KS.Raw.Orb.bIf_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨Nat.le_of_ble_eq_true h1, fun h0 => ?_, fun h0 => ?_⟩
  · subst h0
    simpa using h2
  · have hb : Nat.beq j 0 = false := by
      cases e : Nat.beq j 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) h0
    rw [hb] at h2
    exact Nat.eq_of_beq_eq_true h2

theorem cay_sound {n w k cnt : Nat} {G GI T PL POS SRT SRI M : Nat → Nat}
    (hG : ∀ j < k, G j = pidn n w)
    (hGI : ∀ j < k, canonK n w (mask w) (n * w) (GI j) = true)
    (hT0 : T 0 = pidn n w)
    (hp : ∀ i < cnt, penumPtK n w (mask w) (n * w) true G GI k cnt T PL POS SRT SRI i = true)
    (hc : ∀ c < cnt * cnt, cayPtK cnt k PL POS M c = true) :
    ∀ i < cnt, ∀ j < cnt, r32 M (cnt * i + j) < cnt ∧
      pcomp n w (mask w) (T i) (T j) = T (r32 M (cnt * i + j)) := by
  intro i hi j
  induction j using Nat.strongRecOn with
  | _ j ih =>
    intro hj
    have hcj : cnt * i + j < cnt * cnt := by
      have := Nat.mul_le_mul_left cnt (Nat.succ_le_of_lt hi)
      rw [Nat.mul_succ] at this
      omega
    obtain ⟨hq, h0, hs⟩ := cayPtK_spec hj (hc _ hcj)
    have hTi := (penumPt_specH (hp i hi)).1
    refine ⟨hq, ?_⟩
    rcases Nat.eq_zero_or_pos j with rfl | hjp
    · rw [h0 rfl, hT0]
      exact (pcomp_id_c hTi).1
    · have hj0 : j ≠ 0 := by omega
      obtain ⟨hpar, hlab, hTj, -⟩ := (penumPt_specH (hp j hj)).2.1 hj0
      obtain ⟨hq', e'⟩ := ih (parOf PL j) hpar (by omega)
      obtain ⟨hpos, hTpos, -⟩ :=
        (penumPt_specH (hp _ hq')).2.2.1 (labOf PL j) hlab
      have hGl := hGI (labOf PL j) hlab
      have step : ∀ t, canonK n w (mask w) (n * w) t = true →
          stepK n w (mask w) true G GI (labOf PL j) t = pcomp n w (mask w) t (GI (labOf PL j)) := by
        intro t ht
        change pcomp n w (mask w) (pcomp n w (mask w) (G (labOf PL j)) t) (GI (labOf PL j)) = _
        rw [hG _ hlab, (pcomp_id_c ht).2]
      have hTpar := (penumPt_specH (hp _ (by omega : parOf PL j < cnt))).1
      have hTq' := (penumPt_specH (hp _ hq')).1
      rw [hs hj0, hTpos, step _ hTq', ← e', hTj, step _ hTpar, pcomp_assoc_c hTi hGl]

end CFSG.KS.MulHCay

end
