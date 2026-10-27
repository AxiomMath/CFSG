module

public import CFSG.Certificates.Kernel.MaxD2.Test
public import Certificates.Data.Kernel.MaxD2.Pair

public section

namespace CFSG.KS.MaxD2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.Row CFSG.PSL3Four.Native

theorem testK_spec' {n w np kw cnt : Nat} {PT T FS KS RB : Nat → Nat} {RP RPI k h : Nat}
    (hn : szOK n w = true) (hT : ∀ e < cnt, Cn n w (T e))
    (hs : ∀ s < cnt, sortK w np kw cnt PT T FS KS s = true) (hP : ∀ t < np, PT t < n)
    (hRP : ∀ x < n, pg w (mask w) RP x < n)
    (hRB : ∀ t < np, RB t = pg w (mask w) RP (PT t)) (hk : k < cnt)
    (ht : testK n w np kw cnt T FS KS RP RPI RB k h = true) :
    (∃ e < cnt, T e = pcomp n w (mask w) (pcomp n w (mask w) RPI (T k)) RP) ↔
      Nat.land h 1 = 1 := by
  have hY : ∀ x < n, pg w (mask w) (pcomp n w (mask w) (pcomp n w (mask w) RPI (T k)) RP) x =
      pg w (mask w) RPI (pg w (mask w) (T k) (pg w (mask w) RP x)) := fun x hx => by
    rw [pg_pc hn hx, pg_pc hn (hRP x hx)]
  have hkey : keyT w np (fun t => pg w (mask w) RPI (pg w (mask w) (T k) (RB t))) =
      fpK w np PT (pcomp n w (mask w) (pcomp n w (mask w) RPI (T k)) RP) := by
    unfold fpK
    refine keyT_congr fun t htt => ?_
    rw [hY _ (hP t htt), hRB t htt]
  unfold testK at ht
  rw [PK.strictB_eq] at ht
  by_cases h1 : Nat.beq (Nat.land h 1) 1 = true
  · have ht' := bif_t h1 ht
    rw [PK.strictB_eq] at ht'
    obtain ⟨he, hq⟩ := band_e ht'
    exact ⟨fun _ => Nat.eq_of_beq_eq_true h1,
      fun _ => ⟨_, Nat.blt_eq.mp he, (Nat.eq_of_beq_eq_true hq).symm⟩⟩
  · have ht' := bif_f (Bool.eq_false_iff.2 h1) ht
    rw [PK.strictB_eq, hkey] at ht'
    have hne : Nat.land h 1 ≠ 1 := fun e => h1 (by rw [e]; rfl)
    refine ⟨fun ⟨e, he, hEq⟩ => absurd ?_ hne, fun e => absurd e hne⟩
    by_cases h2 : Nat.beq (Nat.land h 2) 0 = true
    · have h3 := bif_t h2 ht'
      rw [PK.strictB_eq] at h3
      obtain ⟨hq, h3⟩ := band_e h3
      obtain ⟨h0, h1'⟩ := band_e h3
      refine absurd (congrArg (fpK w np PT) hEq) (sort_absent hs (Nat.ble_eq.mp hq) ?_ ?_ he)
      · rcases bor_e h0 with z | z
        · exact Or.inl (Nat.eq_of_beq_eq_true z)
        · exact Or.inr (Nat.blt_eq.mp z)
      · rcases bor_e h1' with z | z
        · exact Or.inl (Nat.eq_of_beq_eq_true z)
        · exact Or.inr (Nat.blt_eq.mp z)
    · have h3 := bif_f (Bool.eq_false_iff.2 h2) ht'
      rw [PK.strictB_eq, PK.strictB_eq] at h3
      obtain ⟨hsc, h3⟩ := band_e h3
      obtain ⟨hpn, h3⟩ := band_e h3
      obtain ⟨hy, hd⟩ := band_e h3
      have hs' := Nat.blt_eq.mp hsc
      have hp' := Nat.blt_eq.mp hpn
      have e1 : fpK w np PT (T e) = fpK w np PT (T (r32 FS (Nat.land (Nat.shiftRight h 2) 65535))) := by
        rw [hEq, Nat.eq_of_beq_eq_true hy, (sort_pt hs hs').2.1]
      have e2 := sort_keyInj hs he (sort_pt hs hs').1 e1
      rw [← e2, hEq, hY _ hp', Nat.beq_refl] at hd
      exact absurd hd (by decide)

theorem pairK_spec {n w np kw cnt : Nat} {PT T FS KS REP REPI RB2 H2 : Nat → Nat} {q i j k : Nat}
    (hn : szOK n w = true) (hT : ∀ e < cnt, Cn n w (T e))
    (hs : ∀ s < cnt, sortK w np kw cnt PT T FS KS s = true) (hP : ∀ t < np, PT t < n)
    (hRP : ∀ x < n, pg w (mask w) (REP j) x < n) (hk : k < cnt)
    (hp : pairK n w np kw cnt PT T FS KS REP REPI RB2 H2 q i j = true) :
    ¬ ∃ e < cnt, T e = pcomp n w (mask w) (pcomp n w (mask w) (REPI i) (T k)) (REP j) := by
  unfold pairK at hp
  simp only [PK.strictB_eq] at hp
  obtain ⟨hrb, hts⟩ := band_e hp
  have hk' := (PK.allN_iff.1 hts) k hk
  obtain ⟨hev, ht⟩ := band_e hk'
  rw [testK_spec' hn hT hs hP hRP
    (fun t htt => Nat.eq_of_beq_eq_true ((PK.allN_iff.1 hrb) t htt)) hk ht,
    Nat.eq_of_beq_eq_true hev]
  decide

end CFSG.KS.MaxD2

end
