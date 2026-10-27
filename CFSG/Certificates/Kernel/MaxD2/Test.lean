module

public import CFSG.Certificates.Kernel.MaxD2.Basic

public section

namespace CFSG.KS.MaxD2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.Row CFSG.PSL3Four.Native
open Certificates.MaxD2Perm

theorem ite_true_or {c b : Bool} (h : (if c = true then true else b) = true) :
    c = true ∨ b = true := by
  cases c
  · exact Or.inr h
  · exact Or.inl rfl

theorem keyT_succ (w np : Nat) (g : Nat → Nat) :
    keyT w (np + 1) g = Nat.lor (keyT w np g) (Nat.shiftLeft (g np) (Nat.mul w np)) := rfl

theorem keyT_congr {w : Nat} {f g : Nat → Nat} : ∀ {np : Nat}, (∀ t < np, f t = g t) →
    keyT w np f = keyT w np g
  | 0, _ => rfl
  | np + 1, h => by
    rw [keyT_succ, keyT_succ, keyT_congr fun t ht => h t (by omega), h np (by omega)]

@[expose] def PtsOK (n np : Nat) (pts : List Nat) (PT : Nat → Nat) : Prop :=
  pts.length = np ∧ ∀ t < np, pts[t]! = PT t ∧ PT t < n

theorem fpK_of_fpTab {n w np : Nat} {pts : List Nat} {PT : Nat → Nat} (hP : PtsOK n np pts PT)
    {a b : Nat} (h : fpTab pts (unpack n w a) = fpTab pts (unpack n w b)) :
    fpK w np PT a = fpK w np PT b := by
  unfold fpK
  refine keyT_congr fun t ht => ?_
  obtain ⟨hl, hp⟩ := hP
  have e := congrArg (fun A : Tab => A[t]!) h
  simp only [fpTab] at e
  have htl : t < pts.length := by omega
  rw [getElem!_pos _ t (by simpa using htl), getElem!_pos _ t (by simpa using htl)] at e
  simp only [List.getElem_toArray, List.getElem_map] at e
  have hpt : pts[t] = PT t := by
    have := (hp t ht).1
    rwa [getElem!_pos pts t htl] at this
  rw [hpt, get_u (hp t ht).2, get_u (hp t ht).2] at e
  exact e

section

variable {w np kw cnt : Nat} {PT T FS KS : Nat → Nat}

local notation "K" s => rg kw (mask kw) KS (nat_lit 0) s

theorem sort_pt (hs : ∀ s < cnt, sortK w np kw cnt PT T FS KS s = true) {s : Nat} (h : s < cnt) :
    r32 FS s < cnt ∧ (K s) = fpK w np PT (T (r32 FS s)) ∧ (s + 1 < cnt → (K s) < (K (s + 1))) := by
  have e := hs s h
  unfold sortK at e
  rw [PK.strictB_eq, PK.strictB_eq] at e
  obtain ⟨h1, e⟩ := band_e e
  obtain ⟨h2, h3⟩ := band_e e
  exact ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2,
    fun hc => Nat.blt_eq.mp (bif_t (Nat.blt_eq.mpr hc) h3)⟩

theorem sort_mono (hs : ∀ s < cnt, sortK w np kw cnt PT T FS KS s = true) {s s' : Nat}
    (h : s < s') (h' : s' < cnt) : (K s) < (K s') := by
  induction s' with
  | zero => omega
  | succ s' ih =>
    have step := (sort_pt hs (s := s') (by omega)).2.2 h'
    rcases Nat.lt_or_ge s s' with a | a
    · exact lt_trans (ih a (by omega)) step
    · have : s = s' := by omega
      subst this
      exact step

theorem sort_inj (hs : ∀ s < cnt, sortK w np kw cnt PT T FS KS s = true) {s s' : Nat}
    (h : s < cnt) (h' : s' < cnt) (e : (K s) = (K s')) : s = s' := by
  rcases Nat.lt_trichotomy s s' with a | a | a
  · exact absurd e (Nat.ne_of_lt (sort_mono hs a h'))
  · exact a
  · exact absurd e.symm (Nat.ne_of_lt (sort_mono hs a h))

theorem sort_cover (hs : ∀ s < cnt, sortK w np kw cnt PT T FS KS s = true) {m : Nat}
    (hm : m < cnt) : ∃ s < cnt, r32 FS s = m := by
  have hsurj := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range cnt) (t := Finset.range cnt)
    (fun a _ => r32 FS a) (fun a ha => by simpa using (sort_pt hs (by simpa using ha)).1)
    (fun a₁ a₂ h₁ h₂ e => by
      have h₁' : a₁ < cnt := by simpa using h₁
      have h₂' : a₂ < cnt := by simpa using h₂
      have e' : r32 FS a₁ = r32 FS a₂ := e
      refine sort_inj hs h₁' h₂' ?_
      rw [(sort_pt hs h₁').2.1, (sort_pt hs h₂').2.1, e']) le_rfl
  obtain ⟨s, hs', e⟩ := hsurj m (by simpa using hm)
  exact ⟨s, by simpa using hs', e.symm⟩

theorem sort_keyInj (hs : ∀ s < cnt, sortK w np kw cnt PT T FS KS s = true) {a b : Nat}
    (ha : a < cnt) (hb : b < cnt) (e : fpK w np PT (T a) = fpK w np PT (T b)) : a = b := by
  obtain ⟨s, hs1, rfl⟩ := sort_cover hs ha
  obtain ⟨s', hs2, rfl⟩ := sort_cover hs hb
  rw [← (sort_pt hs hs1).2.1, ← (sort_pt hs hs2).2.1] at e
  rw [sort_inj hs hs1 hs2 e]

theorem sort_absent (hs : ∀ s < cnt, sortK w np kw cnt PT T FS KS s = true) {q y : Nat}
    (hq : q ≤ cnt) (h0 : q = 0 ∨ (K (q - 1)) < y) (h1 : q = cnt ∨ y < (K q)) {m : Nat}
    (hm : m < cnt) : fpK w np PT (T m) ≠ y := by
  intro e
  obtain ⟨s, hs1, rfl⟩ := sort_cover hs hm
  rw [← (sort_pt hs hs1).2.1] at e
  rcases Nat.lt_or_ge s q with a | a
  · rcases h0 with h0 | h0
    · omega
    · have : (K s) ≤ (K (q - 1)) := by
        rcases Nat.lt_or_ge s (q - 1) with b | b
        · exact Nat.le_of_lt (sort_mono hs b (by omega))
        · rw [show s = q - 1 by omega]
      omega
  · rcases h1 with h1 | h1
    · omega
    · have : (K q) ≤ (K s) := by
        rcases Nat.lt_or_ge q s with b | b
        · exact Nat.le_of_lt (sort_mono hs b hs1)
        · rw [show s = q by omega]
      omega

end

theorem testK_spec {n w np kw cnt : Nat} {PT T FS KS RB : Nat → Nat} {RP RPI k h : Nat}
    (hn : szOK n w = true) (hT : ∀ e < cnt, Cn n w (T e))
    (hs : ∀ s < cnt, sortK w np kw cnt PT T FS KS s = true) (hP : ∀ t < np, PT t < n)
    (hRP : permOK n w (mask w) (n * w) RP RPI = true)
    (hRB : ∀ t < np, RB t = pg w (mask w) RP (PT t)) (hk : k < cnt)
    (ht : testK n w np kw cnt T FS KS RP RPI RB k h = true) :
    (∃ e < cnt, T e = pcomp n w (mask w) (pcomp n w (mask w) RPI (T k)) RP) ↔
      Nat.land h 1 = 1 := by
  have hpr := perm_spec hRP
  have hY : ∀ x < n, pg w (mask w) (pcomp n w (mask w) (pcomp n w (mask w) RPI (T k)) RP) x =
      pg w (mask w) RPI (pg w (mask w) (T k) (pg w (mask w) RP x)) := fun x hx => by
    rw [pg_pc hn hx, pg_pc hn ((hpr.1 x hx).1)]
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

end CFSG.KS.MaxD2

end
