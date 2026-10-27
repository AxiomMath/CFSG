module

public import Certificates.Data.Kernel.Spor.OrbTreeK
public import CFSG.Sporadic.FischerOddCore.FischerOuterFi22CheckInputs
import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KS.OrbTree

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem upk_size (n w P : Nat) : (unpack n w P).size = n := by
  simp [unpack]

theorem get_of_shr {m w L : Nat} (h : Nat.shiftRight L (m * w) = 0) (x : Nat) :
    (unpack m w L)[x]! = pg w (mask w) L x := by
  rcases Nat.lt_or_ge x m with hx | hx
  · exact Orb.unpack_get hx
  · rw [getElem!_neg _ _ (by rw [upk_size]; omega), Orb.pg_eq]
    have hL : L < 2 ^ (m * w) := by
      have e : Nat.shiftRight L (m * w) = L / 2 ^ (m * w) := Nat.shiftRight_eq_div_pow L _
      rw [e] at h
      rcases Nat.div_eq_zero_iff.1 h with h' | h'
      · exact absurd h' (Nat.two_pow_pos _).ne'
      · exact h'
    have hle : 2 ^ (m * w) ≤ 2 ^ (w * x) :=
      Nat.pow_le_pow_right (by decide) (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left w hx)
    rw [Nat.div_eq_of_lt (by omega)]
    rfl

theorem isInvA_ord {m wl ORD : Nat}
    (h : permOK m wl (mask wl) (m * wl) ORD (pinvS m wl (mask wl) ORD) = true) :
    isInvA m (unpack m wl ORD) (invCand m (unpack m wl ORD)) = true := by
  have hr := (rep_permOfArr (Orb.isInvA_unpack h)).1
  exact isInvA_of_rep hr (rep_invCand hr)

theorem ofFn_get {kS : Nat} {f : Nat → Array Nat} {g : Nat} (hg : g < kS) :
    (Array.ofFn (n := kS) fun i => f i.val)[g]! = f g := by
  rw [getElem!_pos _ g (by simpa using hg), Array.getElem_ofFn]

theorem le_of_succ {f : Nat → Nat} {K : Nat} (h : ∀ c < K, f c < f (c + 1)) :
    ∀ c ≤ K, f c ≤ f K := by
  have key : ∀ j c, c + j = K → f c ≤ f K := by
    intro j
    induction j with
    | zero =>
      intro c hc
      rw [← hc]
      rfl
    | succ j ih =>
      intro c hc
      exact (h c (by omega)).le.trans (ih (c + 1) (by omega))
  intro c hc
  exact key (K - c) c (by omega)

theorem treeK_sound {m w wl wb kS : Nat} {PS : Nat → Nat} {ORD PAR GEN : Nat}
    (hk : 2 ≤ kS) (h : treeK m w wl wb PS ORD PAR GEN = true) :
    fo22TreeOK m (Array.ofFn (n := kS) fun g => unpack m w (PS g.val)) (unpack m wl ORD)
      (unpack m wl PAR) (unpack m wb GEN) = true := by
  simp only [treeK, Orb.bAnd_eq, Bool.and_eq_true, Orb.allN_iff] at h
  obtain ⟨hperm, h0, -, -, hall⟩ := h
  obtain ⟨-, -, hpf⟩ := Orb.permOK_facts hperm
  unfold fo22TreeOK
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc]
  refine ⟨upk_size _ _ _, upk_size _ _ _, upk_size _ _ _, isInvA_ord hperm, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [unpack]
    · rw [Orb.unpack_get hm]
      exact Nat.eq_of_beq_eq_true h0
  · rw [allLt_iff]
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rfl
    · have hh := hall i hi
      have hb : Nat.beq i 0 = false := by
        cases e : Nat.beq i 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e) (by omega)
      rw [Orb.bIf_eq, hb] at hh
      simp only [Bool.false_eq_true, ↓reduceIte, Orb.strictB_eq, Bool.and_eq_true,
        Nat.blt_eq] at hh
      obtain ⟨hp, hg, he⟩ := hh
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      right
      rw [Orb.unpack_get (P := PAR) hi, Orb.unpack_get (P := GEN) hi,
        Orb.unpack_get (P := ORD) hi, Orb.unpack_get (P := ORD) (by omega : _ < m),
        ofFn_get (f := fun g => unpack m w (PS g)) (by omega : _ < kS),
        Orb.unpack_get (hpf _ (by omega)).1]
      exact ⟨⟨hp, hg⟩, Nat.eq_of_beq_eq_true he⟩

theorem subK_sound {m w wl wb kS k : Nat} {PS : Nat → Nat} {start : Array Nat}
    {LAB ORD TPAR TGEN : Nat} (hm : 0 < m) (hs : start.size = k + 1)
    (h : subK m w wl wb kS k PS (fun c => start[c]!) LAB ORD TPAR TGEN = true) :
    fo22SubOK m (Array.ofFn (n := kS) fun g => unpack m w (PS g.val)) (unpack m wb LAB)
      (unpack m wl ORD) (unpack m wl TPAR) (unpack m wb TGEN) start k = true := by
  simp only [subK, Orb.bAnd_eq, Bool.and_eq_true, Orb.allN_iff, Orb.strictB_eq, Nat.add_eq,
    Nat.sub_eq, Nat.succ_eq_add_one] at h
  obtain ⟨hperm, hL, -, -, hlab, hs0, hsk, hinc, hl0, ho0, hcls, hinv⟩ := h
  obtain ⟨-, -, hpf⟩ := Orb.permOK_facts hperm
  have hLg := get_of_shr (Nat.eq_of_beq_eq_true hL)
  have hmono := le_of_succ (f := fun c => start[c]!) (fun c hc => Nat.blt_eq.mp (hinc c hc))
  have hskm : start[k]! = m := Nat.eq_of_beq_eq_true hsk
  unfold fo22SubOK
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc]
  refine ⟨upk_size _ _ _, upk_size _ _ _, upk_size _ _ _, upk_size _ _ _, hs, ?_,
    isInvA_ord hperm, Nat.eq_of_beq_eq_true hs0, hskm, ?_, ?_, ?_, ?_, ?_⟩
  · rw [allLt_iff]
    intro p hp
    rw [Orb.unpack_get hp]
    exact decide_eq_true (Nat.blt_eq.mp (hlab p hp))
  · rw [allLt_iff]
    intro c hc
    exact decide_eq_true (Nat.blt_eq.mp (hinc c hc))
  · rw [Orb.unpack_get hm]
    exact Nat.eq_of_beq_eq_true hl0
  · rw [Orb.unpack_get hm]
    exact Nat.eq_of_beq_eq_true ho0
  · rw [allLt_iff]
    intro c hc
    rw [allLt_iff]
    intro d hd
    have hh := hcls c hc d hd
    have hcm : start[c + 1]! ≤ m := hskm ▸ hmono (c + 1) (by omega)
    have hi : start[c]! + d < m := by omega
    have ho := hpf _ hi
    obtain ⟨h1, h2⟩ := hh
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
    rw [Orb.unpack_get (P := ORD) hi, Orb.unpack_get ho.1]
    refine ⟨Nat.eq_of_beq_eq_true h1, ?_⟩
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · exact Or.inl rfl
    · right
      have hb : Nat.beq d 0 = false := by
        cases e : Nat.beq d 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e) (by omega)
      rw [Orb.bIf_eq, hb] at h2
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, Nat.blt_eq,
        Nat.ble_eq] at h2
      obtain ⟨ht1, ht2, ht3, ht4, ht5⟩ := h2
      rw [Orb.unpack_get (P := TPAR) hi, Orb.unpack_get (P := TGEN) hi, Array.size_ofFn,
        ofFn_get (f := fun g => unpack m w (PS g)) ht3, Orb.unpack_get hm,
        Orb.unpack_get (P := ORD) (by omega : _ < m)]
      rw [Orb.unpack_get (hpf _ (by omega)).1]
      exact ⟨⟨⟨⟨ht1, ht2⟩, ht3⟩, Nat.eq_of_beq_eq_true ht4⟩, Nat.eq_of_beq_eq_true ht5⟩
  · rw [Array.size_ofFn, allLt_iff]
    intro g hg
    have hh := hinv g hg
    rw [ofFn_get (f := fun g => unpack m w (PS g)) hg, Orb.unpack_get hm]
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq]
    by_cases h0 : pg w (mask w) (PS g) 0 = 0
    · right
      have hb : Nat.beq (pg w (mask w) (PS g) 0) 0 = true := by rw [h0]; rfl
      rw [Orb.bIf_eq, hb] at hh
      simp only [↓reduceIte, Orb.allN_iff] at hh
      rw [allLt_iff]
      intro p hp
      rw [Orb.unpack_get hp, hLg, hLg, beq_iff_eq]
      exact Nat.eq_of_beq_eq_true (hh p hp)
    · exact Or.inl h0

theorem orbitK_sound {n m w wn kS kN : Nat} {NS PS : Nat → Nat} {O : Nat} (hm : 0 < m)
    (hk : 2 ≤ kS) (hkN : 2 ≤ kN) (hn : n ≤ 3510) (h : orbitK n m w wn NS PS O = true) :
    fo22OrbitOK (Array.ofFn (n := kN) fun g => unpack n wn (NS g.val)) (unpack m wn O)
      (Array.ofFn (n := kS) fun g => unpack m w (PS g.val)) m = true := by
  simp only [orbitK, Orb.bAnd_eq, Bool.and_eq_true, Orb.allN_iff, Orb.strictB_eq, Nat.blt_eq,
    Nat.sub_eq, Nat.succ_eq_add_one] at h
  obtain ⟨-, hlast, hinc, hall⟩ := h
  have hmono := le_of_succ (f := fun j => pg wn (mask wn) O j) hinc
  have hon : ∀ j < m, pg wn (mask wn) O j < n := fun j hj =>
    lt_of_le_of_lt (hmono j (by omega)) hlast
  unfold fo22OrbitOK
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc]
  refine ⟨upk_size _ _ _, ?_, ?_, ?_⟩
  · rw [Orb.unpack_get (by omega : m - 1 < m)]
    omega
  · rw [allLt_iff]
    intro j hj
    rw [Orb.unpack_get (by omega : j < m), Orb.unpack_get (by omega : j + 1 < m)]
    exact decide_eq_true (hinc j hj)
  · rw [allLt_iff]
    intro j hj
    obtain ⟨h0a, h0b⟩ := hall j hj 0 (by omega)
    obtain ⟨h1a, h1b⟩ := hall j hj 1 (by omega)
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    rw [ofFn_get (f := fun g => unpack m w (PS g)) (by omega : 0 < kS),
      ofFn_get (f := fun g => unpack m w (PS g)) (by omega : 1 < kS),
      ofFn_get (f := fun g => unpack n wn (NS g)) (by omega : 0 < kN),
      ofFn_get (f := fun g => unpack n wn (NS g)) (by omega : 1 < kN),
      Orb.unpack_get (P := PS 0) hj, Orb.unpack_get (P := PS 1) hj,
      Orb.unpack_get (P := O) hj, Orb.unpack_get (hon j hj), Orb.unpack_get (hon j hj),
      Orb.unpack_get h0a, Orb.unpack_get h1a]
    exact ⟨⟨⟨h0a, h1a⟩, Nat.eq_of_beq_eq_true h0b⟩, Nat.eq_of_beq_eq_true h1b⟩

theorem cex_orbitK : orbitK 4000 1 1 12 (fun _ => Nat.shiftLeft 3600 43200) (fun _ => 0) 3600 =
    true := by
  decide +kernel

theorem cex_fo22OrbitOK : fo22OrbitOK
    (Array.ofFn (n := 2) fun g => unpack 4000 12 ((fun _ => Nat.shiftLeft 3600 43200) g.val))
    (unpack 1 12 3600) (Array.ofFn (n := 2) fun g => unpack 1 1 ((fun _ => 0) g.val)) 1 =
      false := by
  decide +kernel

theorem orbitK_sound_false : ¬ ∀ (n m w wn kS kN : Nat) (NS PS : Nat → Nat) (O : Nat),
    0 < m → 2 ≤ kS → 2 ≤ kN → orbitK n m w wn NS PS O = true →
      fo22OrbitOK (Array.ofFn (n := kN) fun g => unpack n wn (NS g.val)) (unpack m wn O)
        (Array.ofFn (n := kS) fun g => unpack m w (PS g.val)) m = true := by
  intro h
  have := h 4000 1 1 12 2 2 (fun _ => Nat.shiftLeft 3600 43200) (fun _ => 0) 3600 (by omega)
    (by omega) (by omega) cex_orbitK
  rw [cex_fo22OrbitOK] at this
  exact Bool.false_ne_true this

end CFSG.KS.OrbTree

end
