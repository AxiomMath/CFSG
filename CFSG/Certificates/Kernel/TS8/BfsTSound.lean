module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8D8Check
public import CFSG.Certificates.Kernel.S63K.OrbRunSound
public import CFSG.Certificates.Kernel.BfsPinAlg

public section

namespace CFSG.KC.TS8

open CFSG.EvenSporadicStandard.Fin76b.TS8D8 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2
  CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.S63K

abbrev TSt := Array (Array ℕ) × Array ℕ × Array ℕ × Std.HashMap (Array ℕ) ℕ

@[expose] def tK (n : ℕ) (gens : Array (Array ℕ)) (i : ℕ) (s : TSt) (k : ℕ) : TSt :=
  if (!s.2.2.2.contains (compA n s.1[i]! gens[k]!)) = true then
    (s.1.push (compA n s.1[i]! gens[k]!), s.2.1.push i, s.2.2.1.push k,
      s.2.2.2.insert (compA n s.1[i]! gens[k]!) s.1.size)
  else s

@[expose] def tI (n : ℕ) (gens : Array (Array ℕ)) (s : TSt) (i : ℕ) : TSt :=
  if i < s.1.size then (List.range' 0 gens.size).foldl (tK n gens i) s else s

theorem bfsT_eq (n : ℕ) (gens : Array (Array ℕ)) :
    bfsT n gens = (fun s : TSt => (s.1, s.2.1, s.2.2.1))
      ((List.range' 0 256).foldl (tI n gens)
        (#[idA n], #[0], #[0], (∅ : Std.HashMap (Array ℕ) ℕ).insert (idA n) 0)) := by
  unfold bfsT
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [forIn_yield (tI n gens)]
  · rfl
  · intro i s
    obtain ⟨E, par, gen, idx⟩ := s
    unfold tI
    dsimp only
    split
    · rw [forIn_yield (tK n gens i)]
      · rfl
      · intro k t
        obtain ⟨a, b, c, d⟩ := t
        unfold tK
        dsimp only
        split <;> rfl
    · rfl

variable {n w ng : ℕ} {GW EP W Pa La : ℕ → ℕ}

theorem eqA_self (t : Array ℕ) : eqA n t t = true := by
  unfold eqA
  rw [allLt_iff]
  intro i _
  exact beq_self_eq_true _

theorem unpack_inj {p q : ℕ} (hp : PP n w p) (hq : PP n w q)
    (h : unpack n w p = unpack n w q) : p = q := by
  have e := eqA_PP hp hq
  rw [h, eqA_self] at e
  exact (Nat.eq_of_beq_eq_true e.symm)

structure TInv (n w : ℕ) (EP Pa La : ℕ → ℕ) (c : ℕ) (s : TSt) : Prop where
  esz : s.1.size = c
  e : ∀ i < c, s.1[i]! = unpack n w (EP i)
  psz : s.2.1.size = c
  par : ∀ i < c, s.2.1[i]! = Pa i
  lsz : s.2.2.1.size = c
  lab : ∀ i < c, s.2.2.1[i]! = La i
  idx : ∀ j < 256, s.2.2.2.contains (unpack n w (EP j)) = decide (j < c)

@[expose] def TTree (n w ng : ℕ) (GW EP Pa La : ℕ → ℕ) (c : ℕ) : Prop :=
  ∀ i, 0 < i → i < c → Pa i < i ∧ La i < ng ∧ pcomp n w (mask w) (EP (Pa i)) (GW (La i)) = EP i

theorem inv_pushT {c : ℕ} {s : TSt} (hPP : ∀ i < 256, PP n w (EP i))
    (hd : ∀ a < 256, ∀ b < 256, EP a = EP b → a = b) (hs : TInv n w EP Pa La c s)
    (hc : c < 256) {h k : ℕ} (hPa : Pa c = h) (hLa : La c = k) :
    TInv n w EP Pa La (c + 1)
      (s.1.push (unpack n w (EP c)), s.2.1.push h, s.2.2.1.push k,
        s.2.2.2.insert (unpack n w (EP c)) s.1.size) := by
  obtain ⟨hesz, he, hpsz, hpar, hlsz, hlab, hidx⟩ := hs
  refine ⟨by simp [hesz], fun i hi => ?_, by simp [hpsz], fun i hi => ?_, by simp [hlsz],
    fun i hi => ?_, fun j hj => ?_⟩
  · rw [push_get _ _ hesz hi]
    split
    · exact he i ‹_›
    · congr 2
      omega
  · rw [push_get _ _ hpsz hi]
    split
    · exact hpar i ‹_›
    · rw [← hPa]
      congr 1
      omega
  · rw [push_get _ _ hlsz hi]
    split
    · exact hlab i ‹_›
    · rw [← hLa]
      congr 1
      omega
  · rw [Std.HashMap.contains_insert, hidx j hj]
    by_cases e : j = c
    · subst e
      simp
    · have hne : (unpack n w (EP c) == unpack n w (EP j)) = false := by
        rw [beq_eq_false_iff_ne]
        intro h1
        exact e (hd j hj c hc (unpack_inj (hPP j hj) (hPP c hc) h1.symm))
      rw [hne, Bool.false_or]
      by_cases h2 : j < c
      · rw [decide_eq_true h2, decide_eq_true (by omega)]
      · rw [decide_eq_false h2, decide_eq_false (by omega)]

theorem tRow_replay {gens : Array (Array ℕ)} (hg : ∀ k < ng, gens[k]! = unpack n w (GW k))
    (hPP : ∀ i < 256, PP n w (EP i)) (hGP : ∀ k < ng, PP n w (GW k))
    (hd : ∀ a < 256, ∀ b < 256, EP a = EP b → a = b)
    (hact : ∀ h < 256, ∀ k < ng, W (ng * h + k) < 256 ∧
      pcomp n w (mask w) (EP h) (GW k) = EP (W (ng * h + k))) {h : ℕ} :
    ∀ m j c (s : TSt), j + m ≤ ng → h < c →
      TInv n w EP Pa La c s → TTree n w ng GW EP Pa La c →
      orbRowK W Pa La ng h m j c ≠ 0 → orbRowK W Pa La ng h m j c ≤ 256 →
      TInv n w EP Pa La (orbRowK W Pa La ng h m j c) ((List.range' j m).foldl (tK n gens h) s) ∧
        TTree n w ng GW EP Pa La (orbRowK W Pa La ng h m j c) := by
  intro m
  induction m with
  | zero =>
    intro j c s _ _ hs ht _ _
    exact ⟨hs, ht⟩
  | succ m ih =>
    intro j c s hjm hhc hs ht hne hle
    have hmono := orbRowK_mono (W := W) (Pa := Pa) (La := La) (k := ng) h (m + 1) j c hne
    have hcc : c ≤ 256 := Nat.le_trans hmono hle
    rw [List.range'_succ, List.foldl_cons]
    rw [orbRowK_succ] at hne hle hmono ⊢
    obtain ⟨hw, hy⟩ := hact h (by omega) j (by omega)
    have hprod : compA n s.1[h]! gens[j]! = unpack n w (EP (W (ng * h + j))) := by
      rw [hs.e h hhc, hg j (by omega), compA_PP (hPP h (by omega)) (hGP j (by omega)), hy]
    unfold tK
    rw [hprod, hs.idx _ hw]
    by_cases hwc : W (ng * h + j) < c
    · rw [if_pos hwc] at hne hle hmono ⊢
      rw [decide_eq_true hwc]
      exact ih (j + 1) c s (by omega) hhc hs ht hne hle
    · rw [if_neg hwc] at hne hle hmono ⊢
      by_cases hn : W (ng * h + j) = c ∧ Pa c = h ∧ La c = j
      · rw [if_pos hn] at hne hle hmono ⊢
        obtain ⟨hwc', hpc, hlc⟩ := hn
        have hcN : c < 256 := by omega
        rw [decide_eq_false hwc, hwc']
        simp only [Bool.not_false, ↓reduceIte]
        refine ih (j + 1) (c + 1) _ (by omega) (by omega) (inv_pushT hPP hd hs hcN hpc hlc)
          (fun i h0 hi => ?_) hne hle
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact ht i h0 hi
        · refine ⟨by omega, by omega, ?_⟩
          rw [hpc, hlc, hy, hwc']
      · rw [if_neg hn] at hne
        exact absurd rfl hne

theorem fold_idleT (n : ℕ) (gens : Array (Array ℕ)) :
    ∀ m h (s : TSt), s.1.size ≤ h → (List.range' h m).foldl (tI n gens) s = s
  | 0, _, _, _ => rfl
  | m + 1, h, s, hs => by
    rw [List.range'_succ, List.foldl_cons]
    have e : tI n gens s h = s := by
      unfold tI
      rw [if_neg (by omega)]
    rw [e]
    exact fold_idleT n gens m (h + 1) s (by omega)

theorem tRun_replay {gens : Array (Array ℕ)} (hng : gens.size = ng)
    (hg : ∀ k < ng, gens[k]! = unpack n w (GW k))
    (hPP : ∀ i < 256, PP n w (EP i)) (hGP : ∀ k < ng, PP n w (GW k))
    (hd : ∀ a < 256, ∀ b < 256, EP a = EP b → a = b)
    (hact : ∀ h < 256, ∀ k < ng, W (ng * h + k) < 256 ∧
      pcomp n w (mask w) (EP h) (GW k) = EP (W (ng * h + k))) :
    ∀ fuel h c (s : TSt) m, h + m = 256 → c ≤ 256 →
      TInv n w EP Pa La c s → TTree n w ng GW EP Pa La c →
      orbRunK W Pa La ng fuel h c = 256 →
      TInv n w EP Pa La 256 ((List.range' h m).foldl (tI n gens) s) ∧
        TTree n w ng GW EP Pa La 256 := by
  intro fuel
  induction fuel with
  | zero =>
    intro h c s m _ _ _ _ hr
    have : orbRunK W Pa La ng 0 h c = 0 := rfl
    omega
  | succ fuel ih =>
    intro h c s m hm hcN hs ht hr
    have hmono := orbRunK_mono (W := W) (Pa := Pa) (La := La) (k := ng) (fuel + 1) h c
      (by omega)
    rw [orbRunK_succ] at hr hmono
    by_cases hc : h < c
    · rw [if_pos hc] at hr hmono
      by_cases h0 : orbRowK W Pa La ng h ng 0 c = 0
      · rw [if_pos h0] at hr
        omega
      · rw [if_neg h0] at hr hmono
        have hle : orbRowK W Pa La ng h ng 0 c ≤ 256 := by
          have := orbRunK_mono (W := W) (Pa := Pa) (La := La) (k := ng) fuel (h + 1)
            (orbRowK W Pa La ng h ng 0 c) (by rw [hr]; omega)
          rw [hr] at this
          exact this
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        rw [List.range'_succ, List.foldl_cons]
        have e : tI n gens s h = (List.range' 0 ng).foldl (tK n gens h) s := by
          unfold tI
          rw [if_pos (by rw [hs.esz]; exact hc), hng]
        rw [e]
        obtain ⟨hs', ht'⟩ := tRow_replay hg hPP hGP hd hact ng 0 c s (by omega) hc hs ht h0 hle
        exact ih (h + 1) _ _ m' (by omega) hle hs' ht' hr
    · rw [if_neg hc] at hr
      subst hr
      rw [fold_idleT n gens m h s (by rw [hs.esz]; omega)]
      exact ⟨hs, ht⟩

theorem tInv_init (hsz : szOK n w = true) (hPP : ∀ i < 256, PP n w (EP i))
    (hd : ∀ a < 256, ∀ b < 256, EP a = EP b → a = b) (h0 : EP 0 = pidn n w) (hp0 : Pa 0 = 0)
    (hl0 : La 0 = 0) :
    TInv n w EP Pa La 1 (#[idA n], #[0], #[0], (∅ : Std.HashMap (Array ℕ) ℕ).insert (idA n) 0) := by
  have hid : idA n = unpack n w (EP 0) := by rw [h0, idA_eq hsz]
  refine ⟨rfl, fun i hi => ?_, rfl, fun i hi => ?_, rfl, fun i hi => ?_, fun j hj => ?_⟩
  · obtain rfl : i = 0 := by omega
    rw [← hid]
    rfl
  · obtain rfl : i = 0 := by omega
    rw [hp0]
    rfl
  · obtain rfl : i = 0 := by omega
    rw [hl0]
    rfl
  · rw [Std.HashMap.contains_insert, hid, Std.HashMap.contains_empty, Bool.or_false]
    by_cases e : j = 0
    · subst e
      simp
    · rw [beq_eq_false_iff_ne.2 (fun h1 => e (hd j hj 0 (by norm_num)
        (unpack_inj (hPP j hj) (hPP 0 (by norm_num)) h1.symm))), decide_eq_false (by omega)]

theorem bfsT_of_K {gens : Array (Array ℕ)} (hsz : szOK n w = true) (hng : gens.size = ng)
    (hg : ∀ k < ng, gens[k]! = unpack n w (GW k))
    (hPP : ∀ i < 256, PP n w (EP i)) (hGP : ∀ k < ng, PP n w (GW k))
    (hd : ∀ a < 256, ∀ b < 256, EP a = EP b → a = b) (h0 : EP 0 = pidn n w) (hp0 : Pa 0 = 0)
    (hl0 : La 0 = 0)
    (hact : ∀ h < 256, ∀ k < ng, W (ng * h + k) < 256 ∧
      pcomp n w (mask w) (EP h) (GW k) = EP (W (ng * h + k)))
    (hrun : orbRunK W Pa La ng 257 0 1 = 256) :
    (bfsT n gens).1.size = 256 ∧ (∀ i < 256, (bfsT n gens).1[i]! = unpack n w (EP i)) ∧
      (bfsT n gens).2.1.size = 256 ∧ (∀ i < 256, (bfsT n gens).2.1[i]! = Pa i) ∧
      (bfsT n gens).2.2.size = 256 ∧ (∀ i < 256, (bfsT n gens).2.2[i]! = La i) ∧
      TTree n w ng GW EP Pa La 256 := by
  obtain ⟨hs, ht⟩ := tRun_replay hng hg hPP hGP hd hact 257 0 1 _ 256 (by omega) (by omega)
    (tInv_init hsz hPP hd h0 hp0 hl0) (fun i h1 h2 => by omega) hrun
  rw [bfsT_eq]
  generalize (List.range' 0 256).foldl (tI n gens)
    (#[idA n], #[0], #[0], (∅ : Std.HashMap (Array ℕ) ℕ).insert (idA n) 0) = F at hs ⊢
  exact ⟨hs.esz, hs.e, hs.psz, hs.par, hs.lsz, hs.lab, ht⟩

end CFSG.KC.TS8

end
