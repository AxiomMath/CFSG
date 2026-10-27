module

public import CFSG.Certificates.Kernel.LceSP.Loops
public import CFSG.Certificates.Kernel.LceSP.Popcount
import Mathlib.Tactic.Group
public import Certificates.Data.Kernel.LceSTab
public import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Certificates.LceP

open CFSG.KC CFSG.KC.LceS CFSG.KC.Loop CFSG.Certificates.LCE Finset

theorem blt_true {a b : ℕ} (h : Nat.blt a b = true) : a < b := by
  rwa [Nat.blt_eq] at h

theorem wtPer_spec {WT : ℕ → ℕ} {m : ℕ} (h : wtPer WT m = true) :
    ∀ k < 65536, WT k = WT (k % m) := by
  intro k hk
  have h1 := (allRec2_iff (fun h => Nat.rec (motive := fun _ => Bool) true (fun l ih2 => andB
      ((fun k => Nat.beq (WT k) (WT (Nat.mod k m))) (Nat.add (Nat.shiftLeft h (nat_lit 8)) l)) ih2)
      (nat_lit 256)) (nat_lit 256)).1 h (k / 256) (by change k / 256 < 256; omega)
  have h2 := (allRec2_iff (fun l =>
      (fun k => Nat.beq (WT k) (WT (Nat.mod k m))) (Nat.add (Nat.shiftLeft (k / 256) (nat_lit 8)) l))
      (nat_lit 256)).1 h1 (k % 256) (by change k % 256 < 256; omega)
  have e : Nat.add (Nat.shiftLeft (k / 256) 8) (k % 256) = k := by
    change (k / 256) <<< 8 + k % 256 = k
    rw [Nat.shiftLeft_eq]
    omega
  have h3 : Nat.beq (WT (Nat.add (Nat.shiftLeft (k / 256) 8) (k % 256)))
      (WT (Nat.mod (Nat.add (Nat.shiftLeft (k / 256) 8) (k % 256)) m)) = true := h2
  rw [e, Nat.beq_eq] at h3
  exact h3

theorem relsNorm_spec {RT : ℕ → ℕ} {nR : ℕ} (h : relsNorm RT nR = true) :
    ∀ r < nR, wWord (RT r) < 256 ^ wLen (RT r) := by
  intro r hr
  have h1 := (allRec2_iff (fun r => Nat.blt (wWord (RT r))
    (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 8) (wLen (RT r))))) nR).1 h r hr
  rw [Nat.blt_eq] at h1
  change wWord (RT r) < 1 <<< (8 * wLen (RT r)) at h1
  rwa [Nat.shiftLeft_eq, Nat.one_mul, two_pow_eight_mul] at h1

theorem word_check {INV INV8 w r : ℕ} {RT ST : ℕ → ℕ}
    (h : Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) true
        (wSub INV (wWord w) (wLen w) (wWord (ST r)) (wLen (ST r))) (Nat.beq (wKind w) (nat_lit 3)))
      (wRel INV INV8 (wWord w) (wLen w) (wWord (RT r)) (wLen (RT r)))
      (Nat.beq (wKind w) (nat_lit 2)) = true) :
    (wKind w = 2 → wRel INV INV8 (wWord w) (wLen w) (wWord (RT r)) (wLen (RT r)) = true) ∧
    (wKind w = 3 → wSub INV (wWord w) (wLen w) (wWord (ST r)) (wLen (ST r)) = true) := by
  constructor
  · intro hk
    have hb : Nat.beq (wKind w) (nat_lit 2) = true := by rw [Nat.beq_eq]; exact hk
    rw [hb] at h
    exact h
  · intro hk
    have hb3 : Nat.beq (wKind w) (nat_lit 3) = true := by rw [Nat.beq_eq]; exact hk
    cases hb2 : Nat.beq (wKind w) (nat_lit 2)
    · rw [hb2, hb3] at h
      exact h
    · have : wKind w = 2 := Nat.eq_of_beq_eq_true hb2
      omega

theorem hint_check {w h R K : ℕ}
    (hh : Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) true (Nat.blt h K) (Nat.beq (wKind w) (nat_lit 3)))
      (Nat.blt h R) (Nat.beq (wKind w) (nat_lit 2)) = true) :
    (wKind w = 2 → h < R) ∧ (wKind w = 3 → h < K) := by
  constructor
  · intro hk
    have hb : Nat.beq (wKind w) (nat_lit 2) = true := by rw [Nat.beq_eq]; exact hk
    rw [hb] at hh
    exact blt_true hh
  · intro hk
    have hb3 : Nat.beq (wKind w) (nat_lit 3) = true := by rw [Nat.beq_eq]; exact hk
    cases hb2 : Nat.beq (wKind w) (nat_lit 2)
    · rw [hb2, hb3] at hh
      exact blt_true hh
    · have : wKind w = 2 := Nat.eq_of_beq_eq_true hb2
      omega

theorem words_spec {G : Type*} [Group G] (gen : ℕ → G) {WT RT ST : ℕ → ℕ}
    {INV INV8 L m Hs nR nS : ℕ} (hinv : invOK INV INV8 L = true)
    (hwords : wordsOK WT RT ST INV INV8 m Hs = true)
    (hhints : CFSG.KC.Bind.hintsOK WT m nR nS Hs = true)
    (hrels : ∀ r < nR, bv gen (wWord (RT r)) (wLen (RT r)) = 1)
    (hnorm : ∀ r < nR, wWord (RT r) < 256 ^ wLen (RT r)) :
    ∀ j < m, WOK gen (Subgroup.closure ((fun j => bv gen (wWord (ST j)) (wLen (ST j))) ''
      {j | j < nS})) (WT j) := by
  intro j hj
  have hw := hintLoop (fun j H => (fun w r => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) true
        (wSub INV (wWord w) (wLen w) (wWord (ST r)) (wLen (ST r))) (Nat.beq (wKind w) (nat_lit 3)))
      (wRel INV INV8 (wWord w) (wLen w) (wWord (RT r)) (wLen (RT r)))
      (Nat.beq (wKind w) (nat_lit 2))) (WT j) (Nat.land H (nat_lit 65535)))
    m (nat_lit 16) m le_rfl Hs hwords j hj
  have hh := hintLoop (fun j H => (fun w h => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) true (Nat.blt h nS) (Nat.beq (wKind w) (nat_lit 3)))
      (Nat.blt h nR) (Nat.beq (wKind w) (nat_lit 2))) (WT j) (Nat.land H (nat_lit 65535)))
    m (nat_lit 16) m le_rfl Hs hhints j hj
  rw [Nat.sub_self, Nat.zero_add] at hw hh
  obtain ⟨hw2, hw3⟩ := word_check hw
  obtain ⟨hh2, hh3⟩ := hint_check hh
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · have hr := hh2 hk
    have hn := hnorm _ hr
    rw [← two_pow_eight_mul] at hn
    exact wRel_sound gen hinv (hw2 hk) hn (hrels _ hr)
  · have hr := hh3 hk
    rw [wSub_sound gen (hw3 hk)]
    exact Subgroup.subset_closure ⟨_, hr, rfl⟩

theorem land_two_pow (x j : ℕ) : x &&& 2 ^ j = if x.testBit j then 2 ^ j else 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  split_ifs with h
  · rw [Nat.testBit_two_pow]
    by_cases hij : j = i
    · subst hij
      simp [h]
    · simp [hij]
  · by_cases hij : j = i
    · subst hij
      simp [h]
    · simp [hij]

theorem alive_spec (LVs : ℕ → ℕ) (y : ℕ) :
    alive LVs y = true ↔ LVs (y / 4096) / 2 ^ (y % 4096) % 2 = 1 := by
  unfold alive
  simp only [letB_eq]
  rw [Nat.blt_eq, shr_eq, land_lit y 12 4095 (by norm_num)]
  change 0 < LVs (y / 2 ^ 12) &&& (1 <<< (y % 2 ^ 12)) ↔ _
  rw [Nat.shiftLeft_eq, Nat.one_mul, land_two_pow, Nat.testBit_eq_decide_div_mod_eq]
  have e : (2 : ℕ) ^ 12 = 4096 := by norm_num
  rw [e]
  split_ifs with h
  · simp only [decide_eq_true_eq] at h
    exact ⟨fun _ => h, fun _ => by positivity⟩
  · simp only [decide_eq_true_eq] at h
    exact ⟨fun h0 => absurd h0 (lt_irrefl 0), fun h1 => absurd h1 h⟩

@[expose] noncomputable def cntRec (LVs : ℕ → ℕ) (M : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k ih => Bool.rec (motive := fun _ => Nat) (Nat.add (nat_lit 1048576) ih)
      (Nat.add (pc4096 (LVs k)) ih)
      (Nat.blt (LVs k) (Nat.shiftLeft (nat_lit 1) (nat_lit 4096)))) M

theorem aliveOK_spec {LVs : ℕ → ℕ} {M nC a : ℕ} (h : aliveOK LVs M nC a = true) :
    M = (nC + 4095) / 4096 ∧ 0 < nC ∧ alive LVs 0 = true ∧ cntRec LVs M = a := by
  unfold aliveOK at h
  obtain ⟨h1, h⟩ := (andB_iff _ _).1 h
  obtain ⟨h2, h⟩ := (andB_iff _ _).1 h
  obtain ⟨h3, h4⟩ := (andB_iff _ _).1 h
  have hM : M = (nC + 4095) / 4096 := by
    have := Nat.eq_of_beq_eq_true h1
    rw [← this]
    change (nC + 4095) >>> 12 = (nC + 4095) / 4096
    rw [Nat.shiftRight_eq_div_pow]
  refine ⟨hM, ?_, h3, Nat.eq_of_beq_eq_true h4⟩
  rcases Nat.eq_zero_or_pos nC with h0 | h0
  · exfalso
    have hM0 : M = 0 := by rw [hM, h0]
    have h2' := Nat.eq_of_beq_eq_true h2
    rw [hM0, h0] at h2'
    change LVs 0 >>> 0 = 0 at h2'
    rw [Nat.shiftRight_zero] at h2'
    rw [alive_spec] at h3
    simp [h2'] at h3
  · exact h0

theorem bits_le (x : ℕ) : ∑ j ∈ range 4096, x / 2 ^ j % 2 ≤ 4096 := by
  calc ∑ j ∈ range 4096, x / 2 ^ j % 2 ≤ ∑ _j ∈ range 4096, 1 :=
        sum_le_sum fun j _ => by have := Nat.mod_lt (x / 2 ^ j) (by norm_num : 0 < 2); omega
    _ = 4096 := by simp

theorem count_le (LVs : ℕ → ℕ) : ∀ M,
    ∑ y ∈ range (4096 * M), (if alive LVs y = true then 1 else 0) ≤ cntRec LVs M
  | 0 => by simp
  | M + 1 => by
    rw [Nat.mul_add, Nat.mul_one, sum_range_add]
    have hblk : ∑ j ∈ range 4096, (if alive LVs (4096 * M + j) = true then 1 else 0) =
        ∑ j ∈ range 4096, LVs M / 2 ^ j % 2 := by
      apply sum_congr rfl
      intro j hj
      rw [mem_range] at hj
      have e1 : (4096 * M + j) / 4096 = M := by omega
      have e2 : (4096 * M + j) % 4096 = j := by omega
      have ha := alive_spec LVs (4096 * M + j)
      rw [e1, e2] at ha
      have := Nat.mod_two_eq_zero_or_one (LVs M / 2 ^ j)
      by_cases hc : alive LVs (4096 * M + j) = true
      · rw [ite_eq_left hc]
        have := ha.mp hc
        omega
      · rw [ite_eq_right hc]
        have := mt ha.mpr hc
        omega
    rw [hblk]
    change _ ≤ Bool.rec (motive := fun _ => Nat) (Nat.add 1048576 (cntRec LVs M))
      (Nat.add (pc4096 (LVs M)) (cntRec LVs M)) (Nat.blt (LVs M) (Nat.shiftLeft 1 4096))
    rw [brec_eq]
    have ih := count_le LVs M
    have hb := bits_le (LVs M)
    split_ifs
    · rw [Nat.add_eq, pc4096_eq]
      omega
    · rw [Nat.add_eq]
      omega

theorem lv_even' {G : Type*} [Group G] (gen : ℕ → G) {g : ℕ} (h : 2 * g < 255) :
    lv gen (2 * g) = gen g := by
  have h1 : 2 * g ≠ 255 := Nat.ne_of_lt h
  have h2 : 2 * g % 2 = 0 := by omega
  have h3 : 2 * g / 2 = g := by omega
  unfold lv
  rw [ite_eq_right h1, ite_eq_left h2, h3]

theorem lv_odd' {G : Type*} [Group G] (gen : ℕ → G) {g : ℕ} (h : 2 * g + 1 < 255) :
    lv gen (2 * g + 1) = (gen g)⁻¹ := by
  have h1 : 2 * g + 1 ≠ 255 := by omega
  have h2 : ¬ (2 * g + 1) % 2 = 0 := by omega
  have h3 : (2 * g + 1) / 2 = g := by omega
  unfold lv
  rw [ite_eq_right h1, ite_eq_right h2, h3]

theorem slotOK_spec {blk LVs : ℕ → ℕ} {nf K e : ℕ} (h : slotOK blk LVs nf K e = true) :
    Nat.shiftRight e 1 < nf ∧
      ((fxc (fct blk (Nat.shiftRight e 1)) = K ∧ alive LVs (fy (fct blk (Nat.shiftRight e 1))) = true) ∨
       (fyic (fct blk (Nat.shiftRight e 1)) = K ∧
          alive LVs (fx (fct blk (Nat.shiftRight e 1))) = true)) := by
  unfold slotOK at h
  simp only [andB_iff, letB_eq, Nat.blt_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, ?_⟩
  rw [brec_eq] at h2
  split_ifs at h2
  · right
    simpa only [andB_iff, Nat.beq_eq] using h2
  · left
    simpa only [andB_iff, Nat.beq_eq] using h2

theorem lceOk_sound' {blk WT RT ST LVs : ℕ → ℕ}
    {INV INV8 L nC nCl mLV a m Hs nR nS nf : ℕ} {Cs CCs : List ℕ} {S0 S1 X0 X1 : ℕ}
    (h : CFSG.Certificates.LCE.lceOk blk WT RT ST LVs INV INV8 L nC nCl mLV a m Hs nR nS nf Cs CCs
      S0 S1 X0 X1 = true)
    {G : Type*} [Group G] (gen : ℕ → G)
    (hrels : ∀ r < nR, bv gen (wWord (RT r)) (wLen (RT r)) = 1) :
    (Subgroup.closure ((fun j => bv gen (wWord (ST j)) (wLen (ST j))) '' {j | j < nS})).relIndex
        (Subgroup.closure (gen '' {g | 2 * g < L})) ≠ 0 ∧
      (Subgroup.closure ((fun j => bv gen (wWord (ST j)) (wLen (ST j))) '' {j | j < nS})).relIndex
        (Subgroup.closure (gen '' {g | 2 * g < L})) ≤ a := by
  set H := Subgroup.closure ((fun j => bv gen (wWord (ST j)) (wLen (ST j))) '' {j | j < nS})
  set K := Subgroup.closure (gen '' {g | 2 * g < L})
  unfold CFSG.Certificates.LCE.lceOk at h
  obtain ⟨hinv, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hwords, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hhints, h⟩ := (andB_iff _ _).1 h
  obtain ⟨halive, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hnC, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hle, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hnf, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hm, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hper, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hnorm, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hS0, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hrun, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hS1, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hX0, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hcov, hX1⟩ := (andB_iff _ _).1 h
  have hnC' : nC = nCl := Nat.eq_of_beq_eq_true hnC
  subst hnC'
  have hle' : nC ≤ 1048576 := Nat.le_of_ble_eq_true hle
  have hnf' : nf < 4294967296 := blt_true hnf
  have hm' : 0 < m := blt_true hm
  have hS0' : S0 = mkS 0 1 := Nat.eq_of_beq_eq_true hS0
  have hrun' := Nat.eq_of_beq_eq_true hrun
  have hS1' : S1 = mkS nf nC := Nat.eq_of_beq_eq_true hS1
  have hX0' : X0 = 1 := Nat.eq_of_beq_eq_true hX0
  have hcov' := Nat.eq_of_beq_eq_true hcov
  have hX1' : X1 = nC + 1 := Nat.eq_of_beq_eq_true hX1
  obtain ⟨hL, hL2, hinvc⟩ := invOK_spec hinv
  obtain ⟨hMLV, hnC0, halive0, hcnt⟩ := aliveOK_spec halive
  have hK : ∀ c < L, lv gen c ∈ K := by
    intro c hc
    have hg : gen (c / 2) ∈ K := Subgroup.subset_closure ⟨c / 2, by change 2 * (c / 2) < L; omega, rfl⟩
    unfold lv
    split_ifs
    · exact K.one_mem
    · exact hg
    · exact K.inv_mem hg
  have hWT : ∀ k < 65536, WOK gen H (WT k) := by
    intro k hk
    rw [wtPer_spec hper k hk]
    exact words_spec gen hinv hwords hhints hrels (relsNorm_spec hnorm) _ (Nat.mod_lt _ hm')
  have hG0 : FGood gen H K blk INV nC S0 := by
    rw [hS0']
    exact FGood_mkS gen H K (by norm_num) le_rfl (fun _ => FInv_zero gen H K blk INV nC 1)
  have hG1 := runFacts_good gen H K hinv hWT hK Cs S0 hG0
  rw [hrun', hS1'] at hG1
  rcases hG1 with h0 | ⟨-, hF⟩
  · rw [mkS_eq nC hnf'] at h0
    omega
  rw [sI_eq, sN_eq, mkS_eq nC hnf'] at hF
  have e1 : (nf + nC * 4294967296) % 4294967296 = nf := by omega
  have e2 : (nf + nC * 4294967296) / 4294967296 = nC := by omega
  rw [e1, e2] at hF
  obtain ⟨hrecs, rep, hrep0, hrepK, hfacts⟩ := hF
  have hfact : ∀ h < nf, el gen rep (fct blk h) ∈ H := hfacts rep (fun _ _ => rfl)
  have hC0 : CGood blk LVs nf L X0 := by
    rw [hX0']
    exact Or.inr ⟨le_rfl, fun x hx => absurd hx (Nat.not_lt_zero x)⟩
  have hC1 := runCover_good CCs X0 hC0
  rw [hcov', hX1'] at hC1
  rcases hC1 with h0 | ⟨-, hC⟩
  · omega
  have hcover : ∀ x < nC, alive LVs x = true → ∀ c < L,
      ∃ y, y < nC ∧ alive LVs y = true ∧ rep x * lv gen c * (rep y)⁻¹ ∈ H := by
    intro x hx hal c hc
    obtain ⟨e, he⟩ := hC x (by omega) hal c hc
    obtain ⟨hh, hdir⟩ := slotOK_spec he
    set R := fct blk (Nat.shiftRight e 1)
    obtain ⟨hfx, hfy, -⟩ := recOK_spec (hrecs _ hh)
    rw [lor20 c (show x < 1048576 by omega)] at hdir
    rcases hdir with ⟨hk, hy⟩ | ⟨hk, hy⟩
    · rw [fxc_eq] at hk
      have := fx_lt R
      have := fc_lt R
      have h1 : fx R = x := by omega
      have h2 : fc R = c := by omega
      refine ⟨fy R, hfy, hy, ?_⟩
      have := hfact _ hh
      unfold el at this
      rw [h1, h2] at this
      exact this
    · rw [fyic_eq] at hk
      have := fy_lt R
      have := fic_lt blk (Nat.shiftRight e 1)
      have h1 : fy R = x := by omega
      have h2 : fic R = c := by omega
      refine ⟨fx R, hfx, hy, ?_⟩
      have hl := (lv_fic gen blk hinv (hrecs _ hh)).1
      rw [h2] at hl
      have := H.inv_mem (hfact _ hh)
      unfold el at this
      rw [h1] at this
      rw [hl]
      have e : (rep (fx R) * lv gen (fc R) * (rep x)⁻¹)⁻¹ = rep x * (lv gen (fc R))⁻¹ * (rep (fx R))⁻¹ := by
        group
      rw [e] at this
      exact this
  have hmove : ∀ k ∈ K, ∀ x < nC, alive LVs x = true →
      ∃ y, y < nC ∧ alive LVs y = true ∧ rep x * k * (rep y)⁻¹ ∈ H := by
    intro k hk
    induction hk using Subgroup.closure_induction'' with
    | mem g hg =>
      obtain ⟨g', hg', rfl⟩ := hg
      intro x hx hal
      have h2 : 2 * g' < L := hg'
      have h255 : 2 * g' < 255 := by omega
      have := hcover x hx hal (2 * g') h2
      rwa [lv_even' gen h255] at this
    | inv_mem g hg =>
      obtain ⟨g', hg', rfl⟩ := hg
      intro x hx hal
      have h2 : 2 * g' < L := hg'
      have h255 : 2 * g' + 1 < 255 := by omega
      have := hcover x hx hal (2 * g' + 1) (by omega)
      rwa [lv_odd' gen h255] at this
    | one =>
      intro x hx hal
      exact ⟨x, hx, hal, by rw [mul_one, mul_inv_cancel]; exact H.one_mem⟩
    | mul k1 k2 _ _ ih1 ih2 =>
      intro x hx hal
      obtain ⟨y1, hy1, hal1, hm1⟩ := ih1 x hx hal
      obtain ⟨y2, hy2, hal2, hm2⟩ := ih2 y1 hy1 hal1
      refine ⟨y2, hy2, hal2, ?_⟩
      have := H.mul_mem hm1 hm2
      have e : rep x * k1 * (rep y1)⁻¹ * (rep y1 * k2 * (rep y2)⁻¹) =
          rep x * (k1 * k2) * (rep y2)⁻¹ := by group
      rwa [e] at this
  set A := (range nC).filter (fun y => alive LVs y = true)
  have hrepA : ∀ y ∈ A, (rep y)⁻¹ ∈ K := fun y hy =>
    K.inv_mem (hrepK y (mem_range.mp (mem_filter.mp hy).1))
  let f : A → K ⧸ H.subgroupOf K := fun y => QuotientGroup.mk ⟨(rep y)⁻¹, hrepA y y.2⟩
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨y, hy, hal, hmem⟩ := hmove _ (K.inv_mem k.2) 0 hnC0 halive0
    rw [hrep0, one_mul] at hmem
    refine ⟨⟨y, mem_filter.mpr ⟨mem_range.mpr hy, hal⟩⟩, ?_⟩
    apply QuotientGroup.eq.mpr
    rw [Subgroup.mem_subgroupOf]
    have := H.inv_mem hmem
    rw [mul_inv_rev, inv_inv, inv_inv] at this
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    exact this
  have hfin : Finite (K ⧸ H.subgroupOf K) := Finite.of_surjective f hf
  have hcard : Nat.card (K ⧸ H.subgroupOf K) ≤ A.card := by
    have := Nat.card_le_card_of_surjective f hf
    rwa [Nat.card_eq_fintype_card (α := {x // x ∈ A}), Fintype.card_coe] at this
  have hAa : A.card ≤ a := by
    rw [← hcnt]
    change ((range nC).filter (fun y => alive LVs y = true)).card ≤ _
    rw [card_filter]
    calc ∑ y ∈ range nC, (if alive LVs y = true then 1 else 0)
        ≤ ∑ y ∈ range (4096 * mLV), (if alive LVs y = true then 1 else 0) := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro y hy
            rw [mem_range] at hy ⊢
            omega
          · intros
            exact Nat.zero_le _
      _ ≤ cntRec LVs mLV := count_le LVs mLV
  refine ⟨Subgroup.index_ne_zero_of_finite, ?_⟩
  change Nat.card (K ⧸ H.subgroupOf K) ≤ a
  omega

end CFSG.Certificates.LceP

end
