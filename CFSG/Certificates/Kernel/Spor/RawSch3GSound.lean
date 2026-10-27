module

public import Certificates.Data.Kernel.Spor.RawSch3G
public import CFSG.Certificates.Kernel.Spor.RawSch3FSound
public import CFSG.Certificates.Kernel.Enum.ZCSound

public section

namespace CFSG.KS.Raw.Orb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Mathieu CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Co2 CFSG.Certificates.Native

section Core

variable {G : Type*} [Group G]

def InU (c1 c2 : Nat) (t1 t2 : Nat → G) (g : G) : Prop := ∃ a < c1, ∃ b < c2, g = t1 a * t2 b

theorem mulU {c1 c2 : Nat} {t1 t2 : Nat → G} {L1 L2 : Set G}
    (h2 : ∀ σ ∈ L2, ∀ b < c2, ∃ b' < c2, σ * t2 b = t2 b')
    (h1 : ∀ σ ∈ L1, ∀ a < c1, ∃ a' < c1, ∃ b' < c2, σ * t1 a = t1 a' * t2 b')
    (m1 : ∀ a < c1, t1 a ∈ Submonoid.closure L1) (m2 : ∀ b < c2, t2 b ∈ Submonoid.closure L2)
    (inc : L2 ⊆ L1) {u v : G} (hu : InU c1 c2 t1 t2 u) (hv : InU c1 c2 t1 t2 v) :
    InU c1 c2 t1 t2 (u * v) := by
  let M2 : Submonoid G :=
    { carrier := {g | ∀ b < c2, ∃ b' < c2, g * t2 b = t2 b'}
      mul_mem' := fun {x y} hx hy b hb => by
        obtain ⟨b1, hb1, e1⟩ := hy b hb
        obtain ⟨b2, hb2, e2⟩ := hx b1 hb1
        exact ⟨b2, hb2, by rw [mul_assoc, e1, e2]⟩
      one_mem' := fun b hb => ⟨b, hb, one_mul _⟩ }
  have hM2 : Submonoid.closure L2 ≤ M2 := Submonoid.closure_le.2 h2
  let M1 : Submonoid G :=
    { carrier := {g | ∀ v, InU c1 c2 t1 t2 v → InU c1 c2 t1 t2 (g * v)}
      mul_mem' := fun {x y} hx hy v hv => by
        rw [mul_assoc]
        exact hx _ (hy v hv)
      one_mem' := fun v hv => by rwa [one_mul] }
  have hL1 : L1 ⊆ M1 := by
    rintro σ hσ v ⟨a, ha, b, hb, rfl⟩
    obtain ⟨a', ha', b', hb', e⟩ := h1 σ hσ a ha
    have hb2 : t2 b' ∈ M2 := hM2 (m2 b' hb')
    obtain ⟨b'', hb'', e2⟩ := hb2 b hb
    exact ⟨a', ha', b'', hb'', by rw [← mul_assoc, e, mul_assoc, e2]⟩
  have hM1 : Submonoid.closure L1 ≤ M1 := Submonoid.closure_le.2 hL1
  obtain ⟨a, ha, b, hb, rfl⟩ := hu
  have h1m : t1 a ∈ M1 := hM1 (m1 a ha)
  have h2m : t2 b ∈ M1 := hM1 (Submonoid.closure_mono inc (m2 b hb))
  have hm : t1 a * t2 b ∈ M1 := M1.mul_mem h1m h2m
  exact hm v hv

theorem mulC {c0 c1 c2 : Nat} {t0 t1 t2 : Nat → G} {L : Set G}
    (hU : ∀ u v, InU c1 c2 t1 t2 u → InU c1 c2 t1 t2 v → InU c1 c2 t1 t2 (u * v))
    (h0 : ∀ σ ∈ L, ∀ h < c0, ∃ k < c0, ∃ u, InU c1 c2 t1 t2 u ∧ σ * t0 h = t0 k * u)
    (hone : InU c1 c2 t1 t2 1) {g : G} (hg : g ∈ Submonoid.closure L) :
    ∀ h < c0, ∃ k < c0, ∃ u, InU c1 c2 t1 t2 u ∧ g * t0 h = t0 k * u := by
  let M : Submonoid G :=
    { carrier := {g | ∀ h < c0, ∀ v, InU c1 c2 t1 t2 v →
        ∃ k < c0, ∃ u, InU c1 c2 t1 t2 u ∧ g * (t0 h * v) = t0 k * u}
      mul_mem' := fun {x y} hx hy h hh v hv => by
        obtain ⟨k, hk, u, hu, e⟩ := hy h hh v hv
        obtain ⟨k', hk', u', hu', e'⟩ := hx k hk u hu
        exact ⟨k', hk', u', hu', by rw [mul_assoc, e, e']⟩
      one_mem' := fun h hh v hv => ⟨h, hh, v, hv, one_mul _⟩ }
  have hL : L ⊆ M := by
    intro σ hσ h hh v hv
    obtain ⟨k, hk, u, hu, e⟩ := h0 σ hσ h hh
    exact ⟨k, hk, u * v, hU u v hu hv, by rw [← mul_assoc, e, mul_assoc]⟩
  have hgM : g ∈ M := Submonoid.closure_le.2 hL hg
  intro h hh
  obtain ⟨k, hk, u, hu, e⟩ := hgM h hh 1 hone
  exact ⟨k, hk, u, hu, by rw [← e, mul_one]⟩

theorem inv_mem_closure [Finite G] {L : Set G} {x : G} (hx : x ∈ Submonoid.closure L) :
    x⁻¹ ∈ Submonoid.closure L := by
  have ho := orderOf_pos x
  have e : x ^ (orderOf x - 1) = x⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel ho, pow_orderOf_eq_one]
  rw [← e]
  exact Submonoid.pow_mem _ hx _

end Core

theorem fix_of_closure {n : Nat} {L : Set (Equiv.Perm (Fin n))} {x : Fin n}
    (hL : ∀ g ∈ L, g x = x) {g : Equiv.Perm (Fin n)} (hg : g ∈ Submonoid.closure L) :
    g x = x := by
  induction hg using Submonoid.closure_induction with
  | mem g h => exact hL g h
  | one => rfl
  | mul a b _ _ ha hb => rw [Equiv.Perm.mul_apply, hb, ha]

noncomputable def pp (n w P : Nat) : Equiv.Perm (Fin n) := permOfArr n (unpack n w P)

theorem prep_pp {n w P Q : Nat} (h : permOK n w (mask w) (n * w) P Q = true) :
    PRep n w P (pp n w P) ∧ PRep n w Q (pp n w P)⁻¹ := by
  have hr := rep_permOfArr (isInvA_unpack h)
  exact ⟨prep_of_rep hr.1, prep_of_rep hr.2⟩

noncomputable def lp (n w : Nat) (S : Nat → Nat) (kS l : Nat) : Equiv.Perm (Fin n) :=
  if l < kS then pp n w (S l) else (pp n w (S (l - kS)))⁻¹

theorem prep_lp {n w kS l : Nat} {S SI : Nat → Nat}
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (S j) (SI j)) = true)
    (hl : l < kS + kS) : PRep n w (letterK S SI kS l) (lp n w S kS l) := by
  unfold letterK lp
  simp only [nIf_eq, Nat.blt_eq]
  by_cases h : l < kS
  · rw [if_pos h, if_pos h]
    exact (prep_pp (allN_iff.1 hp l h)).1
  · rw [if_neg h, if_neg h, Nat.sub_eq]
    exact (prep_pp (allN_iff.1 hp (l - kS) (by omega))).2

def LT (n w : Nat) (S : Nat → Nat) (kS T : Nat) : Set (Equiv.Perm (Fin n)) :=
  {g | ∃ j < stCnt T, g = lp n w S kS (stAt T j)}

def LJ (n w : Nat) (S : Nat → Nat) (kS TJ : Nat) : Set (Equiv.Perm (Fin n)) :=
  {g | ∃ a < Nat.shiftRight (stCnt TJ) (nat_lit 1), stAt TJ a < kS ∧ g = lp n w S kS (stAt TJ a)}

noncomputable def tp (n w : Nat) (TR : Nat → Nat) (R k : Nat) : Equiv.Perm (Fin n) :=
  pp n w (TR (roff n (n * w) R + k))

theorem invTab_facts {kS T : Nat} (h : invTabK kS T = true) :
    ∃ q, stCnt T = q + q ∧ ∀ j < q, stAt T j < kS ∧ stAt T (q + j) = kS + stAt T j := by
  unfold invTabK at h
  simp only [strictB_eq] at h
  generalize Nat.shiftRight (stCnt T) (nat_lit 1) = q at h
  simp only [bAnd_iff, Nat.beq_eq, allN_iff, Nat.blt_eq, Nat.add_eq, strictB_eq] at h
  exact ⟨q, h⟩

theorem letter_lt {kS T : Nat} (h : invTabK kS T = true) : ∀ j < stCnt T, stAt T j < kS + kS := by
  obtain ⟨q, hq, hf⟩ := invTab_facts h
  intro j hj
  rcases Nat.lt_or_ge j q with h1 | h1
  · have := (hf j h1).1
    omega
  · obtain ⟨j', rfl⟩ : ∃ j', j = q + j' := ⟨j - q, by omega⟩
    have := hf j' (by omega)
    omega

theorem anyLt_spec {f : Nat → Bool} : ∀ {n : Nat}, anyLt n f = true → ∃ j < n, f j = true
  | 0, h => absurd h Bool.false_ne_true
  | n + 1, h => by
    have e : anyLt (n + 1) f = bIf(f n, true, anyLt n f) := rfl
    rw [e, bIf_eq] at h
    split at h
    · exact ⟨n, by omega, ‹_›⟩
    · obtain ⟨j, hj, h'⟩ := anyLt_spec h
      exact ⟨j, by omega, h'⟩

theorem inc_sub {n w kS T1 T2 : Nat} {S : Nat → Nat} (h : incK T2 T1 = true) :
    LT n w S kS T2 ⊆ LT n w S kS T1 := by
  rintro g ⟨j, hj, rfl⟩
  unfold incK at h
  have h1 := allN_iff.1 h j hj
  rw [strictB_eq] at h1
  obtain ⟨j', hj', e⟩ := anyLt_spec h1
  exact ⟨j', hj', by rw [Nat.eq_of_beq_eq_true e]⟩

theorem fix_LT {n w kS T p : Nat} {S SI : Nat → Nat}
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (S j) (SI j)) = true)
    (hT : ∀ j < stCnt T, stAt T j < kS + kS) (h : fixK w (mask w) S SI kS T p = true)
    (hpn : p < n) : ∀ g ∈ LT n w S kS T, g ⟨p, hpn⟩ = ⟨p, hpn⟩ := by
  rintro g ⟨j, hj, rfl⟩
  unfold fixK at h
  apply Fin.ext
  have e := prep_lp hp (hT j hj) ⟨p, hpn⟩
  rw [← e]
  exact Nat.eq_of_beq_eq_true (allN_iff.1 h j hj)

theorem tree_facts {n w kS root T R : Nat} {S SI TR TRI : Nat → Nat}
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (S j) (SI j)) = true)
    (hl : levelK n w (mask w) (n * w) (mask (n * w)) (pidn n w) S SI TR TRI kS root T R = true)
    (hT : ∀ j < stCnt T, stAt T j < kS + kS) :
    ∀ k < rcnt R, tp n w TR R k ∈ Submonoid.closure (LT n w S kS T) ∧
      ∀ hr : root < n, ((tp n w TR R k) ⟨root, hr⟩ : Nat) = rpt w (mask w) R k := by
  obtain ⟨hsz, -, hR, h0, hstep, hperm⟩ := levelK_facts hl
  obtain ⟨hn24, hw⟩ := szOK_facts hsz
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hpk := (prep_pp (hperm k hk)).1
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · have h1 : PRep n w (TR (roff n (n * w) R + 0)) 1 := by
        rw [Nat.add_zero, h0]
        exact prep_pidn hn24 hw
      have e : tp n w TR R 0 = 1 := prep_unique hpk h1
      refine ⟨by rw [e]; exact Submonoid.one_mem _, fun hr => ?_⟩
      rw [e, hR.root]
      rfl
    · have hpar := hR.par_lt k hk hk0
      have hlab := hR.lab_lt k hk hk0
      obtain ⟨ih1, ih2⟩ := ih _ hpar (by omega)
      have hL := prep_lp hp (hT _ hlab)
      have e : tp n w TR R k = lp n w S kS (stAt T (rlab n (n * w) R k)) *
          tp n w TR R (rpar w (mask w) (n * w) R k) :=
        prep_unique hpk (CFSG.KC.EnumSound.eq2_prep (hstep k hk hk0) hL
          (prep_pp (hperm _ (by omega))).1)
      refine ⟨by rw [e]; exact Submonoid.mul_mem _ (Submonoid.subset_closure ⟨_, hlab, rfl⟩) ih1,
        fun hr => ?_⟩
      rw [e, Equiv.Perm.mul_apply, ← hL, ih2 hr]
      exact hR.edge k hk hk0

theorem wv_facts {n w kS TJ : Nat} {S SI : Nat → Nat} (hn24 : n < 16777216) (hw : n + 1 < 2 ^ w)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (S j) (SI j)) = true) :
    ∀ wd : List Nat, wlK kS TJ wd = true →
      ∃ g, PRep n w (wvK n w (mask w) (pidn n w) S SI kS TJ wd) g ∧
        g ∈ Submonoid.closure (LJ n w S kS TJ)
  | [], _ => ⟨1, prep_pidn hn24 hw, Submonoid.one_mem _⟩
  | a :: wd, h => by
    have e : wlK kS TJ (a :: wd) = bAnd(Nat.blt a (Nat.shiftRight (stCnt TJ) (nat_lit 1)),
        bAnd(Nat.blt (stAt TJ a) kS, wlK kS TJ wd)) := rfl
    rw [e] at h
    simp only [bAnd_iff, Nat.blt_eq] at h
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨g, hg, hm⟩ := wv_facts hn24 hw hp wd h3
    have ev : wvK n w (mask w) (pidn n w) S SI kS TJ (a :: wd) = pcomp n w (mask w)
        (letterK S SI kS (stAt TJ a)) (wvK n w (mask w) (pidn n w) S SI kS TJ wd) := by
      change strictN _ _ = _
      rw [strictN_eq]
      rfl
    refine ⟨lp n w S kS (stAt TJ a) * g, ?_, Submonoid.mul_mem _
      (Submonoid.subset_closure ⟨a, h1, h2, rfl⟩) hm⟩
    rw [ev]
    exact prep_pcomp (by omega) (prep_lp hp (by omega)) hg

theorem wds_facts {n w kS TJ : Nat} {S SI : Nat → Nat} (hn24 : n < 16777216)
    (hw : n + 1 < 2 ^ w)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (S j) (SI j)) = true) :
    ∀ (W : List (List Nat)) (j : Nat), wdsK n w (mask w) (pidn n w) S SI kS TJ W j = true →
      ∀ j', j ≤ j' → j' < kS → pp n w (S j') ∈ Submonoid.closure (LJ n w S kS TJ)
  | [], j, h, j', h1, h2 => by
    have : j = kS := Nat.eq_of_beq_eq_true h
    omega
  | wd :: W, j, h, j', h1, h2 => by
    have e : wdsK n w (mask w) (pidn n w) S SI kS TJ (wd :: W) j = bAnd(wlK kS TJ wd,
        bAnd(Nat.beq (S j) (wvK n w (mask w) (pidn n w) S SI kS TJ wd),
          wdsK n w (mask w) (pidn n w) S SI kS TJ W (Nat.succ j))) := rfl
    rw [e] at h
    simp only [bAnd_iff] at h
    obtain ⟨h1', h2', h3'⟩ := h
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · obtain ⟨g, hg, hm⟩ := wv_facts hn24 hw hp wd h1'
      have hg' : PRep n w (S j) g := by
        rw [Nat.eq_of_beq_eq_true h2']
        exact hg
      have : pp n w (S j) = g := prep_unique (prep_pp (allN_iff.1 hp j h2)).1 hg'
      rw [this]
      exact hm
    · exact wds_facts hn24 hw hp W (Nat.succ j) h3' j' hlt h2

theorem schK_at {n w kS BP nb i T N CH : Nat} {S SI LR TR TRI : Nat → Nat}
    (hc : rcnt (LR i) ≤ N * CH)
    (hs : ∀ s < N, schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP nb i T (s * CH) CH =
      true) {h : Nat} (hh : h < rcnt (LR i)) :
    ∀ j < stCnt T, rpos w (mask w) (n * w) (LR i) (pg w (mask w) (letterK S SI kS (stAt T j))
        (rpt w (mask w) (LR i) h)) < rcnt (LR i) ∧
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP (Nat.sub nb (Nat.succ i)) (Nat.succ i)
        (pcomp n w (mask w) (TRI (Nat.add (roff n (n * w) (LR i)) (rpos w (mask w) (n * w) (LR i)
          (pg w (mask w) (letterK S SI kS (stAt T j)) (rpt w (mask w) (LR i) h)))))
          (pcomp n w (mask w) (letterK S SI kS (stAt T j)) (TR (Nat.add (roff n (n * w) (LR i)) h))))
        = true := by
  have hCH : 0 < CH := by
    rcases Nat.eq_zero_or_pos CH with h0 | h0
    · rw [h0, Nat.mul_zero] at hc
      omega
    · exact h0
  have hsN : h / CH < N := (Nat.div_lt_iff_lt_mul hCH).2 (by omega)
  have h1 := Nat.div_add_mod h CH
  have h2 := Nat.mod_lt h hCH
  exact schK_spec (hs _ hsN) (by rw [Nat.mul_comm]; omega) (by rw [Nat.mul_comm]; omega) hh

set_option maxHeartbeats 1000000 in
theorem schK_of_sch3GL {n w kS kO BP i D NSi N1 N2 CH TJ : Nat} {S SI LR TR TRI U : Nat → Nat}
    {W : List (List Int)} {WS : List (List Nat)}
    (hh : headK n w (mask w) (n * w) (pidn n w) S SI kS kO W (i + 3) BP = true)
    (hl : LevelsOK n w S SI LR TR TRI kS (i + 3) BP)
    (hinv : invTabK kS (stepsAt n w S kS BP i) = true)
    (h12 : lv12K w (mask w) S SI kS BP i (stepsAt n w S kS BP (i + 1))
      (stepsAt n w S kS BP (i + 1 + 1)) = true)
    (hU : utabF n w (mask w) (n * w) LR TR U i D = true)
    (hW : wdsK n w (mask w) (pidn n w) S SI kS TJ WS 0 = true)
    (hc : rcnt (LR i) ≤ NSi * CH)
    (hs : ∀ s < NSi, sch3F n w (mask w) (n * w) S SI LR TR TRI U kS BP i TJ D (s * CH) CH = true)
    (hc1 : rcnt (LR (i + 1)) ≤ N1 * CH)
    (hs1 : ∀ s < N1, schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP (i + 3) (i + 1)
      (stepsAt n w S kS BP (i + 1)) (s * CH) CH = true)
    (hc2 : rcnt (LR (i + 1 + 1)) ≤ N2 * CH)
    (hs2 : ∀ s < N2, schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP (i + 3) (i + 1 + 1)
      (stepsAt n w S kS BP (i + 1 + 1)) (s * CH) CH = true)
    (h₀ cnt : Nat) :
    schK n w (mask w) (n * w) (pidn n w) S SI LR TR TRI kS BP (i + 3) i
      (stepsAt n w S kS BP i) h₀ cnt = true := by
  obtain ⟨hp, -, -⟩ := head_facts hh
  obtain ⟨hsz, -, hR0, -, -, hp0⟩ := levelK_facts (hl i (by omega))
  obtain ⟨-, -, hR1, -, -, hp1⟩ := levelK_facts (hl (i + 1) (by omega))
  obtain ⟨-, -, hR2, -, -, hp2⟩ := levelK_facts (hl (i + 1 + 1) (by omega))
  obtain ⟨hn24, hw⟩ := szOK_facts hsz
  have hn : n < 2 ^ 32 := by omega
  unfold lv12K at h12
  simp only [bAnd_iff, Nat.succ_eq_add_one] at h12
  obtain ⟨hinv1, hinv2, hfx1, hfx2, hinc⟩ := h12
  have hT0 := letter_lt hinv
  have hT1 := letter_lt hinv1
  have hT2 := letter_lt hinv2
  have F0 := tree_facts hp (hl i (by omega)) hT0
  have F1 := tree_facts hp (hl (i + 1) (by omega)) hT1
  have F2 := tree_facts hp (hl (i + 1 + 1) (by omega)) hT2
  have hb0 : pg w (mask w) BP i < n := by rw [← hR0.root]; exact (hR0.pt 0 hR0.c_pos).1
  have hb1 : pg w (mask w) BP (i + 1) < n := by rw [← hR1.root]; exact (hR1.pt 0 hR1.c_pos).1
  have hb2 : pg w (mask w) BP (i + 1 + 1) < n := by
    rw [← hR2.root]
    exact (hR2.pt 0 hR2.c_pos).1
  have hinc' := inc_sub (n := n) (w := w) (kS := kS) (S := S) hinc
  have hA2 : ∀ σ ∈ LT n w S kS (stepsAt n w S kS BP (i + 1 + 1)), ∀ b < rcnt (LR (i + 1 + 1)),
      ∃ b' < rcnt (LR (i + 1 + 1)), σ * tp n w TR (LR (i + 1 + 1)) b =
        tp n w TR (LR (i + 1 + 1)) b' := by
    rintro σ ⟨j, hj, rfl⟩ b hb
    obtain ⟨hk, hsift⟩ := schK_at hc2 hs2 hb j hj
    refine ⟨_, hk, ?_⟩
    have e3 : Nat.sub (i + 3) (Nat.succ (i + 1 + 1)) = 0 := by
      simp only [Nat.sub_eq, Nat.succ_eq_add_one]
      omega
    rw [e3, siftK_zero] at hsift
    simp only [Nat.add_eq] at hsift
    have hG := Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 hsift).2
    have hPG := prep_pcomp hn (prep_pp (hp2 _ hk)).2
      (prep_pcomp hn (prep_lp hp (hT2 j hj)) (prep_pp (hp2 b hb)).1)
    rw [hG] at hPG
    exact (inv_mul_eq_one.1 (prep_unique hPG (prep_pidn hn24 hw))).symm
  have hA1 : ∀ σ ∈ LT n w S kS (stepsAt n w S kS BP (i + 1)), ∀ a < rcnt (LR (i + 1)),
      ∃ a' < rcnt (LR (i + 1)), ∃ b' < rcnt (LR (i + 1 + 1)),
        σ * tp n w TR (LR (i + 1)) a = tp n w TR (LR (i + 1)) a' * tp n w TR (LR (i + 1 + 1)) b' := by
    rintro σ ⟨j, hj, rfl⟩ a ha
    obtain ⟨hk, hsift⟩ := schK_at hc1 hs1 ha j hj
    have e3 : Nat.sub (i + 3) (Nat.succ (i + 1)) = 0 + 1 := by
      simp only [Nat.sub_eq, Nat.succ_eq_add_one]
      omega
    rw [e3, siftK_succ] at hsift
    simp only [strictB_eq, bIf_eq, Nat.blt_eq, Nat.add_eq, Nat.succ_eq_add_one] at hsift
    split at hsift
    · rename_i hk2
      rw [siftK_zero] at hsift
      have hG := Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 hsift).2
      have hPG := prep_pcomp hn (prep_pp (hp2 _ hk2)).2 (prep_pcomp hn (prep_pp (hp1 _ hk)).2
        (prep_pcomp hn (prep_lp hp (hT1 j hj)) (prep_pp (hp1 a ha)).1))
      rw [hG] at hPG
      have e := inv_mul_eq_one.1 (prep_unique hPG (prep_pidn hn24 hw))
      refine ⟨_, hk, _, hk2, ?_⟩
      unfold tp
      rw [e, mul_inv_cancel_left]
    · exact absurd hsift Bool.false_ne_true
  have hUU : ∀ u v, InU (rcnt (LR (i + 1))) (rcnt (LR (i + 1 + 1))) (tp n w TR (LR (i + 1)))
      (tp n w TR (LR (i + 1 + 1))) u → InU (rcnt (LR (i + 1))) (rcnt (LR (i + 1 + 1)))
      (tp n w TR (LR (i + 1))) (tp n w TR (LR (i + 1 + 1))) v →
      InU (rcnt (LR (i + 1))) (rcnt (LR (i + 1 + 1))) (tp n w TR (LR (i + 1)))
      (tp n w TR (LR (i + 1 + 1))) (u * v) := fun u v hu hv =>
    mulU hA2 hA1 (fun a ha => (F1 a ha).1) (fun b hb => (F2 b hb).1) hinc' hu hv
  have h10 : tp n w TR (LR (i + 1)) 0 = 1 := by
    obtain ⟨-, -, -, h0, -, -⟩ := levelK_facts (hl (i + 1) (by omega))
    have h1 : PRep n w (TR (roff n (n * w) (LR (i + 1)) + 0)) 1 := by
      rw [Nat.add_zero, h0]
      exact prep_pidn hn24 hw
    exact prep_unique (prep_pp (hp1 0 hR1.c_pos)).1 h1
  have h20 : tp n w TR (LR (i + 1 + 1)) 0 = 1 := by
    obtain ⟨-, -, -, h0, -, -⟩ := levelK_facts (hl (i + 1 + 1) (by omega))
    have h1 : PRep n w (TR (roff n (n * w) (LR (i + 1 + 1)) + 0)) 1 := by
      rw [Nat.add_zero, h0]
      exact prep_pidn hn24 hw
    exact prep_unique (prep_pp (hp2 0 hR2.c_pos)).1 h1
  have hone : InU (rcnt (LR (i + 1))) (rcnt (LR (i + 1 + 1))) (tp n w TR (LR (i + 1)))
      (tp n w TR (LR (i + 1 + 1))) 1 := ⟨0, hR1.c_pos, 0, hR2.c_pos, by rw [h10, h20, mul_one]⟩
  unfold utabF at hU
  simp only [strictB_eq, allN_iff, Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at hU
  have hF := t3K_of_sch3F hc hs
  have hD : ∀ σ ∈ LJ n w S kS TJ, ∀ h < rcnt (LR i), ∃ k < rcnt (LR i), ∃ u,
      InU (rcnt (LR (i + 1))) (rcnt (LR (i + 1 + 1))) (tp n w TR (LR (i + 1)))
        (tp n w TR (LR (i + 1 + 1))) u ∧ σ * tp n w TR (LR i) h = tp n w TR (LR i) k * u := by
    rintro σ ⟨a, ha, hak, rfl⟩ h hh
    obtain ⟨hk, hk1, hk2, hE⟩ := t3K_facts (hF h hh a ha) rfl rfl rfl rfl rfl
    refine ⟨_, hk, _, ⟨_, hk1, _, hk2, rfl⟩, ?_⟩
    have hP1 := prep_pcomp hn (prep_lp hp (by omega : stAt TJ a < kS + kS)) (prep_pp (hp0 h hh)).1
    rw [hE, hU _ hk1 _ hk2] at hP1
    exact prep_unique hP1 (prep_pcomp hn (prep_pp (hp0 _ hk)).1
      (prep_pcomp hn (prep_pp (hp1 _ hk1)).1 (prep_pp (hp2 _ hk2)).1))
  have hWm := wds_facts hn24 hw hp WS 0 hW
  obtain ⟨q, hq, hqf⟩ := invTab_facts hinv
  have hmem : ∀ j < stCnt (stepsAt n w S kS BP i),
      lp n w S kS (stAt (stepsAt n w S kS BP i) j) ∈ Submonoid.closure (LJ n w S kS TJ) := by
    intro j hj
    rcases Nat.lt_or_ge j q with h1 | h1
    · have hl := (hqf j h1).1
      have e : lp n w S kS (stAt (stepsAt n w S kS BP i) j) =
          pp n w (S (stAt (stepsAt n w S kS BP i) j)) := by
        unfold lp
        exact if_pos hl
      rw [e]
      exact hWm _ (Nat.zero_le _) hl
    · obtain ⟨j', rfl⟩ : ∃ j', j = q + j' := ⟨j - q, by omega⟩
      obtain ⟨hl, e1⟩ := hqf j' (by omega)
      have e : lp n w S kS (stAt (stepsAt n w S kS BP i) (q + j')) =
          (pp n w (S (stAt (stepsAt n w S kS BP i) j')))⁻¹ := by
        unfold lp
        rw [if_neg (by omega), e1, Nat.add_sub_cancel_left]
      rw [e]
      exact inv_mem_closure (hWm _ (Nat.zero_le _) hl)
  have e2 : Nat.sub (i + 3) (Nat.succ i) = 0 + 1 + 1 := by
    simp only [Nat.sub_eq, Nat.succ_eq_add_one]
    omega
  unfold schK
  rw [e2]
  simp only [strictB_eq, allN_iff, bIf_eq, Nat.blt_eq, Nat.add_eq, Nat.succ_eq_add_one]
  intro dh _
  split
  case isFalse => rfl
  rename_i hc'
  rw [allN_iff]
  intro j hj
  have hσ := prep_lp hp (hT0 j hj)
  obtain ⟨k', hk', u, ⟨a, ha, b, hb, rfl⟩, e⟩ :=
    mulC hUU hD hone (hmem j hj) (h₀ + dh) hc'
  have f1 : ∀ x (hx : x < n), (∀ g ∈ LT n w S kS (stepsAt n w S kS BP (i + 1)),
      g ⟨x, hx⟩ = ⟨x, hx⟩) → tp n w TR (LR (i + 1)) a ⟨x, hx⟩ = ⟨x, hx⟩ ∧
        tp n w TR (LR (i + 1 + 1)) b ⟨x, hx⟩ = ⟨x, hx⟩ := fun x hx hL =>
    ⟨fix_of_closure hL (F1 a ha).1,
      fix_of_closure (fun g hg => hL g (hinc' hg)) (F2 b hb).1⟩
  obtain ⟨fa, fb⟩ := f1 _ hb0 (fix_LT hp hT1 hfx1 hb0)
  have fb1 : tp n w TR (LR (i + 1 + 1)) b ⟨_, hb1⟩ = ⟨_, hb1⟩ :=
    fix_of_closure (fix_LT hp hT2 hfx2 hb1) (F2 b hb).1
  have ept : pg w (mask w) (letterK S SI kS (stAt (stepsAt n w S kS BP i) j))
      (rpt w (mask w) (LR i) (h₀ + dh)) = rpt w (mask w) (LR i) k' := by
    rw [← (F0 _ hc').2 hb0, hσ, ← Equiv.Perm.mul_apply, e, Equiv.Perm.mul_apply,
      Equiv.Perm.mul_apply, fb, fa, (F0 k' hk').2 hb0]
  have ek : rpos w (mask w) (n * w) (LR i) (pg w (mask w)
      (letterK S SI kS (stAt (stepsAt n w S kS BP i) j)) (rpt w (mask w) (LR i) (h₀ + dh))) = k' := by
    rw [ept]
    exact (hR0.pt k' hk').2
  rw [ek, if_pos hk']
  have hPG : PRep n w _ ((tp n w TR (LR i) k')⁻¹ *
      (lp n w S kS (stAt (stepsAt n w S kS BP i) j) * tp n w TR (LR i) (h₀ + dh))) :=
    prep_pcomp hn (prep_pp (hp0 _ hk')).2 (prep_pcomp hn hσ (prep_pp (hp0 _ hc')).1)
  rw [e, inv_mul_cancel_left] at hPG
  have hPa := (prep_pp (hp1 a ha)).1
  have hPb := (prep_pp (hp2 b hb)).1
  have hPai : PRep n w (TRI (roff n (n * w) (LR (i + 1)) + a)) (tp n w TR (LR (i + 1)) a)⁻¹ :=
    (prep_pp (hp1 a ha)).2
  refine sift2_of_fields hsz hb2 ?_ ha ?_ hb (hp1 a ha) (hp2 b hb) (fun x hx => ?_)
  · have h1 : pg w (mask w) _ (pg w (mask w) BP (i + 1)) = _ := hPG ⟨_, hb1⟩
    rw [h1, Equiv.Perm.mul_apply, fb1, (F1 a ha).2 hb1]
    exact (hR1.pt a ha).2
  · have h1 : pg w (mask w) _ (pg w (mask w) BP (i + 1 + 1)) = _ := hPG ⟨_, hb2⟩
    rw [h1, hPai, ← Equiv.Perm.mul_apply, inv_mul_cancel_left, (F2 b hb).2 hb2]
    exact (hR2.pt b hb).2
  · have h1 : pg w (mask w) _ x = _ := hPG ⟨x, hx⟩
    have h2 : pg w (mask w) _ x = _ := hPb ⟨x, hx⟩
    rw [h1, h2, hPa, Equiv.Perm.mul_apply]
    rfl

end CFSG.KS.Raw.Orb

end
