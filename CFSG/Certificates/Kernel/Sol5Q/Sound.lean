module

public import Certificates.Data.Kernel.Sol5Q.Check
public import CFSG.Certificates.Kernel.BalanceSC.BalSound
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5QChk
import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Order
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5QArr
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5QTab

public section

namespace CFSG.KC.Sol5Q

open CFSG.KC.Enum (pg pcomp pidn strictN strictB)
open CFSG.KS (mask pinvS)
open CFSG.KS.Raw (unpack szOK)
open CFSG.KC.BfsPin (PP)
open CFSG.KC.BalanceSC (notB tab64 memL anyL zipAll)
open CFSG.KC.Misc.ArrEnum (permB pp_of_permB)
open CFSG.KC.BalanceSC.SylowEq (mulA_u eqA_u idA_u bAnd_eq notB_eq)
open CFSG.OddStandard.Solomon75 CFSG.OddStandard.Solomon75.AhatData
open Certificates.Solomon75Sec5Q (sigA cardC)
open Equiv Equiv.Perm Subgroup

open scoped commutatorElement

theorem fc2_of_le {n : ℕ} [NeZero n] (hn : n ≤ 11) (σ : Perm (Fin n)) : FC2 n σ := by
  intro x _ ⟨j, hj⟩
  have hdvd : orderOf x ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj
  have h8 : orderOf x ∣ 8 := by
    rw [← Equiv.Perm.lcm_cycleType]
    refine Multiset.lcm_dvd.2 fun c hc => ?_
    obtain ⟨a, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      ((Equiv.Perm.dvd_of_mem_cycleType hc).trans hdvd)
    have hle : 2 ^ a ≤ 11 :=
      ((Equiv.Perm.le_card_support_of_mem_cycleType hc).trans
        ((Finset.card_le_univ _).trans_eq (Fintype.card_fin n))).trans hn
    have ha : a ≤ 3 := by
      by_contra h
      have : 2 ^ 4 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact (pow_dvd_pow 2 ha).trans (by norm_num)
  exact orderOf_dvd_iff_pow_eq_one.1 h8

@[expose] noncomputable def dec (n p : ℕ) : Perm (Fin n) :=
  if h : CFSG.KS.PinvS.InjK n 4 p then
    Equiv.ofBijective (fun i : Fin n => (⟨pg 4 (mask 4) p i, h.1 i i.2⟩ : Fin n))
      (Finite.injective_iff_bijective.1 fun a b e =>
        Fin.ext (h.2 a a.2 b b.2 (congrArg Fin.val e)))
  else 1

variable {n : ℕ}

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by cases y <;> rfl

theorem rep_dec {p : ℕ} (hp : PP n 4 p) : Rep n (unpack n 4 p) (dec n p) := fun i => by
  rw [CFSG.KS.Raw.Orb.unpack_get i.2]
  unfold dec
  rw [dif_pos hp.2]
  rfl

theorem pp_pc {p q : ℕ} (hp : PP n 4 p) (hq : PP n 4 q) : PP n 4 (pc n p q) := hp.mul hq

theorem pp_pinv {p : ℕ} (hp : PP n 4 p) : PP n 4 (pinv n p) := hp.inv

theorem dec_mul {p q : ℕ} (hp : PP n 4 p) (hq : PP n 4 q) :
    dec n (pc n p q) = dec n p * dec n q := by
  refine Rep.unique (rep_dec (pp_pc hp hq)) ?_
  have := rep_mulA (rep_dec hp) (rep_dec hq)
  rw [mulA_u hp hq] at this
  exact this

theorem dec_pinv {p : ℕ} (hp : PP n 4 p) : dec n (pinv n p) = (dec n p)⁻¹ :=
  Rep.unique (rep_dec (pp_pinv hp)) (CFSG.KC.BalanceSC.BalSound.rep_pinvS hp (rep_dec hp))

theorem dec_id (hsz : szOK n 4 = true) : dec n (pidn n 4) = 1 := by
  refine Rep.unique (rep_dec (CFSG.KC.BfsPin.PP.id hsz)) ?_
  rw [← idA_u hsz]
  exact rep_idA

theorem dec_inj {p q : ℕ} (hp : PP n 4 p) (hq : PP n 4 q) (h : dec n p = dec n q) : p = q := by
  have h2 := (eqA_iff (rep_dec hp) (rep_dec hq)).2 h
  rw [eqA_u hp hq] at h2
  exact Nat.eq_of_beq_eq_true h2

theorem sz_of_le (hn' : n ≤ 11) : szOK n 4 = true := by
  interval_cases n <;> rfl

theorem pw_succ (e p k : ℕ) : pw n e p (k + 1) = pc n p (pw n e p k) := strictN_eq _ _

theorem dec_pw (hsz : szOK n 4 = true) {p : ℕ} (hp : PP n 4 p) :
    ∀ k, PP n 4 (pw n (pidn n 4) p k) ∧ dec n (pw n (pidn n 4) p k) = dec n p ^ k
  | 0 => ⟨CFSG.KC.BfsPin.PP.id hsz, by rw [pow_zero]; exact dec_id hsz⟩
  | k + 1 => by
    obtain ⟨h1, h2⟩ := dec_pw hsz hp k
    rw [pw_succ]
    exact ⟨pp_pc hp h1, by rw [dec_mul hp h1, h2, pow_succ']⟩

theorem pow_eq_one_of (hsz : szOK n 4 = true) {p k : ℕ} (hp : PP n 4 p)
    (h : pw n (pidn n 4) p k = pidn n 4) : dec n p ^ k = 1 := by
  rw [← (dec_pw hsz hp k).2, h, dec_id hsz]

theorem pow_ne_one_of (hsz : szOK n 4 = true) {p k : ℕ} (hp : PP n 4 p)
    (h : pw n (pidn n 4) p k ≠ pidn n 4) : dec n p ^ k ≠ 1 := fun e =>
  h (dec_inj (dec_pw hsz hp k).1 (CFSG.KC.BfsPin.PP.id hsz)
    (by rw [(dec_pw hsz hp k).2, e, dec_id hsz]))

theorem fixC_eq_sum (p : ℕ) : ∀ m, fixC m p = ∑ i ∈ Finset.range m, if pg 4 15 p i = i then 1 else 0
  | 0 => by simp [fixC]
  | m + 1 => by
    rw [Finset.sum_range_succ, ← fixC_eq_sum p m]
    change Nat.add (fixC m p) (Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.beq (pg 4 15 p m) m)) = _
    cases h : Nat.beq (pg 4 15 p m) m
    · simp [Nat.ne_of_beq_eq_false h]
    · simp [Nat.eq_of_beq_eq_true h]

theorem fixC_eq {p : ℕ} (hp : PP n 4 p) : fixC n p = fixCount (dec n p) := by
  rw [fixC_eq_sum, fixCount, Finset.card_filter,
    ← Fin.sum_univ_eq_sum_range (fun i => if pg 4 15 p i = i then 1 else 0)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := rep_dec hp i
  rw [CFSG.KS.Raw.Orb.unpack_get i.2] at h
  have e : (dec n p i = i) ↔ pg 4 15 p i = i := by
    rw [Fin.ext_iff]
    exact ⟨fun h' => h.trans h', fun h' => h.symm.trans h'⟩
  by_cases hc : dec n p i = i
  · rw [if_pos hc, if_pos (e.1 hc)]
  · rw [if_neg hc, if_neg (fun h' => hc (e.2 h'))]

theorem fix_add_supp (σ : Perm (Fin n)) : fixCount σ + σ.support.card = n := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i => σ i = i)
  rwa [Finset.card_univ, Fintype.card_fin] at h

theorem badK_sound (hsz : szOK n 4 = true) {r : ℕ} (hr : PP n 4 r)
    (h : badK n (pidn n 4) r = true) :
    dec n r * dec n r = 1 ∧ dec n r ≠ 1 ∧ 4 ≤ fixCount (dec n r) := by
  unfold badK at h
  rw [bAnd_eq, bAnd_eq, notB_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, fun e => ?_, ?_⟩
  · rw [← dec_mul hr hr, Nat.eq_of_beq_eq_true h1, dec_id hsz]
  · exact Nat.ne_of_beq_eq_false h2
      (dec_inj hr (CFSG.KC.BfsPin.PP.id hsz) (by rw [e, dec_id hsz]))
  · rw [← fixC_eq hr]
    exact Nat.le_of_ble_eq_true h3

theorem even_of {σ : Perm (Fin n)} {m : ℕ} (h1 : σ ^ m ≠ 1) (h2 : σ ^ (m + m) = 1) :
    Even (orderOf σ) := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  have hd : orderOf σ ∣ m * 2 := by
    rw [mul_two]
    exact orderOf_dvd_of_pow_eq_one h2
  exact h1 (orderOf_dvd_iff_pow_eq_one.1 (hodd.coprime_two_right.dvd_of_dvd_mul_right hd))

theorem dec_cjK {HB x j : ℕ} (hx : PP n 4 x) (hh : PP n 4 (tab64 HB j)) :
    PP n 4 (cjK n HB x j) ∧
      dec n (cjK n HB x j) = dec n (tab64 HB j) * dec n x * (dec n (tab64 HB j))⁻¹ := by
  unfold cjK
  rw [strictN_eq]
  refine ⟨pp_pc hh (pp_pc hx (pp_pinv hh)), ?_⟩
  rw [dec_mul hh (pp_pc hx (pp_pinv hh)), dec_mul hx (pp_pinv hh), dec_pinv hh, mul_assoc]

theorem dec_commK {a b : ℕ} (ha : PP n 4 a) (hb : PP n 4 b) :
    PP n 4 (commK n a b) ∧ dec n (commK n a b) = ⁅dec n a, dec n b⁆ := by
  unfold commK
  refine ⟨pp_pc (pp_pc ha hb) (pp_pc (pp_pinv ha) (pp_pinv hb)), ?_⟩
  rw [dec_mul (pp_pc ha hb) (pp_pc (pp_pinv ha) (pp_pinv hb)), dec_mul ha hb,
    dec_mul (pp_pinv ha) (pp_pinv hb), dec_pinv ha, dec_pinv hb, commutatorElement_def]
  group

theorem allL_iff {L : List ℕ} {f : ℕ → Bool} : allL L f = true ↔ ∀ d ∈ L, f d = true := by
  induction L with
  | nil => exact iff_of_true rfl (by simp)
  | cons d L ih =>
    change bAnd(f d, allL L f) = true ↔ _
    rw [bAnd_eq, Bool.and_eq_true, ih, List.forall_mem_cons]

@[expose] noncomputable def ctF (n S card : ℕ) (CT : List ℕ) : ℕ → ℕ → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun _ c => Nat.beq c card)
    (fun x _ ih lo c => bAnd(Nat.ble lo x, bAnd(permB n (nat_lit 4) x,
      bAnd(Nat.beq (pc n S x) (pc n x S), strictB (Nat.succ c) (ih (Nat.succ x)))))) CT

theorem ctF_cons (S card x lo c : ℕ) (CT : List ℕ) : ctF n S card (x :: CT) lo c =
    (Nat.ble lo x && (permB n 4 x && (Nat.beq (pc n S x) (pc n x S) &&
      ctF n S card CT (x + 1) (c + 1)))) := by
  change bAnd(Nat.ble lo x, bAnd(permB n 4 x, bAnd(Nat.beq (pc n S x) (pc n x S),
    strictB (Nat.succ c) (ctF n S card CT (Nat.succ x))))) = _
  rw [CFSG.KC.BalanceSC.SylowEq.strictB_eq, bAnd_eq, bAnd_eq, bAnd_eq]

theorem ctF_sound {S card : ℕ} : ∀ (CT : List ℕ) (lo c : ℕ), ctF n S card CT lo c = true →
    (∀ x ∈ CT, lo ≤ x) ∧ CT.Pairwise (· < ·) ∧
      (∀ x ∈ CT, permB n 4 x = true ∧ pc n S x = pc n x S) ∧ c + CT.length = card
  | [], lo, c, h => ⟨by simp, List.Pairwise.nil, by simp, by
      simpa using Nat.eq_of_beq_eq_true h⟩
  | x :: CT, lo, c, h => by
    rw [ctF_cons, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    obtain ⟨i1, i2, i3, i4⟩ := ctF_sound CT (x + 1) (c + 1) h4
    have hx := Nat.le_of_ble_eq_true h1
    refine ⟨?_, List.pairwise_cons.2 ⟨fun y hy => i1 y hy, i2⟩, ?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hx
      · have := i1 y hy
        omega
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ⟨h2, Nat.eq_of_beq_eq_true h3⟩
      · exact i3 y hy
    · rw [List.length_cons]
      omega

theorem ctOK_sound {S card : ℕ} {CT : List ℕ} (h : ctOK n S card CT = true) :
    CT.Pairwise (· < ·) ∧ (∀ x ∈ CT, permB n 4 x = true ∧ pc n S x = pc n x S) ∧
      CT.length = card := by
  obtain ⟨-, i2, i3, i4⟩ := ctF_sound CT 0 0 h
  exact ⟨i2, i3, by omega⟩

theorem atL_sound {f : ℕ → Bool} : ∀ (L : List ℕ) (i : ℕ), atL L i f = true → ∃ d ∈ L, f d = true
  | [], _, h => absurd h Bool.false_ne_true
  | d :: _, 0, h => ⟨d, List.mem_cons_self, h⟩
  | _ :: L, j + 1, h => by
    obtain ⟨e, he, hf⟩ := atL_sound L j h
    exact ⟨e, List.mem_cons_of_mem _ he, hf⟩

@[expose] noncomputable def hF (n HB NH : ℕ) (HG : List ℕ) (HPL : List (ℕ × ℕ)) : ℕ → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun k => Nat.beq k NH)
    (fun pl _ ih k => bAnd(Nat.blt pl.1 k, bAnd(atL HG pl.2 fun g =>
        Nat.beq (tab64 HB k) (pc n (tab64 HB pl.1) g), strictB (Nat.succ k) ih))) HPL

theorem hF_cons (HB NH k : ℕ) (HG : List ℕ) (pl : ℕ × ℕ) (HPL : List (ℕ × ℕ)) :
    hF n HB NH HG (pl :: HPL) k = (Nat.blt pl.1 k && (atL HG pl.2 (fun g =>
      Nat.beq (tab64 HB k) (pc n (tab64 HB pl.1) g)) && hF n HB NH HG HPL (k + 1))) := by
  change bAnd(Nat.blt pl.1 k, bAnd(atL HG pl.2 fun g =>
    Nat.beq (tab64 HB k) (pc n (tab64 HB pl.1) g), strictB (Nat.succ k) (hF n HB NH HG HPL))) = _
  rw [CFSG.KC.BalanceSC.SylowEq.strictB_eq, bAnd_eq, bAnd_eq]

theorem hF_sound {HB NH : ℕ} {HG : List ℕ} : ∀ (HPL : List (ℕ × ℕ)) (k : ℕ),
    hF n HB NH HG HPL k = true →
      ∀ k', k ≤ k' → k' < NH → ∃ par < k', ∃ g ∈ HG, tab64 HB k' = pc n (tab64 HB par) g
  | [], k, h, k', hk, hk' => by
    have := Nat.eq_of_beq_eq_true h
    omega
  | pl :: HPL, k, h, k', hk, hk' => by
    rw [hF_cons, Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨h1, h2, h3⟩ := h
    rcases Nat.eq_or_lt_of_le hk with rfl | hlt
    · obtain ⟨g, hg, hgq⟩ := atL_sound HG pl.2 h2
      exact ⟨pl.1, Nat.blt_eq.mp h1, g, hg, Nat.eq_of_beq_eq_true hgq⟩
    · exact hF_sound HPL (k + 1) h3 k' hlt hk'

theorem hOK_sound {e HB NH : ℕ} {HG : List ℕ} {HPL : List (ℕ × ℕ)}
    (h : hOK n e HB NH HG HPL = true) :
    tab64 HB 0 = e ∧ ∀ k, 0 < k → k < NH → ∃ par < k, ∃ g ∈ HG, tab64 HB k = pc n (tab64 HB par) g := by
  change bAnd(Nat.beq (tab64 HB (nat_lit 0)) e, hF n HB NH HG HPL 1) = true at h
  rw [bAnd_eq, Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, fun k hk hk' => hF_sound HPL 1 h.2 k hk hk'⟩

theorem gensK_sound {e S : ℕ} {HG : List ℕ} (h : gensK n e S HG = true) :
    ∀ g ∈ HG, permB n 4 g = true ∧ pc n S g = pc n g S ∧ (pw n e g 3 = e ∨
      (pc n g g = e ∧ fixC n g = n - 8 ∧ fixC n (pc n g S) = n - 8)) := by
  intro g hg
  have h1 := allL_iff.1 h g hg
  simp only [bAnd_eq, CFSG.KC.BalanceSC.SylowEq.bIf_true_eq, Bool.and_eq_true,
    Bool.or_eq_true] at h1
  obtain ⟨hp, hc, h3⟩ := h1
  refine ⟨hp, Nat.eq_of_beq_eq_true hc, ?_⟩
  rcases h3 with h3 | ⟨a, b, c⟩
  · exact Or.inl (Nat.eq_of_beq_eq_true h3)
  · exact Or.inr ⟨Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true b, Nat.eq_of_beq_eq_true c⟩

theorem evK_sound {e w m : ℕ} (h : evK n e w m = true) :
    pw n e w m ≠ e ∧ pw n e w (m + m) = e := by
  unfold evK at h
  rw [bAnd_eq, notB_eq, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨Nat.ne_of_beq_eq_false h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem fcbK_sound {e HB NH : ℕ} {BN CT : List ℕ} {RB : List (List ℕ)}
    (h : fcbK n e HB NH BN CT RB = true) :
    ∀ b ∈ CT, (∃ m, pw n e b m ≠ e ∧ pw n e b (m + m) = e) ∨ b ∈ BN ∨
      ∃ j < NH, ∃ m, pw n e (pc n b (cjK n HB b j)) m ≠ e ∧
        pw n e (pc n b (cjK n HB b j)) (m + m) = e := by
  intro b hb
  obtain ⟨r, -, hr⟩ := CFSG.KC.BalanceSC.TableSound.zipAll_mem h b hb
  rcases r with _ | ⟨t, rest⟩
  · exact absurd hr Bool.false_ne_true
  change Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool)
    (atL rest (nat_lit 0) fun h => atL rest (nat_lit 1) fun m =>
      bAnd(Nat.blt h NH, strictB (pc n b (cjK n HB b h)) fun w => evK n e w m))
    (memL b BN) (Nat.beq t (nat_lit 1))) (atL rest (nat_lit 0) (evK n e b))
    (Nat.beq t (nat_lit 0)) = true at hr
  generalize Nat.beq t (nat_lit 0) = c0 at hr
  generalize Nat.beq t (nat_lit 1) = c1 at hr
  cases c0
  · cases c1
    · obtain ⟨j, -, hj⟩ := atL_sound rest 0 hr
      obtain ⟨m, -, hm⟩ := atL_sound rest 1 hj
      rw [bAnd_eq, Bool.and_eq_true, CFSG.KC.BalanceSC.SylowEq.strictB_eq] at hm
      exact Or.inr (Or.inr ⟨j, Nat.blt_eq.mp hm.1, m, evK_sound hm.2⟩)
    · exact Or.inr (Or.inl ((CFSG.KC.BalanceSC.SylowEq.memL_iff b BN).1 hr))
  · obtain ⟨m, -, hm⟩ := atL_sound rest 0 hr
    exact Or.inl ⟨m, evK_sound hm⟩

private theorem fc_bIf (c a b : Bool) : bIf(c, a, b) = (if c = true then a else b) := by
  cases c <;> rfl

private theorem zipAll_mem_right {α β : Type} {f : α → β → Bool} :
    ∀ {as : List α} {bs : List β}, zipAll f as bs = true → ∀ b ∈ bs, ∃ a ∈ as, f a b = true
  | _, [], _, b, hb => absurd hb List.not_mem_nil
  | [], _ :: _, h, _, _ => by
    rw [CFSG.KC.BalanceSC.TableSound.zipAll_nil_cons] at h
    exact absurd h Bool.false_ne_true
  | x :: as, y :: bs, h, b, hb => by
    rw [CFSG.KC.BalanceSC.TableSound.zipAll_cons_cons, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨x, List.mem_cons_self, h.1⟩
    · obtain ⟨a, ha, hab⟩ := zipAll_mem_right h.2 b hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hab⟩

private theorem rowK_sound {e : ℕ} {big : Bool} {BN Sl : List ℕ} : ∀ (CT rs Gs : List ℕ),
    rowK n e big BN Sl CT rs Gs = true →
      (∀ g ∈ CT, (∃ t ∈ Sl, ∀ b ∈ BN, pc n g t ≠ pc n (pc n b t) g) ∨
        (big = false ∧ pw n e g 8 = e) ∨ (big = true ∧ g ∈ Gs)) ∧ ∀ a ∈ Gs, a ∈ CT
  | [], rs, Gs, h => by
    change bAnd(emptyL rs, emptyL Gs) = true at h
    rw [bAnd_eq, Bool.and_eq_true] at h
    cases Gs with
    | nil => exact ⟨fun g hg => absurd hg List.not_mem_nil, fun a ha => absurd ha List.not_mem_nil⟩
    | cons a Gs => exact absurd h.2 Bool.false_ne_true
  | _ :: _, [], _, h => absurd h Bool.false_ne_true
  | g :: CT, c :: rs, Gs, h => by
    cases c with
    | succ i =>
      change bAnd(atL Sl i fun t => CFSG.KC.BalanceSC.notB (anyL BN fun b => Nat.beq (pc n g t) (pc n (pc n b t) g)),
        rowK n e big BN Sl CT rs Gs) = true at h
      rw [bAnd_eq, Bool.and_eq_true] at h
      obtain ⟨hA, hB⟩ := rowK_sound CT rs Gs h.2
      refine ⟨fun g' hg' => ?_, fun a ha => List.mem_cons_of_mem _ (hB a ha)⟩
      rcases List.mem_cons.1 hg' with rfl | hg'
      · obtain ⟨t, ht, hnt⟩ := atL_sound Sl i h.1
        rw [notB_eq, Bool.not_eq_true', CFSG.KC.BalanceSC.SylowEq.anyL_eq,
          List.any_eq_false] at hnt
        refine Or.inl ⟨t, ht, fun b hb he => hnt b hb ?_⟩
        rw [Nat.beq_eq]
        exact he
      · exact hA g' hg'
    | zero =>
      cases big with
      | false =>
        change bAnd(Nat.beq (pw n e g 8) e, rowK n e false BN Sl CT rs Gs) = true at h
        rw [bAnd_eq, Bool.and_eq_true] at h
        obtain ⟨hA, hB⟩ := rowK_sound CT rs Gs h.2
        refine ⟨fun g' hg' => ?_, fun a ha => List.mem_cons_of_mem _ (hB a ha)⟩
        rcases List.mem_cons.1 hg' with rfl | hg'
        · exact Or.inr (Or.inl ⟨rfl, Nat.eq_of_beq_eq_true h.1⟩)
        · exact hA g' hg'
      | true =>
        cases Gs with
        | nil => exact absurd h Bool.false_ne_true
        | cons a Gs =>
          change bAnd(Nat.beq a g, rowK n e true BN Sl CT rs Gs) = true at h
          rw [bAnd_eq, Bool.and_eq_true] at h
          have hag : a = g := Nat.eq_of_beq_eq_true h.1
          obtain ⟨hA, hB⟩ := rowK_sound CT rs Gs h.2
          refine ⟨fun g' hg' => ?_, fun a' ha' => ?_⟩
          · rcases List.mem_cons.1 hg' with rfl | hg'
            · exact Or.inr (Or.inr ⟨rfl, hag ▸ List.mem_cons_self⟩)
            · rcases hA g' hg' with h1 | h1 | ⟨h1, h2⟩
              · exact Or.inl h1
              · exact Or.inr (Or.inl h1)
              · exact Or.inr (Or.inr ⟨h1, List.mem_cons_of_mem _ h2⟩)
          · rcases List.mem_cons.1 ha' with rfl | ha'
            · rw [hag]
              exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (hB a' ha')

private noncomputable def fcrF (n e S HB NH : ℕ) (big : Bool) (BN CT : List ℕ) :
    List ℕ → List (List ℕ) → List (List ℕ × List ℕ × List ℕ × List ℕ) → Bool :=
  List.rec
    (motive := fun _ => List (List ℕ) → List (List ℕ × List ℕ × List ℕ × List ℕ) → Bool)
    (fun RR GD => bAnd(emptyL RR, emptyL GD))
    (fun x _ ih RR GD => List.rec (motive := fun _ => Bool) false (fun r RR' _ =>
      List.rec (motive := fun _ => Bool) false (fun t rest _ =>
        bIf(Nat.beq t (nat_lit 0), bAnd(CFSG.KC.BalanceSC.notB (Nat.beq (pw n e x (nat_lit 8)) e), ih RR' GD),
        bIf(Nat.beq t (nat_lit 1), bAnd(bIf(Nat.beq x e, true, Nat.beq x S), ih RR' GD),
        bIf(Nat.beq t (nat_lit 2), bAnd(allL rest (fun c => Nat.ble c NH),
            bAnd(badK n e (prodK n e S HB x rest), ih RR' GD)),
          List.rec (motive := fun _ => Bool) false
            (fun g GD' _ => bAnd(goodK n e HB NH big BN CT x rest g, ih RR' GD')) GD)))) r) RR)

private theorem fcrF_cons (e S HB NH : ℕ) (big : Bool) (BN CT : List ℕ) (x : ℕ) (L : List ℕ)
    (t : ℕ) (rest : List ℕ) (RR : List (List ℕ)) (GD : List (List ℕ × List ℕ × List ℕ × List ℕ)) :
    fcrF n e S HB NH big BN CT (x :: L) ((t :: rest) :: RR) GD =
      bIf(Nat.beq t 0, bAnd(CFSG.KC.BalanceSC.notB (Nat.beq (pw n e x 8) e), fcrF n e S HB NH big BN CT L RR GD),
      bIf(Nat.beq t 1, bAnd(bIf(Nat.beq x e, true, Nat.beq x S),
          fcrF n e S HB NH big BN CT L RR GD),
      bIf(Nat.beq t 2, bAnd(allL rest (fun c => Nat.ble c NH),
          bAnd(badK n e (prodK n e S HB x rest), fcrF n e S HB NH big BN CT L RR GD)),
        List.rec (motive := fun _ => Bool) false
          (fun g GD' _ => bAnd(goodK n e HB NH big BN CT x rest g,
            fcrF n e S HB NH big BN CT L RR GD')) GD))) := rfl

private def FcrC (e S HB NH : ℕ) (big : Bool) (BN CT : List ℕ) (x : ℕ) : Prop :=
  pw n e x 8 ≠ e ∨ x = e ∨ x = S ∨
    (∃ cs : List ℕ, (∀ c ∈ cs, c ≤ NH) ∧ badK n e (prodK n e S HB x cs) = true) ∨
    ∃ Sl Gl Kl : List ℕ, (∀ s ∈ Sl, ∃ j < NH, s = cjK n HB x j) ∧ (∀ a ∈ Gl, a ∈ CT) ∧
      (∀ g ∈ CT, (∃ t ∈ Sl, ∀ b ∈ BN, pc n g t ≠ pc n (pc n b t) g) ∨
        (big = false ∧ pw n e g 8 = e) ∨ (big = true ∧ g ∈ Gl)) ∧
      (big = true → (∀ a ∈ Gl, ∀ b ∈ Gl, commK n a b ∈ Kl) ∧
        ∀ u ∈ Kl, ∀ v ∈ Kl, pc n u v = pc n v u)

private theorem fcrF_sound {e S HB NH : ℕ} {big : Bool} {BN CT : List ℕ} :
    ∀ (L : List ℕ) (RR : List (List ℕ)) (GD : List (List ℕ × List ℕ × List ℕ × List ℕ)),
      fcrF n e S HB NH big BN CT L RR GD = true → ∀ x ∈ L, FcrC (n := n) e S HB NH big BN CT x
  | [], _, _, _, x, hx => absurd hx List.not_mem_nil
  | _ :: _, [], _, h, _, _ => absurd h Bool.false_ne_true
  | _ :: _, [] :: _, _, h, _, _ => absurd h Bool.false_ne_true
  | x :: L, (t :: rest) :: RR', GD, h, y, hy => by
    suffices H : FcrC (n := n) e S HB NH big BN CT x ∧
        ∃ RR GD, fcrF n e S HB NH big BN CT L RR GD = true by
      rcases List.mem_cons.1 hy with rfl | hy
      · exact H.1
      · obtain ⟨RR, GD, h'⟩ := H.2
        exact fcrF_sound L RR GD h' y hy
    rw [fcrF_cons] at h
    by_cases h0 : Nat.beq t 0 = true
    · rw [fc_bIf (Nat.beq t 0), if_pos h0, bAnd_eq, Bool.and_eq_true, notB_eq,
        Bool.not_eq_true'] at h
      exact ⟨Or.inl (Nat.ne_of_beq_eq_false h.1), RR', GD, h.2⟩
    rw [fc_bIf (Nat.beq t 0), if_neg h0, fc_bIf (Nat.beq t 1)] at h
    by_cases h1 : Nat.beq t 1 = true
    · rw [if_pos h1, bAnd_eq, Bool.and_eq_true, fc_bIf (Nat.beq x e)] at h
      refine ⟨?_, RR', GD, h.2⟩
      by_cases hxe : Nat.beq x e = true
      · exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true hxe))
      · rw [if_neg hxe] at h
        exact Or.inr (Or.inr (Or.inl (Nat.eq_of_beq_eq_true h.1)))
    rw [if_neg h1, fc_bIf (Nat.beq t 2)] at h
    by_cases h2 : Nat.beq t 2 = true
    · rw [if_pos h2, bAnd_eq, Bool.and_eq_true, bAnd_eq, Bool.and_eq_true] at h
      exact ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨rest,
        fun c hc => Nat.le_of_ble_eq_true (allL_iff.1 h.1 c hc), h.2.1⟩))), RR', GD, h.2.2⟩
    rw [if_neg h2] at h
    cases GD with
    | nil => exact absurd h Bool.false_ne_true
    | cons g GD' =>
      change bAnd(goodK n e HB NH big BN CT x rest g, fcrF n e S HB NH big BN CT L RR' GD') =
        true at h
      rw [bAnd_eq, Bool.and_eq_true] at h
      refine ⟨?_, RR', GD', h.2⟩
      have hg := h.1
      unfold goodK at hg
      rw [bAnd_eq, Bool.and_eq_true, bAnd_eq, Bool.and_eq_true] at hg
      obtain ⟨hz, hrow, hbig⟩ := hg
      obtain ⟨hA, hB⟩ := rowK_sound CT g.2.1 g.2.2.1 hrow
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨g.1, g.2.2.1, g.2.2.2, ?_, hB, hA, ?_⟩)))
      · intro s hs
        obtain ⟨j, -, hj⟩ := zipAll_mem_right hz s hs
        rw [bAnd_eq, Bool.and_eq_true] at hj
        exact ⟨j, Nat.blt_eq.mp hj.1, (Nat.eq_of_beq_eq_true hj.2).symm⟩
      · intro hb
        subst hb
        change bAnd(allL g.2.2.1 fun a => allL g.2.2.1 fun b => memL (commK n a b) g.2.2.2,
          allL g.2.2.2 fun u => allL g.2.2.2 fun v => Nat.beq (pc n u v) (pc n v u)) = true at hbig
        rw [bAnd_eq, Bool.and_eq_true] at hbig
        refine ⟨fun a ha b hb => ?_, fun u hu v hv => ?_⟩
        · exact (CFSG.KC.BalanceSC.SylowEq.memL_iff _ _).1
            (allL_iff.1 (allL_iff.1 hbig.1 a ha) b hb)
        · exact Nat.eq_of_beq_eq_true (allL_iff.1 (allL_iff.1 hbig.2 u hu) v hv)

theorem fcrK_sound {e S HB NH : ℕ} {big : Bool} {BN CT : List ℕ} {RR : List (List ℕ)}
    {GD : List (List ℕ × List ℕ × List ℕ × List ℕ)} (h : fcrK n e S HB NH big BN CT RR GD = true) :
    ∀ x ∈ CT, pw n e x 8 ≠ e ∨ x = e ∨ x = S ∨
      (∃ cs : List ℕ, (∀ c ∈ cs, c ≤ NH) ∧ badK n e (prodK n e S HB x cs) = true) ∨
      ∃ Sl Gl Kl : List ℕ, (∀ s ∈ Sl, ∃ j < NH, s = cjK n HB x j) ∧ (∀ a ∈ Gl, a ∈ CT) ∧
        (∀ g ∈ CT, (∃ t ∈ Sl, ∀ b ∈ BN, pc n g t ≠ pc n (pc n b t) g) ∨
          (big = false ∧ pw n e g 8 = e) ∨ (big = true ∧ g ∈ Gl)) ∧
        (big = true → (∀ a ∈ Gl, ∀ b ∈ Gl, commK n a b ∈ Kl) ∧
          ∀ u ∈ Kl, ∀ v ∈ Kl, pc n u v = pc n v u) :=
  fcrF_sound (n := n) CT RR GD h

theorem fco2K_sound {e HB NH : ℕ} {big : Bool} {FO : List ℕ} (h : fco2K n e HB NH big FO = true) :
    ∃ i < NH, ∃ j < NH,
      (big = false ∧ pw n e (tab64 HB i) 3 = e ∧ pw n e (tab64 HB j) 3 = e ∧
        badK n e (pc n (tab64 HB i) (tab64 HB j)) = true) ∨
      (big = true ∧ ∃ k < NH, ∃ l < NH,
        badK n e (commK n (commK n (tab64 HB i) (tab64 HB j))
          (commK n (tab64 HB k) (tab64 HB l))) = true) := by
  rcases FO with _ | ⟨i, _ | ⟨j, r2⟩⟩
  · exact absurd h Bool.false_ne_true
  · exact absurd h Bool.false_ne_true
  change bAnd(Nat.blt i NH, bAnd(Nat.blt j NH,
    strictB (tab64 HB i) fun a => strictB (tab64 HB j) fun b =>
    List.rec (motive := fun _ => Bool)
      (bAnd(CFSG.KC.BalanceSC.notB big, bAnd(Nat.beq (pw n e a (nat_lit 3)) e,
        bAnd(Nat.beq (pw n e b (nat_lit 3)) e, badK n e (pc n a b)))))
      (fun k r3 _ => List.rec (motive := fun _ => Bool) false (fun l r4 _ =>
        bAnd(big, bAnd(emptyL r4, bAnd(Nat.blt k NH, bAnd(Nat.blt l NH,
          badK n e (commK n (commK n a b) (commK n (tab64 HB k) (tab64 HB l)))))))) r3) r2))
    = true at h
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, CFSG.KC.BalanceSC.SylowEq.strictB_eq,
    CFSG.KC.BalanceSC.SylowEq.strictB_eq] at h
  obtain ⟨hi, hj, h⟩ := h
  refine ⟨i, Nat.blt_eq.mp hi, j, Nat.blt_eq.mp hj, ?_⟩
  rcases r2 with _ | ⟨k, _ | ⟨l, r4⟩⟩
  · left
    change bAnd(CFSG.KC.BalanceSC.notB big, bAnd(Nat.beq (pw n e (tab64 HB i) (nat_lit 3)) e,
      bAnd(Nat.beq (pw n e (tab64 HB j) (nat_lit 3)) e,
        badK n e (pc n (tab64 HB i) (tab64 HB j))))) = true at h
    rw [bAnd_eq, bAnd_eq, bAnd_eq, notB_eq, Bool.and_eq_true, Bool.and_eq_true,
      Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨h.1, Nat.eq_of_beq_eq_true h.2.1, Nat.eq_of_beq_eq_true h.2.2.1, h.2.2.2⟩
  · exact absurd h Bool.false_ne_true
  · right
    change bAnd(big, bAnd(emptyL r4, bAnd(Nat.blt k NH, bAnd(Nat.blt l NH,
      badK n e (commK n (commK n (tab64 HB i) (tab64 HB j))
        (commK n (tab64 HB k) (tab64 HB l))))))) = true at h
    rw [bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true,
      Bool.and_eq_true, Bool.and_eq_true] at h
    exact ⟨h.1, k, Nat.blt_eq.mp h.2.2.1, l, Nat.blt_eq.mp h.2.2.2.1, h.2.2.2.2⟩

variable [NeZero n]

theorem pp_sig {S : ℕ} (hSp : permB n 4 S = true) (hn' : n ≤ 11) : PP n 4 S :=
  pp_of_permB (sz_of_le hn') hSp

theorem ct_facts (hn : 8 ≤ n) (hn' : n ≤ 11) {S : ℕ} {CT : List ℕ} (hSp : PP n 4 S)
    (hdS : dec n S = sig0 n) (hct : ctOK n S (cardC n) CT = true) :
    (∀ x ∈ CT, PP n 4 x ∧ dec n x ∈ centralizer ({sig0 n} : Set (Perm (Fin n)))) ∧
      ∀ σ ∈ centralizer ({sig0 n} : Set (Perm (Fin n))), ∃ x ∈ CT, PP n 4 x ∧ dec n x = σ := by
  classical
  obtain ⟨hinc, hmem, hlen⟩ := ctOK_sound hct
  have hin : ∀ x ∈ CT, PP n 4 x ∧ dec n x ∈ centralizer ({sig0 n} : Set (Perm (Fin n))) := by
    intro x hx
    obtain ⟨hp, hc⟩ := hmem x hx
    have hxp := pp_of_permB (sz_of_le hn') hp
    refine ⟨hxp, mem_centralizer_singleton_iff.2 ?_⟩
    have := congrArg (dec n) hc
    rw [dec_mul hSp hxp, dec_mul hxp hSp, hdS] at this
    exact this.symm
  refine ⟨hin, ?_⟩
  have hnd : (CT.map (dec n)).Nodup :=
    List.Nodup.map_on (fun a ha b hb e => dec_inj (hin a ha).1 (hin b hb).1 e)
      (hinc.imp fun h => ne_of_lt h)
  have hsp := sig0_spec n hn hn'
  have hcent : Nat.card (centralizer ({sig0 n} : Set (Perm (Fin n)))) = cardC n := by
    rw [card_centralizer_involution hsp.1 (k := 4) (by rw [hsp.2.1]) (by norm_num)]
    exact factorial_eq_cardC hn hn'
  have hcard : (Finset.univ.filter
      (fun g => g ∈ centralizer ({sig0 n} : Set (Perm (Fin n))))).card = cardC n := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact hcent
  have hsub : (CT.map (dec n)).toFinset ⊆ Finset.univ.filter
      (fun g => g ∈ centralizer ({sig0 n} : Set (Perm (Fin n)))) := by
    intro σ hσ
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hσ)
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (hin x hx).2⟩
  have heq := Finset.eq_of_subset_of_card_le hsub
    (by rw [hcard, List.toFinset_card_of_nodup hnd, List.length_map, hlen])
  intro σ hσ
  have : σ ∈ (CT.map (dec n)).toFinset := by
    rw [heq]
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hσ⟩
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 this)
  exact ⟨x, hx, (hin x hx).1, rfl⟩

theorem gens_facts (hn : 8 ≤ n) (hn' : n ≤ 11) {S : ℕ} {HG : List ℕ} (hSp : PP n 4 S)
    (hdS : dec n S = sig0 n) (hg : gensK n (pidn n 4) S HG = true) :
    ∀ g ∈ HG, PP n 4 g ∧ GenP (sig0 n) (dec n g) := by
  have hsz := sz_of_le (n := n) hn'
  intro g hgm
  obtain ⟨hp, hc, hcase⟩ := gensK_sound hg g hgm
  have hgp := pp_of_permB hsz hp
  have hcomm : dec n g * sig0 n = sig0 n * dec n g := by
    have := congrArg (dec n) hc
    rw [dec_mul hSp hgp, dec_mul hgp hSp, hdS] at this
    exact this.symm
  refine ⟨hgp, hcomm, ?_⟩
  rcases hcase with h3 | ⟨h2, hf, hf'⟩
  · have hσ3 : dec n g ^ 3 = 1 := pow_eq_one_of hsz hgp h3
    have hodd : Odd (orderOf (dec n g)) :=
      Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hσ3)
    refine ⟨?_, Or.inl hodd⟩
    have h3' : (sign (dec n g)) ^ 3 = 1 := by rw [← map_pow, hσ3, map_one]
    rcases Int.units_eq_one_or (sign (dec n g)) with h1 | h1
    · exact h1
    · rw [h1] at h3'
      exact absurd h3' (by decide)
  · have hsq : dec n g * dec n g = 1 := by rw [← dec_mul hgp hgp, h2, dec_id hsz]
    have hs8 : (dec n g).support.card = 8 := by
      have := fix_add_supp (dec n g)
      rw [← fixC_eq hgp, hf] at this
      omega
    have hs8' : (dec n g * sig0 n).support.card = 8 := by
      have := fix_add_supp (dec n g * sig0 n)
      rw [← hdS, ← dec_mul hgp hSp, ← fixC_eq (pp_pc hgp hSp), hf'] at this
      rw [← hdS, ← dec_mul hgp hSp]
      omega
    exact ⟨IsoI.sign_eq_one ⟨hsq, hs8⟩, Or.inr ⟨hsq, hs8, hs8'⟩⟩

theorem h_facts (hn : 8 ≤ n) (hn' : n ≤ 11) {S HB NH : ℕ} {HG : List ℕ} {HPL : List (ℕ × ℕ)}
    (hSp : PP n 4 S) (hdS : dec n S = sig0 n) (hh : hOK n (pidn n 4) HB NH HG HPL = true)
    (hg : gensK n (pidn n 4) S HG = true) :
    ∀ k < NH, PP n 4 (tab64 HB k) ∧ dec n (tab64 HB k) ∈ H0 (sig0 n) := by
  have hsz := sz_of_le (n := n) hn'
  obtain ⟨h0, hstep⟩ := hOK_sound hh
  have hG := gens_facts hn hn' hSp hdS hg
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · rw [h0]
      exact ⟨CFSG.KC.BfsPin.PP.id hsz, by rw [dec_id hsz]; exact one_mem _⟩
    · obtain ⟨par, hpar, g, hgm, he⟩ := hstep k hpos hk
      obtain ⟨hpp, hpm⟩ := ih par hpar (by omega)
      obtain ⟨hgp, hgP⟩ := hG g hgm
      rw [he]
      exact ⟨pp_pc hpp hgp, by
        rw [dec_mul hpp hgp]
        exact mul_mem hpm (Subgroup.subset_closure hgP)⟩

@[expose] def c11 : ℕ := 9523927724560

theorem pp_c11 : PP 11 4 c11 := pp_of_permB (sz_of_le (n := 11) le_rfl) (by decide +kernel)

theorem dec_c11 : dec 11 c11 = swapsPerm 11 [(8, 9), (9, 10)] := by
  refine Rep.unique (rep_dec pp_c11) ?_
  unfold AhatData.Rep
  decide +kernel

theorem bn_facts (hn' : n ≤ 11) {BN : List ℕ}
    (hBN : BN = if n = 11 then [pidn n 4, c11, pc 11 c11 c11] else [pidn n 4]) :
    (∀ b ∈ BN, PP n 4 b ∧ dec n b ∈ Bn n) ∧ ∀ β ∈ Bn n, ∃ b ∈ BN, PP n 4 b ∧ dec n b = β := by
  have hsz := sz_of_le (n := n) hn'
  by_cases h11 : n = 11
  · subst h11
    rw [if_pos rfl] at hBN
    subst hBN
    rw [Chk.Bn_eleven]
    have hpp2 : PP 11 4 (pc 11 c11 c11) := pp_pc pp_c11 pp_c11
    have hd2 : dec 11 (pc 11 c11 c11) = swapsPerm 11 [(8, 9), (9, 10)] ^ 2 := by
      rw [dec_mul pp_c11 pp_c11, dec_c11, sq]
    constructor
    · intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl
      · exact ⟨CFSG.KC.BfsPin.PP.id hsz, by rw [dec_id hsz]; exact one_mem _⟩
      · exact ⟨pp_c11, by rw [dec_c11]; exact mem_zpowers _⟩
      · exact ⟨hpp2, by rw [hd2]; exact pow_mem (mem_zpowers _) 2⟩
    · intro β hβ
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hβ
      have hord : orderOf (swapsPerm 11 [(8, 9), (9, 10)]) = 3 :=
        orderOf_eq_prime Chk.c0_pow_three Chk.c0_ne_one
      rw [← zpow_mod_orderOf, hord]
      have hk : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
      rcases hk with hk | hk | hk <;> rw [hk]
      · exact ⟨pidn 11 4, by simp, CFSG.KC.BfsPin.PP.id hsz, by rw [dec_id hsz]; simp⟩
      · exact ⟨c11, by simp, pp_c11, by rw [dec_c11]; simp⟩
      · refine ⟨pc 11 c11 c11, by simp, hpp2, ?_⟩
        rw [hd2]
        exact (zpow_natCast _ 2).symm
  · rw [if_neg h11] at hBN
    subst hBN
    rw [Chk.Bn_of_ne h11]
    constructor
    · intro b hb
      rw [List.mem_singleton] at hb
      subst hb
      exact ⟨CFSG.KC.BfsPin.PP.id hsz, by rw [dec_id hsz]; exact one_mem _⟩
    · intro β hβ
      rw [Subgroup.mem_bot] at hβ
      subst hβ
      exact ⟨pidn n 4, List.mem_singleton_self _, CFSG.KC.BfsPin.PP.id hsz, dec_id hsz⟩

@[expose] noncomputable def prodF (n S HB x : ℕ) (cs : List ℕ) (acc : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
    (fun c _ ih acc => strictN (pc n acc (elK n S HB x c)) ih) cs acc

omit [NeZero n] in
theorem prodK_eq (e S HB x : ℕ) (cs : List ℕ) : prodK n e S HB x cs = prodF n S HB x cs e := rfl

omit [NeZero n] in
theorem prodF_cons (S HB x c acc : ℕ) (cs : List ℕ) :
    prodF n S HB x (c :: cs) acc = prodF n S HB x cs (pc n acc (elK n S HB x c)) :=
  strictN_eq _ _

theorem prodK_mem (hn' : n ≤ 11) {S HB NH x : ℕ} (hSp : PP n 4 S) (hdS : dec n S = sig0 n)
    (hH : ∀ k < NH, PP n 4 (tab64 HB k) ∧ dec n (tab64 HB k) ∈ H0 (sig0 n)) (hx : PP n 4 x) :
    ∀ (cs : List ℕ) (acc : ℕ), (∀ c ∈ cs, c ≤ NH) → PP n 4 acc →
      dec n acc ∈ Subgroup.closure (conjSet (H0 (sig0 n)) (dec n x) ∪ {sig0 n}) →
      PP n 4 (prodF n S HB x cs acc) ∧
        dec n (prodF n S HB x cs acc) ∈
          Subgroup.closure (conjSet (H0 (sig0 n)) (dec n x) ∪ {sig0 n})
  | [], acc, _, hp, hm => ⟨hp, hm⟩
  | c :: cs, acc, hc, hp, hm => by
    rw [prodF_cons]
    have hel : PP n 4 (elK n S HB x c) ∧ dec n (elK n S HB x c) ∈
        Subgroup.closure (conjSet (H0 (sig0 n)) (dec n x) ∪ {sig0 n}) := by
      rcases c with _ | j
      · exact ⟨hSp, Subgroup.subset_closure (Or.inr (Set.mem_singleton_iff.2 hdS))⟩
      · have hj : j < NH := by have := hc (j + 1) List.mem_cons_self; omega
        obtain ⟨hpp, hdc⟩ := dec_cjK (HB := HB) (j := j) hx (hH j hj).1
        refine ⟨hpp, Subgroup.subset_closure (Or.inl ⟨_, (hH j hj).2, ?_⟩)⟩
        exact hdc
    exact prodK_mem hn' hSp hdS hH hx cs _ (fun c' hc' => hc c' (List.mem_cons_of_mem _ hc'))
      (pp_pc hp hel.1) (by rw [dec_mul hp hel.1]; exact mul_mem hm hel.2)

theorem fcAll_of_checks {n : ℕ} [NeZero n] (hn : 8 ≤ n) (hn' : n ≤ 11) {E S HB NH : ℕ}
    {CT HG BN FO : List ℕ} {HPL : List (ℕ × ℕ)} {RR RB : List (List ℕ)}
    {GD : List (List ℕ × List ℕ × List ℕ × List ℕ)} {big : Bool}
    (hE : E = pidn n 4) (hS : unpack n 4 S = sigA n) (hSp : permB n 4 S = true)
    (hbig : big = (n == 11))
    (hBN : BN = if n = 11 then [E, c11, pc 11 c11 c11] else [E])
    (hct : ctOK n S (cardC n) CT = true) (hh : hOK n E HB NH HG HPL = true)
    (hg : gensK n E S HG = true) (hb : fcbK n E HB NH BN CT RB = true)
    (hr : fcrK n E S HB NH big BN CT RR GD = true) (ho : fco2K n E HB NH big FO = true) :
    FCAll n := by
  subst hE
  have hsz := sz_of_le (n := n) hn'
  have hSp' := pp_sig hSp hn'
  have hdS : dec n S = sig0 n := Rep.unique (rep_dec hSp') (by rw [hS]; exact rep_sigA n hn)
  obtain ⟨hCin, hC⟩ := ct_facts hn hn' hSp' hdS hct
  have hH := h_facts hn hn' hSp' hdS hh hg
  obtain ⟨hBs, hBc⟩ := bn_facts hn' hBN
  have hid : PP n 4 (pidn n 4) := CFSG.KC.BfsPin.PP.id hsz
  refine ⟨fc2_of_le hn' _, ?_, ?_, ?_⟩
  ·
    intro x hx hx8 hxσ
    obtain ⟨xp, hxCT, hxp, rfl⟩ := hC x hx
    rcases fcrK_sound hr xp hxCT with h8 | h1 | hS1 | ⟨cs, hcs, hbad⟩ |
      ⟨Sl, Gl, Kl, hSl, -, hrow, hbigf⟩
    · exact absurd hx8 (pow_ne_one_of hsz hxp h8)
    · exact absurd (by rw [h1, dec_id hsz]; exact one_mem _) hxσ
    · exact absurd (by rw [hS1, hdS]; exact mem_zpowers _) hxσ
    · left
      obtain ⟨hpp, hmem⟩ := prodK_mem hn' hSp' hdS hH hxp cs (pidn n 4) hcs hid
        (by rw [dec_id hsz]; exact one_mem _)
      rw [prodK_eq] at hbad
      exact ⟨_, hmem, badK_sound hsz hpp hbad⟩
    · right
      have hSlp : ∀ s ∈ Sl, PP n 4 s ∧ dec n s ∈ conjSet (H0 (sig0 n)) (dec n xp) := by
        intro s hs
        obtain ⟨j, hj, rfl⟩ := hSl s hs
        obtain ⟨hpp, hdc⟩ := dec_cjK (HB := HB) (j := j) hxp (hH j hj).1
        exact ⟨hpp, _, (hH j hj).2, hdc⟩
      refine ⟨{t | ∃ s ∈ Sl, dec n s = t}, ?_, ?_⟩
      · rintro t ⟨s, hs, rfl⟩
        exact (hSlp s hs).2
      have hΓ : ∀ g ∈ centralizer ({sig0 n} : Set (Perm (Fin n))),
          (∀ t ∈ {t | ∃ s ∈ Sl, dec n s = t}, ⁅g, t⁆ ∈ Bn n) →
          ∃ gp ∈ CT, PP n 4 gp ∧ dec n gp = g ∧
            ((big = false ∧ pw n (pidn n 4) gp 8 = pidn n 4) ∨ (big = true ∧ gp ∈ Gl)) := by
        intro g hg hgt
        obtain ⟨gp, hgCT, hgp, rfl⟩ := hC g hg
        refine ⟨gp, hgCT, hgp, rfl, ?_⟩
        rcases hrow gp hgCT with ⟨t, ht, hne⟩ | h2 | h3
        · exfalso
          obtain ⟨htp, -⟩ := hSlp t ht
          obtain ⟨b, hbB, hbp, hbd⟩ := hBc _ (hgt _ ⟨t, ht, rfl⟩)
          apply hne b hbB
          refine dec_inj (pp_pc hgp htp) (pp_pc (pp_pc hbp htp) hgp) ?_
          rw [dec_mul hgp htp, dec_mul (pp_pc hbp htp) hgp, dec_mul hbp htp, hbd,
            commutatorElement_def]
          group
        · exact Or.inl h2
        · exact Or.inr h3
      by_cases h10 : n ≤ 10
      · have hbf : big = false := by rw [hbig]; simp; omega
        left
        refine ⟨h10, fun g hg => ?_⟩
        obtain ⟨gp, -, hgp, rfl, hcase⟩ := hΓ g hg.1 hg.2
        rcases hcase with ⟨-, h8⟩ | ⟨hbt, -⟩
        · exact pow_eq_one_of hsz hgp h8
        · rw [hbf] at hbt
          exact absurd hbt (by decide)
      · have h11 : n = 11 := by omega
        have hbt : big = true := by rw [hbig, h11]; rfl
        right
        obtain ⟨hK1, hK2⟩ := hbigf hbt
        have hin : ∀ g ∈ {g | g ∈ centralizer ({sig0 n} : Set (Perm (Fin n))) ∧
            ∀ t ∈ {t | ∃ s ∈ Sl, dec n s = t}, ⁅g, t⁆ ∈ Bn n},
            ∃ gp ∈ Gl, PP n 4 gp ∧ dec n gp = g := by
          intro g hg
          obtain ⟨gp, -, hgp, rfl, hcase⟩ := hΓ g hg.1 hg.2
          rcases hcase with ⟨hbf, -⟩ | ⟨-, hgl⟩
          · rw [hbt] at hbf
            exact absurd hbf (by decide)
          · exact ⟨gp, hgl, hgp, rfl⟩
        refine ⟨h11, fun a ha b hb c hc d hd => ?_⟩
        obtain ⟨ap, hap, happ, rfl⟩ := hin a ha
        obtain ⟨bp, hbp, hbpp, rfl⟩ := hin b hb
        obtain ⟨cp, hcp, hcpp, rfl⟩ := hin c hc
        obtain ⟨dp, hdp, hdpp, rfl⟩ := hin d hd
        obtain ⟨hu, hud⟩ := dec_commK happ hbpp
        obtain ⟨hv, hvd⟩ := dec_commK hcpp hdpp
        have e := hK2 _ (hK1 ap hap bp hbp) _ (hK1 cp hcp dp hdp)
        have e' := congrArg (dec n) e
        rw [dec_mul hu hv, dec_mul hv hu, hud, hvd] at e'
        exact commutatorElement_eq_one_iff_mul_comm.2 e'
  ·
    intro b hbm hodd hbn
    obtain ⟨xp, hxCT, hxp, rfl⟩ := hC b hbm
    rcases fcbK_sound hb xp hxCT with ⟨m, h1, h2⟩ | hbB | ⟨j, hj, m, h1, h2⟩
    · exact absurd (even_of (pow_ne_one_of hsz hxp h1) (pow_eq_one_of hsz hxp h2))
        (Nat.not_even_iff_odd.2 hodd)
    · exact absurd (hBs xp hbB).2 hbn
    · obtain ⟨hcp, hcd⟩ := dec_cjK (HB := HB) (j := j) hxp (hH j hj).1
      have hwp := pp_pc hxp hcp
      refine ⟨dec n (tab64 HB j), (hH j hj).2, ?_⟩
      have := even_of (pow_ne_one_of hsz hwp h1) (pow_eq_one_of hsz hwp h2)
      rwa [dec_mul hxp hcp, hcd] at this
  ·
    obtain ⟨i, hi, j, hj, hcase⟩ := fco2K_sound ho
    obtain ⟨hip, him⟩ := hH i hi
    obtain ⟨hjp, hjm⟩ := hH j hj
    rcases hcase with ⟨hbf, hi3, hj3, hbad⟩ | ⟨hbt, k, hk, l, hl, hbad⟩
    · have h10 : n ≤ 10 := by
        by_contra h
        have : n = 11 := by omega
        rw [hbig, this] at hbf
        exact absurd hbf (by decide)
      have hoi : Odd (orderOf (dec n (tab64 HB i))) := Odd.of_dvd_nat (by decide : Odd 3)
        (orderOf_dvd_of_pow_eq_one (pow_eq_one_of hsz hip hi3))
      have hoj : Odd (orderOf (dec n (tab64 HB j))) := Odd.of_dvd_nat (by decide : Odd 3)
        (orderOf_dvd_of_pow_eq_one (pow_eq_one_of hsz hjp hj3))
      have hpp := pp_pc hip hjp
      refine ⟨_, ?_, badK_sound hsz hpp hbad⟩
      rw [dec_mul hip hjp]
      simp only [Wn, h10, ↓reduceIte]
      exact mul_mem (subset_closure ⟨him, hoi⟩) (subset_closure ⟨hjm, hoj⟩)
    · have h10 : ¬ n ≤ 10 := by
        intro h
        have : (n == 11) = false := by simp; omega
        rw [hbig, this] at hbt
        exact absurd hbt (by decide)
      obtain ⟨hkp, hkm⟩ := hH k hk
      obtain ⟨hlp, hlm⟩ := hH l hl
      obtain ⟨hu, hud⟩ := dec_commK hip hjp
      obtain ⟨hv, hvd⟩ := dec_commK hkp hlp
      obtain ⟨hw, hwd⟩ := dec_commK hu hv
      refine ⟨_, ?_, badK_sound hsz hw hbad⟩
      rw [hwd, hud, hvd]
      simp only [Wn, h10, ↓reduceIte]
      exact Subgroup.commutator_mem_commutator (Subgroup.commutator_mem_commutator him hjm)
        (Subgroup.commutator_mem_commutator hkm hlm)

end CFSG.KC.Sol5Q

end
