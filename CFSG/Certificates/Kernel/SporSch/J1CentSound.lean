module

public import Certificates.Data.Kernel.SporSch.J1Cent
public import CFSG.Certificates.Kernel.SporSch.ChainIdxSound
public import CFSG.Certificates.Kernel.SporSch.KeyBfsSound
public import CFSG.Certificates.Kernel.SporSch.TblSound

public section

namespace CFSG.KS.SporSch.J1C

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.SporSch.MOC CFSG.KS.SporSch.CIdx
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Certificates
open CFSG.Sporadic.Schreier CFSG.KS.KeyBfs

theorem lexLtK_iff {a b c d : Nat} : lexLtK a b c d = true ↔ KeyBfs.LexLt a b c d := by
  unfold lexLtK KeyBfs.LexLt
  by_cases h : a < c
  · have : Nat.blt a c = true := by rw [Nat.blt_eq]; exact h
    rw [this]
    simp [h]
  · have : Nat.blt a c = false := Bool.eq_false_iff.2 fun e => h (by rw [Nat.blt_eq] at e; exact e)
    rw [this]
    change Bool.rec (motive := fun _ => Bool) false (Nat.blt b d) (Nat.beq a c) = true ↔ _
    rw [bAnd_iff', Nat.beq_eq, Nat.blt_eq]
    omega

theorem bIf_eq (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by cases c <;> rfl

theorem blt_iff {a b : Nat} : Nat.blt a b = true ↔ a < b := by rw [Nat.blt_eq]

theorem beq_iff {a b : Nat} : Nat.beq a b = true ↔ a = b := by rw [Nat.beq_eq]

section Chain

variable {n w kS kO nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
  {base : Array Nat} {D : List (List Int)}
  (hQ : ChainCK n w PS PSI LR TR TRI kS kO nb BP S base D)
include hQ

theorem acts_elJ (j : Nat) :
    Acts n (elJ n w (mask w) (n * w) nb LR TR j) (el n S base nb j) := fun y =>
  apL_elemT hQ j y

structure BfsFacts (n : Nat) (S : Array (Array Nat)) (base : Array Nat) (nb N : Nat)
    (σ : Nat → Equiv.Perm (Fin n) → Equiv.Perm (Fin n)) (ng c : Nat) (J PA LB POS : Nat → Nat) :
    Prop where
  c_pos : 0 < c
  lt : ∀ k < c, J k < N
  inj : ∀ a < c, ∀ b < c, J a = J b → a = b
  tree : ∀ k, 0 < k → k < c → PA k < k ∧ LB k < ng ∧ POS (PA k * ng + LB k) = k
  order : ∀ k, 0 < k → k + 1 < c → KeyBfs.LexLt (PA k) (LB k) (PA (k + 1)) (LB (k + 1))
  close : ∀ k < c, ∀ l < ng, POS (k * ng + l) < c ∧
    el n S base nb (J (POS (k * ng + l))) = σ l (el n S base nb (J k)) ∧
    (POS (k * ng + l) = 0 ∨ ¬ KeyBfs.LexLt k l (PA (POS (k * ng + l))) (LB (POS (k * ng + l))))
  par_zero : PA 0 = 0
  lab_zero : LB 0 = 0

omit hQ in
theorem sort_inj {c : Nat} {J SRT SRI : Nat → Nat}
    (h : ∀ k < c, SRT k < c ∧ SRI (SRT k) = k ∧ (k + 1 < c → J (SRT k) < J (SRT (k + 1)))) :
    ∀ a < c, ∀ b < c, J a = J b → a = b := by
  have hmono : ∀ k k', k < k' → k' < c → J (SRT k) < J (SRT k') := by
    intro k k' hk hk'
    induction k' with
    | zero => omega
    | succ k' ih =>
      rcases Nat.lt_or_ge k k' with h1 | h1
      · exact (ih h1 (by omega)).trans ((h k' (by omega)).2.2 hk')
      · obtain rfl : k = k' := by omega
        exact (h k (by omega)).2.2 hk'
  have hinj : ∀ k < c, ∀ k' < c, J (SRT k) = J (SRT k') → k = k' := by
    intro k hk k' hk' e
    rcases Nat.lt_trichotomy k k' with h1 | h1 | h1
    · exact absurd e (Nat.ne_of_lt (hmono k k' h1 hk'))
    · exact h1
    · exact absurd e.symm (Nat.ne_of_lt (hmono k' k h1 hk))
  have hsurj : ∀ a < c, ∃ k < c, SRT k = a := by
    intro a ha
    have hi : Set.InjOn SRT (Set.Iio c) := fun x hx y hy e => by
      have := congrArg SRI e
      rw [(h x hx).2.1, (h y hy).2.1] at this
      exact this
    have hm : Set.MapsTo SRT (Set.Iio c) (Set.Iio c) := fun x hx => (h x hx).1
    have hs := Finset.surjOn_of_injOn_of_card_le (s := Finset.range c) (t := Finset.range c) SRT
      (fun x hx => Finset.mem_range.2 (hm (Finset.mem_range.1 hx)))
      (fun x hx y hy e => hi (Finset.mem_range.1 hx) (Finset.mem_range.1 hy) e) le_rfl
      (Finset.mem_coe.2 (Finset.mem_range.2 ha))
    obtain ⟨k, hk, e⟩ := hs
    exact ⟨k, Finset.mem_range.1 hk, e⟩
  intro a ha b hb e
  obtain ⟨k, hk, rfl⟩ := hsurj a ha
  obtain ⟨k', hk', rfl⟩ := hsurj b hb
  rw [hinj k hk k' hk' e]

theorem bfs_facts {N c cap jR ng : Nat} {stp : Nat → (Nat → Nat) → Nat → Nat}
    {σ : Nat → Equiv.Perm (Fin n) → Equiv.Perm (Fin n)} {J PA LB POS SRT SRI : Nat → Nat}
    (hN : N = ordK LR nb)
    (hstp : ∀ l < ng, ∀ f g, Acts n f g → g ∈ Gen n S kO →
      Acts n (stp l f) (σ l g) ∧ σ l g ∈ Gen n S kO)
    (hh : bfsHdK c cap jR J PA LB = true)
    (hp : ∀ k < c, bfsPtK n w (mask w) (n * w) BP nb N LR TR stp ng c J PA LB POS SRT SRI k =
      true) :
    BfsFacts n S base nb N σ ng c J PA LB POS ∧ c ≤ cap ∧ J 0 = jR := by
  unfold bfsHdK at hh
  simp only [bAnd_iff', blt_iff, beq_iff, Nat.ble_eq] at hh
  obtain ⟨hc, hcap, hJ0, hP0, hL0⟩ := hh
  have hpt : ∀ k < c, J k < N ∧
      (k = 0 ∨ (PA k < k ∧ LB k < ng ∧ POS (PA k * ng + LB k) = k ∧
        (k + 1 < c → KeyBfs.LexLt (PA k) (LB k) (PA (k + 1)) (LB (k + 1))))) ∧
      (∀ l < ng, POS (k * ng + l) < c ∧
        eqB w (mask w) BP nb (elJ n w (mask w) (n * w) nb LR TR (J (POS (k * ng + l))))
          (stp l (elJ n w (mask w) (n * w) nb LR TR (J k))) = true ∧
        (POS (k * ng + l) = 0 ∨ ¬ KeyBfs.LexLt k l (PA (POS (k * ng + l))) (LB (POS (k * ng + l))))) ∧
      (SRT k < c ∧ SRI (SRT k) = k ∧ (k + 1 < c → J (SRT k) < J (SRT (k + 1)))) := by
    intro k hk
    have h := hp k hk
    unfold bfsPtK at h
    simp only [Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h
    rw [bAnd_iff', bAnd_iff', bAnd_iff', blt_iff, CIdx.strictB_eq, bAnd_iff', bAnd_iff', blt_iff,
      beq_iff] at h
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    refine ⟨h1, ?_, fun l hl => ?_, h4, h5, fun hk1 => ?_⟩
    · rw [bIf_eq] at h2
      by_cases hk0 : k = 0
      · exact Or.inl hk0
      · have : Nat.beq k 0 = false := Bool.eq_false_iff.2 fun e => hk0 (beq_iff.1 e)
        rw [this] at h2
        simp only [Bool.false_eq_true, ite_false] at h2
        rw [bAnd_iff', bAnd_iff', bAnd_iff', blt_iff, blt_iff, beq_iff, bIf_eq] at h2
        obtain ⟨a1, a2, a3, a4⟩ := h2
        refine Or.inr ⟨a1, a2, a3, fun hk1 => ?_⟩
        have hk1' : Nat.blt (Nat.succ k) c = true := blt_iff.2 hk1
        rw [hk1'] at a4
        exact lexLtK_iff.1 (by simpa using a4)
    · have := allN_iff.1 h3 l hl
      rw [CIdx.strictB_eq, bAnd_iff', bAnd_iff', blt_iff, bIf_eq, bIf_eq] at this
      obtain ⟨b1, b2, b3⟩ := this
      refine ⟨b1, b2, ?_⟩
      by_cases hq0 : POS (k * ng + l) = 0
      · exact Or.inl hq0
      · right
        have : Nat.beq (POS (k * ng + l)) 0 = false :=
          Bool.eq_false_iff.2 fun e => hq0 (beq_iff.1 e)
        rw [this] at b3
        simp only [Bool.false_eq_true, ite_false] at b3
        intro hl'
        rw [lexLtK_iff.2 hl'] at b3
        simp at b3
    · rw [bIf_eq] at h6
      have hk1' : Nat.blt (Nat.succ k) c = true := blt_iff.2 hk1
      rw [hk1'] at h6
      simpa [blt_iff] using h6
  have hmem : ∀ k < c, el n S base nb (J k) ∈ Gen n S kO := fun k hk =>
    el_mem hQ (hN ▸ (hpt k hk).1)
  refine ⟨⟨hc, fun k hk => (hpt k hk).1, ?_, fun k hk0 hk => ?_, fun k hk0 hk1 => ?_,
    fun k hk l hl => ?_, hP0, hL0⟩, hcap, hJ0⟩
  · intro a ha b hb e
    exact sort_inj (fun k hk => (hpt k hk).2.2.2) a ha b hb e
  · rcases (hpt k hk).2.1 with h0 | ⟨a1, a2, a3, -⟩
    · omega
    · exact ⟨a1, a2, a3⟩
  · rcases (hpt k (by omega)).2.1 with h0 | ⟨-, -, -, a4⟩
    · omega
    · exact a4 hk1
  · obtain ⟨b1, b2, b3⟩ := (hpt k hk).2.2.1 l hl
    obtain ⟨hs, hsm⟩ := hstp l hl _ _ (acts_elJ hQ (J k)) (hmem k hk)
    exact ⟨b1, (eqB_iff_eq hQ (acts_elJ hQ _) hs (hmem _ b1) hsm).1 b2, b3⟩

theorem replay_of_bfs {N ng c : Nat} {σ : Nat → Equiv.Perm (Fin n) → Equiv.Perm (Fin n)}
    {J PA LB POS : Nat → Nat} (F : BfsFacts n S base nb N σ ng c J PA LB POS)
    (hN : N = ordK LR nb) {st : Nat → CFSG.Sporadic.Th.Native.Table →
      CFSG.Sporadic.Th.Native.Table}
    (hst : ∀ l < ng, ∀ k < c,
      st l (toTable (el n S base nb (J k))) = toTable (σ l (el n S base nb (J k)))) :
    KReplay n st ng (toTable (el n S base nb (J 0))) c (fun k => toTable (el n S base nb (J k)))
      PA LB (fun h l => POS (h * ng + l)) := by
  have hn : n < 2 ^ 32 := by have := n_lt hQ; omega
  have hrep : ∀ g : Equiv.Perm (Fin n), CFSG.Sporadic.Th.Rep n (toTable g) g := rep_toTable hn
  refine ⟨F.c_pos, rfl, F.par_zero, F.lab_zero, fun a ha b hb e => ?_, fun k hk0 hk => ?_,
    F.order, fun h hh l hl => ?_⟩
  · have := CFSG.KS.Tbl.key_inj (hrep _) (hrep _) e
    exact F.inj a ha b hb (el_inj hQ (hN ▸ F.lt a ha) (hN ▸ F.lt b hb) this)
  · obtain ⟨a1, a2, a3⟩ := F.tree k hk0 hk
    refine ⟨a1, a2, ?_⟩
    obtain ⟨-, b2, -⟩ := F.close (PA k) (by omega) (LB k) a2
    rw [a3] at b2
    rw [hst _ a2 _ (by omega), b2]
  · obtain ⟨b1, b2, b3⟩ := F.close h hh l hl
    exact ⟨b1, by rw [hst l hl h hh, b2], b3⟩

omit hQ in
theorem prod_facts {N ng c : Nat} {d : Nat → Equiv.Perm (Fin n)} {J PA LB POS PT INV : Nat → Nat}
    (F : BfsFacts n S base nb N (fun l g => g * d l) ng c J PA LB POS)
    (h1 : el n S base nb (J 0) = 1)
    (hp : ∀ a < c, prodPtK ng c PA LB POS PT INV a = true) :
    ∀ a < c, (∀ b < c, PT (a * c + b) < c ∧
      el n S base nb (J (PT (a * c + b))) = el n S base nb (J a) * el n S base nb (J b)) ∧
      INV a < c ∧ el n S base nb (J a) * el n S base nb (J (INV a)) = 1 := by
  intro a ha
  have h := hp a ha
  unfold prodPtK at h
  simp only [Nat.add_eq, Nat.mul_eq] at h
  rw [bAnd_iff', bAnd_iff', blt_iff, beq_iff] at h
  obtain ⟨hall, hi1, hi2⟩ := h
  have hb : ∀ b < c, PT (a * c + b) < c ∧ (b = 0 → PT (a * c + b) = a) ∧
      (0 < b → PT (a * c + b) = POS (PT (a * c + PA b) * ng + LB b)) := by
    intro b hbc
    have := allN_iff.1 hall b hbc
    rw [CIdx.strictB_eq, bAnd_iff', blt_iff, bIf_eq] at this
    obtain ⟨h1', h2'⟩ := this
    refine ⟨h1', fun hb0 => ?_, fun hb0 => ?_⟩
    · subst hb0
      simpa [beq_iff] using h2'
    · have : Nat.beq b 0 = false := Bool.eq_false_iff.2 fun e => by
        rw [beq_iff] at e
        omega
      rw [this] at h2'
      simpa [beq_iff] using h2'
  have key : ∀ b < c, PT (a * c + b) < c ∧
      el n S base nb (J (PT (a * c + b))) = el n S base nb (J a) * el n S base nb (J b) := by
    intro b
    induction b using Nat.strong_induction_on with
    | _ b ih =>
      intro hbc
      refine ⟨(hb b hbc).1, ?_⟩
      rcases Nat.eq_zero_or_pos b with rfl | hb0
      · rw [(hb 0 hbc).2.1 rfl, h1, mul_one]
      · obtain ⟨t1, t2, t3⟩ := F.tree b hb0 hbc
        obtain ⟨ih1, ih2⟩ := ih (PA b) t1 (by omega)
        obtain ⟨-, c2, -⟩ := F.close _ ih1 (LB b) t2
        obtain ⟨-, c2', -⟩ := F.close (PA b) (by omega) (LB b) t2
        rw [t3] at c2'
        rw [(hb b hbc).2.2 hb0, c2, ih2, c2', mul_assoc]
  refine ⟨key, hi1, ?_⟩
  have := (key (INV a) hi1).2
  rw [hi2, h1] at this
  exact this.symm

theorem cent_facts {N mo cK : Nat} {R : List Nat} {r : Equiv.Perm (Fin n)}
    {K W1 W2 W3 W4 : Nat → Nat} (hN : N = ordK LR nb) (hR : Acts n (apL w (mask w) R) r)
    (hr : r ∈ Gen n S kO)
    (hp : ∀ k < cK, centPtK n w (mask w) (n * w) BP nb N mo LR TR R K W1 W2 W3 W4 cK k = true) :
    (∀ k < cK, K k < N ∧ el n S base nb (K k) * r = r * el n S base nb (K k)) ∧
    (∀ k < cK, ∀ k' < cK, K k = K k' → k = k') ∧
    ∀ k < cK, el n S base nb (K k) = 1 ∨ el n S base nb (K k) ^ mo ≠ 1 ∨
      (∃ h < cK, (el n S base nb (K k) * el n S base nb (K h) * el n S base nb (K k) *
        (el n S base nb (K h))⁻¹) ^ mo ≠ 1) ∨
      ∃ h < cK, ∃ h2 < cK, (el n S base nb (K k) * el n S base nb (K h) * el n S base nb (K k) *
        (el n S base nb (K h))⁻¹ * el n S base nb (K h2) * el n S base nb (K k) *
          (el n S base nb (K h2))⁻¹) ^ mo ≠ 1 := by
  set e := fun k => el n S base nb (K k)
  have hpt : ∀ k < cK, K k < N ∧ (k + 1 < cK → K k < K (k + 1)) ∧
      eqB w (mask w) BP nb (fun x => apL w (mask w) R (elK n w (mask w) (n * w) nb LR TR K k x))
        (fun x => elK n w (mask w) (n * w) nb LR TR K k (apL w (mask w) R x)) = true ∧
      oddPtK w (mask w) BP nb mo cK (elK n w (mask w) (n * w) nb LR TR K) W1 W2 W3 W4 k = true := by
    intro k hk
    have h := hp k hk
    unfold centPtK at h
    rw [show Nat.blt k cK = true from blt_iff.2 hk] at h
    change Bool.rec (motive := fun _ => Bool) false _ (Nat.blt (K k) N) = true at h
    rw [bAnd_iff', bAnd_iff', bAnd_iff', blt_iff, bIf_eq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨h1, fun hk1 => ?_, h3, h4⟩
    rw [show Nat.blt (Nat.succ k) cK = true from blt_iff.2 hk1] at h2
    simpa [blt_iff] using h2
  have hmem : ∀ k < cK, e k ∈ Gen n S kO := fun k hk => el_mem hQ (hN ▸ (hpt k hk).1)
  have hact : ∀ k, Acts n (elK n w (mask w) (n * w) nb LR TR K k) (e k) := fun k y =>
    apL_elemT hQ (K k) y
  have actM : ∀ {f f' : Nat → Nat} {g g' : Equiv.Perm (Fin n)}, Acts n f g → Acts n f' g' →
      Acts n (fun x => f (f' x)) (g * g') := fun hf hf' y => by
    simp only [Equiv.Perm.mul_apply, hf' y]
    exact hf _
  have hmono : ∀ k k', k < k' → k' < cK → K k < K k' := by
    intro k k' hk hk'
    induction k' with
    | zero => omega
    | succ k' ih =>
      rcases Nat.lt_or_ge k k' with h1 | h1
      · exact (ih h1 (by omega)).trans ((hpt k' (by omega)).2.1 hk')
      · obtain rfl : k = k' := by omega
        exact (hpt k (by omega)).2.1 hk'
  refine ⟨fun k hk => ⟨(hpt k hk).1, ?_⟩, fun k hk k' hk' e' => ?_, fun k hk => ?_⟩
  · have := (eqB_iff_eq hQ (actM hR (hact k)) (actM (hact k) hR)
      (Subgroup.mul_mem _ hr (hmem k hk)) (Subgroup.mul_mem _ (hmem k hk) hr)).1 (hpt k hk).2.2.1
    exact this.symm
  · rcases Nat.lt_trichotomy k k' with h1 | h1 | h1
    · exact absurd e' (Nat.ne_of_lt (hmono k k' h1 hk'))
    · exact h1
    · exact absurd e'.symm (Nat.ne_of_lt (hmono k' k h1 hk))
  · have ho := (hpt k hk).2.2.2
    have hfix : ∀ {f : Nat → Nat} {g : Equiv.Perm (Fin n)}, Acts n f g → g ∈ Gen n S kO →
        (fixB w (mask w) BP nb f = true ↔ g = 1) := fun hf hg => fixB_iff_eq_one hQ hf hg
    have hmov : ∀ {f : Nat → Nat} {g : Equiv.Perm (Fin n)}, Acts n f g → g ∈ Gen n S kO →
        movB w (mask w) BP nb mo f = true → g ^ mo ≠ 1 := fun hf hg h => by
      unfold movB at h
      rw [bIf_eq] at h
      intro e1
      have := (hfix (acts_itF hf mo) (Subgroup.pow_mem _ hg mo)).2 e1
      rw [this] at h
      simp at h
    unfold oddPtK at ho
    rw [bIf_eq] at ho
    by_cases h1 : fixB w (mask w) BP nb (elK n w (mask w) (n * w) nb LR TR K k) = true
    · exact Or.inl ((hfix (hact k) (hmem k hk)).1 h1)
    rw [ite_eq_right h1, bIf_eq] at ho
    by_cases h2 : fixB w (mask w) BP nb (itF (elK n w (mask w) (n * w) nb LR TR K k) mo) = true
    swap
    · refine Or.inr (Or.inl fun e1 => h2 ?_)
      exact (hfix (acts_itF (hact k) mo) (Subgroup.pow_mem _ (hmem k hk) mo)).2 e1
    rw [ite_eq_left h2, CIdx.strictB_eq, CIdx.strictB_eq] at ho
    simp only [bAnd_iff', blt_iff] at ho
    obtain ⟨hw1, hh, hhi, hinv, ho⟩ := ho
    have hiv : e (Nat.pred (W1 k)) * e (W2 k) = 1 :=
      (hfix (actM (hact _) (hact _)) (Subgroup.mul_mem _ (hmem _ hh) (hmem _ hhi))).1 hinv
    have hhi' : e (W2 k) = (e (Nat.pred (W1 k)))⁻¹ := eq_inv_of_mul_eq_one_right hiv
    rw [bIf_eq] at ho
    by_cases h3 : Nat.beq (W3 k) 0 = true
    · rw [ite_eq_left h3] at ho
      refine Or.inr (Or.inr (Or.inl ⟨Nat.pred (W1 k), hh, ?_⟩))
      have hm := hmov (actM (hact k) (actM (hact _) (actM (hact k) (hact _))))
        (Subgroup.mul_mem _ (hmem k hk) (Subgroup.mul_mem _ (hmem _ hh)
          (Subgroup.mul_mem _ (hmem k hk) (hmem _ hhi)))) ho
      rw [hhi'] at hm
      simpa only [mul_assoc] using hm
    · rw [ite_eq_right h3] at ho
      unfold oddW2 at ho
      rw [CIdx.strictB_eq, CIdx.strictB_eq] at ho
      simp only [bAnd_iff', blt_iff] at ho
      obtain ⟨hh2, hi2, hinv2, ho⟩ := ho
      have hiv2 : e (Nat.pred (W3 k)) * e (W4 k) = 1 :=
        (hfix (actM (hact _) (hact _)) (Subgroup.mul_mem _ (hmem _ hh2) (hmem _ hi2))).1 hinv2
      have hi2' : e (W4 k) = (e (Nat.pred (W3 k)))⁻¹ := eq_inv_of_mul_eq_one_right hiv2
      refine Or.inr (Or.inr (Or.inr ⟨Nat.pred (W1 k), hh, Nat.pred (W3 k), hh2, ?_⟩))
      have m := fun a b => Subgroup.mul_mem (Gen n S kO) (x := a) (y := b)
      have hm := hmov (actM (hact k) (actM (hact _) (actM (hact k) (actM (hact _)
        (actM (hact _) (actM (hact k) (hact _)))))))
        (m _ _ (hmem k hk) (m _ _ (hmem _ hh) (m _ _ (hmem k hk) (m _ _ (hmem _ hhi)
          (m _ _ (hmem _ hh2) (m _ _ (hmem k hk) (hmem _ hi2))))))) ho
      rw [hhi', hi2'] at hm
      simpa only [mul_assoc] using hm

omit hQ in
theorem prod_sz : ∀ d, (((trLists n S base 0 d)).map List.length).prod = ordG n S base d
  | 0 => rfl
  | d + 1 => by
    unfold trLists
    rw [List.range_succ, List.map_append, List.map_append, List.prod_append, ordG,
      ← prod_sz d]
    unfold trLists
    simp [Nat.mul_comm]

theorem card_gen : Nat.card (Gen n S kO) = ordK LR nb := by
  obtain ⟨hm, hnd⟩ := products_spec hQ nb 0 (by omega)
  have hc := card_subtype_eq_countP (Gen n S kO) (products (trLists n S base 0 nb)) hnd
    (fun g => by rw [hm, fix_zero]) (fun _ => True)
  simp only [decide_true, List.countP_true] at hc
  rw [ordK_eq hQ nb le_rfl, ← prod_sz, ← length_products, ← hc]
  exact (Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial))).symm

theorem card_filter (P : Equiv.Perm (Fin n) → Prop) [DecidablePred P] :
    Nat.card {g : Equiv.Perm (Fin n) // g ∈ Gen n S kO ∧ P g} =
      (products (trLists n S base 0 nb)).countP fun g => decide (P g) := by
  obtain ⟨hm, hnd⟩ := products_spec hQ nb 0 (by omega)
  rw [← card_subtype_eq_countP (Gen n S kO) _ hnd (fun g => by rw [hm, fix_zero]) P]
  exact Nat.card_congr ⟨fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩, fun y => ⟨y.1.1, y.1.2, y.2⟩,
    fun x => rfl, fun y => rfl⟩

end Chain

theorem conj_closed {n kO : Nat} {S : Array (Array Nat)} {C : Set (Equiv.Perm (Fin n))}
    (hC : C.Finite) (h : ∀ j < kO, ∀ x ∈ C, permOfArr n S[j]! * x * (permOfArr n S[j]!)⁻¹ ∈ C) :
    ∀ g ∈ Gen n S kO, ∀ x ∈ C, g * x * g⁻¹ ∈ C := by
  intro g hg
  refine Subgroup.closure_induction (p := fun g _ => ∀ x ∈ C, g * x * g⁻¹ ∈ C) ?_ ?_ ?_ ?_ hg
  · rintro _ ⟨j, rfl⟩ x hx
    exact h j.val j.isLt x hx
  · intro x hx
    simpa using hx
  · intro g g' _ _ hg hg' x hx
    have := hg _ (hg' x hx)
    simpa only [mul_inv_rev, mul_assoc] using this
  · intro g _ hg y hy
    have : Finite C := hC.to_subtype
    let f : C → C := fun x => ⟨g * x * g⁻¹, hg x x.2⟩
    have hf : Function.Injective f := fun x x' e => by
      have e' := congrArg Subtype.val e
      simp only [f, mul_left_inj, mul_right_inj] at e'
      exact Subtype.ext e'
    obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.1 hf) ⟨y, hy⟩
    have e := congrArg Subtype.val hx
    simp only [f] at e
    rw [← e]
    simpa only [inv_inv, mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] using x.2

theorem card_cent_mul {n : Nat} (G : Subgroup (Equiv.Perm (Fin n))) {a : Equiv.Perm (Fin n)}
    (ha : a ∈ G) {C : Set (Equiv.Perm (Fin n))} (hC : ∀ x, x ∈ C ↔ ∃ g ∈ G, g * a * g⁻¹ = x) :
    Nat.card {g : Equiv.Perm (Fin n) // g ∈ G ∧ g * a = a * g} * C.ncard = Nat.card G := by
  let a' : G := ⟨a, ha⟩
  have h1 := Subgroup.card_mul_index (Subgroup.centralizer ({a'} : Set G))
  rw [Subgroup.index_centralizer_eq_ncard] at h1
  have e1 : Nat.card (Subgroup.centralizer ({a'} : Set G)) =
      Nat.card {g : Equiv.Perm (Fin n) // g ∈ G ∧ g * a = a * g} := by
    refine Nat.card_congr ⟨fun x => ⟨x.1.1, x.1.2, ?_⟩, fun y => ⟨⟨y.1, y.2.1⟩, ?_⟩,
      fun x => rfl, fun y => rfl⟩
    · have := Subgroup.mem_centralizer_iff.1 x.2 a' (Set.mem_singleton _)
      exact (congrArg Subtype.val this).symm
    · rw [Subgroup.mem_centralizer_iff]
      rintro _ rfl
      exact Subtype.ext y.2.2.symm
  have e2 : (conjugatesOf a').ncard = C.ncard := by
    have : (Subtype.val '' conjugatesOf a') = C := by
      ext x
      rw [hC]
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨c, hc⟩ := isConj_iff.1 hy
        exact ⟨c.1, c.2, congrArg Subtype.val hc⟩
      · rintro ⟨g, hg, rfl⟩
        exact ⟨⟨g, hg⟩ * a' * ⟨g, hg⟩⁻¹, isConj_iff.2 ⟨⟨g, hg⟩, rfl⟩, rfl⟩
    rw [← this, Set.ncard_image_of_injective _ Subtype.val_injective]
  rw [← e1, ← e2]
  exact h1

end CFSG.KS.SporSch.J1C

end
