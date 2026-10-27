module

public import Certificates.Data.Kernel.Misc.PermClos
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.SetTheory.Cardinal.Finite
import CFSG.Certificates.Kernel.LocalQTPermSound
import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.KC.Misc.Clos

open Equiv CFSG.KC.LQT

@[expose] def pcode {n : ℕ} (σ : Perm (Fin n)) : ℕ :=
  ((List.finRange n).map fun i => (σ i : ℕ) * 32 ^ (i : ℕ)).sum

structure ClosEnc {H : Type*} [Group H] (enc : H → ℕ) (M : ℕ → ℕ → ℕ) (one : ℕ) : Prop where
  enc_one : enc 1 = one
  enc_mul : ∀ a b, enc (a * b) = M (enc a) (enc b)
  inj : Function.Injective enc

@[expose] def ExactList {G : Type*} [Group G] (enc : G → ℕ) (H : Subgroup G) (N : ℕ) (E : ℕ → ℕ) :
    Prop :=
  (∀ k < N, ∃ g ∈ H, enc g = E k) ∧ (∀ g ∈ H, ∃ k < N, enc g = E k) ∧
    (∀ i < N, ∀ j < N, E i = E j → i = j)

theorem sort_distinct {N : ℕ} {E SG : ℕ → ℕ} (hs : ∀ i < N, sortAt N E SG i = true) :
    ∀ i < N, ∀ j < N, E i = E j → i = j := by
  have h1 : ∀ i < N, SG i < N ∧ (i + 1 < N → E (SG i) < E (SG (i + 1))) := by
    intro i hi
    obtain ⟨ha, hb⟩ := P.andB_iff.1 (hs i hi)
    exact ⟨Nat.blt_eq.mp ha, fun h => Nat.blt_eq.mp (P.impB_iff.1 hb (Nat.blt_eq.mpr h))⟩
  have hmono : ∀ a b, a < b → b < N → E (SG a) < E (SG b) := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h | rfl
      · exact (ih h (by omega)).trans ((h1 b (by omega)).2 hb)
      · exact (h1 a (by omega)).2 hb
  have hinj : ∀ a < N, ∀ b < N, SG a = SG b → a = b := by
    intro a ha b hb h
    rcases Nat.lt_trichotomy a b with hab | hab | hab
    · exact absurd (congrArg E h) (hmono a b hab hb).ne
    · exact hab
    · exact absurd (congrArg E h) (hmono b a hab ha).ne'
  let f : Fin N → Fin N := fun a => ⟨SG a, (h1 a a.isLt).1⟩
  have hf : Function.Injective f := fun a b h =>
    Fin.ext (hinj a a.isLt b b.isLt (congrArg Fin.val h))
  have hsurj := Finite.surjective_of_injective hf
  intro i hi j hj hij
  obtain ⟨a, ha⟩ := hsurj ⟨i, hi⟩
  obtain ⟨b, hb⟩ := hsurj ⟨j, hj⟩
  have ea : SG a = i := congrArg Fin.val ha
  have eb : SG b = j := congrArg Fin.val hb
  rw [← ea, ← eb] at hij ⊢
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · exact absurd hij (hmono a b hab b.isLt).ne
  · rw [hab]
  · exact absurd hij (hmono b a hab a.isLt).ne'

theorem clos_card {H : Type*} [Group H] [Finite H] {enc : H → ℕ} {M : ℕ → ℕ → ℕ} {one : ℕ}
    (henc : ClosEnc enc M one) (gens : List H) {G : ℕ → ℕ} {N : ℕ} {E PA SG : ℕ → ℕ}
    (hG : ∀ j < gens.length, G j = enc (gens.getD j 1)) (hN : 0 < N)
    (ht : ∀ k < N, treeAt M one G gens.length E PA k = true)
    (hs : ∀ i < N, sortAt N E SG i = true) :
    (∀ k < N, ∃ g ∈ Subgroup.closure {g | g ∈ gens}, enc g = E k) ∧
      N ≤ Nat.card (Subgroup.closure {g | g ∈ gens}) ∧
      ∀ {CT : ℕ → ℕ}, (∀ k < N, closedAt M G gens.length N E CT k = true) →
        Nat.card (Subgroup.closure {g | g ∈ gens}) = N ∧
          ∀ g ∈ Subgroup.closure {g | g ∈ gens}, ∃ k < N, enc g = E k := by
  classical
  have hgen : ∀ l < gens.length, gens.getD l 1 ∈ Subgroup.closure {g | g ∈ gens} := fun l hl =>
    Subgroup.subset_closure (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
      exact List.getElem_mem hl)
  have h0 : Nat.beq (E 0) one = true := ht 0 hN
  have htree : ∀ k < N, ∃ g ∈ Subgroup.closure {g | g ∈ gens}, enc g = E k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      cases k with
      | zero => exact ⟨1, Subgroup.one_mem _, by rw [henc.enc_one, Nat.eq_of_beq_eq_true h0]⟩
      | succ k =>
        have h : P.letB (PA (k + 1)) (fun r => P.letB (Nat.land r 16777215) fun p =>
            P.letB (Nat.shiftRight r 24) fun l => CFSG.KC.Ord.andB (Nat.blt p (k + 1))
              (CFSG.KC.Ord.andB (Nat.blt l gens.length) (Nat.beq (E (k + 1)) (M (E p) (G l))))) =
            true := ht (k + 1) hk
        rw [P.letB_eq, P.letB_eq, P.letB_eq] at h
        obtain ⟨hp, h⟩ := P.andB_iff.1 h
        obtain ⟨hl, h⟩ := P.andB_iff.1 h
        have hp' := Nat.blt_eq.mp hp
        have hl' := Nat.blt_eq.mp hl
        obtain ⟨g, hg, hge⟩ := ih _ hp' (by omega)
        refine ⟨g * gens.getD _ 1, Subgroup.mul_mem _ hg (hgen _ hl'), ?_⟩
        rw [henc.enc_mul, hge, ← hG _ hl']
        exact (Nat.eq_of_beq_eq_true h).symm
  have hdist := sort_distinct hs
  choose! f hfS hfe using htree
  let F : Fin N → Subgroup.closure {g | g ∈ gens} := fun k => ⟨f k, hfS k k.isLt⟩
  have hF : Function.Injective F := by
    intro a b hab
    have hab' : f a = f b := congrArg Subtype.val hab
    exact Fin.ext (hdist a a.isLt b b.isLt (by rw [← hfe a a.isLt, ← hfe b b.isLt, hab']))
  refine ⟨fun k hk => ⟨f k, hfS k hk, hfe k hk⟩, ?_, ?_⟩
  · simpa using Nat.card_le_card_of_injective F hF
  · intro CT hc
    have hcl : ∀ k < N, ∀ j < gens.length, ∃ t < N, E t = M (E k) (G j) := by
      intro k hk j hj
      have h := (P.allN_iff _ _).1 (hc k hk) j hj
      rw [P.letB_eq] at h
      obtain ⟨h1, h2⟩ := P.andB_iff.1 h
      exact ⟨_, Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2⟩
    have key : ∀ g ∈ Submonoid.closure {g | g ∈ gens}, ∃ k < N, enc g = E k := by
      intro g hg
      induction hg using Submonoid.closure_induction_right with
      | one => exact ⟨0, hN, by rw [henc.enc_one, Nat.eq_of_beq_eq_true h0]⟩
      | mul_right x _ y hy ih =>
        obtain ⟨k, hk, hxk⟩ := ih
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hy
        obtain ⟨t, ht', het⟩ := hcl k hk j hj
        refine ⟨t, ht', ?_⟩
        rw [henc.enc_mul, hxk, het, hG j hj, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hj, Option.getD_some]
    have hall : ∀ g ∈ Subgroup.closure {g | g ∈ gens}, ∃ k < N, enc g = E k := fun g hg =>
      key g (by rw [← Subgroup.closure_toSubmonoid_of_finite]; exact hg)
    refine ⟨?_, hall⟩
    have hsurj : Function.Surjective F := by
      rintro ⟨g, hg⟩
      obtain ⟨k, hk, hgk⟩ := hall g hg
      exact ⟨⟨k, hk⟩, Subtype.ext (henc.inj (by rw [hfe k hk, hgk]))⟩
    simpa using (Nat.card_eq_of_bijective F ⟨hF, hsurj⟩).symm

theorem pcode_enc {n : ℕ} (hn : n ≤ 32) :
    ClosEnc (pcode (n := n)) (P.mul n) (P.one n) :=
  ⟨P.code_one.symm, fun a b => (P.code_mul hn a b).symm, fun _ _ h => P.code_inj hn h⟩

theorem pcode_inv {n : ℕ} (hn : n ≤ 32) (σ : Perm (Fin n)) : P.inv n (pcode σ) = pcode σ⁻¹ :=
  P.code_inv hn σ

theorem pcode_img {n : ℕ} (hn : n ≤ 32) (σ : Perm (Fin n)) (i : Fin n) :
    P.img (pcode σ) i = σ i :=
  P.img_code hn σ i

theorem letB_eq (y : ℕ) (k : ℕ → Bool) : P.letB y k = k y := by
  cases y <;> rfl

theorem impB_eq_true {a b : Bool} (h : P.impB a b = true) (ha : a = true) : b = true := by
  subst ha
  exact h

theorem andB_eq_true {a b : Bool} (h : CFSG.KC.Ord.andB a b = true) : a = true ∧ b = true := by
  cases a
  · exact absurd h (by simp [CFSG.KC.Ord.andB])
  · exact ⟨rfl, h⟩

theorem allN_iff (m : ℕ) (f : ℕ → Bool) : P.allN m f = true ↔ ∀ i < m, f i = true := by
  induction m with
  | zero => simp [P.allN]
  | succ m ih =>
    change CFSG.KC.Ord.andB (f m) (P.allN m f) = true ↔ _
    cases hf : f m
    · simp only [CFSG.KC.Ord.andB, Bool.false_eq_true, false_iff, not_forall]
      exact ⟨m, Nat.lt_succ_self m, by rw [hf]; simp⟩
    · change P.allN m f = true ↔ _
      rw [ih]
      constructor
      · intro h i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact h i hi
        · exact hf
      · exact fun h i hi => h i (Nat.lt_succ_of_lt hi)

theorem anyN_iff (m : ℕ) (f : ℕ → Bool) : P.anyN m f = true ↔ ∃ i < m, f i = true := by
  induction m with
  | zero => simp [P.anyN]
  | succ m ih =>
    change CFSG.KC.Ord.orB (f m) (P.anyN m f) = true ↔ _
    cases hf : f m
    · change P.anyN m f = true ↔ _
      rw [ih]
      constructor
      · rintro ⟨i, hi, h⟩
        exact ⟨i, Nat.lt_succ_of_lt hi, h⟩
      · rintro ⟨i, hi, h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact ⟨i, hi, h⟩
        · rw [hf] at h
          cases h
    · simp only [CFSG.KC.Ord.orB, true_iff]
      exact ⟨m, Nat.lt_succ_self m, hf⟩

theorem allR_iff (lo cnt : ℕ) (f : ℕ → Bool) :
    allR lo cnt f = true ↔ ∀ i, lo ≤ i → i < lo + cnt → f i = true := by
  rw [allR, allN_iff]
  constructor
  · intro h i h1 h2
    have := h (i - lo) (Nat.sub_lt_left_of_lt_add h1 h2)
    rwa [show Nat.add lo (i - lo) = i from Nat.add_sub_cancel' h1] at this
  · intro h d hd
    exact h _ (Nat.le_add_right _ _) (by change lo + d < lo + cnt; omega)

theorem forall_of_chunks (s m : ℕ) (f : ℕ → Bool) (h : ∀ c < m, allR (s * c) s f = true) :
    ∀ i < s * m, f i = true := by
  intro i hi
  have hs : 0 < s := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hi
  have hc : i / s < m := (Nat.div_lt_iff_lt_mul hs).2 (by rw [Nat.mul_comm]; exact hi)
  refine (allR_iff _ _ _).1 (h (i / s) hc) i ?_ ?_
  · exact Nat.mul_div_le i s
  · have := Nat.lt_div_mul_add (a := i) hs
    rw [Nat.mul_comm] at this
    exact this

theorem forall_lt_of_chunks {P : ℕ → Prop} {lo hi : ℕ} (h₁ : ∀ i, 0 ≤ i → i < lo → P i)
    (h₂ : ∀ i, lo ≤ i → i < hi → P i) : ∀ i, 0 ≤ i → i < hi → P i := by
  intro i _ hi'
  rcases Nat.lt_or_ge i lo with h | h
  · exact h₁ i (Nat.zero_le _) h
  · exact h₂ i h hi'

theorem word_mem {n : ℕ} (hn : n ≤ 32) (gs : List (Perm (Fin n))) {A : ℕ → ℕ}
    (hA : ∀ a < gs.length, A a = pcode (gs.getD a 1)) {w : List ℕ}
    (hw : lettersK gs.length w = true) :
    ∃ g ∈ Subgroup.closure {g | g ∈ gs}, pcode g = wordK n A gs.length w := by
  induction w with
  | nil => exact ⟨1, Subgroup.one_mem _, (pcode_enc hn).enc_one⟩
  | cons l w ih =>
    change CFSG.KC.Ord.andB (Nat.blt l (gs.length + gs.length)) (lettersK gs.length w) = true at hw
    have hl : Nat.blt l (gs.length + gs.length) = true := by
      cases h : Nat.blt l (gs.length + gs.length)
      · rw [h] at hw; exact absurd hw (by simp [CFSG.KC.Ord.andB])
      · rfl
    rw [hl] at hw
    obtain ⟨g, hg, hgw⟩ := ih hw
    have hl' : l < gs.length + gs.length := Nat.blt_eq.mp hl
    have hmem : ∀ a < gs.length, gs.getD a 1 ∈ Subgroup.closure {g | g ∈ gs} := fun a ha =>
      Subgroup.subset_closure (by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha, Option.getD_some]
        exact List.getElem_mem ha)
    have hlet : ∃ u ∈ Subgroup.closure {g | g ∈ gs}, pcode u = letterK n A gs.length l := by
      unfold letterK
      cases hb : Nat.blt l gs.length
      · have hge : gs.length ≤ l := Nat.not_lt.1 fun h => by
          rw [Nat.blt_eq.mpr h] at hb
          cases hb
        have hlt : l - gs.length < gs.length := by omega
        refine ⟨(gs.getD (l - gs.length) 1)⁻¹, Subgroup.inv_mem _ (hmem _ hlt), ?_⟩
        change pcode _ = P.inv n (A (l - gs.length))
        rw [hA _ hlt, pcode_inv hn]
      · exact ⟨gs.getD l 1, hmem l (Nat.blt_eq.mp hb), (hA l (Nat.blt_eq.mp hb)).symm⟩
    obtain ⟨u, hu, hul⟩ := hlet
    refine ⟨u * g, Subgroup.mul_mem _ hu hg, ?_⟩
    change pcode (u * g) = P.mul n (letterK n A gs.length l) (wordK n A gs.length w)
    rw [(pcode_enc hn).enc_mul, hul, hgw]

end CFSG.KC.Misc.Clos

end
