module

public import CFSG.Certificates.Kernel.Misc.PermClosSound
import CFSG.Certificates.Kernel.LocalQTPermSound
import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.KC.Misc.Clos

open Equiv CFSG.KC.LQT

theorem pcode_enc_proved {n : ℕ} (hn : n ≤ 32) :
    ClosEnc (pcode (n := n)) (P.mul n) (P.one n) where
  enc_one := P.code_one.symm
  enc_mul a b := (P.code_mul hn a b).symm
  inj _ _ h := P.code_inj hn h

theorem pcode_inv_proved {n : ℕ} (hn : n ≤ 32) (σ : Perm (Fin n)) :
    P.inv n (pcode σ) = pcode σ⁻¹ :=
  P.code_inv hn σ

theorem pcode_img_proved {n : ℕ} (hn : n ≤ 32) (σ : Perm (Fin n)) (i : Fin n) :
    P.img (pcode σ) i = σ i :=
  P.img_code hn σ i

theorem sortAt_spec {N : ℕ} {E SG : ℕ → ℕ} {i : ℕ} (h : sortAt N E SG i = true) :
    SG i < N ∧ (i + 1 < N → E (SG i) < E (SG (i + 1))) := by
  obtain ⟨a, b⟩ := andB_eq_true h
  exact ⟨Nat.blt_eq.mp a, fun hi => Nat.blt_eq.mp (impB_eq_true b (Nat.blt_eq.mpr hi))⟩

theorem sort_distinct_proved {N : ℕ} {E SG : ℕ → ℕ} (hs : ∀ i < N, sortAt N E SG i = true) :
    ∀ i < N, ∀ j < N, E i = E j → i = j := by
  have hmono : ∀ i j, i < j → j < N → E (SG i) < E (SG j) := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | rfl
      · exact (ih h (by omega)).trans ((sortAt_spec (hs j (by omega))).2 hj)
      · exact (sortAt_spec (hs i (by omega))).2 hj
  have hne : ∀ a b : Fin N, a ≠ b → E (SG a) ≠ E (SG b) := by
    intro a b hab e
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h | h
    · exact absurd e (hmono a b h b.2).ne
    · exact absurd e.symm (hmono b a h a.2).ne
  let f : Fin N → Fin N := fun i => ⟨SG i, (sortAt_spec (hs i i.2)).1⟩
  have finj : Function.Injective f := fun a b hab => by
    by_contra h
    exact hne a b h (congrArg E (congrArg Fin.val hab))
  have fsurj : Function.Surjective f := Finite.injective_iff_surjective.1 finj
  intro i hi j hj e
  obtain ⟨a, ha⟩ := fsurj ⟨i, hi⟩
  obtain ⟨b, hb⟩ := fsurj ⟨j, hj⟩
  have hai : SG a = i := congrArg Fin.val ha
  have hbj : SG b = j := congrArg Fin.val hb
  by_contra hij
  exact hne a b (fun h => hij (by rw [← hai, ← hbj, h])) (by rw [hai, hbj, e])

theorem clos_card_proved {H : Type*} [Group H] [Finite H] {enc : H → ℕ} {M : ℕ → ℕ → ℕ}
    {one : ℕ} (henc : ClosEnc enc M one) (gens : List H) {G : ℕ → ℕ} {N : ℕ} {E PA SG : ℕ → ℕ}
    (hG : ∀ j < gens.length, G j = enc (gens.getD j 1)) (hN : 0 < N)
    (ht : ∀ k < N, treeAt M one G gens.length E PA k = true)
    (hs : ∀ i < N, sortAt N E SG i = true) :
    (∀ k < N, ∃ g ∈ Subgroup.closure {g | g ∈ gens}, enc g = E k) ∧
      N ≤ Nat.card (Subgroup.closure {g | g ∈ gens}) ∧
      ∀ {CT : ℕ → ℕ}, (∀ k < N, closedAt M G gens.length N E CT k = true) →
        Nat.card (Subgroup.closure {g | g ∈ gens}) = N ∧
          ∀ g ∈ Subgroup.closure {g | g ∈ gens}, ∃ k < N, enc g = E k := by
  set C := Subgroup.closure {g | g ∈ gens}
  have hgetD : ∀ j (hj : j < gens.length), gens.getD j 1 = gens[j] := fun j hj => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  have hmem : ∀ j < gens.length, gens.getD j 1 ∈ C := fun j hj =>
    Subgroup.subset_closure (by rw [hgetD j hj]; exact List.getElem_mem hj)
  have hE0 : E 0 = enc 1 := by
    have h : Nat.beq (E 0) one = true := ht 0 hN
    rw [henc.enc_one]
    exact Nat.eq_of_beq_eq_true h
  have htree : ∀ k < N, ∃ g ∈ C, enc g = E k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      cases k with
      | zero => exact ⟨1, C.one_mem, hE0.symm⟩
      | succ k =>
        have h := ht (k + 1) hk
        simp only [treeAt, letB_eq] at h
        obtain ⟨hp, h⟩ := andB_eq_true h
        obtain ⟨hl, he⟩ := andB_eq_true h
        have hp' := Nat.blt_eq.mp hp
        have hl' := Nat.blt_eq.mp hl
        obtain ⟨g, hg, hge⟩ := ih _ hp' (by omega)
        refine ⟨g * gens.getD _ 1, C.mul_mem hg (hmem _ hl'), ?_⟩
        rw [henc.enc_mul, hge, ← hG _ hl']
        exact (Nat.eq_of_beq_eq_true he).symm
  have hdist := sort_distinct_proved hs
  choose! gk hgkC hgk using htree
  have hle : N ≤ Nat.card C := by
    have hinj : Function.Injective fun k : Fin N => (⟨gk k, hgkC k k.2⟩ : C) := by
      intro a b hab
      have : gk a = gk b := congrArg Subtype.val hab
      exact Fin.ext (hdist a a.2 b b.2 (by rw [← hgk a a.2, ← hgk b b.2, this]))
    simpa using Nat.card_le_card_of_injective _ hinj
  refine ⟨fun k hk => ⟨gk k, hgkC k hk, hgk k hk⟩, hle, ?_⟩
  intro CT hc
  let S : Set H := {g | ∃ k < N, enc g = E k}
  let T : Set H := {g | ∀ x ∈ S, x * g ∈ S}
  have hTmul : ∀ a ∈ T, ∀ b ∈ T, a * b ∈ T := fun a ha b hb x hx => by
    rw [← mul_assoc]; exact hb _ (ha x hx)
  have hTpow : ∀ a ∈ T, ∀ m : ℕ, a ^ m ∈ T := by
    intro a ha m
    induction m with
    | zero => intro x hx; simpa using hx
    | succ m ih => rw [pow_succ]; exact hTmul _ ih _ ha
  have hTgen : ∀ g ∈ {g | g ∈ gens}, g ∈ T := by
    intro g hg x ⟨k, hk, hxk⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hg
    have h := (allN_iff _ _).1 (hc k hk) j hj
    simp only [letB_eq] at h
    obtain ⟨htN, hte⟩ := andB_eq_true h
    refine ⟨_, Nat.blt_eq.mp htN, ?_⟩
    rw [henc.enc_mul, hxk, Nat.eq_of_beq_eq_true hte, hG j hj, hgetD j hj]
  have hT : ∀ g ∈ C, g ∈ T := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hTgen x hx
    | one => intro x hx; simpa using hx
    | mul a b _ _ ha hb => exact hTmul a ha b hb
    | inv a _ ha =>
      have hpos := orderOf_pos a
      have e : a⁻¹ = a ^ (orderOf a - 1) := by
        refine (eq_inv_of_mul_eq_one_left ?_).symm
        rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
      rw [e]
      exact hTpow a ha _
  have hall : ∀ g ∈ C, ∃ k < N, enc g = E k := fun g hg => by
    have := hT g hg 1 ⟨0, hN, hE0.symm⟩
    rwa [one_mul] at this
  refine ⟨le_antisymm ?_ hle, hall⟩
  choose! kg hkgN hkg using hall
  have hinj : Function.Injective fun g : C => (⟨kg g, hkgN g g.2⟩ : Fin N) := by
    intro a b hab
    have : kg a = kg b := congrArg Fin.val hab
    exact Subtype.ext (henc.inj (by rw [hkg a a.2, hkg b b.2, this]))
  simpa using Nat.card_le_card_of_injective _ hinj

theorem word_mem_proved {n : ℕ} (hn : n ≤ 32) (gs : List (Perm (Fin n))) {A : ℕ → ℕ}
    (hA : ∀ a < gs.length, A a = pcode (gs.getD a 1)) {w : List ℕ}
    (hw : lettersK gs.length w = true) :
    ∃ g ∈ Subgroup.closure {g | g ∈ gs}, pcode g = wordK n A gs.length w := by
  induction w with
  | nil => exact ⟨1, Subgroup.one_mem _, (pcode_enc_proved hn).enc_one⟩
  | cons l w ih =>
    change CFSG.KC.Ord.andB (Nat.blt l (gs.length + gs.length)) (lettersK gs.length w) = true at hw
    obtain ⟨hl, hw⟩ := andB_eq_true hw
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
        rw [hA _ hlt, pcode_inv_proved hn]
      · exact ⟨gs.getD l 1, hmem l (Nat.blt_eq.mp hb), (hA l (Nat.blt_eq.mp hb)).symm⟩
    obtain ⟨u, hu, hul⟩ := hlet
    refine ⟨u * g, Subgroup.mul_mem _ hu hg, ?_⟩
    change pcode (u * g) = P.mul n (letterK n A gs.length l) (wordK n A gs.length w)
    rw [(pcode_enc_proved hn).enc_mul, hul, hgw]

end CFSG.KC.Misc.Clos

end
