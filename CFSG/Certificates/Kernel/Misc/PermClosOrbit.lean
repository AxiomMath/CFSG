module

import CFSG.Certificates.Kernel.Misc.PermClosProof
import CFSG.Certificates.Kernel.LocalQTPermSound
import Mathlib.GroupTheory.OrderOfElement
public import Certificates.Data.Kernel.Misc.PermClos
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.KC.Misc.Clos

open CFSG.KC.LQT

theorem orbit_card_proved {H X : Type*} [Group H] [Finite H] [MulAction H X] {enc : X → ℕ}
    (hinj : Function.Injective enc) {M : ℕ → ℕ → ℕ} (gens : List H) {G : ℕ → ℕ}
    (hM : ∀ j < gens.length, ∀ x, enc (gens.getD j 1 • x) = M (enc x) (G j)) (x₀ : X)
    {N : ℕ} {E PA SG CT : ℕ → ℕ} (hN : 0 < N)
    (ht : ∀ k < N, treeAt M (enc x₀) G gens.length E PA k = true)
    (hs : ∀ i < N, sortAt N E SG i = true)
    (hc : ∀ k < N, closedAt M G gens.length N E CT k = true) :
    (∀ k < N, ∃ g ∈ Subgroup.closure {g | g ∈ gens}, enc (g • x₀) = E k) ∧
      (∀ g ∈ Subgroup.closure {g | g ∈ gens}, ∃ k < N, enc (g • x₀) = E k) ∧
      Nat.card {y : X // ∃ g ∈ Subgroup.closure {g | g ∈ gens}, g • x₀ = y} = N := by
  classical
  set C := Subgroup.closure {g | g ∈ gens}
  have hgetD : ∀ j (hj : j < gens.length), gens.getD j 1 = gens[j] := fun j hj => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  have hgen : ∀ l < gens.length, gens.getD l 1 ∈ C := fun l hl =>
    Subgroup.subset_closure (by rw [hgetD l hl]; exact List.getElem_mem hl)
  have hE0 : E 0 = enc x₀ := Nat.eq_of_beq_eq_true (ht 0 hN)
  have htree : ∀ k < N, ∃ g ∈ C, enc (g • x₀) = E k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      cases k with
      | zero => exact ⟨1, C.one_mem, by rw [one_smul, hE0]⟩
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
        refine ⟨gens.getD _ 1 * g, C.mul_mem (hgen _ hl') hg, ?_⟩
        rw [mul_smul, hM _ hl', hge]
        exact (Nat.eq_of_beq_eq_true h).symm
  have hdist := sort_distinct_proved hs
  let S : Set X := {y | ∃ k < N, enc y = E k}
  let T : Set H := {g | ∀ y ∈ S, g • y ∈ S}
  have hTmul : ∀ a ∈ T, ∀ b ∈ T, a * b ∈ T := fun a ha b hb y hy => by
    rw [mul_smul]; exact ha _ (hb y hy)
  have hTpow : ∀ a ∈ T, ∀ m : ℕ, a ^ m ∈ T := by
    intro a ha m
    induction m with
    | zero => intro y hy; simpa using hy
    | succ m ih => rw [pow_succ]; exact hTmul _ ih _ ha
  have hTgen : ∀ g ∈ {g | g ∈ gens}, g ∈ T := by
    intro g hg y ⟨k, hk, hyk⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hg
    have h := (P.allN_iff _ _).1 (hc k hk) j hj
    rw [P.letB_eq] at h
    obtain ⟨htN, hte⟩ := P.andB_iff.1 h
    refine ⟨_, Nat.blt_eq.mp htN, ?_⟩
    rw [← hgetD j hj, hM j hj, hyk, Nat.eq_of_beq_eq_true hte]
  have hT : ∀ g ∈ C, g ∈ T := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hTgen x hx
    | one => intro y hy; simpa using hy
    | mul a b _ _ ha hb => exact hTmul a ha b hb
    | inv a _ ha =>
      have hpos := orderOf_pos a
      have e : a⁻¹ = a ^ (orderOf a - 1) := by
        refine (eq_inv_of_mul_eq_one_left ?_).symm
        rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
      rw [e]
      exact hTpow a ha _
  have hall : ∀ g ∈ C, ∃ k < N, enc (g • x₀) = E k := fun g hg =>
    hT g hg x₀ ⟨0, hN, hE0.symm⟩
  refine ⟨htree, hall, ?_⟩
  have hkey : ∀ y : {y : X // ∃ g ∈ C, g • x₀ = y}, ∃ k < N, enc y.1 = E k := by
    rintro ⟨y, g, hg, rfl⟩
    exact hall g hg
  choose kf hkfN hkf using hkey
  let f : {y : X // ∃ g ∈ C, g • x₀ = y} → Fin N := fun y => ⟨kf y, hkfN y⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => Subtype.ext (hinj ?_), fun k => ?_⟩
    · rw [hkf a, hkf b]
      exact congrArg E (congrArg Fin.val hab)
    · obtain ⟨g, hg, hgk⟩ := htree k k.isLt
      refine ⟨⟨g • x₀, g, hg, rfl⟩, Fin.ext ?_⟩
      exact hdist _ (hkfN _) _ k.isLt (by rw [← hkf, hgk])
  rw [Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_fin]

end CFSG.KC.Misc.Clos

end
