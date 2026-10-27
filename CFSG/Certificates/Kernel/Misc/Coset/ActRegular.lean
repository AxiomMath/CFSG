module

public import Certificates.Data.Kernel.Misc.Coset.ActReg
public import CFSG.Certificates.Kernel.Misc.Coset.ActSound

public section

namespace CFSG.KC.MiscCoset.Act

open CFSG.CosetTable CFSG.Certificates.CosetEnumeration

theorem downAt_spec {A : ℕ → ℕ} {L x : ℕ} :
    ∀ {n : ℕ}, downAt A L n x = true → ∃ c < n, step A L x c < x
  | 0, h => absurd (h : false = true) Bool.false_ne_true
  | n + 1, h => by
    have h' : Bool.rec (motive := fun _ => Bool) (downAt A L n x) true
        (Nat.blt (step A L x n) x) = true := h
    cases hb : Nat.blt (step A L x n) x with
    | false =>
      rw [hb] at h'
      obtain ⟨c, hc, hs⟩ := downAt_spec (n := n) h'
      exact ⟨c, Nat.lt_succ_of_lt hc, hs⟩
    | true =>
      rw [Nat.blt_eq] at hb
      exact ⟨n, Nat.lt_succ_self n, hb⟩

theorem fixAll_spec {A : ℕ → ℕ} {L : ℕ} :
    ∀ {us : List (List ℕ)}, fixAll A L us = true → ∀ u ∈ us, walk A L u 0 = 0
  | [], _, u, hu => absurd hu List.not_mem_nil
  | v :: vs, h, u, hu => by
    change andB (fixOK A L v) (fixAll A L vs) = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hu with rfl | hu
    · exact Nat.eq_of_beq_eq_true h.1
    · exact fixAll_spec h.2 u hu

theorem orbit_all {m N : ℕ} {ws : List (List (Fin m × Bool))} {A : ℕ → ℕ} (hN : 0 < N)
    (hl : ∀ x < N, LetOK A m N x)
    (ψ : PG m ws →* (Equiv.Perm {c : ℕ // c < N})ᵐᵒᵖ)
    (hψ : ∀ y < 2 * m, ∀ c : {c : ℕ // c < N},
      ((ψ (presLetter {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} y)).unop c).1 =
        step A (m + m) c.1 y)
    (hdown : ∀ x, 0 < x → x < N → downAt A (Nat.add m m) (Nat.add m m) x = true) :
    ∀ x (hx : x < N), ∃ g, (ψ g).unop ⟨0, hN⟩ = ⟨x, hx⟩ := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hx
    rcases Nat.eq_zero_or_pos x with rfl | hpos
    · exact ⟨1, by simp⟩
    · obtain ⟨c, hc, hlt⟩ := downAt_spec (hdown x hpos hx)
      have hc' : c < 2 * m := by
        have : c < m + m := hc
        omega
      have hy : step A (m + m) x c < N := (hl x hx).1 c (by omega)
      obtain ⟨g, hg⟩ := ih _ hlt hy
      refine ⟨g * presLetter {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (invCode c), ?_⟩
      apply Subtype.ext
      rw [map_mul, MulOpposite.unop_mul, Equiv.Perm.mul_apply, hg, hψ _ (invCode_lt hc')]
      exact step_invCode (hl x hx) hc'

theorem eq_one_of_walk_zero {m N : ℕ} (ws : List (List (Fin m × Bool))) {rels : List (List ℕ)}
    (hrels : codes ws = rels) {A : ℕ → ℕ} (hN : 0 < N)
    (hpt : ∀ x < N, pointOK A m N rels x = true)
    (hdown : ∀ x, 0 < x → x < N → downAt A (Nat.add m m) (Nat.add m m) x = true)
    (hcard : Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ N) {u : List (Fin m × Bool)}
    (hu : walk A (m + m) (u.map letterCode) 0 = 0) :
    PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (FreeGroup.mk u) = 1 := by
  obtain ⟨ψ, hψ⟩ := exists_act ws (fun r hr => hrels ▸ hr) hpt
  have hl : ∀ x < N, LetOK A m N x := fun x hx => (pointOK_spec (hpt x hx)).1
  have hfin := hcard.1
  let f : PG m ws → {c : ℕ // c < N} := fun g => (ψ g).unop ⟨0, hN⟩
  have hsurj : Function.Surjective f := fun x => orbit_all hN hl ψ hψ hdown x.1 x.2
  have hN' : Nat.card {c : ℕ // c < N} = N := by
    rw [← Nat.card_congr Fin.equivSubtype, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hbij := hsurj.bijective_of_nat_card_le (hcard.2.trans hN'.ge)
  apply hbij.1
  apply Subtype.ext
  change ((ψ (PresentedGroup.mk _ (FreeGroup.mk u))).unop ⟨0, hN⟩).1 = ((ψ 1).unop ⟨0, hN⟩).1
  rw [act_mk ψ hψ u ⟨0, hN⟩, hu, map_one, MulOpposite.unop_one, Equiv.Perm.one_apply]

end CFSG.KC.MiscCoset.Act

end
