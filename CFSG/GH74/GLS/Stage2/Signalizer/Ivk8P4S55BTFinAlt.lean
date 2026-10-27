module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinAlt5
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinA8
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55AltHH
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinAltM

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Equiv Equiv.Perm Subgroup CFSG FinGlue FinAltW FinAlt5 FinCyc

namespace FinAltB

theorem hhobsAt_of_altWit {Y : Type} [Group Y] {n : ℕ} (hn5 : 5 ≤ n) (hn6 : n ≠ 6)
    (e : Y ≃* alternatingGroup (Fin n)) {p r : ℕ} (hr : r.Prime) (hrp : r ≠ p) (b : MulAut Y)
    (hb : AltWit r (autTransport hn5 hn6 e b)) : HHObsAt p r Y b := by
  obtain ⟨Q, hQA, hQp, hQc, hQn, q, hqQ, hqn⟩ := hb
  let f : Y →* Perm (Fin n) := ((alternatingGroup (Fin n)).subtype).comp e.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hmemE : ∀ y, y ∈ Q.comap f ↔ ((e y : alternatingGroup (Fin n)) : Perm (Fin n)) ∈ Q :=
    fun y => Iff.rfl
  refine ⟨hr, hrp, Q.comap f, hQp.comap_of_injective f hf, ?_, ?_, ?_⟩
  · intro hr2 x hx y hy
    have h' : ((e x : alternatingGroup (Fin n)) : Perm (Fin n)) * (e y : alternatingGroup (Fin n)) =
        (e y : alternatingGroup (Fin n)) * (e x : alternatingGroup (Fin n)) := hQc hr2 _ hx _ hy
    apply e.injective
    apply Subtype.ext
    simpa using h'
  · intro x hx
    rw [hmemE, autTransport_apply hn5 hn6 e b x]
    exact hQn _ hx
  · obtain ⟨x, hx⟩ := e.surjective ⟨q, hQA hqQ⟩
    refine ⟨x, ?_, ?_⟩
    · rw [hmemE, hx]
      exact hqQ
    · intro h
      apply hqn
      have h1 := autTransport_apply hn5 hn6 e b x
      rw [h, hx] at h1
      simpa using h1.symm

theorem altWit_cell {n : ℕ} (h9 : 9 ≤ n) (h11 : n ≤ 11) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X U I : Subgroup (Perm (Fin n))} (hX : IsPGroup p ↥X) (hU : IVK.IsFourSubgroup U)
    (hI1 : I ≠ ⊥) (hI : ⁅I, I⁆ = I) (hIU : I ≤ centralizer (U : Set (Perm (Fin n))))
    (hUX : U ≤ normalizer (X : Set (Perm (Fin n))))
    (hIX : I ≤ normalizer (X : Set (Perm (Fin n)))) {σ : Perm (Fin n)} (hσX : σ ∈ X)
    (hσ : orderOf σ = p) : AltWit 2 σ := by
  obtain ⟨m, hm⟩ := cycleType_prime_order (σ := σ) (by rw [hσ]; exact hp)
  rw [hσ] at hm
  have hs : σ.support.card = (m + 1) * p := by
    rw [← sum_cycleType, hm, Multiset.sum_replicate, smul_eq_mul]
  have hsn : σ.support.card ≤ n := by
    have := Finset.card_le_univ σ.support
    rwa [Fintype.card_fin] at this
  have hp1 := hp.two_le
  have hX1 : X ≠ ⊥ := fun h => by
    rw [h, mem_bot] at hσX
    rw [hσX, orderOf_one] at hσ
    omega
  by_cases h3 : p = 3
  · subst h3
    exact altWit_of_three h9 hσ (by omega)
  by_cases h5 : p = 5
  · subst h5
    by_cases hm0 : m = 0
    · subst hm0
      exact (false_of_fiveCycle h11 hX hU hI1 hI hIU hUX hIX hσX
        (isCycle_of_orderOf (by norm_num) hσ (by omega)).1 (by omega)).elim
    · exact altWit_of_five (by omega) hσ (by omega)
  · exfalso
    have hp11 : p ≤ 11 := by
      have : p ≤ (m + 1) * p := Nat.le_mul_of_pos_left p (by omega)
      omega
    have hp7 : 7 ≤ p := by
      interval_cases p <;> first | omega | exact absurd hp (by norm_num)
    exact false_of_ge_seven h11 hp hp7 hX hX1 hI1 hI hIX

theorem finCellB_alt9 {Y : Type} [Group Y] {n : ℕ} (h9 : 9 ≤ n) (h11 : n ≤ 11)
    (e : Y ≃* alternatingGroup (Fin n)) : FinCellB Y := by
  have hn5 : 5 ≤ n := by omega
  have hn6 : n ≠ 6 := by omega
  intro p hp hp2 X U I Q hX hU hQ hQI _ hI hIU hUX hIX b hb hbp
  let φ := autTransport hn5 hn6 e
  have hI1 : I.map φ.toMonoidHom ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ φ.injective]
    intro hbot
    have hQ1 : Q = ⊥ := le_bot_iff.mp (hbot ▸ hQI)
    have h4 := hQ.2
    rw [hQ1, card_bot] at h4
    omega
  refine ⟨2, hhobsAt_of_altWit hn5 hn6 e Nat.prime_two (Ne.symm hp2) b ?_⟩
  exact altWit_cell h9 h11 hp hp2 (hX.map φ.toMonoidHom) (isFourSubgroup_map φ hU) hI1
    (map_perfect φ hI) (map_le_centralizer φ hIU) (map_le_normalizer φ hUX)
    (map_le_normalizer φ hIX) ⟨b, hb, rfl⟩ ((MulEquiv.orderOf_eq φ b).trans hbp)

end FinAltB

theorem finCellB_alt {Y : Type} [Group Y] {n : ℕ} (h8 : 8 ≤ n) (h11 : n ≤ 11)
    (h : Nonempty (Y ≃* alternatingGroup (Fin n))) : FinCellB Y := by
  rcases Nat.lt_or_ge n 9 with hn | hn
  · obtain rfl : n = 8 := by omega
    exact finCellB_a8 h
  · obtain ⟨e⟩ := h
    exact FinAltB.finCellB_alt9 hn h11 e

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
