module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp23ThreeHyp

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

namespace Perp23

namespace Three

section Alpha

theorem eq_one_of_sq_of_mem_odd {G : Type} [Group G] [Finite G] {O : Subgroup G}
    (hO : Odd (Nat.card O)) {w : G} (hw : w ∈ O) (hw2 : w * w = 1) : w = 1 := by
  have hdvd : orderOf w ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hw
  have h2 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hw2)
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
  · exact orderOf_eq_one_iff.mp h
  · exfalso
    rw [h] at hdvd
    exact (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr hdvd)


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  (d : Data r n Y R S t)

namespace Data

include d

@[expose] def alpha : Subgroup Y := alphaOf (Subgroup.closure ({d.D.u, t} : Set Y))

theorem bGrp_comm' {x y : Y} (hx : x ∈ bGrp d.D) (hy : y ∈ bGrp d.D) : x * y = y * x :=
  bGrp_comm d.D d.hc x hx y hy

theorem bGrp_le_centralizer {x : Y} (hx : x ∈ bGrp d.D) :
    bGrp d.D ≤ Subgroup.centralizer ({x} : Set Y) := fun y hy =>
  Subgroup.mem_centralizer_singleton_iff.mpr (d.bGrp_comm' hy hx)

theorem isElemAbelian2_pair {a b : Y} (ha : a ∈ bGrp d.D) (hb : b ∈ bGrp d.D) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hab : a ≠ b) :
    IsElemAbelian2 (Subgroup.closure ({a, b} : Set Y)) 2 :=
  T7A.isElemAbelian2_closure_pair (bGrp_sq d.D d.hc a ha) (bGrp_sq d.D d.hc b hb) ha1 hb1 hab
    (d.bGrp_comm' ha hb)

theorem pair_le {a b : Y} (ha : a ∈ bGrp d.D) (hb : b ∈ bGrp d.D) :
    Subgroup.closure ({a, b} : Set Y) ≤ bGrp d.D := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact ha
  · exact hb

variable (hH : Hyp51 (bGrp d.D))

include hH

theorem alpha_const (he1 : d.D.ce ≠ 1) :
    ∀ A : Subgroup Y, A ≤ bGrp d.D → IsElemAbelian2 A 2 → alphaOf A = d.alpha := by
  have hut := d.isElemAbelian2_pair (u_mem_bGrp d.D d.hc) (t_mem_bGrp d.D) (d.u_ne_one he1)
    (t_ne_one d.D) d.u_ne_t
  exact (lemma54_odd_and_eq hH (d.pair_le (u_mem_bGrp d.D d.hc) (t_mem_bGrp d.D)) hut).2

theorem alpha_odd (he1 : d.D.ce ≠ 1) : Odd (Nat.card d.alpha) := by
  have hut := d.isElemAbelian2_pair (u_mem_bGrp d.D d.hc) (t_mem_bGrp d.D) (d.u_ne_one he1)
    (t_ne_one d.D) d.u_ne_t
  exact (lemma54_odd_and_eq hH (d.pair_le (u_mem_bGrp d.D d.hc) (t_mem_bGrp d.D)) hut).1

omit hH d in
theorem mem_normalizer_alphaOf_of_mem_normalizer {G : Type} [Group G] {A : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) :
    g ∈ Subgroup.normalizer (alphaOf A : Set G) := by
  rw [mem_normalizer_iff_conjSub_eq] at hg ⊢
  have := alphaOf_conjSub g A
  rw [hg] at this
  exact this.symm

omit hH in
theorem alphaOf_pair_comm {a b : Y} : alphaOf (Subgroup.closure ({a, b} : Set Y)) =
    alphaOf (Subgroup.closure ({b, a} : Set Y)) := by
  rw [Set.pair_comm]

theorem oddCore_t_le (he1 : d.D.ce ≠ 1) :
    oddCoreOf (Subgroup.centralizer ({t} : Set Y)) ≤ Subgroup.normalizer (d.alpha : Set Y) :=
  T7A.oddCore_le_normalizer_alpha (u := d.D.u) (z := t) (isElemAbelian_bGrp d.D d.hc)
    (card_bGrp d.D d.hc he1) (d.bGrp_le_centralizer (t_mem_bGrp d.D)) (d.alpha_const hH he1)

theorem oddCore_u_le (he1 : d.D.ce ≠ 1) :
    oddCoreOf (Subgroup.centralizer ({d.D.u} : Set Y)) ≤ Subgroup.normalizer (d.alpha : Set Y) := by
  have h := T7A.oddCore_le_normalizer_alpha (u := t) (z := d.D.u) (isElemAbelian_bGrp d.D d.hc)
    (card_bGrp d.D d.hc he1) (d.bGrp_le_centralizer (u_mem_bGrp d.D d.hc))
    (fun A hA hA2 => (d.alpha_const hH he1 A hA hA2).trans (d.alphaOf_pair_comm))
  have e : alphaOf (Subgroup.closure ({t, d.D.u} : Set Y)) = d.alpha :=
    (d.alphaOf_pair_comm).symm
  rwa [e] at h

theorem alpha_ju (he1 : d.D.ce ≠ 1) :
    alphaOf (Subgroup.closure ({d.D.F.j, d.D.u} : Set Y)) = d.alpha :=
  d.alpha_const hH he1 _ (d.pair_le (j_mem_bGrp d.D) (u_mem_bGrp d.D d.hc))
    (d.isElemAbelian2_pair (j_mem_bGrp d.D) (u_mem_bGrp d.D d.hc) (j_ne_one d.D) (d.u_ne_one he1)
      (d.j_ne_u he1))

theorem centralizer_u_le_normalizer (he1 : d.D.ce ≠ 1)
    (hZ : ∀ ℓ ∈ Subgroup.centralizer ({d.D.u} : Set Y),
      d.D.F.j * ℓ * d.D.F.j⁻¹ * ℓ⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({d.D.u} : Set Y))) :
    Subgroup.centralizer ({d.D.u} : Set Y) ≤ Subgroup.normalizer (d.alpha : Set Y) := by
  intro ℓ hℓ
  have hO : oddCoreOf (Subgroup.centralizer ({d.D.u} : Set Y)) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({d.D.F.j, d.D.u} : Set Y)) : Set Y) := by
    rw [d.alpha_ju hH he1]
    exact d.oddCore_u_le hH he1
  have := T7B.mem_normalizer_alphaOf_of_commutator (t := d.D.F.j) (z := d.D.u) (ℓ := ℓ) d.D.j_sq
    (d.bGrp_comm' (u_mem_bGrp d.D d.hc) (j_mem_bGrp d.D)) hℓ (hZ ℓ hℓ) hO
  rwa [d.alpha_ju hH he1] at this

omit hH in
theorem r_mem_normalizer_alpha :
    d.D.F.ρ.r ∈ Subgroup.normalizer (d.alpha : Set Y) := by
  apply mem_normalizer_alphaOf_of_mem_normalizer (A := Subgroup.closure ({d.D.u, t} : Set Y))
  refine Two.mem_normalizer_closure_pair ?_ ?_
  · rw [d.D.r_u d.hc]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  · have hrt : d.D.F.ρ.r * t * d.D.F.ρ.r⁻¹ = t := by rw [d.D.r_t]; group
    rw [hrt]
    exact Subgroup.subset_closure (by simp)

theorem centralizer_t_le_normalizer (he1 : d.D.ce ≠ 1)
    (hStar : ∀ ℓ ∈ Subgroup.centralizer ({t} : Set Y),
      d.D.u * ℓ * d.D.u⁻¹ * ℓ⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)) ∨
      d.D.u * (d.D.F.ρ.r⁻¹ * ℓ) * d.D.u⁻¹ * (d.D.F.ρ.r⁻¹ * ℓ)⁻¹ ∈
        oddCoreOf (Subgroup.centralizer ({t} : Set Y))) :
    Subgroup.centralizer ({t} : Set Y) ≤ Subgroup.normalizer (d.alpha : Set Y) := by
  have key : ∀ ℓ ∈ Subgroup.centralizer ({t} : Set Y),
      d.D.u * ℓ * d.D.u⁻¹ * ℓ⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)) →
        ℓ ∈ Subgroup.normalizer (d.alpha : Set Y) := by
    intro ℓ hℓ hcomm
    exact T7B.mem_normalizer_alphaOf_of_commutator (t := d.D.u) (z := t) (ℓ := ℓ)
      (u_mul_self d.D d.hc) (d.bGrp_comm' (t_mem_bGrp d.D) (u_mem_bGrp d.D d.hc)) hℓ hcomm
      (d.oddCore_t_le hH he1)
  intro ℓ hℓ
  rcases hStar ℓ hℓ with h | h
  · exact key ℓ hℓ h
  · have hrC : d.D.F.ρ.r ∈ Subgroup.centralizer ({t} : Set Y) :=
      Subgroup.mem_centralizer_singleton_iff.mpr d.D.r_t
    have hℓ' : d.D.F.ρ.r⁻¹ * ℓ ∈ Subgroup.centralizer ({t} : Set Y) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hrC) hℓ
    have h1 := key _ hℓ' h
    have h2 := Subgroup.mul_mem _ d.r_mem_normalizer_alpha h1
    simpa using h2

theorem alpha_eq_bot (he1 : d.D.ce ≠ 1)
    (hZ : ∀ ℓ ∈ Subgroup.centralizer ({d.D.u} : Set Y),
      d.D.F.j * ℓ * d.D.F.j⁻¹ * ℓ⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({d.D.u} : Set Y)))
    (hStar : ∀ ℓ ∈ Subgroup.centralizer ({t} : Set Y),
      d.D.u * ℓ * d.D.u⁻¹ * ℓ⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)) ∨
      d.D.u * (d.D.F.ρ.r⁻¹ * ℓ) * d.D.u⁻¹ * (d.D.F.ρ.r⁻¹ * ℓ)⁻¹ ∈
        oddCoreOf (Subgroup.centralizer ({t} : Set Y)))
    (hG : Subgroup.centralizer ({d.D.u} : Set Y) ⊔ Subgroup.centralizer ({t} : Set Y) = ⊤) :
    d.alpha = ⊥ := by
  have hN : Subgroup.normalizer (d.alpha : Set Y) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← hG]
    exact sup_le (d.centralizer_u_le_normalizer hH he1 hZ)
      (d.centralizer_t_le_normalizer hH he1 hStar)
  have hn : d.alpha.Normal := Subgroup.normalizer_eq_top_iff.mp hN
  have hle : d.alpha ≤ classicalInvolutionOddCore Y := le_sSup ⟨hn, d.alpha_odd hH he1⟩
  rw [d.h.core.oddFree] at hle
  exact le_bot_iff.mp hle

omit hH in
theorem u_ne_ce (he1 : d.D.ce ≠ 1) : d.D.u ≠ d.D.ce := by
  intro h
  have h1 := e_mul_j d.D d.hc
  rw [← h] at h1
  have h2 : d.D.u * d.D.F.j = d.D.u * 1 := by rw [mul_one]; exact h1
  exact j_ne_one d.D (mul_left_cancel h2)

omit hH in
theorem ce_eq_u_mul_j : d.D.ce = d.D.u * d.D.F.j := by
  have h1 := e_mul_j d.D d.hc
  calc d.D.ce = (d.D.ce * d.D.F.j) * d.D.F.j⁻¹ := by group
    _ = d.D.u * d.D.F.j := by rw [h1, inv_eq_of_mul_eq_one_right d.D.j_sq]

theorem centralizer_u_le_centralizer_ce (he1 : d.D.ce ≠ 1) (hα1 : d.alpha = ⊥)
    (hZ : ∀ ℓ ∈ Subgroup.centralizer ({d.D.u} : Set Y),
      d.D.F.j * ℓ * d.D.F.j⁻¹ * ℓ⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({d.D.u} : Set Y))) :
    ∀ ℓ ∈ Subgroup.centralizer ({d.D.u} : Set Y), ℓ * d.D.ce = d.D.ce * ℓ := by
  intro ℓ hℓ
  set w : Y := d.D.F.j * ℓ * d.D.F.j⁻¹ * ℓ⁻¹ with hw
  have hwO : w ∈ oddCoreOf (Subgroup.centralizer ({d.D.u} : Set Y)) := hZ ℓ hℓ
  have hwO' : w⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({d.D.u} : Set Y)) :=
    (oddCoreOf (Subgroup.centralizer ({d.D.u} : Set Y))).inv_mem hwO
  have hwC : w⁻¹ ∈ Subgroup.centralizer ({d.D.u} : Set Y) := oddCoreIn_le _ hwO'
  have huw : w⁻¹ * d.D.u = d.D.u * w⁻¹ := Subgroup.mem_centralizer_singleton_iff.mp hwC
  have hℓu : ℓ * d.D.u = d.D.u * ℓ := Subgroup.mem_centralizer_singleton_iff.mp hℓ
  have hA2 := d.isElemAbelian2_pair (u_mem_bGrp d.D d.hc) (e_mem_bGrp d.D) (d.u_ne_one he1) he1
    (d.u_ne_ce he1)
  have hαA : alphaOf (Subgroup.closure ({d.D.u, d.D.ce} : Set Y)) = ⊥ := by
    rw [d.alpha_const hH he1 _ (d.pair_le (u_mem_bGrp d.D d.hc) (e_mem_bGrp d.D)) hA2, hα1]
  have heA : d.D.ce ∈ Subgroup.closure ({d.D.u, d.D.ce} : Set Y) :=
    Subgroup.subset_closure (by simp)
  have huA : d.D.u ∈ Subgroup.closure ({d.D.u, d.D.ce} : Set Y) :=
    Subgroup.subset_closure (by simp)
  have hcomm : ⁅w⁻¹, d.D.ce⁆ ∈ ⁅oddCoreOf (Subgroup.centralizer ({d.D.u} : Set Y)),
      Subgroup.closure ({d.D.u, d.D.ce} : Set Y)⁆ :=
    Subgroup.commutator_mem_commutator hwO' heA
  have h1 : ⁅w⁻¹, d.D.ce⁆ ∈ alphaOf (Subgroup.closure ({d.D.u, d.D.ce} : Set Y)) :=
    commutator_le_alphaOf _ huA (d.u_ne_one he1) hcomm
  rw [hαA, Subgroup.mem_bot, commutatorElement_def] at h1
  have hwe : w⁻¹ * d.D.ce = d.D.ce * w⁻¹ := by
    calc w⁻¹ * d.D.ce = (w⁻¹ * d.D.ce * (w⁻¹)⁻¹ * d.D.ce⁻¹) * (d.D.ce * w⁻¹) := by group
      _ = d.D.ce * w⁻¹ := by rw [h1, one_mul]
  have hlj : ℓ * d.D.F.j * ℓ⁻¹ = w⁻¹ * d.D.F.j := by rw [hw]; group
  have hℓu' : ℓ * d.D.u * ℓ⁻¹ = d.D.u := by rw [hℓu]; group
  have hconj : ℓ * d.D.ce * ℓ⁻¹ = w⁻¹ * d.D.ce := by
    calc ℓ * d.D.ce * ℓ⁻¹ = ℓ * (d.D.u * d.D.F.j) * ℓ⁻¹ := by rw [← ce_eq_u_mul_j d]
      _ = (ℓ * d.D.u * ℓ⁻¹) * (ℓ * d.D.F.j * ℓ⁻¹) := by group
      _ = d.D.u * (w⁻¹ * d.D.F.j) := by rw [hℓu', hlj]
      _ = (d.D.u * w⁻¹) * d.D.F.j := by group
      _ = (w⁻¹ * d.D.u) * d.D.F.j := by rw [huw]
      _ = w⁻¹ * (d.D.u * d.D.F.j) := by group
      _ = w⁻¹ * d.D.ce := by rw [← ce_eq_u_mul_j d]
  have hsq : (w⁻¹ * d.D.ce) * (w⁻¹ * d.D.ce) = 1 := by
    have h2 : (ℓ * d.D.ce * ℓ⁻¹) * (ℓ * d.D.ce * ℓ⁻¹) = 1 := by
      calc (ℓ * d.D.ce * ℓ⁻¹) * (ℓ * d.D.ce * ℓ⁻¹) = ℓ * (d.D.ce * d.D.ce) * ℓ⁻¹ := by group
        _ = 1 := by rw [ce_mul_self d.D d.hc]; group
    rwa [hconj] at h2
  have hsq' : w⁻¹ * w⁻¹ = 1 := by
    calc w⁻¹ * w⁻¹ = (w⁻¹ * d.D.ce) * (w⁻¹ * d.D.ce) := by
          calc w⁻¹ * w⁻¹ = w⁻¹ * (d.D.ce * d.D.ce) * w⁻¹ := by rw [ce_mul_self d.D d.hc]; group
            _ = w⁻¹ * d.D.ce * (d.D.ce * w⁻¹) := by group
            _ = w⁻¹ * d.D.ce * (w⁻¹ * d.D.ce) := by rw [hwe]
      _ = 1 := hsq
  have hw1 : w⁻¹ = 1 :=
    eq_one_of_sq_of_mem_odd (odd_card_oddCoreIn _) hwO' hsq'
  rw [hw1, one_mul] at hconj
  calc ℓ * d.D.ce = (ℓ * d.D.ce * ℓ⁻¹) * ℓ := by group
    _ = d.D.ce * ℓ := by rw [hconj]

theorem centralizer_t_le_centralizer_ce (he1 : d.D.ce ≠ 1) (hα1 : d.alpha = ⊥)
    (hZ : ∀ ℓ ∈ Subgroup.centralizer ({d.D.u} : Set Y),
      d.D.F.j * ℓ * d.D.F.j⁻¹ * ℓ⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({d.D.u} : Set Y)))
    (hStar : ∀ ℓ ∈ Subgroup.centralizer ({t} : Set Y),
      d.D.u * ℓ * d.D.u⁻¹ * ℓ⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)) ∨
      d.D.u * (d.D.F.ρ.r⁻¹ * ℓ) * d.D.u⁻¹ * (d.D.F.ρ.r⁻¹ * ℓ)⁻¹ ∈
        oddCoreOf (Subgroup.centralizer ({t} : Set Y))) :
    ∀ ℓ ∈ Subgroup.centralizer ({t} : Set Y), ℓ * d.D.ce = d.D.ce * ℓ := by
  have hu2 := u_mul_self d.D d.hc
  have key : ∀ ℓ ∈ Subgroup.centralizer ({t} : Set Y),
      d.D.u * ℓ * d.D.u⁻¹ * ℓ⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)) →
        ℓ * d.D.ce = d.D.ce * ℓ := by
    intro ℓ hℓ hv
    set v : Y := d.D.u * ℓ * d.D.u⁻¹ * ℓ⁻¹ with hvdef
    have hvO' : v⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)) :=
      (oddCoreOf (Subgroup.centralizer ({t} : Set Y))).inv_mem hv
    have htA : t ∈ Subgroup.closure ({d.D.u, t} : Set Y) := Subgroup.subset_closure (by simp)
    have huA : d.D.u ∈ Subgroup.closure ({d.D.u, t} : Set Y) := Subgroup.subset_closure (by simp)
    have hcomm : ⁅v⁻¹, d.D.u⁆ ∈ ⁅oddCoreOf (Subgroup.centralizer ({t} : Set Y)),
        Subgroup.closure ({d.D.u, t} : Set Y)⁆ := Subgroup.commutator_mem_commutator hvO' huA
    have h1 : ⁅v⁻¹, d.D.u⁆ ∈ alphaOf (Subgroup.closure ({d.D.u, t} : Set Y)) :=
      commutator_le_alphaOf _ htA (t_ne_one d.D) hcomm
    have hα1' : alphaOf (Subgroup.closure ({d.D.u, t} : Set Y)) = ⊥ := hα1
    rw [hα1', Subgroup.mem_bot, commutatorElement_def] at h1
    have hvu : v⁻¹ * d.D.u = d.D.u * v⁻¹ := by
      calc v⁻¹ * d.D.u = (v⁻¹ * d.D.u * (v⁻¹)⁻¹ * d.D.u⁻¹) * (d.D.u * v⁻¹) := by group
        _ = d.D.u * v⁻¹ := by rw [h1, one_mul]
    have hconj : ℓ * d.D.u * ℓ⁻¹ = v⁻¹ * d.D.u := by rw [hvdef]; group
    have hsq : (v⁻¹ * d.D.u) * (v⁻¹ * d.D.u) = 1 := by
      have h2 : (ℓ * d.D.u * ℓ⁻¹) * (ℓ * d.D.u * ℓ⁻¹) = 1 := by
        calc (ℓ * d.D.u * ℓ⁻¹) * (ℓ * d.D.u * ℓ⁻¹) = ℓ * (d.D.u * d.D.u) * ℓ⁻¹ := by group
          _ = 1 := by rw [hu2]; group
      rwa [hconj] at h2
    have hsq' : v⁻¹ * v⁻¹ = 1 := by
      calc v⁻¹ * v⁻¹ = v⁻¹ * (d.D.u * d.D.u) * v⁻¹ := by rw [hu2]; group
        _ = v⁻¹ * d.D.u * (d.D.u * v⁻¹) := by group
        _ = v⁻¹ * d.D.u * (v⁻¹ * d.D.u) := by rw [hvu]
        _ = 1 := hsq
    have hv1 : v⁻¹ = 1 := eq_one_of_sq_of_mem_odd (odd_card_oddCoreIn _) hvO' hsq'
    rw [hv1, one_mul] at hconj
    have hℓu : ℓ ∈ Subgroup.centralizer ({d.D.u} : Set Y) := by
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc ℓ * d.D.u = (ℓ * d.D.u * ℓ⁻¹) * ℓ := by group
        _ = d.D.u * ℓ := by rw [hconj]
    exact d.centralizer_u_le_centralizer_ce hH he1 hα1 hZ ℓ hℓu
  intro ℓ hℓ
  rcases hStar ℓ hℓ with h | h
  · exact key ℓ hℓ h
  · have hrC : d.D.F.ρ.r ∈ Subgroup.centralizer ({t} : Set Y) :=
      Subgroup.mem_centralizer_singleton_iff.mpr d.D.r_t
    have hℓ' : d.D.F.ρ.r⁻¹ * ℓ ∈ Subgroup.centralizer ({t} : Set Y) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hrC) hℓ
    have h1 := key _ hℓ' h
    have hr := d.D.mgrp_fix_e d.hΩ d.hW d.ctx d.D.F.ρ.r d.D.r_mem_mgrp
    calc ℓ * d.D.ce = d.D.F.ρ.r * ((d.D.F.ρ.r⁻¹ * ℓ) * d.D.ce) := by group
      _ = d.D.F.ρ.r * (d.D.ce * (d.D.F.ρ.r⁻¹ * ℓ)) := by rw [h1]
      _ = (d.D.F.ρ.r * d.D.ce) * (d.D.F.ρ.r⁻¹ * ℓ) := by group
      _ = (d.D.ce * d.D.F.ρ.r) * (d.D.F.ρ.r⁻¹ * ℓ) := by rw [hr]
      _ = d.D.ce * ℓ := by group

theorem false_of_zStar (he1 : d.D.ce ≠ 1)
    (hZ : ∀ ℓ ∈ Subgroup.centralizer ({d.D.u} : Set Y),
      d.D.F.j * ℓ * d.D.F.j⁻¹ * ℓ⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({d.D.u} : Set Y)))
    (hStar : ∀ ℓ ∈ Subgroup.centralizer ({t} : Set Y),
      d.D.u * ℓ * d.D.u⁻¹ * ℓ⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)) ∨
      d.D.u * (d.D.F.ρ.r⁻¹ * ℓ) * d.D.u⁻¹ * (d.D.F.ρ.r⁻¹ * ℓ)⁻¹ ∈
        oddCoreOf (Subgroup.centralizer ({t} : Set Y)))
    (hG : Subgroup.centralizer ({d.D.u} : Set Y) ⊔ Subgroup.centralizer ({t} : Set Y) = ⊤) :
    False := by
  have hα1 := d.alpha_eq_bot hH he1 hZ hStar hG
  have h1 := d.centralizer_u_le_centralizer_ce hH he1 hα1 hZ
  have h2 := d.centralizer_t_le_centralizer_ce hH he1 hα1 hZ hStar
  have hcen : Subgroup.centralizer ({d.D.u} : Set Y) ⊔ Subgroup.centralizer ({t} : Set Y) ≤
      Subgroup.centralizer ({d.D.ce} : Set Y) :=
    sup_le (fun ℓ hℓ => Subgroup.mem_centralizer_singleton_iff.mpr (h1 ℓ hℓ))
      (fun ℓ hℓ => Subgroup.mem_centralizer_singleton_iff.mpr (h2 ℓ hℓ))
  rw [hG] at hcen
  have hce : d.D.ce ∈ Subgroup.center Y :=
    Subgroup.mem_center_iff.mpr fun g =>
      Subgroup.mem_centralizer_singleton_iff.mp (hcen (Subgroup.mem_top g))
  rw [d.h.center_eq_bot, Subgroup.mem_bot] at hce
  exact he1 hce

end Data

end Alpha

end Three

end Perp23

end CFSG.CGT.PushingUpLit.SolKNA.R4
