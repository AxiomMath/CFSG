module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S1
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Layer

public section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup
open scoped commutatorElement

section Local

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

theorem PA5.ub_sq (a : PA5 L t E z) : a.ub * a.ub = 1 := by
  have := pow_orderOf_eq_one a.ub
  rwa [a.ub_ord, pow_two] at this

theorem PA5.ub_ne_one (a : PA5 L t E z) : a.ub ≠ 1 := by
  intro h
  have := a.ub_ord
  rw [h, orderOf_one] at this
  omega

theorem PA5.L_comm_t (hb : PAB G L t E W z) {l : G} (hl : l ∈ L) : l * t = t * l :=
  mem_centralizer_iff.1 hb.t_cent l hl

theorem PA5.Abar_mem_L (a : PA5 L t E z) {x : G} (hx : x ∈ a.Abar) : x ∈ L := (a.Abar_le hx).1

theorem PA5.Abar_comm_u (a : PA5 L t E z) {x : G} (hx : x ∈ a.Abar) : x * a.u = a.u * x :=
  mem_centralizer_singleton_iff.1 (a.Abar_le hx).2

theorem PA5.Abar_comm_t (hb : PAB G L t E W z) (a : PA5 L t E z) {x : G} (hx : x ∈ a.Abar) :
    x * t = t * x := PA5.L_comm_t hb (PA5.Abar_mem_L a hx)

theorem PA5.Abar_comm_ub (hb : PAB G L t E W z) (a : PA5 L t E z) {x : G} (hx : x ∈ a.Abar) :
    x * a.ub = a.ub * x := by
  rcases a.ub_cases with h | h
  · rw [h]; exact PA5.Abar_comm_u a hx
  · rw [h]
    have h1 := PA5.Abar_comm_t hb a hx
    have h2 := PA5.Abar_comm_u a hx
    calc x * (t * a.u) = t * (x * a.u) := by rw [← mul_assoc, h1, mul_assoc]
      _ = t * (a.u * x) := by rw [h2]
      _ = (t * a.u) * x := by rw [mul_assoc]

theorem PA5.t_ub (a : PA5 L t E z) (hb : PAB G L t E W z) : t * a.ub = a.ub * t :=
  (PA5.comm_t_ub hb a).symm

theorem PA5.u_mem_V (hb : PAB G L t E W z) (a : PA5 L t E z) : a.u ∈ Vsub t a.ub := by
  rcases a.ub_cases with h | h
  · rw [h]; exact mem_sup_right (mem_zpowers _)
  · have : a.u = t * a.ub := by
      rw [h, ← mul_assoc, hb.t_mul_t, one_mul]
    rw [this]
    exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))

theorem PA5.cent_decomp (hb : PAB G L t E W z) (a : PA5 L t E z) {g : G} (h1 : g * t = t * g)
    (h2 : g * a.ub = a.ub * g) : ∃ v ∈ Vsub t a.ub, ∃ x ∈ a.Abar, g = v * x := by
  have hgC : g ∈ centralizer ({t} : Set G) := mem_Cen.2 h1
  rw [hb.inner] at hgC
  have hcomm : ∀ n ∈ L, ∀ m ∈ zpowers t, n * m = m * n := by
    intro n hn m hm
    obtain ⟨k, rfl⟩ := hm
    exact (Commute.zpow_right (show Commute n t from PA5.L_comm_t hb hn) k).eq
  obtain ⟨l, hl, m, hm, rfl⟩ := exists_mul_of_mem_sup hcomm hgC
  obtain ⟨k, rfl⟩ := hm
  have hubt : ∀ k : ℤ, t ^ k * a.ub = a.ub * t ^ k := fun k =>
    (Commute.zpow_left (show Commute t a.ub from PA5.t_ub a hb) k).eq
  have hlub : l * a.ub = a.ub * l := by
    have : (l * t ^ k) * a.ub = a.ub * (l * t ^ k) := h2
    have e1 : l * (a.ub * t ^ k) = (a.ub * l) * t ^ k := by
      calc l * (a.ub * t ^ k) = l * (t ^ k * a.ub) := by rw [hubt k]
        _ = (l * t ^ k) * a.ub := by rw [mul_assoc]
        _ = a.ub * (l * t ^ k) := this
        _ = (a.ub * l) * t ^ k := by rw [mul_assoc]
    have e2 : (l * a.ub) * t ^ k = (a.ub * l) * t ^ k := by rw [mul_assoc, ← e1]
    exact mul_right_cancel e2
  have hlu : l * a.u = a.u * l := by
    rcases a.ub_cases with h | h
    · rw [h] at hlub; exact hlub
    · rw [h] at hlub
      have h3 := PA5.L_comm_t hb hl
      have : t * (l * a.u) = t * (a.u * l) := by
        calc t * (l * a.u) = (t * l) * a.u := by rw [mul_assoc]
          _ = (l * t) * a.u := by rw [h3]
          _ = l * (t * a.u) := by rw [mul_assoc]
          _ = (t * a.u) * l := hlub
          _ = t * (a.u * l) := by rw [mul_assoc]
      exact mul_left_cancel this
  have hlI : l ∈ L ⊓ Cen a.u := ⟨hl, mem_Cen.2 hlu⟩
  rw [a.Abar_comp] at hlI
  have hcomm2 : ∀ n ∈ zpowers a.u, ∀ m ∈ a.Abar, n * m = m * n := by
    intro n hn m hm
    obtain ⟨i, rfl⟩ := hn
    exact ((Commute.zpow_right (show Commute m a.u from PA5.Abar_comm_u a hm) i).eq).symm
  obtain ⟨n, hn, x, hx, rfl⟩ := exists_mul_of_mem_sup hcomm2 hlI
  obtain ⟨i, rfl⟩ := hn
  refine ⟨a.u ^ i * t ^ k, mul_mem ?_ (mem_sup_left (mem_zpowers_iff.2 ⟨k, rfl⟩)), x, hx, ?_⟩
  · exact (zpowers_le.2 (PA5.u_mem_V hb a)) (mem_zpowers_iff.2 ⟨i, rfl⟩)
  · have hx1 : x * t ^ k = t ^ k * x :=
      (Commute.zpow_right (show Commute x t from PA5.Abar_comm_t hb a hx) k).eq
    calc a.u ^ i * x * t ^ k = a.u ^ i * (x * t ^ k) := by rw [mul_assoc]
      _ = a.u ^ i * (t ^ k * x) := by rw [hx1]
      _ = a.u ^ i * t ^ k * x := by rw [mul_assoc]

theorem derivedIn_mem_of_commutator {A : Subgroup G} {x x' : G} (hx : x ∈ A) (hx' : x' ∈ A) :
    ⁅x, x'⁆ ∈ derivedIn A :=
  ⟨⁅(⟨x, hx⟩ : ↥A), (⟨x', hx'⟩ : ↥A)⁆, by
    rw [_root_.commutator_def]
    exact Subgroup.commutator_mem_commutator (mem_top _) (mem_top _), rfl⟩

theorem PA5.perfect_le_J (hb : PAB G L t E W z) (a : PA5 L t E z) (Q : Subgroup G)
    (hQt : ∀ q ∈ Q, q * t = t * q) (hQu : ∀ q ∈ Q, q * a.ub = a.ub * q)
    (hQ : ⁅Q, Q⁆ = Q) : Q ≤ derivedIn a.Abar := by
  rw [← hQ]
  refine Subgroup.commutator_le.mpr fun q hq q' hq' => ?_
  obtain ⟨v, hv, x, hx, rfl⟩ := PA5.cent_decomp hb a (hQt q hq) (hQu q hq)
  obtain ⟨v', hv', x', hx', rfl⟩ := PA5.cent_decomp hb a (hQt q' hq') (hQu q' hq')
  have hcx : ∀ y ∈ Vsub t a.ub, ∀ x ∈ a.Abar, y * x = x * y := fun y hy x hx =>
    (commute_Vsub (PA5.Abar_comm_t hb a hx) (PA5.Abar_comm_ub hb a hx) y hy).symm
  rw [comm_mul_mul (hcx v hv x hx) (hcx v hv x' hx') (hcx v' hv' x hx) (hcx v' hv' x' hx')]
  have h1 : ⁅v, v'⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact Vsub_comm (PA5.t_ub a hb) hv hv'
  rw [h1, one_mul]
  exact derivedIn_mem_of_commutator hx hx'

theorem PA5.cent_t_J (hb : PAB G L t E W z) (a : PA5 L t E z) {g : G} (h1 : g * t = t * g)
    (h2 : ∀ j ∈ derivedIn a.Abar, g * j = j * g) : g ∈ Vsub t a.ub := by
  have hgC : g ∈ centralizer ({t} : Set G) := mem_Cen.2 h1
  rw [hb.inner] at hgC
  have hcomm : ∀ n ∈ L, ∀ m ∈ zpowers t, n * m = m * n := by
    intro n hn m hm
    obtain ⟨k, rfl⟩ := hm
    exact (Commute.zpow_right (show Commute n t from PA5.L_comm_t hb hn) k).eq
  obtain ⟨l, hl, m, hm, rfl⟩ := exists_mul_of_mem_sup hcomm hgC
  obtain ⟨k, rfl⟩ := hm
  have htJ : ∀ j ∈ derivedIn a.Abar, t ^ k * j = j * t ^ k := fun j hj =>
    (Commute.zpow_left (show Commute t j from (PA5.L_comm_t hb
      (PA5.Abar_mem_L a (derivedIn_le _ hj))).symm) k).eq
  have hlJ : l ∈ centralizer ((derivedIn a.Abar : Subgroup G) : Set G) := by
    rw [mem_centralizer_iff]
    intro j hj
    have := h2 j hj
    calc j * l = (j * l * t ^ k) * (t ^ k)⁻¹ := by group
      _ = (l * t ^ k * j) * (t ^ k)⁻¹ := by
        have e : j * l * t ^ k = l * t ^ k * j := by
          calc j * l * t ^ k = j * (l * t ^ k) := by rw [mul_assoc]
            _ = (l * t ^ k) * j := this.symm
        rw [e]
      _ = l * (t ^ k * j) * (t ^ k)⁻¹ := by rw [mul_assoc l]
      _ = l * (j * t ^ k) * (t ^ k)⁻¹ := by rw [htJ j hj]
      _ = l * j := by group
  have hlI : l ∈ L ⊓ centralizer ((derivedIn a.Abar : Subgroup G) : Set G) := ⟨hl, hlJ⟩
  rw [a.C_L_J] at hlI
  obtain ⟨i, hi⟩ := hlI
  have hi' : a.u ^ i = l := hi
  rw [← hi']
  refine mul_mem ?_ (mem_sup_left (mem_zpowers_iff.2 ⟨k, rfl⟩))
  exact (zpowers_le.2 (PA5.u_mem_V hb a)) (mem_zpowers_iff.2 ⟨i, rfl⟩)

end Local

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
