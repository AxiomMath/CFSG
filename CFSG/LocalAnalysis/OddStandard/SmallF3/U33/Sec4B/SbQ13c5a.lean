module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13a0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private lemma q13c_invCent_comm_twoCore (h : Q13Om t L S x₁ x₂ lam rho tau om) {a p : G}
    (ha : a ∈ invCent t) (hp : p ∈ twoCore t) : a * p = p * a := by
  have hpt : p ∈ zpowers t := by rwa [h.c11.l43] at hp
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hpt
  have hat : a * t = t * a := S4A.mem_invCent_iff.mp ha
  rw [← hk]
  exact Commute.zpow_right (show Commute a t from hat) k

private lemma q13c_twoCore_le_cent_tau (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    twoCore t ≤ centralizer ({tau} : Set G) := by
  intro p hp
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hpt : p ∈ zpowers t := by rwa [h.c11.l43] at hp
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hpt
  rw [← hk]
  exact Commute.zpow_left (q13a_t_comm h).2.2 k

private lemma q13c_card_cent_L_tau (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥(L ⊓ centralizer ({tau} : Set G)) = 24 := by
  obtain ⟨φ⟩ := h.c11.perm_four
  rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  norm_num [Nat.factorial]

theorem q13c_card_PL_cent_tau_le (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥((twoCore t ⊔ L) ⊓ centralizer ({tau} : Set G)) ≤ 48 := by
  have hP : twoCore t = zpowers t := h.c11.l43
  have hcommPL : ∀ a ∈ twoCore t, ∀ b ∈ L, a * b = b * a := S4A.twoCore_commute h.c11.hyp
  have hPcard : Nat.card (twoCore t) = 2 := by
    rw [hP, Nat.card_zpowers, h.c11.hyp.ord_t]
  have hLCcard := q13c_card_cent_L_tau h
  have hPcent := q13c_twoCore_le_cent_tau h
  have hnorm : ∀ k ∈ L, ∀ p ∈ twoCore t, k * p * k⁻¹ ∈ twoCore t := by
    intro k hk p hp
    have h1 : k * p = p * k := (hcommPL p hp k hk).symm
    have h2 : k * p * k⁻¹ = p := by rw [h1]; group
    rwa [h2]
  let f : ↥(twoCore t) × ↥(L ⊓ centralizer ({tau} : Set G)) →
      ↥((twoCore t ⊔ L) ⊓ centralizer ({tau} : Set G)) := fun q =>
    ⟨(q.1 : G) * (q.2 : G),
      Subgroup.mem_inf.mpr
        ⟨Subgroup.mul_mem_sup q.1.2 q.2.2.1, by
          rw [Subgroup.mem_centralizer_singleton_iff]
          have hq1 : (q.1 : G) * tau = tau * (q.1 : G) :=
            Subgroup.mem_centralizer_singleton_iff.mp (hPcent q.1.2)
          have hq2 : (q.2 : G) * tau = tau * (q.2 : G) :=
            Subgroup.mem_centralizer_singleton_iff.mp q.2.2.2
          calc (q.1 : G) * (q.2 : G) * tau = (q.1 : G) * ((q.2 : G) * tau) := by group
            _ = (q.1 : G) * (tau * (q.2 : G)) := by rw [hq2]
            _ = (q.1 : G) * tau * (q.2 : G) := by group
            _ = tau * (q.1 : G) * (q.2 : G) := by rw [hq1]
            _ = tau * ((q.1 : G) * (q.2 : G)) := by group⟩⟩
  have hsurj : Function.Surjective f := by
    intro x
    have hxF : (x : G) ∈ twoCore t ⊔ L := (Subgroup.mem_inf.mp x.2).1
    have hxC : (x : G) ∈ centralizer ({tau} : Set G) := (Subgroup.mem_inf.mp x.2).2
    obtain ⟨p, hpP, l, hlL, hx⟩ :=
      (mem_sup_iff_of_normalizes (H := twoCore t) (K := L) hnorm).mp hxF
    have hpC : p * tau = tau * p := Subgroup.mem_centralizer_singleton_iff.mp (hPcent hpP)
    have hxC' : (x : G) * tau = tau * (x : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp hxC
    have hlC : l * tau = tau * l := by
      have hl : l = p⁻¹ * (x : G) := by rw [hx]; group
      rw [hl]
      have hpC' : p⁻¹ * tau = tau * p⁻¹ := by
        calc p⁻¹ * tau = p⁻¹ * (tau * p) * p⁻¹ := by group
          _ = p⁻¹ * (p * tau) * p⁻¹ := by rw [← hpC]
          _ = tau * p⁻¹ := by group
      calc p⁻¹ * (x : G) * tau = p⁻¹ * ((x : G) * tau) := by group
        _ = p⁻¹ * (tau * (x : G)) := by rw [hxC']
        _ = p⁻¹ * tau * (x : G) := by group
        _ = tau * p⁻¹ * (x : G) := by rw [hpC']
        _ = tau * (p⁻¹ * (x : G)) := by group
    refine ⟨(⟨p, hpP⟩, ⟨l, hlL, Subgroup.mem_centralizer_singleton_iff.mpr hlC⟩), ?_⟩
    apply Subtype.ext
    exact hx.symm
  calc Nat.card ↥((twoCore t ⊔ L) ⊓ centralizer ({tau} : Set G))
      ≤ Nat.card (↥(twoCore t) × ↥(L ⊓ centralizer ({tau} : Set G))) :=
        Nat.card_le_card_of_surjective f hsurj
    _ = Nat.card (twoCore t) * Nat.card ↥(L ⊓ centralizer ({tau} : Set G)) := Nat.card_prod _ _
    _ = 2 * 24 := by rw [hPcard, hLCcard]
    _ = 48 := by norm_num

theorem q13c_card_cent_tau_le (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥(invCent t ⊓ centralizer ({tau} : Set G)) ≤ 96 := by
  have h1 := card_le_two_mul_card_inf (A := invCent t)
    (B := invCent t ⊓ centralizer ({tau} : Set G)) (Q := twoCore t ⊔ L)
    inf_le_left h.c11.relIndex_two
  have hle : Nat.card ↥((invCent t ⊓ centralizer ({tau} : Set G)) ⊓ (twoCore t ⊔ L)) ≤ 48 := by
    refine (Subgroup.card_le_of_le ?_).trans (q13c_card_PL_cent_tau_le h)
    intro x hx
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).2, (Subgroup.mem_inf.mp hx).1.2⟩
  calc Nat.card ↥(invCent t ⊓ centralizer ({tau} : Set G))
      ≤ 2 * Nat.card ↥((invCent t ⊓ centralizer ({tau} : Set G)) ⊓ (twoCore t ⊔ L)) := h1
    _ ≤ 2 * 48 := Nat.mul_le_mul_left 2 hle
    _ = 96 := by norm_num

private lemma q13c_conj_mem_cent_tau (h : Q13Om t L S x₁ x₂ lam rho tau om) {c p u x : G}
    (hc : c ∈ invCent t) (hp : p ∈ twoCore t) (hcu : c * u * c⁻¹ = p * tau)
    (hx : x ∈ invCent t ⊓ centralizer ({u} : Set G)) :
    c * x * c⁻¹ ∈ invCent t ⊓ centralizer ({tau} : Set G) := by
  have hxH : x ∈ invCent t := (Subgroup.mem_inf.mp hx).1
  have hxC : x ∈ centralizer ({u} : Set G) := (Subgroup.mem_inf.mp hx).2
  have hxu : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
  refine Subgroup.mem_inf.mpr
    ⟨(invCent t).mul_mem ((invCent t).mul_mem hc hxH) ((invCent t).inv_mem hc), ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hy_cu : (c * x * c⁻¹) * (c * u * c⁻¹) = (c * u * c⁻¹) * (c * x * c⁻¹) := by
    calc c * x * c⁻¹ * (c * u * c⁻¹) = c * (x * u) * c⁻¹ := by group
      _ = c * (u * x) * c⁻¹ := by rw [hxu]
      _ = (c * u * c⁻¹) * (c * x * c⁻¹) := by group
  have hy_p : (c * x * c⁻¹) * p = p * (c * x * c⁻¹) := by
    have h1 : c * p = p * c := q13c_invCent_comm_twoCore h hc hp
    have h2 : x * p = p * x := q13c_invCent_comm_twoCore h hxH hp
    have h3 : c⁻¹ * p = p * c⁻¹ := q13c_invCent_comm_twoCore h ((invCent t).inv_mem hc) hp
    calc c * x * c⁻¹ * p = c * x * (c⁻¹ * p) := by group
      _ = c * x * (p * c⁻¹) := by rw [h3]
      _ = c * (x * p) * c⁻¹ := by group
      _ = c * (p * x) * c⁻¹ := by rw [h2]
      _ = c * p * x * c⁻¹ := by group
      _ = p * c * x * c⁻¹ := by rw [h1]
      _ = p * (c * x * c⁻¹) := by group
  have h1 : (c * x * c⁻¹) * (p * tau) = (p * tau) * (c * x * c⁻¹) := by
    rw [← hcu]; exact hy_cu
  have h2 : p * ((c * x * c⁻¹) * tau) = p * (tau * (c * x * c⁻¹)) := by
    calc p * ((c * x * c⁻¹) * tau) = (p * (c * x * c⁻¹)) * tau := by group
      _ = ((c * x * c⁻¹) * p) * tau := by rw [hy_p]
      _ = (c * x * c⁻¹) * (p * tau) := by group
      _ = (p * tau) * (c * x * c⁻¹) := h1
      _ = p * (tau * (c * x * c⁻¹)) := by group
  exact mul_left_cancel h2

theorem q13c_card_cent_outer (h : Q13Om t L S x₁ x₂ lam rho tau om) {u : G}
    (hu : u ∈ invCent t) (hu2 : u * u = 1) (hout : u ∉ twoCore t ⊔ L) :
    Nat.card ↥(invCent t ⊓ centralizer ({u} : Set G)) ≤ 96 := by
  have hu_sq : u ^ 2 ∈ twoCore t := by
    rw [pow_two, hu2]
    exact (twoCore t).one_mem
  obtain ⟨c, hc, p, hp, hcu⟩ := h.c11.invol_outer u hu hout hu_sq
  let φ : ↥(invCent t ⊓ centralizer ({u} : Set G)) →
      ↥(invCent t ⊓ centralizer ({tau} : Set G)) :=
    fun x => ⟨c * (x : G) * c⁻¹, q13c_conj_mem_cent_tau h hc hp hcu x.2⟩
  have hinj : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    exact mul_left_cancel (mul_right_cancel (congrArg Subtype.val hab))
  calc Nat.card ↥(invCent t ⊓ centralizer ({u} : Set G))
      ≤ Nat.card ↥(invCent t ⊓ centralizer ({tau} : Set G)) :=
        Nat.card_le_card_of_injective φ hinj
    _ ≤ 96 := q13c_card_cent_tau_le h

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
