module

public import CFSG.GH74.Generic.BProg.B3.KG531Crit
public import CFSG.GH74.Generic.S45.LEvSporJ2Spec
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvSpor
public import CFSG.GH74.Orders.LieType
public import CFSG.GH74.Orders.Sporadic
public import CFSG.Sporadic.Mathieu.M11

public section

namespace CFSG.GH74.Generic.BProg.B3

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped MatrixGroups

namespace KG531Ord

theorem exists_mem_dvd_of_prime_dvd_prod {r : ℕ} (hr : r.Prime) :
    ∀ l : List ℕ, r ∣ l.prod → ∃ q ∈ l, r ∣ q
  | [], h => by
    rw [List.prod_nil] at h
    exact absurd (Nat.le_of_dvd one_pos h) (by have := hr.two_le; omega)
  | q :: l, h => by
    rw [List.prod_cons] at h
    rcases (Nat.Prime.dvd_mul hr).1 h with h | h
    · exact ⟨q, List.mem_cons_self, h⟩
    · obtain ⟨q', hq', hd⟩ := exists_mem_dvd_of_prime_dvd_prod hr l h
      exact ⟨q', List.mem_cons_of_mem _ hq', hd⟩

theorem hr_of_factors {N : ℕ} (l : List ℕ) (hl : l.prod = N) (hpr : ∀ q ∈ l, q.Prime)
    (hcheck : ∀ q ∈ l, 5 ≤ q → q ^ 2 ∣ N →
      ¬ q ^ 4 ∣ N ∧ ¬ (q * (q ^ 2 - 1) / 2) * (q * (q ^ 2 - 1)) ∣ N) :
    ∀ r : ℕ, r.Prime → 5 ≤ r → r ^ 2 ∣ N →
      ¬ r ^ 4 ∣ N ∧ ¬ (r * (r ^ 2 - 1) / 2) * (r * (r ^ 2 - 1)) ∣ N := by
  intro r hr hr5 hr2
  have hrN : r ∣ l.prod := hl ▸ (dvd_pow_self r two_ne_zero).trans hr2
  obtain ⟨q, hq, hrq⟩ := exists_mem_dvd_of_prime_dvd_prod hr l hrN
  have hrq' : r = q := (Nat.prime_dvd_prime_iff_eq hr (hpr q hq)).1 hrq
  subst hrq'
  exact hcheck r hq hr5 hr2

theorem le_expr {p f : ℕ} (h5 : 5 ≤ p ^ f) :
    7200 ≤ (p ^ f * (p ^ (2 * f) - 1) / 2) * (p ^ f * (p ^ (2 * f) - 1)) := by
  have hpow : p ^ (2 * f) = (p ^ f) ^ 2 := by rw [← pow_mul, mul_comm]
  rw [hpow]
  generalize p ^ f = q at h5 ⊢
  have h1 : 24 ≤ q ^ 2 - 1 := by
    have := Nat.pow_le_pow_left h5 2
    omega
  have h2 : 120 ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul h5 h1
  have h3 : 60 ≤ q * (q ^ 2 - 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
  exact Nat.mul_le_mul h3 h2

end KG531Ord

theorem KG531Cfg.false_of_order {S : Type} [Group S] {t : S} {B₁ B₂ : Subgroup S} {p f : ℕ}
    (h : KG531Cfg t B₁ B₂ p f) {N : ℕ} (hS : Nat.card S = N) (l : List ℕ) (hl : l.prod = N)
    (hpr : ∀ q ∈ l, q.Prime) (h9 : ¬ 259200 ∣ N) (h27 : ¬ 3 ^ 6 ∣ N)
    (hcheck : ∀ q ∈ l, 5 ≤ q → q ^ 2 ∣ N →
      ¬ q ^ 4 ∣ N ∧ ¬ (q * (q ^ 2 - 1) / 2) * (q * (q ^ 2 - 1)) ∣ N) : False := by
  have hd : (p ^ f * (p ^ (2 * f) - 1) / 2) * (p ^ f * (p ^ (2 * f) - 1)) ∣ N := by
    rw [← hS]
    exact h.card_dvd.trans (Subgroup.card_subgroup_dvd_card _)
  exact not_dvd_of_card h9 h27 (KG531Ord.hr_of_factors l hl hpr hcheck) h.prime h.odd h.five hd

theorem KG531Cfg.false_of_cent_card_lt {S : Type} [Group S] {t : S} {B₁ B₂ : Subgroup S}
    {p f : ℕ} (h : KG531Cfg t B₁ B₂ p f) {N : ℕ}
    (hN : Nat.card ↥(centralizer ({t} : Set S)) = N) (hN0 : 0 < N) (hN7 : N < 7200) : False := by
  have hd := h.card_dvd
  rw [hN] at hd
  have h1 := Nat.le_of_dvd hN0 hd
  have h2 := KG531Ord.le_expr h.five
  omega

theorem kg531_m11 :
    KG531Empty (fun X _ => NativeSporadic.IsSporadic X .M11) := by
  intro S _ _ hS hnab hSp t B₁ B₂ p f h
  exact h.false_of_order (N := 7920)
    (CFSG.GH74.card_eq_of_isSporadic (s := .M11) CFSG.Sporadic.Mathieu.card_M11 hSp)
    [2, 2, 2, 2, 3, 3, 5, 11] (by decide) (by decide) (by decide) (by decide) (by decide)

theorem kg531_m12 :
    KG531Empty (fun X _ => NativeSporadic.IsSporadic X .M12) := by
  intro S _ _ hS hnab hSp t B₁ B₂ p f h
  exact h.false_of_order (N := 95040)
    ((CFSG.GH74.card_of_isSporadic_M12 hSp).trans (by norm_num))
    [2, 2, 2, 2, 2, 2, 3, 3, 3, 5, 11] (by decide) (by decide) (by decide) (by decide) (by decide)

theorem kg531_m22 :
    KG531Empty (fun X _ => NativeSporadic.IsSporadic X .M22) := by
  intro S _ _ hS hnab hSp t B₁ B₂ p f h
  exact h.false_of_order (N := 443520)
    ((CFSG.GH74.card_of_isSporadic_M22 hSp).trans (by norm_num))
    [2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 7, 11] (by decide) (by decide) (by decide) (by decide)
    (by decide)

theorem kg531_m23 :
    KG531Empty (fun X _ => NativeSporadic.IsSporadic X .M23) := by
  intro S _ _ hS hnab hSp t B₁ B₂ p f h
  exact h.false_of_order (N := 10200960)
    ((CFSG.GH74.card_of_isSporadic_M23 hSp).trans (by norm_num))
    [2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 7, 11, 23] (by decide) (by decide) (by decide) (by decide)
    (by decide)

theorem kg531_j1 :
    KG531Empty (fun X _ => NativeSporadic.IsSporadic X .J1) := by
  intro S _ _ hS hnab hSp t B₁ B₂ p f h
  exact h.false_of_order (N := 175560)
    ((CFSG.GH74.card_of_isSporadic_J1 hSp).trans (by norm_num))
    [2, 2, 2, 3, 5, 7, 11, 19] (by decide) (by decide) (by decide) (by decide) (by decide)

theorem kg531_j3 :
    KG531Empty (fun X _ => NativeSporadic.IsSporadic X .J3) := by
  intro S _ _ hS hnab hSp t B₁ B₂ p f h
  exact h.false_of_order (N := 50232960)
    ((CFSG.GH74.card_of_isSporadic_J3 hSp).trans (by norm_num))
    [2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 5, 17, 19] (by decide) (by decide) (by decide)
    (by decide) (by decide)

theorem kg531_l28 : KG531Empty (fun X _ => LieModel X .PSL 2 2 3) := by
  intro S _ _ hS hnab hL t B₁ B₂ p f h
  have hc := CFSG.GH74.card_of_lieModel_PSL (n := 2) (by norm_num) hL
  exact h.false_of_order (N := 504) (hc.trans (by decide)) [2, 2, 2, 3, 3, 7] (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem kg531_l216 : KG531Empty (fun X _ => LieModel X .PSL 2 2 4) := by
  intro S _ _ hS hnab hL t B₁ B₂ p f h
  have hc := CFSG.GH74.card_of_lieModel_PSL (n := 2) (by norm_num) hL
  exact h.false_of_order (N := 4080) (hc.trans (by decide)) [2, 2, 2, 2, 3, 5, 17] (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem kg531_l34 : KG531Empty (fun X _ => LieModel X .PSL 3 2 2) := by
  intro S _ _ hS hnab hL t B₁ B₂ p f h
  have hc := CFSG.GH74.card_of_lieModel_PSL (n := 3) (by norm_num) hL
  exact h.false_of_order (N := 20160) (hc.trans (by decide)) [2, 2, 2, 2, 2, 2, 3, 3, 5, 7]
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem kg531_u34 : KG531Empty (fun X _ => LieModel X .PSU 3 2 2) := by
  intro S _ _ hS hnab hL t B₁ B₂ p f h
  have hc := CFSG.GH74.Generic.S1.kl5_card_mul_gcd_psu_three
    (CFSG.GH74.statedClassicalModel_of_lieModel (by norm_num) hL)
  exact h.false_of_order (N := 62400) (by norm_num at hc; exact hc)
    [2, 2, 2, 2, 2, 2, 3, 5, 5, 13] (by decide) (by decide) (by decide) (by decide)
    (by decide)

theorem kg531_sz8 :
    KG531Empty (fun X _ => LieModel X .twistedB2 0 2 3) := by
  intro S _ _ hS hnab hL t B₁ B₂ p f h
  have hc := CFSG.GH74.card_of_lieModel_twistedB2 hL
  exact h.false_of_order (N := 29120) (hc.trans (by decide)) [2, 2, 2, 2, 2, 2, 5, 7, 13]
    (by decide) (by decide) (by decide) (by decide) (by decide)

namespace KG531Ord

open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore CFSG.GH74.Generic.S45.EvSpor
  CFSG.GH74.GLS.IVK in
theorem card_centralizer_j2
    {S : Type} [Group S] (hS : NativeSporadic.IsSporadic S .J2) {t : S} (ht : orderOf t = 2) :
    Nat.card ↥(centralizer ({t} : Set S)) = 1920 ∨
      Nat.card ↥(centralizer ({t} : Set S)) = 240 := by
  obtain ⟨e⟩ := hS
  have e' : S ≃* NativeSporadic.J2 := e
  let θ : S ≃* ↥j2P := e'.trans j2PermEquiv
  have hord : orderOf ((θ t : ↥j2P) : Equiv.Perm (Fin 315)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact ht
  rw [GHInv.card_centralizer_eq_centralizerIn j2P θ t]
  rcases j2_cover _ (θ t).2 hord with ⟨g, hg, hgt⟩ | ⟨g, hg, hgt⟩
  · left
    rw [GHInv.card_centralizerIn_eq_of_mem_conjClass j2P (t := tp 315 j2Row2A.rep) ⟨g, hg, hgt⟩]
    exact ((j2_rows_spec.1 j2Row2A j2Row2A_mem).2.2.2.2).trans j2Row2A_centOrder
  · right
    rw [GHInv.card_centralizerIn_eq_of_mem_conjClass j2P (t := tp 315 j2Row2B.rep) ⟨g, hg, hgt⟩]
    exact ((j2_rows_spec.1 j2Row2B j2Row2B_mem).2.2.2.2).trans j2Row2B_centOrder

end KG531Ord

theorem kg531_j2 :
    KG531Empty (fun X _ => NativeSporadic.IsSporadic X .J2) := by
  intro S _ _ hS hnab hSJ t B₁ B₂ p f h
  rcases KG531Ord.card_centralizer_j2 hSJ h.t_ord with hc | hc
  · exact h.false_of_cent_card_lt hc (by norm_num) (by norm_num)
  · exact h.false_of_cent_card_lt hc (by norm_num) (by norm_num)

end CFSG.GH74.Generic.BProg.B3
