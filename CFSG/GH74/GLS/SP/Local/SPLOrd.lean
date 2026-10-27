module

public import CFSG.GH74.GLS.SP.Local.SPLOrdG9
public import CFSG.GH74.GLS.SP.Local.SPLOrdIC
public import CFSG.GH74.ThompsonOrderFormula
public import CFSG.GH74.GLS.SP.Local.SPLOrdG8

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open CFSG.ShultStronglyClosedTI.InvolutionCounting
open scoped Pointwise commutatorElement

namespace CFSG.GH74.GLS.SP.Local

section Ord

variable {G : Type} [Group G] [Finite G] (D : SPLNot3 G)

theorem card_G_core (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) :
    2 * Nat.card G = D.q ^ 4 * (D.q ^ 2 - 1) * (D.q ^ 4 - 1) * Nat.card ↥D.F := by
  have hq5 : 5 ≤ D.q := hs.q_ge
  have hodd : Odd D.q := hs.odd_q
  have hd4 : 4 ∣ D.d := four_dvd_d D.toSPLNot0 hodd
  have hdpos : 4 ≤ D.d := d_pos D hs
  have : NeZero D.d := neZero_d D hs
  have hd2 : 2 ∣ D.d := dvd_two_d D hs
  set s : ℕ := if D.q % 4 = 1 then D.q + 1 else D.q - 1 with hs_def
  have hd_def : D.d = if D.q % 4 = 1 then D.q - 1 else D.q + 1 := rfl
  have hq4 : D.q % 4 = 1 ∨ D.q % 4 = 3 := by
    obtain ⟨m, hm⟩ := hodd
    omega
  have hds : D.d + s = 2 * D.q := by
    rcases hq4 with h | h
    · have h' : D.d = D.q - 1 := by rw [hd_def]; simp [h]
      have h'' : s = D.q + 1 := by rw [hs_def]; simp [h]
      omega
    · have hn : ¬ (D.q % 4 = 1) := by omega
      have h' : D.d = D.q + 1 := by rw [hd_def]; simp [hn]
      have h'' : s = D.q - 1 := by rw [hs_def]; simp [hn]
      omega
  have hds2 : D.d * s + 1 = D.q ^ 2 := by
    obtain ⟨q', hq'⟩ : ∃ q', D.q = q' + 1 := ⟨D.q - 1, by omega⟩
    rcases hq4 with h | h
    · have h' : D.d = D.q - 1 := by rw [hd_def]; simp [h]
      have h'' : s = D.q + 1 := by rw [hs_def]; simp [h]
      rw [h', h'', hq']
      simp only [Nat.add_sub_cancel]
      ring
    · have hn : ¬ (D.q % 4 = 1) := by omega
      have h' : D.d = D.q + 1 := by rw [hd_def]; simp [hn]
      have h'' : s = D.q - 1 := by rw [hs_def]; simp [hn]
      rw [h', h'', hq']
      simp only [Nat.add_sub_cancel]
      ring
  have hcd : s = D.d + 2 ∨ D.d = s + 2 := by
    rcases hq4 with h | h
    · left
      have h' : D.d = D.q - 1 := by rw [hd_def]; simp [h]
      have h'' : s = D.q + 1 := by rw [hs_def]; simp [h]
      omega
    · right
      have hn : ¬ (D.q % 4 = 1) := by omega
      have h' : D.d = D.q + 1 := by rw [hd_def]; simp [hn]
      have h'' : s = D.q - 1 := by rw [hs_def]; simp [hn]
      omega
  have hd2' := hd2
  obtain ⟨δ, hδ⟩ := hd2
  have hδ2 : D.d = 2 * δ := hδ
  have hδ4 : 2 ≤ δ := by omega
  have hδev : Even δ := by
    obtain ⟨k, hk⟩ := hd4
    exact ⟨k, by omega⟩
  have hdδ : D.d / 2 = δ := by omega
  obtain ⟨ε, hε1, hε, hdε⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (D.q : ℤ) ≡ ε [ZMOD 4] ∧
      ((2 * δ : ℕ) : ℤ) = D.q - ε := by
    rcases hq4 with h | h
    · refine ⟨1, Or.inl rfl, by unfold Int.ModEq; omega, ?_⟩
      have h' : D.d = D.q - 1 := by rw [hd_def]; simp [h]
      omega
    · refine ⟨-1, Or.inr rfl, by unfold Int.ModEq; omega, ?_⟩
      have hn : ¬ (D.q % 4 = 1) := by omega
      have h' : D.d = D.q + 1 := by rw [hd_def]; simp [hn]
      omega
  obtain ⟨hI2, hι, hO, hP⟩ := I_counts hc.I_L2 hq5 hodd hε1 hε hdε hδ4 hδev
  have hιd : Nat.card {u : ↥D.I // orderOf u = 2} * D.d = Nat.card ↥D.I := by
    rw [hδ2]; exact hι
  have hι' := sigma_count D hs hc hs_def
  obtain ⟨cd⟩ := nonempty_chatData D hs hc hd2'
  have hrt := rt_eq hs hc cd rfl hιd
  have hside := tside_count (sigmaAut D hc) (sigmaAut_sq D hc) hd2' hd4
    (Nat.card {u : ↥D.I // orderOf u = 2}) (Nat.card {i : ↥D.I // i * sigmaAut D hc i = 1})
    (Nat.card {p : ↥D.I × ↥D.I // orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧
      Odd (orderOf (p.1 * p.2))}) rfl rfl rfl
  rw [hdδ] at hside
  have hrz := rz_eq D hs hc
  have hOeq : Nat.card {γ : ↥D.I // Odd (orderOf (γ : G))} =
      Nat.card {x : ↥D.I // Odd (orderOf x)} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun γ => by rw [Subgroup.orderOf_coe])
  rw [hOeq] at hrz
  obtain ⟨hform, -⟩ := CFSG.GH74.thompson_two_involution_class_order_formula (t := D.t) (u := D.z)
    hs.syl.t_ord hs.syl.z_inv (not_isConj_t_z D hs) (fun x hx => inv_classes D hs hx)
  have hCt : Nat.card ↥(centralizer ({D.t} : Set G)) =
      Nat.card ↥D.I * (2 * D.d) * Nat.card ↥D.F := card_Ct D hs hc
  have hC : Nat.card ↥(centralizer ({D.z} : Set G)) =
      2 * (2 * Nat.card ↥D.I ^ 2) * Nat.card ↥D.F := by
    have e1 : Nat.card ↥(centralizer ({D.z} : Set G)) = Nat.card ↥D.C := rfl
    rw [e1, card_C D hs hc, card_Kt D hs, card_K D hs hc]
  have hδpos : δ ≠ 0 := by omega
  have hprod : 2 ^ δ.factorization 2 * (δ / 2 ^ δ.factorization 2) = δ :=
    Nat.ordProj_mul_ordCompl_eq_self δ 2
  have hv : 1 ≤ δ.factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two hδpos (by
      obtain ⟨k, hk⟩ := hδev
      exact ⟨k, by omega⟩)
  have he : 2 * (δ / 2 ^ δ.factorization 2) ≤ δ := by
    have h2 : 2 ≤ 2 ^ δ.factorization 2 := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ δ.factorization 2 := Nat.pow_le_pow_right (by norm_num) hv
    calc 2 * (δ / 2 ^ δ.factorization 2) ≤ 2 ^ δ.factorization 2 * (δ / 2 ^ δ.factorization 2) :=
          Nat.mul_le_mul_right _ h2
      _ = δ := hprod
  have hid := order_identity D.q D.d s δ (δ / 2 ^ δ.factorization 2) (Nat.card ↥D.I)
    (Nat.card {u : ↥D.I // orderOf u = 2}) (Nat.card {i : ↥D.I // i * sigmaAut D hc i = 1})
    (Nat.card {x : ↥D.I // Odd (orderOf x)})
    (Nat.card {p : ↥D.I × ↥D.I // orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ Odd (orderOf (p.1 * p.2))})
    (Nat.card ↥D.F) hq5 hds hds2 hcd hδ2.symm he hI2 hιd hι' hO hP
  calc 2 * Nat.card G
      = 2 * (Nat.card ↥(centralizer ({D.z} : Set G)) * thompsonPairCount D.t D.z D.t +
          Nat.card ↥(centralizer ({D.t} : Set G)) * thompsonPairCount D.t D.z D.z) := by
        rw [hform]
    _ = 2 * (4 * Nat.card ↥D.F * Nat.card ↥D.I ^ 2 *
          (δ * ((δ - 2 * (δ / 2 ^ δ.factorization 2)) * Nat.card {u : ↥D.I // orderOf u = 2} +
            δ * Nat.card {i : ↥D.I // i * sigmaAut D hc i = 1}) +
            Nat.card {p : ↥D.I × ↥D.I // orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧
              Odd (orderOf (p.1 * p.2))}) +
          4 * δ * Nat.card ↥D.I * Nat.card ↥D.F *
            (Nat.card ↥D.I * Nat.card {x : ↥D.I // Odd (orderOf x)})) := by
        rw [hC, hCt, hrz, hrt, hside, hδ2]
        ring
    _ = _ := hid

end Ord


section Ord2

variable {G : Type} [Group G] [Finite G] (D : SPLNot3 G)

theorem splOrd_core (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) : SPL2Ord D.toSPLNot0 := by
  refine ⟨card_G_core D hs hc, ?_⟩
  intro T
  obtain ⟨k, hk1, hkq⟩ := hs.q_pow
  have hcard := card_G_core D hs hc
  have hf : 0 < Nat.card ↥D.F := Nat.card_pos
  have h := sylow_card_of_card D.p k (Nat.card ↥D.F) hs.prime hs.p_ne_two hk1 hf
    (by rw [← hkq]; exact hcard) T
  rw [hkq]
  exact h

end Ord2

theorem splLeafOrd : SPLLeafOrd := by
  intro G _ _ _ D₂ hs _ hc
  exact splOrd_core ({ toSPLNot2 := D₂, X₁ := ⊥, X₁' := ⊥, Y₁ := ⊥, a := 1 } : SPLNot3 G) hs hc

end CFSG.GH74.GLS.SP.Local
