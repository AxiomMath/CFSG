module

public import CFSG.GH74.GLS.SP.Local.SPLOrdCnt
public import CFSG.GH74.GLS.SP.Local.SPLOrdL2

public section

namespace CFSG.GH74.GLS.SP.Local

namespace OrdIC

theorem two_dvd_of_two_mul_eq {n q : ℕ} (hq : Odd q) (h : 2 * n = q * (q ^ 2 - 1)) : 2 ∣ n := by
  have h4 : 4 ∣ q ^ 2 - 1 := by
    obtain ⟨m, rfl⟩ := hq
    have h1 : (2 * m + 1) ^ 2 = 4 * (m * m + m) + 1 := by ring
    have h2 : (2 * m + 1) ^ 2 - 1 = 4 * (m * m + m) := by omega
    rw [h2]
    exact dvd_mul_right _ _
  have h5 : 4 ∣ 2 * n := by
    rw [h]
    exact Dvd.dvd.mul_left h4 q
  omega

section Subgroups

variable {G : Type*} [Group G] (H : Subgroup G)

theorem card_even_subgroup {g : G} (hg : g ∈ H) :
    Nat.card {x : G // x ∈ H ∧ Even (orderOf x) ∧ x ^ (orderOf x / 2) = g} =
      Nat.card {x : H // Even (orderOf x) ∧ x ^ (orderOf x / 2) = (⟨g, hg⟩ : H)} :=
  Nat.card_congr <| (Equiv.subtypeSubtypeEquivSubtypeInter (fun x : G => x ∈ H)
    (fun x => Even (orderOf x) ∧ x ^ (orderOf x / 2) = g)).symm.trans
    (Equiv.subtypeEquivRight fun y => by
      rw [Subgroup.orderOf_coe, ← Subgroup.coe_pow]
      exact and_congr_right fun _ => ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩)

theorem coe_mem_zpowers_iff (y j : H) :
    (j : G) ∈ Subgroup.zpowers (y : G) ↔ j ∈ Subgroup.zpowers y := by
  simp only [Subgroup.mem_zpowers_iff, ← Subgroup.coe_zpow, SetLike.coe_eq_coe]

theorem card_pairs_subgroup {g : G} (hg : g ∈ H) :
    Nat.card {p : G × G // p.1 ∈ H ∧ p.2 ∈ H ∧ orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧
      g ∈ Subgroup.zpowers (p.1 * p.2)} =
      Nat.card {p : H × H // orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧
        (⟨g, hg⟩ : H) ∈ Subgroup.zpowers (p.1 * p.2)} :=
  Nat.card_congr
    { toFun := fun p => ⟨(⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2.1⟩),
        (Subgroup.orderOf_mk _ _).trans p.2.2.2.1, (Subgroup.orderOf_mk _ _).trans p.2.2.2.2.1,
        (coe_mem_zpowers_iff H _ _).mp p.2.2.2.2.2⟩
      invFun := fun q => ⟨(q.1.1.1, q.1.2.1), q.1.1.2, q.1.2.2,
        (Subgroup.orderOf_coe q.1.1).trans q.2.1, (Subgroup.orderOf_coe q.1.2).trans q.2.2.1,
        (coe_mem_zpowers_iff H _ _).mpr q.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end Subgroups

theorem mem_center_centralizer_self {G : Type*} [Group G] (g : G) :
    (⟨g, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ : Subgroup.centralizer ({g} : Set G)) ∈
      Subgroup.center (Subgroup.centralizer ({g} : Set G)) := by
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp y.2)

end OrdIC

open OrdIC

open Subgroup in
theorem I_counts {I : Type} [Group I] [Finite I] {q δ : ℕ}
    (hI : CFSG.GH74.GLS.IVK.IsL2 I (fun r => r = q)) (hq5 : 5 ≤ q) (hqodd : Odd q)
    {ε : ℤ} (hε1 : ε = 1 ∨ ε = -1) (hε : (q : ℤ) ≡ ε [ZMOD 4])
    (hδ : ((2 * δ : ℕ) : ℤ) = q - ε) (hδ2 : 2 ≤ δ) (hev : Even δ) :
    2 * Nat.card I = q * (q ^ 2 - 1) ∧
    Nat.card {u : I // orderOf u = 2} * (2 * δ) = Nat.card I ∧
    Nat.card {x : I // Odd (orderOf x)} +
        Nat.card {u : I // orderOf u = 2} * (δ - δ / 2 ^ δ.factorization 2) = Nat.card I ∧
    Nat.card {p : I × I // orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ Odd (orderOf (p.1 * p.2))} +
        Nat.card {u : I // orderOf u = 2} * (δ * (δ - δ / 2 ^ δ.factorization 2)) =
      Nat.card {u : I // orderOf u = 2} * Nat.card {u : I // orderOf u = 2} := by
  obtain ⟨h1, hconj, hcent⟩ := L2_involution_facts hI hq5 hqodd hε1 hε hδ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨i₀, hi₀⟩ := exists_prime_orderOf_dvd_card' 2 (two_dvd_of_two_mul_eq hqodd h1)
  obtain ⟨c1, c2, c3⟩ := involution_class_counts i₀ hi₀ hconj
  obtain ⟨eC⟩ := hcent i₀ hi₀
  have hmem : i₀ ∈ centralizer ({i₀} : Set I) := mem_centralizer_singleton_iff.mpr rfl
  have hord : orderOf (⟨i₀, hmem⟩ : centralizer ({i₀} : Set I)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hi₀
  obtain ⟨d1, d2, d3⟩ := dihedral_counts hδ2 hev eC ⟨i₀, hmem⟩ hord (mem_center_centralizer_self i₀)
  have hC : Nat.card (centralizer ({i₀} : Set I)) = 2 * δ := by
    have : NeZero δ := ⟨by omega⟩
    rw [Nat.card_congr eC.toEquiv, DihedralGroup.nat_card]
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [← hC]
    exact c1
  · rw [← d2, ← card_even_subgroup (centralizer ({i₀} : Set I)) hmem]
    exact c2
  · rw [← d3, ← card_pairs_subgroup (centralizer ({i₀} : Set I)) hmem]
    exact c3

end CFSG.GH74.GLS.SP.Local
