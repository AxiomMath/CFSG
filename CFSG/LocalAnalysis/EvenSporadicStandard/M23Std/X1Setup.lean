module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.X1Basic
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup

variable {G : Type} [Group G]

structure Setup (L : Subgroup G) (z t : G) (F L1 N : Subgroup G) : Prop where
  one : OneClassData L z t
  nd : NData L F
  fused : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z)
  F_le : F ≤ L1
  L1_card : Nat.card L1 = 256
  L1_sq : ∀ x ∈ L1, x * x = 1
  L1_comm : ∀ x ∈ L1, ∀ y ∈ L1, x * y = y * x
  K_eq : Ksub z F = L1 ⊔ zpowers z
  L1_cz : ∀ x ∈ L1, z * x = x * z → x ∈ F
  L1_normE : ∀ n : G, (∀ x, x ∈ F ⊔ zpowers z ↔ n * x * n⁻¹ ∈ F ⊔ zpowers z) →
    ∀ x, x ∈ L1 ↔ n * x * n⁻¹ ∈ L1
  L1_normK : ∀ n : G, (∀ x, x ∈ Ksub z F ↔ n * x * n⁻¹ ∈ Ksub z F) →
    ∀ x, x ∈ L1 ↔ n * x * n⁻¹ ∈ L1
  N_le : N ≤ centralizer (L1 : Set G)
  N_norm : ∀ c ∈ centralizer (L1 : Set G), ∀ x ∈ N, c * x * c⁻¹ ∈ N
  N_odd : ¬ 2 ∣ Nat.card N
  N_disj : Disjoint N L1
  N_sup : N ⊔ L1 = centralizer (L1 : Set G)
  phi_onto : ∀ f ∈ F, ∃ k ∈ Ksub z F, phiv z k = f

variable {L : Subgroup G} {z t : G} {F L1 N : Subgroup G}

namespace Setup

variable (S : Setup L z t F L1 N)

include S

theorem z_mem_K : z ∈ Ksub z F :=
  E_le_K S.one S.nd (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))

theorem z_normK : ∀ y, y ∈ Ksub z F ↔ z * y * z⁻¹ ∈ Ksub z F := fun y =>
  Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer S.z_mem_K) y

theorem z_norm : ∀ x, x ∈ L1 ↔ z * x * z⁻¹ ∈ L1 := S.L1_normK z S.z_normK

theorem K_le_X : Ksub z F ≤ normalizer (L1 : Set G) := fun k hk =>
  Subgroup.mem_normalizer_iff.2 (S.L1_normK k
    (Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hk)))

theorem N_comm : ∀ n ∈ N, ∀ l ∈ L1, n * l = l * n := fun _ hn l hl =>
  (mem_centralizer_iff.1 (S.N_le hn) l hl).symm

theorem N_le_X : N ≤ normalizer (L1 : Set G) := fun _ hn =>
  Subgroup.centralizer_le_normalizer (L1 : Set G) (S.N_le hn)

theorem conj_N {g : G} (hg : g ∈ normalizer (L1 : Set G)) {x : G} (hx : x ∈ N) :
    g * x * g⁻¹ ∈ N :=
  conj_mem_complement S.N_norm S.N_le S.N_odd S.N_disj S.L1_sq S.L1_comm S.N_sup hg hx

end Setup

end CFSG.EvenSporadicStandard.M23Std
