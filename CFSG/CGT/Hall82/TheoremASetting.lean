module

public import CFSG.LieType.BorelTits.Basic
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.HardMathSupport.Cooperstein.Coordinator.NaturalBridgeHeart

public section

namespace CFSG.CGT.Hall82.TheoremA

open CFSG.RankThree.PartTwo (altHeart)
open CFSG.QuasithinUnique (evenWeight)
open CFSG.HardMathSupport.Cooperstein.Coordinator (altAct)
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry (pairEW)
open Equiv

@[expose] noncomputable def pc (a b : Fin 6) : altHeart 6 :=
  ((pairEW a b : evenWeight 6) : altHeart 6)

@[expose] noncomputable def fixSub (σ : Perm (Fin 6)) : AddSubgroup (altHeart 6) :=
  AddMonoidHom.eqLocus (altAct σ) (AddMonoidHom.id (altHeart 6))

theorem mem_fixSub {σ : Perm (Fin 6)} {v : altHeart 6} : v ∈ fixSub σ ↔ altAct σ v = v :=
  Iff.rfl

@[expose] noncomputable def stabSub (u : altHeart 6) : Subgroup (Perm (Fin 6)) where
  carrier := {σ | altAct σ u = u}
  one_mem' := CFSG.HardMathSupport.Cooperstein.Coordinator.altAct_one u
  mul_mem' := fun {σ τ} hσ hτ => by
    show altAct (σ * τ) u = u
    rw [CFSG.HardMathSupport.Cooperstein.Coordinator.altAct_mul, Set.mem_setOf_eq.mp hτ,
      Set.mem_setOf_eq.mp hσ]
  inv_mem' := fun {σ} hσ => by
    show altAct σ⁻¹ u = u
    conv_lhs => rw [← Set.mem_setOf_eq.mp hσ]
    exact CFSG.HardMathSupport.Cooperstein.Coordinator.altAct_inv_apply σ u

theorem mem_stabSub {u : altHeart 6} {σ : Perm (Fin 6)} : σ ∈ stabSub u ↔ altAct σ u = u :=
  Iff.rfl

@[expose] def Pres (σ : Perm (Fin 6)) (i j : Fin 6) : Prop :=
  (σ i = i ∧ σ j = j) ∨ (σ i = j ∧ σ j = i)

@[expose] def cyc (i j k : Fin 6) : Perm (Fin 6) := swap i k * swap i j

structure Facts : Prop where
  card : Nat.card (altHeart 6) = 16
  trans : ∀ u v : altHeart 6, u ≠ 0 → v ≠ 0 → ∃ σ : Perm (Fin 6), altAct σ u = v
  faithful : ∀ σ : Perm (Fin 6), (∀ v, altAct σ v = v) → σ = 1
  exists_pc : ∀ v : altHeart 6, v ≠ 0 → ∃ i j : Fin 6, i ≠ j ∧ v = pc i j
  pc_ne_zero : ∀ i j : Fin 6, i ≠ j → pc i j ≠ 0
  altAct_pc : ∀ (σ : Perm (Fin 6)) (i j : Fin 6), altAct σ (pc i j) = pc (σ i) (σ j)
  fixed_pc_iff : ∀ (σ : Perm (Fin 6)) (i j : Fin 6), i ≠ j →
    (altAct σ (pc i j) = pc i j ↔ Pres σ i j)
  indep : ∃ u v w : altHeart 6, u ≠ 0 ∧ v ≠ 0 ∧ w ≠ 0 ∧ u + v ≠ 0 ∧ u + w ≠ 0 ∧ v + w ≠ 0 ∧
    u + v + w ≠ 0
  cyc_sum : ∀ i j k : Fin 6, i ≠ j → j ≠ k → i ≠ k →
    pc i j + altAct (cyc i j k) (pc i j) + altAct (cyc i j k)⁻¹ (pc i j) = 0
  cyc_conj : ∀ (i j k : Fin 6), i ≠ j → j ≠ k → i ≠ k → ∀ σ : Perm (Fin 6), Pres σ i j →
    σ k = k → σ * cyc i j k * σ⁻¹ = cyc i j k ∨ σ * cyc i j k * σ⁻¹ = (cyc i j k)⁻¹
  decomp : ∀ i j : Fin 6, i ≠ j → ∀ σ : Perm (Fin 6), Pres σ i j →
    ∃ σ₁ σ₂ : Perm (Fin 6), σ = σ₁ * σ₂ ∧ Pres σ₁ i j ∧ Pres σ₂ i j ∧
      (∃ k, k ≠ i ∧ k ≠ j ∧ σ₁ k = k) ∧ (∃ k, k ≠ i ∧ k ≠ j ∧ σ₂ k = k)
  index_stabSub : ∀ u : altHeart 6, u ≠ 0 → (stabSub u).index = 15
  card_fix_swap : ∀ i j : Fin 6, i ≠ j → Nat.card (fixSub (swap i j)) = 8
  card_fix_two : Nat.card ↥(fixSub (swap 4 5) ⊓ fixSub (swap 0 2)) = 4
  quad : ∀ i j : Fin 6, i ≠ j → ∀ E : Subgroup (Perm (Fin 6)), (∀ e ∈ E, Pres e i j) →
    (∀ h : Perm (Fin 6), Pres h i j → ∀ e ∈ E, h * e * h⁻¹ ∈ E) → (∀ e ∈ E, e * e = 1) →
    (∀ e ∈ E, ∀ e' ∈ E, ∀ v : altHeart 6,
      altAct e' (altAct e v + v) + (altAct e v + v) = 0) →
    ∀ e ∈ E, e = 1 ∨ e = swap i j

structure Setting (G : Type) [Group G] [Finite G] (M : Subgroup G)
    (θ : ↥M →* Perm (Fin 6)) (z : G)
    (π : ↥(CFSG.Open.pCoreOf 2 M) →* Multiplicative (altHeart 6)) : Prop where
  surj_θ : Function.Surjective θ
  ker_θ : θ.ker = (CFSG.Open.pCoreOf 2 M).subgroupOf M
  z_mem : z ∈ CFSG.Open.pCoreOf 2 M
  z_ne : z ≠ 1
  z_sq : z * z = 1
  z_comm : ∀ m ∈ M, m * z = z * m
  surj_π : Function.Surjective π
  ker_π : π.ker = (Subgroup.zpowers z).subgroupOf (CFSG.Open.pCoreOf 2 M)
  equiv : ∀ (m : ↥M) (q q' : ↥(CFSG.Open.pCoreOf 2 M)), (q' : G) = m * q * m⁻¹ →
    Multiplicative.toAdd (π q') = altAct (θ m) (Multiplicative.toAdd (π q))
  normalizer_eq : Subgroup.normalizer ((CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G) = M
  centralizer_eq : Subgroup.centralizer ({z} : Set G) = M

theorem setting_of_hyps {G : Type} [Group G] [Finite G] {M : Subgroup G}
    {θ : ↥M →* Perm (Fin 6)} {z : G} {π : ↥(CFSG.Open.pCoreOf 2 M) →* Multiplicative (altHeart 6)}
    (h1 : Function.Surjective θ) (h2 : θ.ker = (CFSG.Open.pCoreOf 2 M).subgroupOf M)
    (h3 : z ∈ CFSG.Open.pCoreOf 2 M) (h4 : z ≠ 1) (h5 : z * z = 1) (h6 : ∀ m ∈ M, m * z = z * m)
    (h7 : Function.Surjective π)
    (h8 : π.ker = (Subgroup.zpowers z).subgroupOf (CFSG.Open.pCoreOf 2 M))
    (h9 : ∀ (m : ↥M) (q q' : ↥(CFSG.Open.pCoreOf 2 M)), (q' : G) = m * q * m⁻¹ →
      Multiplicative.toAdd (π q') = altAct (θ m) (Multiplicative.toAdd (π q)))
    (h10 : Subgroup.normalizer ((CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G) = M)
    (h11 : Subgroup.centralizer ({z} : Set G) = M) : Setting G M θ z π :=
  ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

namespace Setting

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {θ : ↥M →* Perm (Fin 6)} {z : G}
  {π : ↥(CFSG.Open.pCoreOf 2 M) →* Multiplicative (altHeart 6)}

theorem V_le (_S : Setting G M θ z π) : CFSG.Open.pCoreOf 2 M ≤ M :=
  CFSG.LieType.BorelTits.pCoreOf_le 2 M

theorem le_normalizer (_S : Setting G M θ z π) :
    M ≤ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G) :=
  CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M

theorem conj_mem (S : Setting G M θ z π) {m : G} (hm : m ∈ M) {q : G}
    (hq : q ∈ CFSG.Open.pCoreOf 2 M) : m * q * m⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
  (Subgroup.mem_normalizer_iff.mp (S.le_normalizer hm) q).mp hq

theorem isPGroup (_S : Setting G M θ z π) : IsPGroup 2 (CFSG.Open.pCoreOf 2 M) :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M

theorem θ_eq_one_iff (S : Setting G M θ z π) (m : ↥M) :
    θ m = 1 ↔ (m : G) ∈ CFSG.Open.pCoreOf 2 M := by
  rw [← MonoidHom.mem_ker, S.ker_θ, Subgroup.mem_subgroupOf]

theorem π_eq_one_iff (S : Setting G M θ z π) (q : ↥(CFSG.Open.pCoreOf 2 M)) :
    π q = 1 ↔ (q : G) = 1 ∨ (q : G) = z := by
  rw [← MonoidHom.mem_ker, S.ker_π, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    have ho : orderOf z = 2 := orderOf_eq_prime (by rw [sq, S.z_sq]) S.z_ne
    have hk' : z ^ (k % 2) = (q : G) := by
      rw [← hk, ← zpow_mod_orderOf z k, ho]
      norm_num
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left; rw [← hk', h0, zpow_zero]
    · right; rw [← hk', h1, zpow_one]
  · rintro (h | h)
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers z

theorem conj_z (S : Setting G M θ z π) {m : G} (hm : m ∈ M) : m * z * m⁻¹ = z := by
  rw [S.z_comm m hm, mul_inv_cancel_right]

theorem π_conj (S : Setting G M θ z π) (m : ↥M) (q : ↥(CFSG.Open.pCoreOf 2 M)) :
    Multiplicative.toAdd (π ⟨m * q * m⁻¹, S.conj_mem m.2 q.2⟩) =
      altAct (θ m) (Multiplicative.toAdd (π q)) :=
  S.equiv m q _ rfl

end Setting

end CFSG.CGT.Hall82.TheoremA
