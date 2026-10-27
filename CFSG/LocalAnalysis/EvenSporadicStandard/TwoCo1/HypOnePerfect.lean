module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers

public section

namespace CFSG.EvenSporadicStandard.TwoCo1.HypOne

open Subgroup CFSG.ComponentClassification.M12Cover

theorem map_perfect_eq_bot {K G : Type*} [Group K] [Group G] [Group.IsSolvable G]
    (f : K →* G) {P : Subgroup K} (hP : P ≤ ⁅P, P⁆) : P.map f = ⊥ := by
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := G)
  have key : ∀ k, P.map f ≤ derivedSeries G k := by
    intro k
    induction k with
    | zero => exact le_top
    | succ k ih =>
      calc P.map f ≤ (⁅P, P⁆).map f := Subgroup.map_mono hP
        _ = ⁅P.map f, P.map f⁆ := Subgroup.map_commutator P P f
        _ ≤ ⁅derivedSeries G k, derivedSeries G k⁆ := Subgroup.commutator_mono ih ih
  exact le_bot_iff.mp (hn ▸ key n)

theorem le_centralizer_of_ncard_conjugatesOf_le_four {K : Type*} [Group K] [Finite K]
    {P : Subgroup K} (hP : P ≤ ⁅P, P⁆) {x : K} (hx : (conjugatesOf x).ncard ≤ 4) :
    P ≤ Subgroup.centralizer ({x} : Set K) := by
  set M : Subgroup K := Subgroup.centralizer ({x} : Set K) with hM
  have hidx : M.index ≤ 4 := by
    rw [hM, Subgroup.index_centralizer_eq_ncard]
    exact hx
  have hcard : Nat.card (K ⧸ M) ≤ 4 := by
    rw [← Subgroup.index]
    exact hidx
  have hsolv : Group.IsSolvable (Equiv.Perm (K ⧸ M)) := Equiv.Perm.isSolvable hcard
  have hbot := map_perfect_eq_bot (MulAction.toPermHom K (K ⧸ M)) hP
  intro p hp
  have h1 : p ∈ (MulAction.toPermHom K (K ⧸ M)).ker := by
    rw [MonoidHom.mem_ker, ← Subgroup.mem_bot, ← hbot]
    exact ⟨p, hp, rfl⟩
  rw [← Subgroup.normalCore_eq_ker] at h1
  exact M.normalCore_le h1

theorem fourClassesLarge_of_perfect {K : Type*} [Group K] [Finite K] {P : Subgroup K}
    (hP : P ≤ ⁅P, P⁆) (hC : ∀ x : K, (∀ p ∈ P, p * x = x * p) → x ^ 4 = 1 → x ^ 2 = 1) :
    FourClassesLarge K := by
  intro x hx4 hx2
  by_contra hlt
  have hlt' : Nat.card {y : K // IsConj x y} ≤ 4 := by omega
  have hset : conjugatesOf x = {y | IsConj x y} := rfl
  have hn : (conjugatesOf x).ncard ≤ 4 := by
    rw [hset, ← Nat.card_coe_set_eq]
    exact hlt'
  have hle := le_centralizer_of_ncard_conjugatesOf_le_four hP hn
  refine hx2 (hC x (fun p hp => ?_) hx4)
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hp)

theorem fourClassesLarge_of_perfect_le {G : Type*} [Group G] {K P : Subgroup G} [Finite K]
    (hPK : P ≤ K) (hP : P ≤ ⁅P, P⁆)
    (hC : ∀ x ∈ K, (∀ p ∈ P, p * x = x * p) → x ^ 4 = 1 → x ^ 2 = 1) :
    FourClassesLarge K := by
  refine fourClassesLarge_of_perfect (P := P.subgroupOf K) ?_ fun x hx hx4 => ?_
  · have hmap : (P.subgroupOf K).map K.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPK
    rw [← Subgroup.map_le_map_iff_of_injective K.subtype_injective, Subgroup.map_commutator, hmap]
    exact hP
  · refine Subtype.ext ?_
    have := hC x x.2 (fun p hp => by
      have := hx ⟨p, hPK hp⟩ hp
      exact congrArg Subtype.val this) (by
      have := congrArg Subtype.val hx4
      simpa using this)
    simpa using this

end CFSG.EvenSporadicStandard.TwoCo1.HypOne
