module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup
open scoped commutatorElement

namespace A5SylowAux

private theorem card_eq_sixty : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.factorial]

private def kfin (p : Fin 5) : Finset (alternatingGroup (Fin 5)) :=
  Finset.univ.filter fun g => g.1 p = p ∧ g * g = 1

private theorem mul_self_eq_one_of_pow_four :
    ∀ g : alternatingGroup (Fin 5), g ^ 4 = 1 → g * g = 1 := by
  decide +kernel

private theorem card_kfin_le : ∀ p : Fin 5, (kfin p).card ≤ 4 := by
  decide +kernel

private theorem exists_kfin_order_three :
    ∀ p q : Fin 5, p ≠ q → ∃ x ∈ kfin p, ∃ y ∈ kfin q, (x * y) ^ 3 = 1 ∧ x * y ≠ 1 := by
  decide +kernel

private theorem exists_kfin_order_five :
    ∀ p q : Fin 5, p ≠ q → ∃ x ∈ kfin p, ∃ y ∈ kfin q, (x * y) ^ 5 = 1 ∧ x * y ≠ 1 := by
  decide +kernel

private theorem mul_self_eq_one_of_card_four {V : Subgroup (alternatingGroup (Fin 5))}
    (hV : Nat.card V = 4) {g : alternatingGroup (Fin 5)} (hg : g ∈ V) : g * g = 1 := by
  apply mul_self_eq_one_of_pow_four
  have h := pow_card_eq_one' (G := ↥V) (x := ⟨g, hg⟩)
  rw [hV] at h
  simpa using congrArg Subtype.val h

private theorem exists_fixed_point {V : Subgroup (alternatingGroup (Fin 5))}
    (hV : Nat.card V = 4) : ∃ p : Fin 5, ∀ g ∈ V, g.1 p = p := by
  have hp : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by simpa using hV)
  have h := hp.card_modEq_card_fixedPoints (Fin 5)
  have hne : (MulAction.fixedPoints V (Fin 5)).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    rw [hempty] at h
    simp at h
    exact absurd h (by decide)
  obtain ⟨p, hp⟩ := hne
  exact ⟨p, fun g hg => hp ⟨g, hg⟩⟩

private theorem coe_eq_kfin {V : Subgroup (alternatingGroup (Fin 5))} (hV : Nat.card V = 4) :
    ∃ p : Fin 5, (V : Set (alternatingGroup (Fin 5))) = ↑(kfin p) := by
  obtain ⟨p, hp⟩ := exists_fixed_point hV
  refine ⟨p, Set.eq_of_subset_of_ncard_le ?_ ?_⟩
  · intro g hg
    simp only [kfin, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    exact ⟨hp g hg, mul_self_eq_one_of_card_four hV hg⟩
  · rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq]
    exact (card_kfin_le p).trans hV.symm.le

end A5SylowAux

theorem a5_perfect_eq_top (H : Subgroup (alternatingGroup (Fin 5))) (hH : ⁅H, H⁆ = H)
    (hne : H ≠ ⊥) : H = ⊤ := by
  by_contra htop
  have hdvd : Nat.card H ∣ 60 := by
    rw [← A5SylowAux.card_eq_sixty]
    exact Subgroup.card_subgroup_dvd_card H
  have hperf : Group.IsPerfect H := Subgroup.isPerfect_iff.mpr hH
  have hnt : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).mpr hne
  have hne60 : Nat.card H ≠ 60 := by
    intro h
    exact htop (Subgroup.eq_top_of_card_eq H (by rw [h, A5SylowAux.card_eq_sixty]))
  have h30 : Nat.card H = 30 := by
    by_contra h30
    have hle : (Nat.card H).primeFactors.card ≤ 2 := by
      have hmem : Nat.card H ∈ Nat.divisors 60 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
      have key : ∀ d ∈ Nat.divisors 60, d ≠ 30 → d ≠ 60 → d.primeFactors.card ≤ 2 := by
        decide +kernel
      exact key _ hmem h30 hne60
    exact Group.IsPerfect.not_isSolvable H
      (CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two hle)
  have hidx : H.index = 2 := by
    have := Subgroup.card_mul_index H
    rw [h30, A5SylowAux.card_eq_sixty] at this
    omega
  have hn : H.Normal := Subgroup.normal_of_index_eq_two hidx
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with h | h
  · exact hne h
  · exact htop h

theorem a5_eq_top_of_two_sylow {V V' H : Subgroup (alternatingGroup (Fin 5))}
    (hV : Nat.card V = 4) (hV' : Nat.card V' = 4) (hne : V ≠ V') (h1 : V ≤ H) (h2 : V' ≤ H) :
    H = ⊤ := by
  obtain ⟨p, hp⟩ := A5SylowAux.coe_eq_kfin hV
  obtain ⟨q, hq⟩ := A5SylowAux.coe_eq_kfin hV'
  have hpq : p ≠ q := by
    rintro rfl
    exact hne (SetLike.coe_injective (hp.trans hq.symm))
  have hmemV : ∀ g, g ∈ A5SylowAux.kfin p → g ∈ V := fun g hg => by
    rw [← SetLike.mem_coe, hp]
    exact hg
  have hmemV' : ∀ g, g ∈ A5SylowAux.kfin q → g ∈ V' := fun g hg => by
    rw [← SetLike.mem_coe, hq]
    exact hg
  have hdiv : ∀ {ℓ : ℕ} [Fact ℓ.Prime] {z : alternatingGroup (Fin 5)}, z ∈ H → z ^ ℓ = 1 →
      z ≠ 1 → ℓ ∣ Nat.card H := by
    intro ℓ _ z hz hzl hz1
    have h := orderOf_dvd_natCard (⟨z, hz⟩ : H)
    rwa [Subgroup.orderOf_mk, orderOf_eq_prime hzl hz1] at h
  obtain ⟨x, hx, y, hy, h3, h31⟩ := A5SylowAux.exists_kfin_order_three p q hpq
  obtain ⟨x', hx', y', hy', h5, h51⟩ := A5SylowAux.exists_kfin_order_five p q hpq
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h3d : 3 ∣ Nat.card H :=
    hdiv (H.mul_mem (h1 (hmemV x hx)) (h2 (hmemV' y hy))) h3 h31
  have h5d : 5 ∣ Nat.card H :=
    hdiv (H.mul_mem (h1 (hmemV x' hx')) (h2 (hmemV' y' hy'))) h5 h51
  have h4d : 4 ∣ Nat.card H := hV ▸ Subgroup.card_dvd_of_le h1
  have h60 : Nat.card H ∣ 60 := by
    rw [← A5SylowAux.card_eq_sixty]
    exact Subgroup.card_subgroup_dvd_card H
  have hle : Nat.card H ≤ 60 := Nat.le_of_dvd (by norm_num) h60
  have hpos : 0 < Nat.card H := Nat.card_pos
  exact Subgroup.eq_top_of_card_eq H (by rw [A5SylowAux.card_eq_sixty]; omega)

end CFSG.OddStandard.Seitz77
