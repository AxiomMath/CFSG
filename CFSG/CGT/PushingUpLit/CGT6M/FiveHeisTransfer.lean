module

public import CFSG.CGT.PushingUpLit.CGT6M.FiveTransfer
public import CFSG.CGT.PushingUpLit.CGT6M.FiveHeis
public import CFSG.CGT.PushingUpLit.CGT6M.FiveHeisNF
public import CFSG.RankThree.PartOne.S11c.HeisenbergSylow

public section

namespace CFSG.CGT.PushingUpLit.CGT6M

open scoped commutatorElement

@[expose] def HeisData (Q : Type*) [Group Q] : Prop :=
  ∃ x y : Q, x ^ 5 = 1 ∧ y ^ 5 = 1 ∧ Commute ⁅y, x⁆ x ∧ Commute ⁅y, x⁆ y ∧ ⁅y, x⁆ ≠ 1 ∧
    ¬ 5 ^ 4 ∣ Nat.card Q

section Lift

variable {L Q : Type*} [Group L] [Finite L] [Group Q]

theorem exists_lifted_heis (π : L →* Q) (hπ : Function.Surjective π)
    (hK : π.ker ≤ Subgroup.center L) (hK5 : ¬ 5 ∣ Nat.card π.ker) {x y : Q} (hx5 : x ^ 5 = 1)
    (hy5 : y ^ 5 = 1) (hzx : Commute ⁅y, x⁆ x) (hzy : Commute ⁅y, x⁆ y) (hz1 : ⁅y, x⁆ ≠ 1) :
    ∃ x' y' : L, x' ^ 5 = 1 ∧ y' ^ 5 = 1 ∧ Commute ⁅y', x'⁆ x' ∧ Commute ⁅y', x'⁆ y' ∧
      ⁅y', x'⁆ ^ 5 = 1 ∧ ⁅y', x'⁆ ≠ 1 := by
  obtain ⟨x', hx', hx5'⟩ := exists_lift_of_pow_eq_one hπ Nat.prime_five hK5 hx5
  obtain ⟨y', hy', hy5'⟩ := exists_lift_of_pow_eq_one hπ Nat.prime_five hK5 hy5
  set z' := ⁅y', x'⁆ with hz'
  have hνz : π z' = ⁅y, x⁆ := by rw [hz', map_commutatorElement, hx', hy']
  have hcent : ∀ c ∈ π.ker, ∀ g : L, Commute c g := fun c hc g =>
    Subgroup.mem_center_iff.mp (hK hc) g |>.symm
  have hw1 : ⁅z', x'⁆ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement, hνz, hx']
    exact commutatorElement_eq_one_iff_mul_comm.mpr hzx.eq
  have hz1x : ⁅z', x'⁆ = 1 :=
    eq_one_of_pow_eq_one_of_mem_ker Nat.prime_five hK5 hw1
      (commutator_pow_eq_one_of_commute (hcent _ hw1 x') hx5')
  have hw2 : ⁅z', y'⁆ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement, hνz, hy']
    exact commutatorElement_eq_one_iff_mul_comm.mpr hzy.eq
  have hz1y : ⁅z', y'⁆ = 1 :=
    eq_one_of_pow_eq_one_of_mem_ker Nat.prime_five hK5 hw2
      (commutator_pow_eq_one_of_commute (hcent _ hw2 y') hy5')
  have hcx' : Commute z' x' := commutatorElement_eq_one_iff_commute.mp hz1x
  have hcy' : Commute z' y' := commutatorElement_eq_one_iff_commute.mp hz1y
  refine ⟨x', y', hx5', hy5', hcx', hcy', ?_, ?_⟩
  · exact commutator_pow_eq_one_of_commute hcx' hx5'
  · intro h
    apply hz1
    have h' : z' = 1 := h
    rw [← hνz, h', map_one]

end Lift

section Transfer

variable {V : Type} [CommGroup V] [Finite V]

theorem false_of_heisData {L Q : Type} [Group L] [Finite L] [Group Q] (ρ : L →* MulAut V)
    (hρ : Function.Injective ρ) (hV : ∀ v : V, v ^ 2 = 1) (π : L →* Q)
    (hπ : Function.Surjective π) (hK : π.ker ≤ Subgroup.center L) (hK5 : ¬ 5 ∣ Nat.card π.ker)
    (hd : HeisData Q) {y : L} (hy1 : y ≠ 1) (hy5 : y ^ 5 = 1)
    (h16 : Nat.card V ≤ 2 ^ 4 * Nat.card (fixSub (ρ y))) : False := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨x, y₀, hx5, hy₀5, hzx, hzy, hz1, hQ⟩ := hd
  obtain ⟨x', y', hx5', hy5', hcx, hcy, hz5, hz1'⟩ :=
    exists_lifted_heis π hπ hK hK5 hx5 hy₀5 hzx hzy hz1
  set S : Subgroup L := Subgroup.closure {x', y'} with hS
  have hS5 : IsPGroup 5 S :=
    CFSG.RankThree.PartOne.HNRed.isPGroup_closure_heisenberg hx5' hy5' hcx hcy hz5
  have hL : ¬ 5 ^ 4 ∣ Nat.card L := not_pow_dvd_card_of_surjective hπ Nat.prime_five hK5 hQ
  obtain ⟨m, hm⟩ := hS5.exists_card_eq
  have hxS : x' ∈ S := Subgroup.subset_closure (by simp)
  have hyS : y' ∈ S := Subgroup.subset_closure (by simp)
  have hnc : ¬ (⟨x', hxS⟩ : S) * ⟨y', hyS⟩ = ⟨y', hyS⟩ * ⟨x', hxS⟩ := by
    intro h
    apply hz1'
    have h' : x' * y' = y' * x' := congrArg Subtype.val h
    rw [commutatorElement_def]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul, h']
  have hm3 : m = 3 := by
    have hle : m ≤ 3 := by
      by_contra h
      have h4 : 4 ≤ m := by omega
      apply hL
      exact (pow_dvd_pow 5 h4).trans (hm ▸ Subgroup.card_subgroup_dvd_card S)
    have hge : 3 ≤ m := by
      by_contra h
      apply hnc
      have hm2 : m = 0 ∨ m = 1 ∨ m = 2 := by omega
      rcases hm2 with rfl | rfl | rfl
      · have : Subsingleton S := (Nat.card_eq_one_iff_unique.mp (by simpa using hm)).1
        exact Subsingleton.elim _ _
      · have : Fact (Nat.Prime (Nat.card S)) := ⟨by rw [hm]; simpa using Nat.prime_five⟩
        have := isCyclic_of_prime_card (p := Nat.card S) rfl
        exact IsCyclic.commGroup.mul_comm _ _
      · have := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 5) (G := S) hm
        exact (IsMulCommutative.is_comm.comm _ _)
    omega
  subst hm3
  obtain ⟨g, hg⟩ := exists_conj_mem_of_card Nat.prime_five S hm hL hy5
  obtain ⟨i, j, k, hijk⟩ := heis_normal_form hx5' hy5' hcx hcy _ hg
  have hρ5x : (ρ x') ^ 5 = 1 := by rw [← map_pow, hx5', map_one]
  have hρ5y : (ρ y') ^ 5 = 1 := by rw [← map_pow, hy5', map_one]
  have hρu : (ρ x') ^ i * (ρ y') ^ j * ⁅ρ y', ρ x'⁆ ^ k = ρ g * ρ y * (ρ g)⁻¹ := by
    rw [← map_commutatorElement, ← map_pow, ← map_pow, ← map_pow, ← map_mul, ← map_mul, ← hijk,
      map_mul, map_mul, map_inv]
  have hu5 : ((ρ x') ^ i * (ρ y') ^ j * ⁅ρ y', ρ x'⁆ ^ k) ^ 5 = 1 := by
    rw [hρu, conj_pow, ← map_pow, hy5, map_one]
    group
  have hu1 : (ρ x') ^ i * (ρ y') ^ j * ⁅ρ y', ρ x'⁆ ^ k ≠ 1 := by
    intro h
    apply hy1
    rw [hρu] at h
    have : ρ y = 1 := by
      have h2 : ρ y = (ρ g)⁻¹ * (ρ g * ρ y * (ρ g)⁻¹) * ρ g := by group
      rw [h2, h]
      group
    exact hρ (this.trans (map_one ρ).symm)
  have hcomm : Nat.card (commSub ((ρ x') ^ i * (ρ y') ^ j * ⁅ρ y', ρ x'⁆ ^ k)) ≤ 16 := by
    rw [hρu, card_commSub_conj]
    exact card_commSub_le_of_card_le h16
  refine false_of_heisenberg (X := ρ x') (Y := ρ y') hρ5x hρ5y ?_ ?_ ?_ hV hu5 hu1 hcomm
  · rw [← map_commutatorElement]
    exact hcx.map ρ
  · rw [← map_commutatorElement]
    exact hcy.map ρ
  · intro h
    apply hz1'
    rw [← map_commutatorElement] at h
    exact hρ (h.trans (map_one ρ).symm)

end Transfer

end CFSG.CGT.PushingUpLit.CGT6M
