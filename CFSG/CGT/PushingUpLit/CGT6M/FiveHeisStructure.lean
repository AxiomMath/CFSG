module

public import CFSG.CGT.PushingUpLit.CGT6M.FiveHeisTransfer
public import CFSG.RankThree.PartTwo.Census.Criteria

public section

namespace CFSG.CGT.PushingUpLit.CGT6M

open scoped commutatorElement
open CFSG.Open

variable {Q : Type*} [Group Q] [Finite Q]

theorem not_isCyclic_sylow_of_exists_noncomm_isPGroup {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {S : Subgroup G} (hS : IsPGroup p S) {a b : G} (ha : a ∈ S) (hb : b ∈ S)
    (hab : a * b ≠ b * a) (T : Sylow p G) : ¬ IsCyclic (T : Subgroup G) := by
  intro hcyc
  have hT : p ^ (Nat.card G).factorization p ∣ Nat.card (T : Subgroup G) := by
    rw [Sylow.card_eq_multiplicity]
  obtain ⟨c, hc⟩ :=
    CFSG.RankThree.PartOne.HNRed.exists_conj_le_of_card_dvd_pow (T : Subgroup G) hT hS
  have hTcomm : IsMulCommutative ↥(T : Subgroup G) := IsCyclic.isMulCommutative
  let f : ↥S →* ↥(T : Subgroup G) :=
    { toFun := fun x => ⟨c * (x : G) * c⁻¹, hc x x.2⟩
      map_one' := by simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        show c * ((x : G) * (y : G)) * c⁻¹ =
          (c * (x : G) * c⁻¹) * (c * (y : G) * c⁻¹)
        group }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have h := congrArg (fun t : ↥(T : Subgroup G) => (t : G)) hxy
    simpa [f] using mul_left_cancel (mul_right_cancel h)
  have hSnab : ¬ IsMulCommutative ↥S := by
    rintro ⟨hcS⟩
    exact hab (congrArg Subtype.val (hcS.comm ⟨a, ha⟩ ⟨b, hb⟩))
  refine hSnab (IsMulCommutative.of_comm fun x y => ?_)
  exact hf (by
    rw [map_mul, map_mul]
    exact hTcomm.is_comm.comm (f x) (f y))

theorem HeisData.exists_isPGroup_card_eq_125 (hd : HeisData Q) :
    ∃ S : Subgroup Q, IsPGroup 5 S ∧ Nat.card S = 125 ∧
      ∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a := by
  obtain ⟨x, y, hx5, hy5, hzx, hzy, hz1, hQ⟩ := hd
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hz5 : ⁅y, x⁆ ^ 5 = 1 := by
    rw [hzy.symm.commutatorElement_pow_left 5, hy5]
    exact commutatorElement_one_left (G := Q) (g := x)
  let S : Subgroup Q := Subgroup.closure {x, y}
  have hS5 : IsPGroup 5 S :=
    CFSG.RankThree.PartOne.HNRed.isPGroup_closure_heisenberg hx5 hy5 hzx hzy hz5
  have hxS : x ∈ S := Subgroup.subset_closure (by simp)
  have hyS : y ∈ S := Subgroup.subset_closure (by simp)
  have hnc : x * y ≠ y * x := by
    intro h
    apply hz1
    rw [← commutatorElement_inv, commutatorElement_eq_one_iff_mul_comm.mpr h, inv_one]
  obtain ⟨m, hm⟩ := hS5.exists_card_eq
  have hm3 : m = 3 := by
    have hle : m ≤ 3 := by
      by_contra h
      have h4 : 4 ≤ m := by omega
      exact hQ ((pow_dvd_pow 5 h4).trans (hm ▸ Subgroup.card_subgroup_dvd_card S))
    have hge : 3 ≤ m := by
      by_contra h
      have hm2 : m = 0 ∨ m = 1 ∨ m = 2 := by omega
      have hcomm : ∀ a b : S, a * b = b * a := by
        rcases hm2 with rfl | rfl | rfl
        · have : Subsingleton S :=
            (Nat.card_eq_one_iff_unique.mp (by simpa using hm)).1
          exact fun a b => Subsingleton.elim _ _
        · have : Fact (Nat.card S).Prime := ⟨by rw [hm]; norm_num⟩
          have : IsCyclic S := isCyclic_of_prime_card (p := Nat.card S) rfl
          exact fun a b => IsCyclic.commGroup.mul_comm a b
        · have hScomm : IsMulCommutative S :=
            IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 5) (G := S) hm
          exact fun a b => hScomm.is_comm.comm a b
      exact hnc (congrArg Subtype.val (hcomm ⟨x, hxS⟩ ⟨y, hyS⟩))
    omega
  refine ⟨S, hS5, ?_, ⟨x, hxS, y, hyS, hnc⟩⟩
  rw [hm, hm3]
  norm_num

theorem HeisData.exists_noncomm (hd : HeisData Q) : ∃ a b : Q, a * b ≠ b * a := by
  obtain ⟨-, -, -, a, -, b, -, hab⟩ := hd.exists_isPGroup_card_eq_125
  exact ⟨a, b, hab⟩

theorem HeisData.not_isCyclic_sylow (hd : HeisData Q) (T : Sylow 5 Q) :
    ¬ IsCyclic (T : Subgroup Q) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨S, hS, -, a, ha, b, hb, hab⟩ := hd.exists_isPGroup_card_eq_125
  exact not_isCyclic_sylow_of_exists_noncomm_isPGroup hS ha hb hab T

section PRank

variable {R : Type} [Group R] [Finite R]

theorem HeisData.pRank_le_two (hd : HeisData R) :
    CFSG.Open.pRank 5 (⊤ : Subgroup R) ≤ 2 := by
  obtain ⟨S, -, hScard, a, ha, b, hb, hab⟩ := hd.exists_isPGroup_card_eq_125
  obtain ⟨-, -, -, -, -, -, -, h4⟩ := hd
  exact CFSG.RankThree.PartTwo.Census.pRank_le_two_of_nonabelian (H := R) Nat.prime_five h4
    hScard ⟨a, ha, b, hb, hab⟩

end PRank

end CFSG.CGT.PushingUpLit.CGT6M
