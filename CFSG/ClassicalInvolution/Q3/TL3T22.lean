module

public import CFSG.ClassicalInvolution.Q3.TL3T21
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPair

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

theorem quat_comm_of_comm {n : ℕ} {u x y : QuaternionGroup n} (hu : u * u ≠ 1)
    (hx : x * u = u * x) (hy : y * u = u * y) : x * y = y * x := by
  cases u with
  | a i =>
    have hi : i + i ≠ 0 := by
      intro h
      apply hu
      rw [QuaternionGroup.a_mul_a, h, QuaternionGroup.one_def]
    have rot : ∀ w : QuaternionGroup n, w * QuaternionGroup.a i = QuaternionGroup.a i * w →
        ∃ j, w = QuaternionGroup.a j := by
      intro w hw
      cases w with
      | a j => exact ⟨j, rfl⟩
      | xa j =>
        exfalso
        rw [QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa] at hw
        have h4 : j + i = j - i := QuaternionGroup.xa.inj hw
        exact hi (by linear_combination h4)
    obtain ⟨j, rfl⟩ := rot x hx
    obtain ⟨j', rfl⟩ := rot y hy
    rw [QuaternionGroup.a_mul_a, QuaternionGroup.a_mul_a, add_comm]
  | xa i =>
    cases x with
    | a j =>
      rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a] at hx
      have hj : j + j = 0 := by
        have := QuaternionGroup.xa.inj hx
        linear_combination -this
      cases y with
      | a j' => rw [QuaternionGroup.a_mul_a, QuaternionGroup.a_mul_a, add_comm]
      | xa j' =>
        rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a]
        congr 1
        linear_combination -hj
    | xa j =>
      rw [QuaternionGroup.xa_mul_xa, QuaternionGroup.xa_mul_xa] at hx
      have hj : (i - j) + (i - j) = 0 := by
        have := QuaternionGroup.a.inj hx
        linear_combination this
      cases y with
      | a j' =>
        rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a] at hy
        have hj' : j' + j' = 0 := by
          have := QuaternionGroup.xa.inj hy
          linear_combination -this
        rw [QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa]
        congr 1
        linear_combination hj'
      | xa j' =>
        rw [QuaternionGroup.xa_mul_xa, QuaternionGroup.xa_mul_xa] at hy
        have hj' : (i - j') + (i - j') = 0 := by
          have := QuaternionGroup.a.inj hy
          linear_combination this
        rw [QuaternionGroup.xa_mul_xa, QuaternionGroup.xa_mul_xa]
        congr 1
        linear_combination hj - hj'

variable {G : Type} [Group G]

theorem isQuatSub_comm_of_comm {R : Subgroup G} (h : IsQuatSub R) {u x y : G} (hu : u ∈ R)
    (hx : x ∈ R) (hy : y ∈ R) (hu2 : u * u ≠ 1) (hxu : x * u = u * x) (hyu : y * u = u * y) :
    x * y = y * x := by
  obtain ⟨k, -, ⟨e⟩⟩ := h
  have key : ∀ {a b : G} (ha : a ∈ R) (hb : b ∈ R), a * b = b * a →
      e ⟨a, ha⟩ * e ⟨b, hb⟩ = e ⟨b, hb⟩ * e ⟨a, ha⟩ := by
    intro a b ha hb hab
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hab
  have hu2' : e ⟨u, hu⟩ * e ⟨u, hu⟩ ≠ 1 := by
    intro h1
    apply hu2
    rw [← map_mul, ← map_one e] at h1
    exact congrArg Subtype.val (e.injective h1)
  have h1 := quat_comm_of_comm hu2' (key hx hu hxu) (key hy hu hyu)
  rw [← map_mul, ← map_mul] at h1
  exact congrArg Subtype.val (e.injective h1)

variable [Finite G]

theorem classicalClause_of_two {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω)
    (h2 : ∀ J ∈ Ω, IsPGroup 2 J) : Q3CL.ClassicalClause Ω where
  subnormal := by
    intro K hK
    obtain ⟨⟨z, hz⟩, -⟩ := hΩ.omega1 K hK
    refine ⟨z, hz.mem, orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one,
      PhilipHall.Frame.isSubnormal_of_hypOmegaGen hΩ hK hz⟩
  commOdd := by
    intro J hJ u a b hu _ huu ha hb hau hbu
    have hq : IsQuatSub J := Sec6Gen.isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isPGroup hJ (h2 J hJ))
    have hab := isQuatSub_comm_of_comm hq hu ha hb huu hau hbu
    have h1 : a * b * a⁻¹ * b⁻¹ = 1 := by
      rw [hab]
      group
    rw [h1]
    exact Subgroup.one_mem _

theorem dLeafCls_holds (r : ℕ) : DLeafCls r :=
  fun _ _ _ _ hD => classicalClause_of_two hD.hyp hD.two

end CFSG.ClassicalInvolution.Q3.TC.Thin
