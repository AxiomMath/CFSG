module

public import CFSG.Assembly.OrderReductions.InvolutionFusion
public import CFSG.Assembly.OrderReductions.FixedPointLifting

public section

namespace CFSG.OrderReductions.OddKernelInvolutions

open CFSG.OrderReductions.InvolutionGraph

theorem involution_image_order {source target : Type*} [Group source] [Group target]
    (homomorphism : source →* target) (odd_kernel : Odd (Nat.card homomorphism.ker))
    (involution : Involution source) : orderOf (homomorphism involution.val) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  apply orderOf_eq_prime
  · rw [← map_pow]
    have square_one : involution.val ^ 2 = 1 := by
      simpa only [involution.property] using pow_orderOf_eq_one involution.val
    rw [square_one, map_one]
  · intro image_one
    have divides := homomorphism.ker.orderOf_dvd_natCard (MonoidHom.mem_ker.mpr image_one)
    rw [involution.property] at divides
    exact odd_kernel.not_two_dvd_nat divides

theorem involution_pow_odd {group : Type*} [Group group] (involution : Involution group)
    (exponent : ℕ) (odd_exponent : Odd exponent) : involution.val ^ exponent = involution.val := by
  obtain ⟨half, exponent_eq⟩ := odd_exponent
  have exponent_eq' : exponent = 2 * half + 1 := by omega
  have square_one : involution.val ^ 2 = 1 := by
    simpa only [involution.property] using pow_orderOf_eq_one involution.val
  rw [exponent_eq', pow_add, pow_mul, square_one, one_pow, pow_one, one_mul]

theorem exists_involution_power_lift {source target : Type*}
    [Group source] [Finite source] [Group target]
    (homomorphism : source →* target) (odd_kernel : Odd (Nat.card homomorphism.ker))
    (involution : Involution target) (element : source)
    (image_eq : homomorphism element = involution.val) :
    ∃ exponent : ℕ, orderOf (element ^ exponent) = 2 ∧
      homomorphism (element ^ exponent) = involution.val := by
  have even_order : 2 ∣ orderOf element := by
    have divides := orderOf_map_dvd homomorphism element
    rwa [image_eq, involution.property] at divides
  have square_mem : element ^ 2 ∈ homomorphism.ker := by
    rw [MonoidHom.mem_ker, map_pow, image_eq]
    simpa only [involution.property] using pow_orderOf_eq_one involution.val
  have odd_square_order : Odd (orderOf (element ^ 2)) :=
    odd_kernel.of_dvd_nat (homomorphism.ker.orderOf_dvd_natCard square_mem)
  have gcd_eq : (orderOf element).gcd 2 = 2 := Nat.gcd_eq_right even_order
  rw [orderOf_pow, gcd_eq] at odd_square_order
  refine ⟨orderOf element / 2,
    orderOf_pow_orderOf_div (ne_of_gt (orderOf_pos element)) even_order, ?_⟩
  rw [map_pow, image_eq]
  exact involution_pow_odd involution _ odd_square_order

theorem exists_involution_lift {source target : Type*}
    [Group source] [Finite source] [Group target]
    (homomorphism : source →* target) (surjective : Function.Surjective homomorphism)
    (odd_kernel : Odd (Nat.card homomorphism.ker)) (involution : Involution target) :
    ∃ lift : Involution source, homomorphism lift.val = involution.val := by
  obtain ⟨element, image_eq⟩ := surjective involution.val
  obtain ⟨exponent, power_order, power_image⟩ :=
    exists_involution_power_lift homomorphism odd_kernel involution element image_eq
  exact ⟨⟨element ^ exponent, power_order⟩, power_image⟩

theorem exists_commuting_involution_lift {source target : Type*}
    [Group source] [Finite source] [Group target]
    (homomorphism : source →* target) (surjective : Function.Surjective homomorphism)
    (odd_kernel : Odd (Nat.card homomorphism.ker)) (first : Involution source)
    (second : Involution target) (commutes : Commute (homomorphism first.val) second.val) :
    ∃ lift : Involution source, homomorphism lift.val = second.val ∧
      Commute first.val lift.val := by
  let source_action := MulAut.conj first.val
  let target_action := MulAut.conj (homomorphism first.val)
  have involutive : Function.Involutive source_action := by
    intro element
    have square_one := CFSG.OrderReductions.InvolutionFusion.involution_mul_self first
    rw [MulAut.conj_apply, MulAut.conj_apply,
      inv_eq_self_of_orderOf_eq_two first.property]
    calc
      first.val * (first.val * element * first.val) * first.val =
          (first.val * first.val) * element * (first.val * first.val) := by group
      _ = element := by rw [square_one, one_mul, mul_one]
  have equivariant : ∀ element : source,
      homomorphism (source_action element) = target_action (homomorphism element) := by
    intro element
    change homomorphism (first.val * element * first.val⁻¹) =
      homomorphism first.val * homomorphism element * (homomorphism first.val)⁻¹
    rw [map_mul, map_mul, map_inv]
  have fixed_second : target_action second.val = second.val := by
    change homomorphism first.val * second.val * (homomorphism first.val)⁻¹ = second.val
    rw [commutes.eq, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨element, element_image, element_fixed⟩ :=
    CFSG.OrderReductions.FixedPointLifting.exists_fixed_lift_of_odd_kernel source_action target_action
      involutive homomorphism surjective odd_kernel equivariant second.val fixed_second
  obtain ⟨exponent, power_order, power_image⟩ :=
    exists_involution_power_lift homomorphism odd_kernel second element element_image
  have element_commutes : Commute first.val element := by
    change first.val * element * first.val⁻¹ = element at element_fixed
    exact mul_inv_eq_iff_eq_mul.mp element_fixed
  exact ⟨⟨element ^ exponent, power_order⟩, power_image, element_commutes.pow_right exponent⟩

theorem exists_four_involutions_lift {source target : Type*}
    [Group source] [Finite source] [Group target]
    (homomorphism : source →* target) (surjective : Function.Surjective homomorphism)
    (odd_kernel : Odd (Nat.card homomorphism.ker)) (first second : Involution target)
    (distinct : first ≠ second) (commutes : Commute first.val second.val) :
    ∃ first_lift second_lift : Involution source,
      first_lift ≠ second_lift ∧ Commute first_lift.val second_lift.val ∧
      homomorphism first_lift.val = first.val ∧ homomorphism second_lift.val = second.val := by
  obtain ⟨first_lift, first_image⟩ := exists_involution_lift homomorphism surjective odd_kernel first
  have first_commutes : Commute (homomorphism first_lift.val) second.val := by
    rwa [first_image]
  obtain ⟨second_lift, second_image, lifts_commute⟩ := exists_commuting_involution_lift
    homomorphism surjective odd_kernel first_lift second first_commutes
  refine ⟨first_lift, second_lift, ?_, lifts_commute, first_image, second_image⟩
  intro equal_lifts
  have equal_images := congrArg (fun lift : Involution source => homomorphism lift.val) equal_lifts
  rw [first_image, second_image] at equal_images
  exact distinct (Subtype.ext equal_images)

theorem quotient_no_four_involutions {source target : Type*}
    [Group source] [Finite source] [Group target]
    (homomorphism : source →* target) (surjective : Function.Surjective homomorphism)
    (odd_kernel : Odd (Nat.card homomorphism.ker))
    (no_four : ∀ first second : Involution source,
      Commute first.val second.val → first = second)
    (first second : Involution target) (commutes : Commute first.val second.val) : first = second := by
  by_contra distinct
  obtain ⟨first_lift, second_lift, lifts_distinct, lifts_commute, _, _⟩ :=
    exists_four_involutions_lift homomorphism surjective odd_kernel first second distinct commutes
  exact lifts_distinct (no_four first_lift second_lift lifts_commute)

theorem common_involution_image_of_central_and_no_four {source target : Type*}
    [Group source] [Finite source] [Group target]
    (homomorphism : source →* target) (surjective : Function.Surjective homomorphism)
    (odd_kernel : Odd (Nat.card homomorphism.ker))
    (no_four : ∀ first second : Involution source,
      Commute first.val second.val → first = second)
    (central_images : ∀ involution : Involution source,
      homomorphism involution.val ∈ Subgroup.center target)
    (first second : Involution source) : homomorphism first.val = homomorphism second.val := by
  let first_image : Involution target :=
    ⟨homomorphism first.val, involution_image_order homomorphism odd_kernel first⟩
  let second_image : Involution target :=
    ⟨homomorphism second.val, involution_image_order homomorphism odd_kernel second⟩
  have commutes : Commute first_image.val second_image.val :=
    ((Subgroup.mem_center_iff.mp (central_images first)) second_image.val).symm
  exact congrArg Subtype.val
    (quotient_no_four_involutions homomorphism surjective odd_kernel no_four
      first_image second_image commutes)

end CFSG.OrderReductions.OddKernelInvolutions
