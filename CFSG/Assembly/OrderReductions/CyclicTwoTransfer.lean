module

public import CFSG.Assembly.OrderReductions.OddCore

public section

namespace CFSG.OrderReductions.CyclicTwoTransfer

theorem transfer_restriction_bijective {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (sylow : Sylow prime group)
    (normalizer_centralizes : Subgroup.normalizer (sylow : Set group) ≤
      Subgroup.centralizer (sylow : Set group)) :
    Function.Bijective ((MonoidHom.transferSylow sylow normalizer_centralizes).domRestrict
      (sylow : Subgroup group)) := by
  rw [MonoidHom.transferSylow_domRestrict_eq_pow]
  exact (sylow.isPGroup'.powEquiv' sylow.not_dvd_index).bijective

theorem transfer_surjective {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (sylow : Sylow prime group)
    (normalizer_centralizes : Subgroup.normalizer (sylow : Set group) ≤
      Subgroup.centralizer (sylow : Set group)) :
    Function.Surjective (MonoidHom.transferSylow sylow normalizer_centralizes) := by
  intro point
  obtain ⟨element, image_eq⟩ :=
    (transfer_restriction_bijective prime sylow normalizer_centralizes).surjective point
  exact ⟨element.val, image_eq⟩

theorem transfer_kernel_card_eq_index {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (sylow : Sylow prime group)
    (normalizer_centralizes : Subgroup.normalizer (sylow : Set group) ≤
      Subgroup.centralizer (sylow : Set group)) :
    Nat.card (MonoidHom.transferSylow sylow normalizer_centralizes).ker =
      (sylow : Subgroup group).index := by
  let transfer := MonoidHom.transferSylow sylow normalizer_centralizes
  have quotient_card := Nat.card_congr
    (QuotientGroup.quotientKerEquivOfSurjective transfer
      (transfer_surjective prime sylow normalizer_centralizes)).toEquiv
  have product_eq := transfer.ker.card_eq_card_quotient_mul_card_subgroup
  rw [quotient_card] at product_eq
  have index_eq := (sylow : Subgroup group).card_mul_index
  have positive : 0 < Nat.card (sylow : Subgroup group) := Nat.card_pos
  nlinarith

theorem cyclic_sylow_two_normal_odd_complement {group : Type*} [Group group] [Finite group]
    (even_group : Even (Nat.card group)) (sylow : Sylow 2 group) (cyclic : IsCyclic sylow) :
    ∃ normal : Subgroup group, normal.Normal ∧ Odd (Nat.card normal) ∧
      (sylow : Subgroup group).IsComplement' normal := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  have minFac_two : (Nat.card group).minFac = 2 :=
    (Nat.minFac_eq_two_iff _).mpr even_group.two_dvd
  have normalizer_centralizes := cyclic.normalizer_le_centralizer minFac_two
  let transfer := MonoidHom.transferSylow sylow normalizer_centralizes
  have kernel_odd : Odd (Nat.card transfer.ker) :=
    Nat.not_even_iff_odd.mp (fun even_kernel =>
      MonoidHom.not_dvd_card_ker_transferSylow sylow normalizer_centralizes even_kernel.two_dvd)
  have kernel_card := transfer_kernel_card_eq_index 2 sylow normalizer_centralizes
  have product_eq : Nat.card (sylow : Subgroup group) * Nat.card transfer.ker = Nat.card group := by
    rw [kernel_card]
    exact (sylow : Subgroup group).card_mul_index
  have disjoint : Disjoint (sylow : Subgroup group) transfer.ker := by
    apply disjoint_iff_inf_le.mpr
    intro element mem_intersection
    change element = 1
    have internal : (⟨element, mem_intersection.1⟩ : (sylow : Subgroup group)) = 1 := by
      apply (transfer_restriction_bijective 2 sylow normalizer_centralizes).injective
      change transfer element = transfer 1
      rw [MonoidHom.mem_ker.mp mem_intersection.2, map_one]
    exact congrArg Subtype.val internal
  exact ⟨transfer.ker, inferInstance, kernel_odd,
    Subgroup.isComplement'_of_card_mul_and_disjoint product_eq disjoint⟩

theorem cyclic_sylow_two_eq_top_of_oddCore_bot {group : Type*}
    [Group group] [Finite group] (even_group : Even (Nat.card group))
    (core_bot : CFSG.OrderReductions.OddCore.oddCore group = ⊥)
    (sylow : Sylow 2 group) (cyclic : IsCyclic sylow) : (sylow : Subgroup group) = ⊤ := by
  obtain ⟨normal, normal_normal, normal_odd, complement⟩ :=
    cyclic_sylow_two_normal_odd_complement even_group sylow cyclic
  have := normal_normal
  have normal_le := CFSG.OrderReductions.OddCore.normal_le_oddCore normal normal_odd
  rw [core_bot] at normal_le
  have normal_bot : normal = ⊥ := le_antisymm normal_le bot_le
  have sup_top := complement.sup_eq_top
  rwa [normal_bot, sup_bot_eq] at sup_top

theorem involution_central_of_cyclic_sylow_and_oddCore_bot {group : Type*}
    [Group group] [Finite group] (even_group : Even (Nat.card group))
    (core_bot : CFSG.OrderReductions.OddCore.oddCore group = ⊥)
    (sylow : Sylow 2 group) (cyclic : IsCyclic sylow)
    (involution : CFSG.OrderReductions.InvolutionGraph.Involution group) :
    involution.val ∈ Subgroup.center group := by
  have sylow_top := cyclic_sylow_two_eq_top_of_oddCore_bot even_group core_bot sylow cyclic
  have commutative : ∀ first second : group, first * second = second * first := by
    intro first second
    have first_mem : first ∈ (sylow : Subgroup group) := by rw [sylow_top]; trivial
    have second_mem : second ∈ (sylow : Subgroup group) := by rw [sylow_top]; trivial
    let : IsCyclic (sylow : Subgroup group) := cyclic
    let : CommGroup (sylow : Subgroup group) := IsMulCommutative.instCommGroup
    have internal_commutes : (⟨first, first_mem⟩ : (sylow : Subgroup group)) *
        ⟨second, second_mem⟩ = ⟨second, second_mem⟩ * ⟨first, first_mem⟩ := mul_comm _ _
    exact congrArg Subtype.val internal_commutes
  exact Subgroup.mem_center_iff.mpr (fun element => commutative element involution.val)

end CFSG.OrderReductions.CyclicTwoTransfer
