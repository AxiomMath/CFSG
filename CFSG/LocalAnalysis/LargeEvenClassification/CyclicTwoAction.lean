module

public import CFSG.LocalAnalysis.LargeEvenClassification.AbelianGeneratorRank

public section

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse targetUniverse

theorem binary_unit_card (exponent : ℕ) :
    Nat.card (ZMod (2 ^ (exponent + 1)))ˣ = 2 ^ exponent := by
  let : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by decide)⟩
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow_succ Nat.prime_two]
  simp

theorem binary_unit_mod_four_kernel_cyclic (exponent : ℕ) :
    IsCyclic (ZMod.unitsMap (show 4 ∣ 2 ^ (exponent + 2) from by
      rw [pow_add]
      exact dvd_mul_left _ _)).ker := by
  let : NeZero (2 ^ (exponent + 2)) := ⟨pow_ne_zero _ (by decide)⟩
  let divides : 4 ∣ 2 ^ (exponent + 2) := by
    rw [pow_add]
    exact dvd_mul_left _ _
  let reduction := ZMod.unitsMap divides
  have hsurjective : Function.Surjective reduction := ZMod.unitsMap_surjective divides
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup reduction.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective reduction hsurjective).toEquiv]
    at hcard
  have hsourceCard : Nat.card (ZMod (2 ^ (exponent + 2)))ˣ = 2 ^ (exponent + 1) :=
    binary_unit_card (exponent + 1)
  have htargetCard : Nat.card (ZMod 4)ˣ = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hkernelCard : Nat.card reduction.ker = 2 ^ exponent := by
    rw [hsourceCard, htargetCard, pow_succ] at hcard
    omega
  let five : (ZMod (2 ^ (exponent + 2)))ˣ :=
    ZMod.unitOfCoprime 5 ((by decide : Nat.Coprime 5 2).pow_right _)
  have hfiveKernel : five ∈ reduction.ker := by
    apply Units.ext
    change ((ZMod.unitsMap divides) five : ZMod 4) = 1
    rw [ZMod.unitsMap_val]
    change (5 : ZMod (2 ^ (exponent + 2))).cast = (1 : ZMod 4)
    rw [show (5 : ZMod (2 ^ (exponent + 2))) = (5 : ℕ) from rfl,
      ZMod.cast_natCast divides]
    decide
  have horder : orderOf (⟨five, hfiveKernel⟩ : reduction.ker) = 2 ^ exponent := by
    rw [Subgroup.orderOf_mk, ← orderOf_units]
    change orderOf (5 : ZMod (2 ^ (exponent + 2))) = 2 ^ exponent
    exact ZMod.orderOf_five exponent
  apply isCyclic_of_card_le_orderOf ⟨five, hfiveKernel⟩
  rw [horder, hkernelCard]

theorem binary_units_two_generators (exponent : ℕ) :
    ∃ generators : Finset (ZMod (2 ^ exponent))ˣ,
      Subgroup.closure (generators : Set (ZMod (2 ^ exponent))ˣ) = ⊤ ∧
        generators.card ≤ 2 := by
  rcases exponent with _ | exponent
  · let : IsCyclic (ZMod (2 ^ 0))ˣ := by simpa using ZMod.isCyclic_units_one
    obtain ⟨generators, hgenerates, hcard⟩ := cyclic_generators (Ambient := (ZMod (2 ^ 0))ˣ)
    exact ⟨generators, hgenerates, hcard.trans (by decide)⟩
  rcases exponent with _ | exponent
  · let : IsCyclic (ZMod (2 ^ 1))ˣ := by simpa using ZMod.isCyclic_units_two
    obtain ⟨generators, hgenerates, hcard⟩ := cyclic_generators (Ambient := (ZMod (2 ^ 1))ˣ)
    exact ⟨generators, hgenerates, hcard.trans (by decide)⟩
  let : NeZero (2 ^ (exponent + 2)) := ⟨pow_ne_zero _ (by decide)⟩
  let divides : 4 ∣ 2 ^ (exponent + 2) := by
    rw [pow_add]
    exact dvd_mul_left _ _
  let reduction := ZMod.unitsMap divides
  let : IsCyclic reduction.ker := binary_unit_mod_four_kernel_cyclic exponent
  let : IsCyclic (ZMod 4)ˣ := ZMod.isCyclic_units_four
  exact extension_generator_bound reduction (ZMod.unitsMap_surjective divides)
    (cyclic_generators (Ambient := reduction.ker)) (cyclic_generators (Ambient := (ZMod 4)ˣ))

theorem binary_units_isPGroup (exponent : ℕ) : IsPGroup 2 (ZMod (2 ^ exponent))ˣ := by
  rcases exponent with _ | exponent
  · apply IsPGroup.of_card (n := 0)
    rw [Nat.card_eq_fintype_card]
    decide
  · exact IsPGroup.of_card (binary_unit_card exponent)

theorem two_group_embedding_binary_units_rank {Source : Type groupUniverse} [Group Source]
    [Finite Source] (exponent : ℕ)
    (embedding : Source →* (ZMod (2 ^ exponent))ˣ) (hinjective : Function.Injective embedding) :
    pGeneratorRank 2 Source ≤ 2 := by
  let : NeZero (2 ^ exponent) := ⟨pow_ne_zero _ (by decide)⟩
  let : CommGroup Source := { (inferInstance : Group Source) with
    mul_comm := fun first second => hinjective (by rw [map_mul, map_mul, mul_comm]) }
  have hbound := commutative_pGeneratorRank_embedding_le Nat.prime_two
    (binary_units_isPGroup exponent) embedding hinjective
  obtain ⟨generators, hgenerates, hcard⟩ := binary_units_two_generators exponent
  exact hbound.trans ((pGeneratorRank_le_generators Nat.prime_two
    (binary_units_isPGroup exponent) generators hgenerates).trans hcard)

theorem cyclic_two_aut_subgroup_generator_rank {Normal : Type groupUniverse} [Group Normal]
    [Finite Normal] [IsCyclic Normal] (hpnormal : IsPGroup 2 Normal)
    (Action : Subgroup (MulAut Normal)) :
    pGeneratorRank 2 Action ≤ 2 := by
  obtain ⟨exponent, hcard⟩ := hpnormal.exists_card_eq
  let equivalence : MulAut Normal ≃* (ZMod (2 ^ exponent))ˣ := by
    rw [← hcard]
    exact IsCyclic.mulAutMulEquiv Normal
  let embedding := equivalence.toMonoidHom.comp Action.subtype
  have hinjective : Function.Injective embedding :=
    equivalence.injective.comp Subtype.val_injective
  exact two_group_embedding_binary_units_rank exponent embedding hinjective

end CFSG.LargeEvenClassification.Helpers
