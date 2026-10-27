module

public import CFSG.LocalAnalysis.LargeEvenClassification.DeepAutomorphisms

public section

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

theorem binary_cyclic_double_four_root {exponent : ℕ} (hlarge : 2 ≤ exponent)
    (element source : ZMod (2 ^ exponent)) (hdouble : 2 * element = 4 * source) :
    ∃ root : ZMod (2 ^ exponent), 2 * root = element := by
  let : NeZero (2 ^ exponent) := ⟨pow_ne_zero _ (by decide)⟩
  have hdivides : 4 ∣ 2 ^ exponent := by
    exact Nat.pow_dvd_pow 2 hlarge
  let reduction := ZMod.castHom hdivides (ZMod 4)
  have hresidue := congrArg reduction hdouble
  have helementCast : reduction element = (element.val : ZMod 4) := by
    calc
      _ = reduction ((element.val : ℕ) : ZMod (2 ^ exponent)) :=
        congrArg reduction (ZMod.natCast_zmod_val element).symm
      _ = _ := map_natCast reduction element.val
  have hdoubleResidue : ((2 * element.val : ℕ) : ZMod 4) = 0 := by
    have hfourZero : (4 : ZMod 4) = 0 := by decide
    simpa only [map_mul, map_ofNat, hfourZero, zero_mul, helementCast, Nat.cast_mul,
      Nat.cast_ofNat] using hresidue
  have hfourDivides : 4 ∣ 2 * element.val := (ZMod.natCast_eq_zero_iff _ _).mp hdoubleResidue
  have htwoDivides : 2 ∣ element.val :=
    Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 2) hfourDivides
  refine ⟨(element.val / 2 : ℕ), ?_⟩
  calc
    _ = ((2 * (element.val / 2) : ℕ) : ZMod (2 ^ exponent)) := by
      simp only [Nat.cast_mul, Nat.cast_ofNat]
    _ = (element.val : ZMod (2 ^ exponent)) := congrArg Nat.cast (Nat.mul_div_cancel' htwoDivides)
    _ = element := ZMod.natCast_zmod_val element

theorem binary_rank_two_power_root {Ambient : Type groupUniverse} [Group Ambient]
    (Normal : Subgroup Ambient) (hcommutative : IsMulCommutative Normal) {upper lower : ℕ}
    (hupper : 2 ≤ upper) (hlower : 2 ≤ lower)
    (coordinates : Normal ≃* Multiplicative (ZMod (2 ^ upper)) ×
      Multiplicative (ZMod (2 ^ lower))) (element : Normal)
    (hfourth : (element : Ambient) ^ 2 ∈ normalPowerSubgroup Normal hcommutative 4) :
    (element : Ambient) ∈ normalPowerSubgroup Normal hcommutative 2 := by
  obtain ⟨source, hsource⟩ := (normalPowerSubgroup_mem Normal hcommutative 4 _).mp hfourth
  have hsquare : element ^ 2 = source ^ 4 := Subtype.ext hsource.symm
  have hcoordinates := congrArg coordinates hsquare
  rw [map_pow, map_pow] at hcoordinates
  have hfirst : 2 * (coordinates element).1.toAdd = 4 * (coordinates source).1.toAdd := by
    have heq := congrArg (fun pair => pair.1.toAdd) hcoordinates
    change 2 • (coordinates element).1.toAdd = 4 • (coordinates source).1.toAdd at heq
    simpa only [nsmul_eq_mul, Nat.cast_ofNat] using heq
  have hsecond : 2 * (coordinates element).2.toAdd = 4 * (coordinates source).2.toAdd := by
    have heq := congrArg (fun pair => pair.2.toAdd) hcoordinates
    change 2 • (coordinates element).2.toAdd = 4 • (coordinates source).2.toAdd at heq
    simpa only [nsmul_eq_mul, Nat.cast_ofNat] using heq
  obtain ⟨firstRoot, hfirstRoot⟩ := binary_cyclic_double_four_root hupper _ _ hfirst
  obtain ⟨secondRoot, hsecondRoot⟩ := binary_cyclic_double_four_root hlower _ _ hsecond
  let root := coordinates.symm (Multiplicative.ofAdd firstRoot, Multiplicative.ofAdd secondRoot)
  apply (normalPowerSubgroup_mem Normal hcommutative 2 _).mpr
  refine ⟨root, ?_⟩
  have hroot : root ^ 2 = element := by
    apply coordinates.injective
    rw [map_pow]
    change (coordinates (coordinates.symm _)) ^ 2 = coordinates element
    rw [coordinates.apply_symm_apply]
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      change 2 • firstRoot = (coordinates element).1.toAdd
      simpa only [nsmul_eq_mul, Nat.cast_ofNat] using hfirstRoot
    · apply Multiplicative.toAdd.injective
      change 2 • secondRoot = (coordinates element).2.toAdd
      simpa only [nsmul_eq_mul, Nat.cast_ofNat] using hsecondRoot
  exact congrArg (fun entry : Normal => (entry : Ambient)) hroot

theorem binary_rank_two_square_kernel_card {Ambient : Type groupUniverse} [Group Ambient]
    (Normal : Subgroup Ambient) (hcommutative : IsMulCommutative Normal) {upper lower : ℕ}
    (hupper : 0 < upper) (hlower : 0 < lower)
    (coordinates : Normal ≃* Multiplicative (ZMod (2 ^ upper)) ×
      Multiplicative (ZMod (2 ^ lower))) :
    Nat.card (normalElementarySquareKernel Normal hcommutative) = 4 := by
  let : NeZero (2 ^ upper) := ⟨pow_ne_zero _ (by decide)⟩
  let : NeZero (2 ^ lower) := ⟨pow_ne_zero _ (by decide)⟩
  let : Finite Normal := Finite.of_equiv _ coordinates.toEquiv.symm
  let : CommGroup Normal := { (inferInstance : Group Normal) with
    mul_comm := @mul_comm' Normal _ hcommutative }
  let kernelEquivalence : (powMonoidHom 2 : Normal →* Normal).ker ≃*
      (powMonoidHom 2 : Multiplicative (ZMod (2 ^ upper)) →* _).ker ×
        (powMonoidHom 2 : Multiplicative (ZMod (2 ^ lower)) →* _).ker := {
    toFun := fun element =>
      (⟨(coordinates element).1, by
        change (coordinates element).1 ^ 2 = 1
        exact congrArg (fun pair : Multiplicative (ZMod (2 ^ upper)) ×
          Multiplicative (ZMod (2 ^ lower)) => pair.1) (show (coordinates element) ^ 2 = 1 from
            by rw [← map_pow, show (element : Normal) ^ 2 = 1 from element.property, map_one])⟩,
      ⟨(coordinates element).2, by
        change (coordinates element).2 ^ 2 = 1
        exact congrArg (fun pair : Multiplicative (ZMod (2 ^ upper)) ×
          Multiplicative (ZMod (2 ^ lower)) => pair.2) (show (coordinates element) ^ 2 = 1 from
            by rw [← map_pow, show (element : Normal) ^ 2 = 1 from element.property, map_one])⟩)
    invFun := fun pair => ⟨coordinates.symm (pair.1.val, pair.2.val), by
      change (coordinates.symm (pair.1.val, pair.2.val)) ^ 2 = 1
      apply coordinates.injective
      rw [map_pow, coordinates.apply_symm_apply, map_one]
      exact Prod.ext pair.1.property pair.2.property⟩
    left_inv := by intro element; apply Subtype.ext; exact coordinates.symm_apply_apply _
    right_inv := by
      intro pair
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg Prod.fst (coordinates.apply_symm_apply (pair.1.val, pair.2.val))
      · apply Subtype.ext
        exact congrArg Prod.snd (coordinates.apply_symm_apply (pair.1.val, pair.2.val))
    map_mul' := by
      intro first second
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg Prod.fst (map_mul coordinates (first : Normal) (second : Normal))
      · apply Subtype.ext
        exact congrArg Prod.snd (map_mul coordinates (first : Normal) (second : Normal)) }
  change Nat.card ((powMonoidHom 2 : Normal →* Normal).ker.map Normal.subtype) = 4
  rw [Subgroup.card_map_of_injective Subtype.val_injective,
    Nat.card_congr kernelEquivalence.toEquiv, Nat.card_prod,
    IsCyclic.card_powMonoidHom_ker, IsCyclic.card_powMonoidHom_ker,
    Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_congr Multiplicative.ofAdd.symm,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ZMod.card, ZMod.card]
  rw [Nat.gcd_eq_right (dvd_pow_self 2 (Nat.ne_zero_of_lt hupper)),
    Nat.gcd_eq_right (dvd_pow_self 2 (Nat.ne_zero_of_lt hlower))]

theorem rank_two_deep_involutions_card_bound {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (hpgroup : IsPGroup 2 Ambient) (Normal : Subgroup Ambient) [Normal.Normal]
    (hcommutative : IsMulCommutative Normal)
    (hselfCentralizing : Subgroup.centralizer (Normal : Set Ambient) = Normal)
    (hnoEight : ∀ Eight : Subgroup Ambient, Eight.Normal →
      CFSG.Open.IsElemAbelian 2 Eight → Nat.card Eight ≠ 8)
    {upper lower : ℕ} (hupper : 2 ≤ upper) (hlower : 2 ≤ lower)
    (coordinates : Normal ≃* Multiplicative (ZMod (2 ^ upper)) ×
      Multiplicative (ZMod (2 ^ lower))) :
    let _ : CommGroup Normal := { (inferInstance : Group Normal) with
      mul_comm := @mul_comm' Normal _ hcommutative }
    ∃ Involutions : Subgroup (MulAut Normal),
      (∀ automorphism : MulAut Normal, automorphism ∈ Involutions ↔
        automorphism ∈ deepAbelianAutomorphisms Normal ∧ automorphism ^ 2 = 1 ∧
          automorphism ∈ (MulAut.conjNormal (H := Normal)).range) ∧ Nat.card Involutions ≤ 4 := by
  dsimp only
  let : CommGroup Normal := { (inferInstance : Group Normal) with
    mul_comm := @mul_comm' Normal _ hcommutative }
  have hroot := binary_rank_two_power_root Normal hcommutative hupper hlower coordinates
  have hcard := binary_rank_two_square_kernel_card Normal hcommutative (by omega) (by omega) coordinates
  let : (normalPowerSubgroup Normal hcommutative 2).Normal :=
    normalPowerSubgroup_normal Normal hcommutative 2
  obtain ⟨Involutions, helementary, hshape, squareMap, hinjective, hsquares⟩ :=
    exists_deep_conjugation_square_injection hpgroup Normal hcommutative hselfCentralizing
      hnoEight hcard hroot
  have hnormalRank : pGeneratorRank 2 Normal ≤ 2 := by
    obtain ⟨generators, hgenerates, hcard⟩ :=
      no_normal_eight_abelian_normal_two_generators hpgroup hnoEight Normal hcommutative
    exact (pGeneratorRank_le_generators Nat.prime_two (hpgroup.to_subgroup Normal)
      generators hgenerates).trans hcard
  have hlifts : ∀ automorphism : Involutions, ∃ lift : Ambient,
      MulAut.conjNormal (H := Normal) lift = (automorphism : MulAut Normal) := by
    intro automorphism
    exact ((hshape _).mp automorphism.property).2.2
  exact ⟨Involutions, hshape, conjugation_square_injection_card_bound hpgroup Normal hcommutative
    hselfCentralizing hnormalRank Involutions helementary hlifts squareMap hinjective hsquares⟩

end CFSG.LargeEvenClassification.Helpers
