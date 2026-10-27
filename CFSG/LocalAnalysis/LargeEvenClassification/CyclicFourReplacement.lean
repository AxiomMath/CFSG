module

public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsLiftSquare
public import CFSG.LocalAnalysis.LargeEvenClassification.RankTwoBinaryEndResidue
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare

public section

namespace CFSG.LargeEvenClassification.Helpers

theorem binary_cyclic_four_torsion_four_root (n : ℕ)
    (z : ZMod (2 ^ (n + 4))) (hz : 4 • z = 0) :
    ∃ r : ZMod (2 ^ (n + 4)), z = 4 • r := by
  have hdiv : 2 ^ (n + 4) ∣ 4 * z.val := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simpa only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val] using hz
  have hpower : 2 ^ (n + 4) = 4 * 2 ^ (n + 2) := by
    rw [show n + 4 = 2 + (n + 2) by omega, pow_add]
    norm_num
  have hdiv' : 2 ^ (n + 2) ∣ z.val := by
    have hscaled : 4 * 2 ^ (n + 2) ∣ 4 * z.val :=
      (dvd_of_eq hpower.symm).trans hdiv
    exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 4) hscaled
  have hfour : 4 ∣ z.val := (Nat.pow_dvd_pow 2 (by omega : 2 ≤ n + 2)).trans hdiv'
  refine ⟨(z.val / 4 : ℕ), ?_⟩
  rw [nsmul_eq_mul, ← Nat.cast_mul, Nat.mul_div_cancel' hfour, ZMod.natCast_zmod_val]

theorem binary_cyclic_double_mod_four_zero (n : ℕ) (z : ZMod (2 ^ (n + 4)))
    (hz : (ZMod.castHom (Nat.pow_dvd_pow 2 (by omega : 2 ≤ n + 4)) (ZMod 4)) (2 • z) = 0) :
    ∃ r : ZMod (2 ^ (n + 4)), 2 • r = z := by
  have hcast : ((2 * z.val : ℕ) : ZMod 4) = 0 := by
    have hval := ZMod.natCast_zmod_val z
    rw [← hval, map_nsmul, map_natCast, nsmul_eq_mul, ← Nat.cast_mul] at hz
    exact hz
  have hdiv : 4 ∣ 2 * z.val := (ZMod.natCast_eq_zero_iff _ _).mp hcast
  have heven : 2 ∣ z.val := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 2) hdiv
  refine ⟨(z.val / 2 : ℕ), ?_⟩
  rw [nsmul_eq_mul, ← Nat.cast_mul, Nat.mul_div_cancel' heven, ZMod.natCast_zmod_val]

theorem involution_action_left_lift_square {S : Type*} [Group S]
    (A : Subgroup S) [A.Normal] (t : S) (b : A)
    (hcommutative : IsMulCommutative A) :
    ((b : S) * t) ^ 2 = (MulAut.conjNormal (H := A) t b * b : A).val * t ^ 2 := by
  have hcomm : Commute (b : S) (MulAut.conjNormal (H := A) t b : S) :=
    congrArg Subtype.val (@mul_comm' A _ hcommutative b (MulAut.conjNormal (H := A) t b))
  change ((b : S) * t) ^ 2 = (MulAut.conjNormal (H := A) t b : S) * b * t ^ 2
  rw [← hcomm, MulAut.conjNormal_apply]
  simp only [pow_two]
  group

theorem power_scalar_principal {A : Type*} [CommGroup A]
    (n : ℕ) (δ : MulAut A) (hδ : ∀ a : A, δ a = a ^ (1 + 2 ^ (n + 2))) :
    abelianAutomorphismUnits A δ ∈ principalFourSubgroup (AddMonoid.End (Additive A)) := by
  refine ⟨(2 ^ n : ℕ) • (1 : AddMonoid.End (Additive A)), ?_⟩
  apply AddMonoid.End.ext
  intro a
  change Additive.ofMul (δ a.toMul) = a + 4 • ((2 ^ n : ℕ) • a)
  rw [hδ]
  change (1 + 2 ^ (n + 2) : ℕ) • a = a + 4 • ((2 ^ n : ℕ) • a)
  rw [add_nsmul, one_nsmul, smul_smul, pow_add]
  congr 1
  norm_num
  rw [Nat.mul_comm]

theorem cyclic_four_adjusted_scalar_lift {S : Type*} [Group S] [Finite S]
    (hpgroup : IsPGroup 2 S) (A : Subgroup S) [A.Normal]
    (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (n : ℕ) (coordinates : A ≃* Multiplicative (ZMod (2 ^ (n + 4))) × Multiplicative (ZMod 4))
    (t : S) (hscalar : ∀ a : A, MulAut.conjNormal (H := A) t a = a ^ (1 + 2 ^ (n + 3))) :
    ∃ t₀ : S, t₀ ^ 2 = (coordinates.symm (1, Multiplicative.ofAdd 1) : S) ∧
      ∀ a : A, MulAut.conjNormal (H := A) t₀ a = a ^ (1 + 2 ^ (n + 3)) := by
  let : CommGroup A := { (inferInstance : Group A) with mul_comm := @mul_comm' _ _ hcommutative }
  let δ := MulAut.conjNormal (H := A) t
  let y := coordinates.symm (1, Multiplicative.ofAdd 1)
  have hlong (a : A) : (coordinates (δ a)).1.toAdd =
      (binaryCongruenceInvolution (n + 1)).val * (coordinates a).1.toAdd := by
    rw [hscalar, map_pow, binaryCongruenceInvolution_val]
    change (1 + 2 ^ (n + 3) : ℕ) • (coordinates a).1.toAdd = _
    rw [nsmul_eq_mul]
    push_cast
    rfl
  have hshort (a : A) : (coordinates (δ a)).2 = (coordinates a).2 := by
    rw [hscalar, map_pow]
    apply Multiplicative.toAdd.injective
    change (1 + 2 ^ (n + 3) : ℕ) • (coordinates a).2.toAdd = _
    rw [nsmul_eq_mul]
    push_cast
    have hzero : (2 : ZMod 4) ^ (n + 3) = 0 := by
      rw [show n + 3 = 2 + (n + 1) by omega, pow_add]
      have htwo : (2 : ZMod 4) ^ 2 = 0 := by decide +kernel
      rw [htwo, zero_mul]
    rw [hzero, add_zero, one_mul]
  have hsquare : δ ^ 2 = 1 := by
    apply MulEquiv.ext
    intro a
    apply coordinates.injective
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      change (coordinates (δ (δ a))).1.toAdd = (coordinates a).1.toAdd
      rw [hlong, hlong, ← mul_assoc]
      have hunit : (binaryCongruenceInvolution (n + 1)).val *
          (binaryCongruenceInvolution (n + 1)).val = 1 := by
        simpa only [pow_two, Units.val_mul, Units.val_one] using
          congrArg Units.val (binaryCongruenceInvolution_sq (n + 1))
      rw [hunit, one_mul]
    · change (coordinates (δ (δ a))).2 = (coordinates a).2
      rw [hshort, hshort]
  have hnontrivial : δ ≠ 1 := by
    intro h
    let x := coordinates.symm (Multiplicative.ofAdd 1, 1)
    have hx := hlong x
    rw [h] at hx
    change (coordinates x).1.toAdd = (binaryCongruenceInvolution (n + 1)).val * (coordinates x).1.toAdd at hx
    dsimp only [x] at hx
    rw [coordinates.apply_symm_apply] at hx
    change (1 : ZMod (2 ^ (n + 4))) = (binaryCongruenceInvolution (n + 1)).val * 1 at hx
    rw [mul_one] at hx
    apply binaryCongruenceInvolution_ne_one (n + 1)
    exact Units.ext hx.symm
  have hcard := binary_rank_two_square_kernel_card A hcommutative
    (by omega : 0 < n + 4) (by decide : 0 < 2) coordinates
  obtain ⟨a, ha, hprimitive⟩ := central_power_involution_primitive_lift_square hpgroup A
    hcommutative hselfCentralizing hnoEight hcard (n + 1) δ hscalar hsquare hnontrivial t rfl
  have hfixed := lift_square_fixed_by_conjugation A t a ha
  have hfixedLong : (binaryCongruenceInvolution (n + 1)).val * (coordinates a).1.toAdd =
      (coordinates a).1.toAdd := (hlong a).symm.trans (congrArg (fun a => (coordinates a).1.toAdd) hfixed)
  obtain ⟨r, hr⟩ := binaryCongruenceInvolution_fixed_square (n + 1) _ hfixedLong
  have hshortNotDouble : ∀ v : ZMod 4, 2 • v ≠ (coordinates a).2.toAdd := by
    intro v hv
    apply hprimitive (coordinates.symm (Multiplicative.ofAdd r, Multiplicative.ofAdd v))
    apply coordinates.injective
    rw [map_pow, coordinates.apply_symm_apply]
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      change (coordinates a).1.toAdd = 2 • r
      simpa only [two_nsmul] using hr.symm
    · apply Multiplicative.toAdd.injective
      exact hv.symm
  have hshortRoot : ∃ v : ZMod 4, 2 • v = 1 - (coordinates a).2.toAdd := by
    have h : ∀ s : ZMod 4, (∀ v : ZMod 4, 2 • v ≠ s) → ∃ v : ZMod 4, 2 • v = 1 - s := by
      decide +kernel
    exact h _ hshortNotDouble
  obtain ⟨v, hv⟩ := hshortRoot
  let root := coordinates.symm (Multiplicative.ofAdd (-r), Multiplicative.ofAdd v)
  have hroot : root ^ 2 = y * a⁻¹ := by
    apply coordinates.injective
    rw [map_pow, map_mul, map_inv]
    dsimp only [root, y]
    rw [coordinates.apply_symm_apply, coordinates.apply_symm_apply]
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      change 2 • (-r) = 0 + -(coordinates a).1.toAdd
      simpa only [nsmul_neg, zero_add, two_nsmul, neg_add] using congrArg Neg.neg hr
    · apply Multiplicative.toAdd.injective
      change 2 • v = 1 + -(coordinates a).2.toAdd
      simpa only [sub_eq_add_neg] using hv
  obtain ⟨_, hnorm⟩ := abelian_principal_norm (hpgroup.to_subgroup A) δ
    (power_scalar_principal (n + 1) δ hscalar)
  obtain ⟨b, hb⟩ := hnorm root
  have hnormalAction : MulAut.conjNormal (H := A) (b : S) = 1 := by
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    have hcomm : Commute (b : S) (a : S) := congrArg Subtype.val (mul_comm b a)
    exact hcomm.mul_inv_cancel
  refine ⟨(b : S) * t, ?_, ?_⟩
  · rw [involution_action_left_lift_square A t b hcommutative, ← ha]
    change ((δ b * b) * a : A).val = y.val
    rw [hb, hroot]
    group
  · intro a
    rw [map_mul, hnormalAction]
    exact hscalar a

theorem cyclic_four_long_even_coordinates {S : Type*} [Group S]
    (A : Subgroup S) (n : ℕ)
    (coordinates : A ≃* Multiplicative (ZMod (2 ^ (n + 4))) × Multiplicative (ZMod 4)) :
    let x := coordinates.symm (Multiplicative.ofAdd 1, 1)
    let y := coordinates.symm (1, Multiplicative.ofAdd 1)
    ∀ a : A, (a : S) ∈ Subgroup.closure ({(x : S) ^ 2, (y : S)} : Set S) ↔
      ∃ r : ZMod (2 ^ (n + 4)), (coordinates a).1.toAdd = 2 • r := by
  dsimp only
  let x := coordinates.symm (Multiplicative.ofAdd 1, 1)
  let y := coordinates.symm (1, Multiplicative.ofAdd 1)
  let binary : A →* Multiplicative (ZMod 2) :=
    (AddMonoidHom.toMultiplicative
      (ZMod.castHom (dvd_pow_self 2 (by omega : n + 4 ≠ 0)) (ZMod 2)).toAddMonoidHom).comp
      ((MonoidHom.fst _ _).comp coordinates.toMonoidHom)
  have hker : binary.ker.map A.subtype =
      Subgroup.closure ({(x : S) ^ 2, (y : S)} : Set S) := by
    apply le_antisymm
    · rintro s ⟨a, ha, rfl⟩
      have hzero : cyclicPairSmallBinaryReduction (2 ^ (n + 4))
          (dvd_pow_self 2 (by omega : n + 4 ≠ 0)) (coordinates a).1.toAdd = 0 := ha
      obtain ⟨r, hr⟩ := (zmod_binary_reduction_zero (2 ^ (n + 4)) _ _).mp hzero
      have hshape : a = x ^ (2 * r.val) * y ^ (coordinates a).2.toAdd.val := by
        apply coordinates.injective
        rw [map_mul, map_pow, map_pow]
        dsimp only [x, y]
        rw [coordinates.apply_symm_apply, coordinates.apply_symm_apply]
        apply Prod.ext
        · apply Multiplicative.toAdd.injective
          simp only [Prod.fst_mul, Prod.pow_fst, one_pow, mul_one]
          change (coordinates a).1.toAdd = (2 * r.val : ℕ) • (1 : ZMod (2 ^ (n + 4)))
          rw [hr, nsmul_eq_mul, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat,
            ZMod.natCast_zmod_val, mul_one]
        · apply Multiplicative.toAdd.injective
          simp only [Prod.snd_mul, Prod.pow_snd, one_pow, one_mul]
          change (coordinates a).2.toAdd = (coordinates a).2.toAdd.val • (1 : ZMod 4)
          rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
      rw [hshape]
      change (x : S) ^ (2 * r.val) * (y : S) ^ (coordinates a).2.toAdd.val ∈ _
      rw [pow_mul]
      exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
        (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    · apply (Subgroup.closure_le _).mpr
      intro s hs
      rcases Set.mem_insert_iff.mp hs with hs | hs
      · rw [hs]
        refine ⟨x ^ 2, ?_, rfl⟩
        change binary (x ^ 2) = 1
        rw [map_pow]
        change (Multiplicative.ofAdd
          ((ZMod.castHom (dvd_pow_self 2 (by omega : n + 4 ≠ 0)) (ZMod 2))
            (coordinates x).1.toAdd)) ^ 2 = 1
        dsimp only [x]
        rw [coordinates.apply_symm_apply]
        change Multiplicative.ofAdd (2 • ((ZMod.castHom
          (dvd_pow_self 2 (by omega : n + 4 ≠ 0)) (ZMod 2)) 1)) = 1
        rw [map_one]
        decide +kernel
      · have hs' : s = (y : S) := Set.mem_singleton_iff.mp hs
        rw [hs']
        refine ⟨y, ?_, rfl⟩
        change binary y = 1
        dsimp only [binary, y]
        change Multiplicative.ofAdd ((ZMod.castHom
          (dvd_pow_self 2 (by omega : n + 4 ≠ 0)) (ZMod 2))
          (coordinates (coordinates.symm (1, Multiplicative.ofAdd 1))).1.toAdd) = 1
        rw [coordinates.apply_symm_apply]
        change Multiplicative.ofAdd ((ZMod.castHom
          (dvd_pow_self 2 (by omega : n + 4 ≠ 0)) (ZMod 2)) 0) = 1
        rw [map_zero]
        rfl
  intro a
  rw [← hker]
  have hmem : (a : S) ∈ binary.ker.map A.subtype ↔ a ∈ binary.ker := by
    constructor
    · rintro ⟨b, hb, heq⟩
      exact Subtype.ext heq ▸ hb
    · exact fun ha => ⟨a, ha, rfl⟩
  rw [hmem]
  change cyclicPairSmallBinaryReduction (2 ^ (n + 4))
    (dvd_pow_self 2 (by omega : n + 4 ≠ 0)) (coordinates a).1.toAdd = 0 ↔ _
  exact zmod_binary_reduction_zero (2 ^ (n + 4)) _ _

theorem cyclic_four_long_even_normal {S : Type*} [Group S]
    (A : Subgroup S) [A.Normal] (n : ℕ)
    (coordinates : A ≃* Multiplicative (ZMod (2 ^ (n + 4))) × Multiplicative (ZMod 4)) :
    let x := coordinates.symm (Multiplicative.ofAdd 1, 1)
    let y := coordinates.symm (1, Multiplicative.ofAdd 1)
    (Subgroup.closure ({(x : S) ^ 2, (y : S)} : Set S)).Normal := by
  dsimp only
  let x := coordinates.symm (Multiplicative.ofAdd 1, 1)
  let y := coordinates.symm (1, Multiplicative.ofAdd 1)
  let A₀ := Subgroup.closure ({(x : S) ^ 2, (y : S)} : Set S)
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  apply Subgroup.le_normalizer_closure_iff.mpr
  intro s _ a ha
  rcases Set.mem_insert_iff.mp ha with rfl | ha
  · let b := MulAut.conjNormal (H := A) s x
    have hrep : s * (x : S) ^ 2 * s⁻¹ = (b ^ 2 : A).val := by
      change s * (x : S) ^ 2 * s⁻¹ = (MulAut.conjNormal (H := A) s x : S) ^ 2
      rw [MulAut.conjNormal_apply]
      simp only [pow_two]
      group
    rw [hrep]
    apply (cyclic_four_long_even_coordinates A n coordinates (b ^ 2)).mpr
    refine ⟨(coordinates b).1.toAdd, ?_⟩
    rw [map_pow]
    rfl
  · have ha' : a = (y : S) := Set.mem_singleton_iff.mp ha
    rw [ha']
    let b := MulAut.conjNormal (H := A) s y
    change b.val ∈ A₀
    apply (cyclic_four_long_even_coordinates A n coordinates b).mpr
    have hyfour : y ^ 4 = 1 := by
      apply coordinates.injective
      rw [map_pow coordinates, map_one coordinates]
      dsimp only [y]
      rw [coordinates.apply_symm_apply]
      apply Prod.ext
      · simp
      · change Multiplicative.ofAdd (4 • (1 : ZMod 4)) = 1
        decide +kernel
    have hbfour : b ^ 4 = 1 := by
      rw [show b = MulAut.conjNormal (H := A) s y from rfl, ← map_pow, hyfour, map_one]
    have hlong : 4 • (coordinates b).1.toAdd = 0 := by
      have h := congrArg (fun b : A => (coordinates b).1.toAdd) hbfour
      rw [map_pow, map_one] at h
      exact h
    obtain ⟨r, hr⟩ := binary_cyclic_four_torsion_four_root n _ hlong
    refine ⟨2 • r, ?_⟩
    rw [hr, smul_smul]
    norm_num

theorem cyclic_four_scalar_conjugate_long_even {S : Type*} [Group S]
    (A : Subgroup S) [A.Normal] (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A) (n : ℕ)
    (coordinates : A ≃* Multiplicative (ZMod (2 ^ (n + 4))) × Multiplicative (ZMod 4))
    (t : S) (hsquare : t ^ 2 = (coordinates.symm (1, Multiplicative.ofAdd 1) : S))
    (hscalar : ∀ a : A, MulAut.conjNormal (H := A) t a = a ^ (1 + 2 ^ (n + 3))) (s : S) :
    ∃ b : A, s * t * s⁻¹ = b.val * t ∧
      ∃ r : ZMod (2 ^ (n + 4)), (coordinates b).1.toAdd = 2 • r := by
  let action : S →* MulAut A := MulAut.conjNormal
  let δ := action t
  let y := coordinates.symm (1, Multiplicative.ofAdd 1)
  have hcentral : Commute δ (action s) := by
    apply MulEquiv.ext
    intro a
    change δ (action s a) = action s (δ a)
    rw [hscalar, hscalar, map_pow]
  have hkernel : action.ker = A := (conjNormal_ker_eq_centralizer A).trans hselfCentralizing
  have hmem : s * t * s⁻¹ * t⁻¹ ∈ A := by
    apply hkernel.le
    change action (s * t * s⁻¹ * t⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    change action s * δ * (action s)⁻¹ * δ⁻¹ = 1
    rw [hcentral.symm.mul_inv_cancel, mul_inv_cancel]
  let b : A := ⟨s * t * s⁻¹ * t⁻¹, hmem⟩
  have hconj : s * t * s⁻¹ = b.val * t := by
    dsimp only [b]
    group
  have hnorm : δ b * b * y = action s y := by
    apply Subtype.ext
    change (δ b * b : A).val * y.val = (action s y : S)
    rw [← hsquare, ← involution_action_left_lift_square A t b hcommutative, ← hconj]
    change (s * t * s⁻¹) ^ 2 = s * y.val * s⁻¹
    rw [← hsquare]
    simp only [pow_two]
    group
  let reduction : ZMod (2 ^ (n + 4)) →+* ZMod 4 :=
    ZMod.castHom (Nat.pow_dvd_pow 2 (by omega : 2 ≤ n + 4)) (ZMod 4)
  have hyfour : y ^ 4 = 1 := by
    apply coordinates.injective
    rw [map_pow coordinates, map_one coordinates]
    dsimp only [y]
    rw [coordinates.apply_symm_apply]
    apply Prod.ext
    · simp
    · change Multiplicative.ofAdd (4 • (1 : ZMod 4)) = 1
      decide +kernel
  have hconjfour : (action s y) ^ 4 = 1 := by rw [← map_pow, hyfour, map_one]
  have hlongfour : 4 • (coordinates (action s y)).1.toAdd = 0 := by
    have h := congrArg (fun a : A => (coordinates a).1.toAdd) hconjfour
    rw [map_pow, map_one] at h
    exact h
  obtain ⟨r, hr⟩ := binary_cyclic_four_torsion_four_root n _ hlongfour
  have hzero : reduction (coordinates (action s y)).1.toAdd = 0 := by
    rw [hr, map_nsmul]
    have h : ∀ v : ZMod 4, 4 • v = 0 := by decide +kernel
    exact h _
  have hlong := congrArg (fun a : A => (coordinates a).1.toAdd) hnorm
  rw [map_mul coordinates, map_mul coordinates, hscalar, map_pow coordinates] at hlong
  have hy : (coordinates y).1.toAdd = 0 := by
    dsimp only [y]
    rw [coordinates.apply_symm_apply]
    rfl
  change (1 + 2 ^ (n + 3) : ℕ) • (coordinates b).1.toAdd +
    (coordinates b).1.toAdd + (coordinates y).1.toAdd = (coordinates (action s y)).1.toAdd at hlong
  rw [hy, add_zero] at hlong
  have hred := congrArg reduction hlong
  rw [map_add, map_nsmul, add_nsmul, one_nsmul] at hred
  have hpower : ∀ v : ZMod 4, (2 ^ (n + 3) : ℕ) • v = 0 := by
    intro v
    rw [nsmul_eq_mul]
    have hcast : ((2 ^ (n + 3) : ℕ) : ZMod 4) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.pow_dvd_pow 2 (by omega : 2 ≤ n + 3))
    rw [hcast, zero_mul]
  rw [hpower, add_zero, hzero] at hred
  have heven : reduction (2 • (coordinates b).1.toAdd) = 0 := by
    rw [map_nsmul, two_nsmul]
    exact hred
  obtain ⟨q, hq⟩ := binary_cyclic_double_mod_four_zero n _ heven
  exact ⟨b, hconj, q, hq.symm⟩

theorem cyclic_four_replacement_normal {S : Type*} [Group S]
    (A : Subgroup S) [A.Normal] (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A) (n : ℕ)
    (coordinates : A ≃* Multiplicative (ZMod (2 ^ (n + 4))) × Multiplicative (ZMod 4))
    (t : S) (hsquare : t ^ 2 = (coordinates.symm (1, Multiplicative.ofAdd 1) : S))
    (hscalar : ∀ a : A, MulAut.conjNormal (H := A) t a = a ^ (1 + 2 ^ (n + 3))) :
    let x := coordinates.symm (Multiplicative.ofAdd 1, 1)
    (Subgroup.closure ({(x : S) ^ 2, t} : Set S)).Normal := by
  dsimp only
  let x := coordinates.symm (Multiplicative.ofAdd 1, 1)
  let y := coordinates.symm (1, Multiplicative.ofAdd 1)
  let A₀ := Subgroup.closure ({(x : S) ^ 2, (y : S)} : Set S)
  let M := Subgroup.closure ({(x : S) ^ 2, t} : Set S)
  have hA₀le : A₀ ≤ M := by
    apply (Subgroup.closure_le _).mpr
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact Subgroup.subset_closure (by simp)
    · rw [Set.mem_singleton_iff.mp ha, ← hsquare]
      exact M.pow_mem (Subgroup.subset_closure (by simp)) _
  let : A₀.Normal := cyclic_four_long_even_normal A n coordinates
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  apply Subgroup.le_normalizer_closure_iff.mpr
  intro s _ a ha
  rcases Set.mem_insert_iff.mp ha with rfl | ha
  · have hxmem : (x : S) ^ 2 ∈ A₀ := Subgroup.subset_closure (Set.mem_insert _ _)
    exact hA₀le (Subgroup.Normal.conj_mem inferInstance _ hxmem s)
  · rw [Set.mem_singleton_iff.mp ha]
    obtain ⟨b, hb, heven⟩ := cyclic_four_scalar_conjugate_long_even A hcommutative
      hselfCentralizing n coordinates t hsquare hscalar s
    rw [hb]
    exact M.mul_mem (hA₀le ((cyclic_four_long_even_coordinates A n coordinates b).mpr heven))
      (Subgroup.subset_closure (by simp))

theorem commuting_cyclic_pair_coordinates {G : Type*} [Group G] [Finite G]
    (x y : G) (hcommute : Commute x y)
    (hdisjoint : Disjoint (Subgroup.zpowers x) (Subgroup.zpowers y))
    (m n : ℕ) (hx : orderOf x = m) (hy : orderOf y = n) :
    Nonempty (Subgroup.closure ({x, y} : Set G) ≃*
      Multiplicative (ZMod m) × Multiplicative (ZMod n)) := by
  let P := Subgroup.zpowers x
  let Q := Subgroup.zpowers y
  have hcomm (p : P) (q : Q) : Commute (P.subtype p) (Q.subtype q) := by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp p.property
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp q.property
    change Commute p.val q.val
    rw [← hi, ← hj]
    exact hcommute.zpow_zpow i j
  let f := P.subtype.noncommCoprod Q.subtype hcomm
  have hinjective : Function.Injective f :=
    (MonoidHom.noncommCoprod_injective P.subtype Q.subtype hcomm).mpr
      ⟨Subtype.val_injective, Subtype.val_injective, by
        rw [Subgroup.subtype_range, Subgroup.subtype_range]
        exact hdisjoint⟩
  have hrange : f.range = Subgroup.closure ({x, y} : Set G) := by
    dsimp only [f]
    rw [MonoidHom.noncommCoprod_range, Subgroup.subtype_range, Subgroup.subtype_range]
    dsimp only [P, Q]
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    simp only [Set.singleton_union]
  have hP : Nat.card P = m := (Nat.card_zpowers x).trans hx
  have hQ : Nat.card Q = n := (Nat.card_zpowers y).trans hy
  let eP : P ≃* Multiplicative (ZMod m) :=
    (zmodCyclicMulEquiv (G := P) inferInstance).symm.trans
      (AddEquiv.toMultiplicative (ZMod.ringEquivCongr hP).toAddEquiv)
  let eQ : Q ≃* Multiplicative (ZMod n) :=
    (zmodCyclicMulEquiv (G := Q) inferInstance).symm.trans
      (AddEquiv.toMultiplicative (ZMod.ringEquivCongr hQ).toAddEquiv)
  exact ⟨((MonoidHom.ofInjective hinjective).trans (MulEquiv.subgroupCongr hrange)).symm.trans
    (eP.prodCongr eQ)⟩

theorem cyclic_four_replacement_coordinates {S : Type*} [Group S] [Finite S]
    (A : Subgroup S) [A.Normal] (n : ℕ)
    (coordinates : A ≃* Multiplicative (ZMod (2 ^ (n + 4))) × Multiplicative (ZMod 4))
    (t : S) (hsquare : t ^ 2 = (coordinates.symm (1, Multiplicative.ofAdd 1) : S))
    (hscalar : ∀ a : A, MulAut.conjNormal (H := A) t a = a ^ (1 + 2 ^ (n + 3))) :
    let x := coordinates.symm (Multiplicative.ofAdd 1, 1)
    Nonempty (Subgroup.closure ({(x : S) ^ 2, t} : Set S) ≃*
      Multiplicative (ZMod (2 ^ (n + 3))) × Multiplicative (ZMod 8)) := by
  dsimp only
  let x := coordinates.symm (Multiplicative.ofAdd 1, 1)
  let y := coordinates.symm (1, Multiplicative.ofAdd 1)
  have hscalarX : MulAut.conjNormal (H := A) t (x ^ 2) = x ^ 2 := by
    apply coordinates.injective
    rw [hscalar, map_pow, map_pow coordinates]
    dsimp only [x]
    rw [coordinates.apply_symm_apply]
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      change (1 + 2 ^ (n + 3) : ℕ) • (2 • (1 : ZMod (2 ^ (n + 4)))) = 2 • 1
      rw [nsmul_eq_mul, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
      have hzero : (2 : ZMod (2 ^ (n + 4))) ^ (n + 3) * 2 = 0 := by
        rw [← pow_succ]
        exact_mod_cast ZMod.natCast_self (2 ^ (n + 4))
      linear_combination hzero
    · simp
  have hcommute : Commute ((x : S) ^ 2) t := by
    have h := congrArg Subtype.val hscalarX
    rw [MulAut.conjNormal_apply] at h
    change t * (x : S) ^ 2 * t⁻¹ = (x : S) ^ 2 at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  have hxorder : orderOf (x : S) = 2 ^ (n + 4) := by
    have h₁ := orderOf_injective A.subtype Subtype.val_injective x
    have h₂ := orderOf_injective coordinates.toMonoidHom coordinates.injective x
    change orderOf (coordinates x) = orderOf x at h₂
    rw [show coordinates x = (Multiplicative.ofAdd 1, 1) from coordinates.apply_symm_apply _] at h₂
    rw [Prod.orderOf, orderOf_one, Nat.lcm_one_right] at h₂
    exact h₁.trans (h₂.symm.trans (ZMod.addOrderOf_one _))
  have hx2order : orderOf ((x : S) ^ 2) = 2 ^ (n + 3) := by
    rw [orderOf_pow_of_dvd (by decide : 2 ≠ 0) (hxorder ▸ dvd_pow_self 2 (by omega : n + 4 ≠ 0)),
      hxorder, pow_succ, Nat.mul_div_cancel]
    decide
  have hyorder : orderOf (y : S) = 4 := by
    have h₁ := orderOf_injective A.subtype Subtype.val_injective y
    have h₂ := orderOf_injective coordinates.toMonoidHom coordinates.injective y
    change orderOf (coordinates y) = orderOf y at h₂
    rw [show coordinates y = (1, Multiplicative.ofAdd 1) from coordinates.apply_symm_apply _] at h₂
    rw [Prod.orderOf, orderOf_one, Nat.lcm_one_left] at h₂
    exact h₁.trans (h₂.symm.trans (ZMod.addOrderOf_one _))
  have htfour : t ^ 4 ≠ 1 := by
    intro h
    have hy2 : (y : S) ^ 2 = 1 := by
      rw [← hsquare, ← pow_mul]
      exact h
    have hdiv : 4 ∣ 2 := hyorder ▸ orderOf_dvd_of_pow_eq_one hy2
    norm_num at hdiv
  have hteight : t ^ 8 = 1 := by
    have hy4 : (y : S) ^ 4 = 1 := hyorder ▸ pow_orderOf_eq_one (y : S)
    rw [← hsquare, ← pow_mul] at hy4
    exact hy4
  have htorder : orderOf t = 8 := by
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime_pow (p := 2) (n := 2) htfour hteight
  have houtside : t ∉ A := by
    intro ht
    have hcommutative : IsMulCommutative A := by
      apply IsMulCommutative.of_comm
      intro a b
      apply coordinates.injective
      rw [map_mul, map_mul, mul_comm]
    have htAction : MulAut.conjNormal (H := A) t = 1 := by
      apply MulEquiv.ext
      intro a
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      have hc : Commute t a.val := congrArg Subtype.val (@mul_comm' A _ hcommutative ⟨t, ht⟩ a)
      exact hc.mul_inv_cancel
    have hx := hscalar x
    rw [htAction] at hx
    have hcoord := congrArg (fun a : A => (coordinates a).1.toAdd) hx
    rw [map_pow] at hcoord
    change (coordinates x).1.toAdd = (1 + 2 ^ (n + 3) : ℕ) • (coordinates x).1.toAdd at hcoord
    dsimp only [x] at hcoord
    rw [coordinates.apply_symm_apply] at hcoord
    change (1 : ZMod (2 ^ (n + 4))) = (1 + 2 ^ (n + 3) : ℕ) • 1 at hcoord
    have hδ : binaryCongruenceInvolution (n + 1) = 1 := by
      apply Units.ext
      rw [binaryCongruenceInvolution_val]
      change (1 + (2 : ZMod (2 ^ (n + 4))) ^ (n + 3)) = 1
      simpa only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat, mul_one] using hcoord.symm
    exact binaryCongruenceInvolution_ne_one (n + 1) hδ
  have hdisjoint : Disjoint (Subgroup.zpowers ((x : S) ^ 2)) (Subgroup.zpowers t) := by
    apply Subgroup.disjoint_def.mpr
    intro a ha ht
    have hamem : a ∈ A := (Subgroup.zpowers_le.mpr (A.pow_mem x.property 2)) ha
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff a t).mp (mem_powers_iff_mem_zpowers.mpr ht)
    have heven : 2 ∣ j := by
      by_contra hodd
      have hjmod : j % 2 = 1 := by omega
      have hpower : t ^ j = (t ^ 2) ^ (j / 2) * t := by
        rw [← pow_mul, ← pow_succ]
        congr 1
        omega
      have htnormal : t ∈ A := by
        have h₁ : (t ^ 2) ^ (j / 2) ∈ A := A.pow_mem (hsquare ▸ y.property) _
        have h₂ : (t ^ 2) ^ (j / 2) * t ∈ A := hpower ▸ hj ▸ hamem
        simpa only [inv_mul_cancel_left] using A.mul_mem (A.inv_mem h₁) h₂
      exact houtside htnormal
    obtain ⟨k, hk⟩ := heven
    have hay : a = (y : S) ^ k := by
      rw [← hj, hk, pow_mul, hsquare]
    have haA : (x ^ 2) ^ i = y ^ k := Subtype.ext (hi.trans hay)
    have h := congrArg (fun a : A => (coordinates a).2) haA
    rw [map_zpow coordinates, map_pow coordinates, map_pow coordinates] at h
    dsimp only [x, y] at h
    rw [coordinates.apply_symm_apply, coordinates.apply_symm_apply] at h
    have hyk : (Multiplicative.ofAdd (1 : ZMod 4)) ^ k = 1 := by simpa using h.symm
    have hykA : y ^ k = 1 := by
      apply coordinates.injective
      rw [map_pow coordinates, map_one coordinates]
      dsimp only [y]
      rw [coordinates.apply_symm_apply]
      apply Prod.ext
      · simp
      · exact hyk
    rw [hay, show (y : S) ^ k = (y ^ k : A).val from rfl, hykA]
    rfl
  exact commuting_cyclic_pair_coordinates ((x : S) ^ 2) t hcommute hdisjoint
    (2 ^ (n + 3)) 8 hx2order htorder

theorem rank_two_cyclic_times_four_normal_replacement {S : Type*} [Group S] [Finite S]
    (hpgroup : IsPGroup 2 S) (A : Subgroup S) [A.Normal]
    (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (n : ℕ) (coordinates : A ≃* Multiplicative (ZMod (2 ^ (n + 4))) × Multiplicative (ZMod 4))
    (hoccurs : ∃ t : S, ∀ a : A,
      MulAut.conjNormal (H := A) t a = a ^ (1 + 2 ^ (n + 3))) :
    ∃ M : Subgroup S, M.Normal ∧ IsMulCommutative M ∧
      Nonempty (M ≃* Multiplicative (ZMod (2 ^ (n + 3))) × Multiplicative (ZMod 8)) := by
  obtain ⟨t, ht⟩ := hoccurs
  obtain ⟨t₀, hsquare, hscalar⟩ := cyclic_four_adjusted_scalar_lift hpgroup A hcommutative
    hselfCentralizing hnoEight n coordinates t ht
  let x := coordinates.symm (Multiplicative.ofAdd 1, 1)
  let M := Subgroup.closure ({(x : S) ^ 2, t₀} : Set S)
  have hnormal : M.Normal := cyclic_four_replacement_normal A hcommutative
    hselfCentralizing n coordinates t₀ hsquare hscalar
  obtain ⟨e⟩ := cyclic_four_replacement_coordinates A n coordinates t₀ hsquare hscalar
  have hMcommutative : IsMulCommutative M := by
    apply IsMulCommutative.of_comm
    intro a b
    apply e.injective
    rw [map_mul, map_mul, mul_comm]
  exact ⟨M, hnormal, hMcommutative, ⟨e⟩⟩

end CFSG.LargeEvenClassification.Helpers
