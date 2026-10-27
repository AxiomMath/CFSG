module

public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoGeneratorStrata
public import CFSG.LocalAnalysis.LargeEvenClassification.LargeExponentFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourLiftSquare
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare

public section

namespace CFSG.LargeEvenClassification.Helpers

open scoped commutatorElement

@[expose] noncomputable def cyclicTwoAutomorphismEquiv {A : Type*} [Group A]
    (hcommutative : IsMulCommutative A) (n : ℕ)
    (coordinates : Additive A ≃+ CyclicTwoSpace n) : MulAut A ≃* CyclicTwoAut n := by
  let : CommGroup A := { (inferInstance : Group A) with mul_comm := @mul_comm' _ _ hcommutative }
  exact (MulEquiv.ofBijective (abelianAutomorphismUnits A)
    ⟨abelianAutomorphismUnits_injective A, abelianAutomorphismUnits_surjective A⟩).trans
    (Units.mapEquiv (addEndCoordinateTransport coordinates).toMulEquiv)

theorem cyclicTwoAutomorphismEquiv_apply {A : Type*} [Group A]
    (hcommutative : IsMulCommutative A) (n : ℕ)
    (coordinates : Additive A ≃+ CyclicTwoSpace n) (α : MulAut A) (a : A) :
    coordinates (Additive.ofMul (α a)) =
      (cyclicTwoAutomorphismEquiv hcommutative n coordinates α).val
        (coordinates (Additive.ofMul a)) := by
  let : CommGroup A := { (inferInstance : Group A) with mul_comm := @mul_comm' _ _ hcommutative }
  change coordinates (Additive.ofMul (α a)) =
    coordinates ((abelianAutomorphismUnits A α).val
      (coordinates.symm (coordinates (Additive.ofMul a))))
  rw [coordinates.symm_apply_apply]
  rfl

@[expose] def cyclicTwoBinaryCoordinates (n : ℕ) : CyclicTwoSpace n →+ ZMod 2 × ZMod 2 where
  toFun x := (cyclicReduction (2 ^ (n + 2)) 2 x.1, x.2)
  map_zero' := Prod.ext (map_zero _) rfl
  map_add' x y := Prod.ext (map_add _ x.1 y.1) rfl

theorem cyclicTwoBinaryCoordinates_two (n : ℕ) (x : CyclicTwoSpace n) :
    cyclicTwoBinaryCoordinates n (2 • x) = 0 := by
  rw [map_nsmul]
  have h : ∀ x : ZMod 2 × ZMod 2, 2 • x = 0 := by decide +kernel
  exact h _

theorem cyclicTwoBinaryCoordinates_zero_iff (n : ℕ) (x : CyclicTwoSpace n) :
    cyclicTwoBinaryCoordinates n x = 0 ↔ ∃ y : CyclicTwoSpace n, 2 • y = x := by
  constructor
  · intro h
    have hlong := congrArg Prod.fst h
    have hshort := congrArg Prod.snd h
    change cyclicReduction (2 ^ (n + 2)) 2 x.1 = 0 at hlong
    change x.2 = 0 at hshort
    have heven : 2 ∣ x.1.val := by
      rw [cyclicReduction_apply] at hlong
      exact (ZMod.natCast_eq_zero_iff _ _).mp hlong
    refine ⟨((x.1.val / 2 : ℕ), 0), ?_⟩
    apply Prod.ext
    · change 2 • ((x.1.val / 2 : ℕ) : ZMod (2 ^ (n + 2) * 2)) = x.1
      rw [nsmul_eq_mul, ← Nat.cast_mul, Nat.mul_div_cancel' heven, ZMod.natCast_zmod_val]
    · simpa using hshort.symm
  · rintro ⟨y, rfl⟩
    exact cyclicTwoBinaryCoordinates_two n y

theorem cyclicTwoBinaryCoordinates_tau (n : ℕ) (x : CyclicTwoSpace n) :
    cyclicTwoBinaryCoordinates n ((cyclicTwoTau n).val x) = cyclicTwoBinaryCoordinates n x := by
  rw [cyclicTwoTau_apply]
  apply Prod.ext
  · change cyclicReduction (2 ^ (n + 2)) 2 (x.1 + scaledCyclicInclusion (2 ^ (n + 2)) 2 x.2) =
      cyclicReduction (2 ^ (n + 2)) 2 x.1
    rw [map_add, cyclicReduction_inclusion]
    have heven : ((2 ^ (n + 2) : ℕ) : ZMod 2) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_pow_self _ (by omega))
    rw [heven, zero_mul, add_zero]
  · rfl

theorem cyclicTwoBinaryCoordinates_scalar (n : ℕ) (u : (ZMod (2 ^ (n + 2) * 2))ˣ)
    (x : CyclicTwoSpace n) :
    cyclicTwoBinaryCoordinates n ((cyclicTwoScalar n u).val x) = cyclicTwoBinaryCoordinates n x := by
  rw [cyclicTwoScalar_apply]
  apply Prod.ext
  · change cyclicReduction (2 ^ (n + 2)) 2 (u.val * x.1) = cyclicReduction (2 ^ (n + 2)) 2 x.1
    rw [map_mul, cyclicTwo_unit_reduction, one_mul]
  · rfl

theorem cyclicTwo_tau_fixed_short (n : ℕ) (x : CyclicTwoSpace n)
    (hfixed : (cyclicTwoTau n).val x = x) : x.2 = 0 := by
  rw [cyclicTwoTau_apply] at hfixed
  have hlong := congrArg Prod.fst hfixed
  have hzero : scaledCyclicInclusion (2 ^ (n + 2)) 2 x.2 = 0 := by
    exact add_left_cancel (hlong.trans (add_zero x.1).symm)
  apply scaledCyclicInclusion_injective (2 ^ (n + 2)) 2 (by positivity)
  rw [map_zero]
  exact hzero

theorem central_commutator_even_power_commute {G : Type*} [Group G] (c v : G)
    (hcentral : Commute ⁅c, v⁆ c) (hsquare : ⁅c, v⁆ ^ 2 = 1)
    (r : ℕ) (heven : Even r) : Commute (c ^ r) v := by
  have htwo : Commute (c ^ 2) v := by
    apply commutatorElement_eq_one_iff_commute.mp
    rw [pow_two, commutatorElement_mul_left_eq_conj_mul, hcentral.symm.mul_inv_cancel]
    simpa only [pow_two] using hsquare
  obtain ⟨j, hj⟩ := heven
  rw [hj, ← two_mul, pow_mul]
  exact htwo.pow_left j

theorem involution_lift_adjustment {S : Type*} [Group S] (A : Subgroup S) [A.Normal]
    (hcommutative : IsMulCommutative A) (v : S) (a : A)
    (hsquare : v ^ 2 = (a : S) ^ 2) (hfixed : MulAut.conjNormal (H := A) v a = a) :
    ∃ v₀ : S, v₀ ^ 2 = 1 ∧ MulAut.conjNormal (H := A) v₀ = MulAut.conjNormal (H := A) v := by
  have hcommute : Commute v (a : S) := by
    have h := congrArg Subtype.val hfixed
    change v * (a : S) * v⁻¹ = a at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have ha : MulAut.conjNormal (H := A) (a : S) = 1 := by
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    change (a : S) * (b : S) * (a : S)⁻¹ = b
    have hcommuteAB : Commute (a : S) (b : S) :=
      congrArg Subtype.val (@mul_comm' A _ hcommutative a b)
    exact hcommuteAB.mul_inv_cancel
  refine ⟨v * (a : S)⁻¹, ?_, ?_⟩
  · rw [hcommute.inv_right.mul_pow, hsquare, inv_pow, mul_inv_cancel]
  · rw [map_mul, map_inv, ha, inv_one, mul_one]

theorem cyclicTwo_delta_fixed_binary_long (n : ℕ) (x : CyclicTwoSpace n)
    (hfixed : (cyclicTwoDelta n).val x = x) : (cyclicTwoBinaryCoordinates n x).1 = 0 := by
  rw [cyclicTwoDelta, cyclicTwoScalar_apply, cyclicTwoTopUnit_val] at hfixed
  have hlong := congrArg Prod.fst hfixed
  have hzero : ((2 ^ (n + 2) : ℕ) : ZMod (2 ^ (n + 2) * 2)) * x.1 = 0 := by
    linear_combination hlong
  have hinclude := scaledCyclicInclusion_scalar (2 ^ (n + 2)) 2 x.1 (1 : ZMod 2)
  rw [mul_one, scaledCyclicInclusion_one] at hinclude
  apply scaledCyclicInclusion_injective (2 ^ (n + 2)) 2 (by positivity)
  change scaledCyclicInclusion (2 ^ (n + 2)) 2 (cyclicReduction (2 ^ (n + 2)) 2 x.1) =
    scaledCyclicInclusion (2 ^ (n + 2)) 2 0
  rw [hinclude, mul_comm x.1, hzero, map_zero]

theorem cyclicTwo_coordinate_top_scalar_square {S : Type*} [Group S] [Finite S]
    (hpgroup : IsPGroup 2 S) (A : Subgroup S) [A.Normal]
    (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (n : ℕ) (coordinates : Additive A ≃+ CyclicTwoSpace n)
    (t : S) (hlift : cyclicTwoAutomorphismEquiv hcommutative n coordinates
      (MulAut.conjNormal (H := A) t) = cyclicTwoDelta n) :
    ∃ a : A, (a : S) = t ^ 2 ∧
      cyclicTwoBinaryCoordinates n (coordinates (Additive.ofMul a)) = (0, 1) ∧
      ∀ b : A, a ≠ b ^ 2 := by
  let : CommGroup A := { (inferInstance : Group A) with mul_comm := @mul_comm' _ _ hcommutative }
  let δ := MulAut.conjNormal (H := A) t
  let e := cyclicTwoAutomorphismEquiv hcommutative n coordinates
  have hpower (a : A) : δ a = a ^ (1 + 2 ^ (n + 2)) := by
    apply coordinates.injective
    change coordinates (Additive.ofMul (δ a)) = coordinates ((1 + 2 ^ (n + 2) : ℕ) • Additive.ofMul a)
    rw [cyclicTwoAutomorphismEquiv_apply hcommutative, hlift, cyclicTwoDelta_apply, map_nsmul]
  have hsquare : δ ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, map_one, hlift, cyclicTwoDelta_square]
  have hnontrivial : δ ≠ 1 := by
    intro h
    have hδ : cyclicTwoDelta n = 1 := hlift.symm.trans (congrArg e h |>.trans (map_one e))
    exact cyclicTwoDelta_ne_one n hδ
  let pairCoordinates : A ≃* Multiplicative (ZMod (2 ^ (n + 3))) × Multiplicative (ZMod 2) :=
    (AddEquiv.toMultiplicativeRight coordinates).trans
      ((MulEquiv.prodMultiplicative (ZMod (2 ^ (n + 2) * 2)) (ZMod 2)).trans
        ((AddEquiv.toMultiplicative
          (ZMod.ringEquivCongr (pow_succ 2 (n + 2)).symm).toAddEquiv).prodCongr (MulEquiv.refl _)))
  have hcard := binary_rank_two_square_kernel_card A hcommutative (by omega : 0 < n + 3)
    (by decide : 0 < 1) pairCoordinates
  obtain ⟨a, ha, hprimitive⟩ := central_power_involution_primitive_lift_square hpgroup A
    hcommutative hselfCentralizing hnoEight hcard n δ hpower hsquare hnontrivial t rfl
  have hfixed : (cyclicTwoDelta n).val (coordinates (Additive.ofMul a)) = coordinates (Additive.ofMul a) := by
    rw [← hlift, ← cyclicTwoAutomorphismEquiv_apply hcommutative]
    exact congrArg (fun b : A => coordinates (Additive.ofMul b))
      (lift_square_fixed_by_conjugation A t a ha)
  have hlong := cyclicTwo_delta_fixed_binary_long n _ hfixed
  have hnonzero : cyclicTwoBinaryCoordinates n (coordinates (Additive.ofMul a)) ≠ 0 := by
    intro h
    obtain ⟨y, hy⟩ := (cyclicTwoBinaryCoordinates_zero_iff n _).mp h
    let b := (coordinates.symm y).toMul
    apply hprimitive b
    apply coordinates.injective
    change coordinates (Additive.ofMul a) = coordinates (2 • coordinates.symm y)
    rw [map_nsmul, coordinates.apply_symm_apply, hy]
  have hshort : (cyclicTwoBinaryCoordinates n (coordinates (Additive.ofMul a))).2 = 1 := by
    have hcases : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide +kernel
    rcases hcases (cyclicTwoBinaryCoordinates n (coordinates (Additive.ofMul a))).2 with h | h
    · exact False.elim (hnonzero (Prod.ext hlong h))
    · exact h
  exact ⟨a, ha, Prod.ext hlong hshort, hprimitive⟩

theorem cyclicTwo_binary_quotient_equal {S : Type*} [Group S]
    (A : Subgroup S) [A.Normal] (hcommutative : IsMulCommutative A)
    (n : ℕ) (coordinates : Additive A ≃+ CyclicTwoSpace n) (a b : A)
    (heq : cyclicTwoBinaryCoordinates n (coordinates (Additive.ofMul a)) =
      cyclicTwoBinaryCoordinates n (coordinates (Additive.ofMul b))) :
    let _ := normalPowerSubgroup_normal A hcommutative 2
    (QuotientGroup.mk' (normalPowerSubgroup A hcommutative 2)) a.val =
    (QuotientGroup.mk' (normalPowerSubgroup A hcommutative 2)) b.val := by
  dsimp only
  let : CommGroup A := { (inferInstance : Group A) with mul_comm := @mul_comm' _ _ hcommutative }
  let P := normalPowerSubgroup A hcommutative 2
  let : P.Normal := normalPowerSubgroup_normal A hcommutative 2
  let projection := QuotientGroup.mk' P
  have hzero : cyclicTwoBinaryCoordinates n (coordinates (Additive.ofMul (a * b⁻¹))) = 0 := by
    change cyclicTwoBinaryCoordinates n (coordinates (Additive.ofMul a + Additive.ofMul b⁻¹)) = 0
    rw [map_add coordinates, map_add (cyclicTwoBinaryCoordinates n), heq,
      ← map_add (cyclicTwoBinaryCoordinates n), ← map_add coordinates]
    change cyclicTwoBinaryCoordinates n (coordinates (Additive.ofMul (b * b⁻¹))) = 0
    rw [mul_inv_cancel]
    change cyclicTwoBinaryCoordinates n (coordinates 0) = 0
    rw [map_zero, map_zero]
  obtain ⟨y, hy⟩ := (cyclicTwoBinaryCoordinates_zero_iff n _).mp hzero
  have hmem : a.val * b.val⁻¹ ∈ P := by
    apply (normalPowerSubgroup_mem A hcommutative 2 _).mpr
    refine ⟨(coordinates.symm y).toMul, ?_⟩
    have hroot : (coordinates.symm y).toMul ^ 2 = a * b⁻¹ := by
      apply coordinates.injective
      change coordinates (2 • coordinates.symm y) = coordinates (Additive.ofMul (a * b⁻¹))
      rw [map_nsmul, coordinates.apply_symm_apply, hy]
    exact congrArg Subtype.val hroot
  have hprojection : projection (a.val * b.val⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hmem
  rw [map_mul, map_inv, mul_inv_eq_one] at hprojection
  exact hprojection

theorem cyclicTwo_binary_action_commutes {S : Type*} [Group S]
    (A : Subgroup S) [A.Normal] (hcommutative : IsMulCommutative A)
    (n : ℕ) (coordinates : Additive A ≃+ CyclicTwoSpace n)
    (g : S) (α : CyclicTwoAut n)
    (hlift : cyclicTwoAutomorphismEquiv hcommutative n coordinates
      (MulAut.conjNormal (H := A) g) = α)
    (htrivial : ∀ x : CyclicTwoSpace n,
      cyclicTwoBinaryCoordinates n (α.val x) = cyclicTwoBinaryCoordinates n x) :
    let _ := normalPowerSubgroup_normal A hcommutative 2
    ∀ a : A, Commute ((QuotientGroup.mk' (normalPowerSubgroup A hcommutative 2)) g)
      ((QuotientGroup.mk' (normalPowerSubgroup A hcommutative 2)) a.val) := by
  dsimp only
  let P := normalPowerSubgroup A hcommutative 2
  let : P.Normal := normalPowerSubgroup_normal A hcommutative 2
  let projection := QuotientGroup.mk' P
  intro a
  have h := cyclicTwo_binary_quotient_equal A hcommutative n coordinates
    (MulAut.conjNormal (H := A) g a) a (by
      rw [cyclicTwoAutomorphismEquiv_apply hcommutative, hlift]
      exact htrivial _)
  dsimp only at h
  rw [MulAut.conjNormal_apply, map_mul, map_mul, map_inv] at h
  exact mul_inv_eq_iff_eq_mul.mp h

theorem cyclicTwo_tau_delta_conjugate (n : ℕ) :
    cyclicTwoRho n * cyclicTwoTau n * (cyclicTwoRho n)⁻¹ =
      cyclicTwoTau n * cyclicTwoDelta n := by
  have hcommutator : ⁅cyclicTwoRho n, cyclicTwoTau n⁆ = cyclicTwoDelta n := by
    rw [← commutatorElement_inv, cyclicTwoTauRho_commutator]
    exact inv_eq_self_of_orderOf_eq_two (cyclicTwo_delta_order n)
  have hδcentral : Commute (cyclicTwoDelta n) (cyclicTwoTau n) :=
    cyclicTwoScalar_central n (cyclicTwoTopUnit n) _
  calc
    _ = ⁅cyclicTwoRho n, cyclicTwoTau n⁆ * cyclicTwoTau n := by
      rw [commutatorElement_def]
      group
    _ = cyclicTwoDelta n * cyclicTwoTau n := by rw [hcommutator]
    _ = cyclicTwoTau n * cyclicTwoDelta n := hδcentral.eq

theorem cyclicTwo_tau_lift_primitive_square {S : Type*} [Group S] [Finite S]
    (hpgroup : IsPGroup 2 S) (A : Subgroup S) [A.Normal]
    (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (n k : ℕ) (hk : k < n) (coordinates : Additive A ≃+ CyclicTwoSpace n)
    (v w c : S)
    (hv : cyclicTwoAutomorphismEquiv hcommutative n coordinates (MulAut.conjNormal (H := A) v) = cyclicTwoTau n)
    (hw : cyclicTwoAutomorphismEquiv hcommutative n coordinates (MulAut.conjNormal (H := A) w) = cyclicTwoRho n)
    (hc : cyclicTwoAutomorphismEquiv hcommutative n coordinates (MulAut.conjNormal (H := A) c) =
      cyclicTwoC n ^ (2 ^ k)) :
    ∃ a : A, a.val = v ^ 2 ∧ cyclicTwoBinaryCoordinates n (coordinates (Additive.ofMul a)) = (1, 0) := by
  let e := cyclicTwoAutomorphismEquiv hcommutative n coordinates
  let action := e.toMonoidHom.comp (MulAut.conjNormal (H := A))
  have hkernel : action.ker = A := by
    ext s
    change e (MulAut.conjNormal (H := A) s) = 1 ↔ s ∈ A
    rw [← map_one e, e.injective.eq_iff]
    exact Subgroup.ext_iff.mp ((conjNormal_ker_eq_centralizer A).trans hselfCentralizing) s
  have hvmem : v ^ 2 ∈ A := by
    apply hkernel.le
    change action (v ^ 2) = 1
    rw [map_pow, show action v = cyclicTwoTau n from hv, cyclicTwoTau_square]
  let a : A := ⟨v ^ 2, hvmem⟩
  have hfixed : (cyclicTwoTau n).val (coordinates (Additive.ofMul a)) = coordinates (Additive.ofMul a) := by
    rw [← hv, ← cyclicTwoAutomorphismEquiv_apply hcommutative]
    exact congrArg (fun a : A => coordinates (Additive.ofMul a))
      (lift_square_fixed_by_conjugation A v a rfl)
  have hshort := cyclicTwo_tau_fixed_short n _ hfixed
  have hnonzero : cyclicTwoBinaryCoordinates n (coordinates (Additive.ofMul a)) ≠ 0 := by
    intro hzero
    obtain ⟨y, hy⟩ := (cyclicTwoBinaryCoordinates_zero_iff n _).mp hzero
    let root := (coordinates.symm (y.1, 0)).toMul
    have hroot : root ^ 2 = a := by
      apply coordinates.injective
      change coordinates (2 • coordinates.symm (y.1, 0)) = coordinates (Additive.ofMul a)
      rw [map_nsmul, coordinates.apply_symm_apply]
      apply Prod.ext
      · have hfirst := congrArg Prod.fst hy
        exact hfirst
      · simpa using hshort.symm
    have hrootFixed : MulAut.conjNormal (H := A) v root = root := by
      apply coordinates.injective
      change coordinates (Additive.ofMul (MulAut.conjNormal (H := A) v root)) =
        coordinates (Additive.ofMul root)
      rw [cyclicTwoAutomorphismEquiv_apply hcommutative, hv]
      change (cyclicTwoTau n).val (coordinates (coordinates.symm (y.1, 0))) =
        coordinates (coordinates.symm (y.1, 0))
      rw [coordinates.apply_symm_apply, cyclicTwoTau_apply, map_zero, add_zero]
    obtain ⟨v₀, hv₀square, hv₀action⟩ := involution_lift_adjustment A hcommutative v root
      (congrArg Subtype.val hroot).symm hrootFixed
    have hv₀ : action v₀ = cyclicTwoTau n := by
      change e (MulAut.conjNormal (H := A) v₀) = _
      rw [hv₀action]
      exact hv
    let r := 2 ^ (n - k)
    let t := c ^ r
    have ht : action t = cyclicTwoDelta n := by
      change action (c ^ r) = _
      rw [map_pow, show action c = cyclicTwoC n ^ (2 ^ k) from hc, ← pow_mul,
        ← pow_add, Nat.add_sub_of_le (by omega : k ≤ n), cyclicTwoC_half_power]
    obtain ⟨b, hb, hbBinary, _⟩ := cyclicTwo_coordinate_top_scalar_square hpgroup A
      hcommutative hselfCentralizing hnoEight n coordinates t ht
    let P := normalPowerSubgroup A hcommutative 2
    let : P.Normal := normalPowerSubgroup_normal A hcommutative 2
    let projection := QuotientGroup.mk' P
    have hcScalar : action c = cyclicTwoScalar n (cyclicTwoFive n ^ (2 ^ k)) := by
      rw [show action c = cyclicTwoC n ^ (2 ^ k) from hc, cyclicTwoC, ← map_pow]
    have hcTrivial := cyclicTwo_binary_action_commutes A hcommutative n coordinates c _ hcScalar
      (cyclicTwoBinaryCoordinates_scalar n (cyclicTwoFive n ^ (2 ^ k)))
    have hv₀Trivial := cyclicTwo_binary_action_commutes A hcommutative n coordinates v₀ _ hv₀
      (cyclicTwoBinaryCoordinates_tau n)
    have hcommutatorMem : ⁅c, v₀⁆ ∈ A := by
      apply hkernel.le
      change action ⁅c, v₀⁆ = 1
      rw [map_commutatorElement, hcScalar, hv₀]
      exact (cyclicTwoScalar_central n _ _).commutator_eq
    have hcommutatorSquare : ⁅projection c, projection v₀⁆ ^ 2 = 1 := by
      rw [← map_commutatorElement, ← map_pow]
      apply (QuotientGroup.eq_one_iff _).mpr
      exact (normalPowerSubgroup_mem A hcommutative 2 _).mpr ⟨⟨_, hcommutatorMem⟩, rfl⟩
    have hcommutatorCentral : Commute ⁅projection c, projection v₀⁆ (projection c) := by
      rw [← map_commutatorElement]
      exact (hcTrivial ⟨_, hcommutatorMem⟩).symm
    have htCommute : Commute (projection t) (projection v₀) := by
      change Commute (projection (c ^ r)) (projection v₀)
      rw [map_pow]
      exact central_commutator_even_power_commute _ _ hcommutatorCentral hcommutatorSquare r
        (even_two.pow_of_ne_zero (by omega : n - k ≠ 0))
    have hconjugateAction : action (w * v₀ * w⁻¹) = action (v₀ * t) := by
      rw [map_mul, map_mul, map_inv, hv₀, show action w = cyclicTwoRho n from hw,
        cyclicTwo_tau_delta_conjugate, map_mul, hv₀, ht]
    have hdmem : (v₀ * t)⁻¹ * (w * v₀ * w⁻¹) ∈ A := by
      apply hkernel.le
      change action ((v₀ * t)⁻¹ * (w * v₀ * w⁻¹)) = 1
      rw [map_mul, map_inv, hconjugateAction, inv_mul_cancel]
    let d : A := ⟨(v₀ * t)⁻¹ * (w * v₀ * w⁻¹), hdmem⟩
    have hconjugate : w * v₀ * w⁻¹ = (v₀ * t) * d.val := by dsimp only [d]; group
    have hdSquare : projection d.val ^ 2 = 1 := by
      rw [← map_pow]
      apply (QuotientGroup.eq_one_iff _).mpr
      exact (normalPowerSubgroup_mem A hcommutative 2 _).mpr ⟨d, rfl⟩
    have htTrivial : Commute (projection t) (projection d.val) := by
      change Commute (projection (c ^ r)) (projection d.val)
      rw [map_pow]
      exact (hcTrivial d).pow_left r
    have hproductCommute : Commute (projection (v₀ * t)) (projection d.val) := by
      rw [map_mul]
      exact (hv₀Trivial d).mul_left htTrivial
    have hv₀Projection : projection v₀ ^ 2 = 1 := by rw [← map_pow, hv₀square, map_one]
    have hconjugateSquare : (w * v₀ * w⁻¹) ^ 2 = 1 := by
      calc
        _ = w * v₀ ^ 2 * w⁻¹ := by simp only [pow_two]; group
        _ = 1 := by rw [hv₀square]; group
    have hbad : projection b.val = 1 := by
      have h := congrArg projection hconjugateSquare
      rw [map_pow, map_one, hconjugate, map_mul, hproductCommute.mul_pow,
        hdSquare, mul_one, map_mul, htCommute.symm.mul_pow, hv₀Projection, one_mul, ← map_pow] at h
      exact hb ▸ h
    have hbPower : b.val ∈ P := (QuotientGroup.eq_one_iff _).mp hbad
    obtain ⟨z, hz⟩ := (normalPowerSubgroup_mem A hcommutative 2 _).mp hbPower
    have hbSquare : b = z ^ 2 := Subtype.ext hz.symm
    have hbZero : cyclicTwoBinaryCoordinates n (coordinates (Additive.ofMul b)) = 0 := by
      rw [hbSquare]
      change cyclicTwoBinaryCoordinates n (coordinates (2 • Additive.ofMul z)) = 0
      rw [map_nsmul, cyclicTwoBinaryCoordinates_two]
    have hneq : ((0, 1) : ZMod 2 × ZMod 2) ≠ 0 := by decide +kernel
    exact hneq (hbBinary.symm.trans hbZero)
  have hlong : (cyclicTwoBinaryCoordinates n (coordinates (Additive.ofMul a))).1 = 1 := by
    have hcases : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide +kernel
    rcases hcases (cyclicTwoBinaryCoordinates n (coordinates (Additive.ofMul a))).1 with h | h
    · exact False.elim (hnonzero (Prod.ext h hshort))
    · exact h
  exact ⟨a, rfl, Prod.ext hlong hshort⟩

@[expose] def cyclicTwoBinaryHom {A : Type*} [Group A] (n : ℕ)
    (coordinates : Additive A ≃+ CyclicTwoSpace n) : A →* Multiplicative (ZMod 2 × ZMod 2) :=
  AddMonoidHom.toMultiplicativeRight ((cyclicTwoBinaryCoordinates n).comp coordinates.toAddMonoidHom)

theorem normal_binary_basis_frattini_saving {G : Type*} [Group G] [Finite G]
    (hpgroup : IsPGroup 2 G) (B : Subgroup G) [B.Normal]
    (hcommutative : IsMulCommutative B)
    (binary : B →* Multiplicative (ZMod 2 × ZMod 2)) (b₀ b₁ : B)
    (h₀ : binary b₀ = Multiplicative.ofAdd (1, 0))
    (h₁ : binary b₁ = Multiplicative.ofAdd (0, 1))
    (hfrattini₀ : b₀.val ∈ frattini G) (hfrattini₁ : b₁.val ∈ frattini G) :
    pGeneratorRank 2 G + 2 ≤ pGeneratorRank 2 (G ⧸ B) + pGeneratorRank 2 B := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CommGroup B := { (inferInstance : Group B) with mul_comm := @mul_comm' _ _ hcommutative }
  let V := Multiplicative (ZMod 2 × ZMod 2)
  have hpB := hpgroup.to_subgroup B
  let : CommGroup (B ⧸ frattini B) := pGroupFrattiniCommGroup Nat.prime_two hpB
  let moduleB : Module (ZMod 2) (Additive (B ⧸ frattini B)) :=
    elementaryZModModule (pGroup_frattini_quotient_exponent Nat.prime_two hpB)
  let := moduleB
  have hkernel : frattini B ≤ binary.ker := by
    rw [commutative_frattini_eq_power_range Nat.prime_two hpB]
    rintro b ⟨a, rfl⟩
    change binary (a ^ 2) = 1
    rw [map_pow]
    have h : ∀ x : V, x ^ 2 = 1 := by decide +kernel
    exact h _
  let induced := QuotientGroup.lift (frattini B) binary hkernel
  let family : Fin 2 → B := ![b₀, b₁]
  let classes := fun i : Fin 2 => Additive.ofMul ((QuotientGroup.mk' (frattini B)) (family i))
  have himage₀ : induced (classes 0).toMul = Multiplicative.ofAdd (1, 0) := h₀
  have himage₁ : induced (classes 1).toMul = Multiplicative.ofAdd (0, 1) := h₁
  have hindependent : LinearIndependent (ZMod 2)
      (fun i : Fin 2 => Additive.ofMul ((QuotientGroup.mk' (frattini B)) (family i))) := by
    apply linearIndependent_fin2.mpr
    constructor
    · intro hzero
      have h := congrArg (fun x : Additive (B ⧸ frattini B) => induced x.toMul) hzero
      change induced (classes 1).toMul = induced 1 at h
      rw [himage₁, map_one] at h
      have hneq : Multiplicative.ofAdd ((0, 1) : ZMod 2 × ZMod 2) ≠ 1 := by decide +kernel
      exact hneq h
    · intro s heq
      have hcases : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide +kernel
      rcases hcases s with h | h
      · rw [h, zero_smul] at heq
        have hzero := congrArg (fun x : Additive (B ⧸ frattini B) => induced x.toMul) heq
        change induced 1 = induced (classes 0).toMul at hzero
        rw [map_one, himage₀] at hzero
        have hneq : (1 : V) ≠ Multiplicative.ofAdd ((1, 0) : ZMod 2 × ZMod 2) := by decide +kernel
        exact hneq hzero
      · rw [h, one_smul] at heq
        have hsame := congrArg (fun x : Additive (B ⧸ frattini B) => induced x.toMul) heq
        change induced (classes 1).toMul = induced (classes 0).toMul at hsame
        rw [himage₀, himage₁] at hsame
        have hneq : Multiplicative.ofAdd ((0, 1) : ZMod 2 × ZMod 2) ≠ Multiplicative.ofAdd (1, 0) := by decide +kernel
        exact hneq hsame
  have hfamily (i : Fin 2) : (family i).val ∈ frattini G := by
    fin_cases i
    · exact hfrattini₀
    · exact hfrattini₁
  have hsave := pGeneratorRank_normal_independent_saving Nat.prime_two hpgroup B family hfamily
    moduleB hindependent
  simpa only [Fintype.card_fin] using hsave

theorem cyclicTwo_coordinate_generator_rank {S : Type*} [Group S] [Finite S]
    (hpgroup : IsPGroup 2 S) (A : Subgroup S) (hcommutative : IsMulCommutative A)
    (n : ℕ) (coordinates : Additive A ≃+ CyclicTwoSpace n) : pGeneratorRank 2 A = 2 := by
  let pairCoordinates : A ≃* Multiplicative (ZMod (2 ^ (n + 3))) × Multiplicative (ZMod 2) :=
    (AddEquiv.toMultiplicativeRight coordinates).trans
      ((MulEquiv.prodMultiplicative (ZMod (2 ^ (n + 2) * 2)) (ZMod 2)).trans
        ((AddEquiv.toMultiplicative
          (ZMod.ringEquivCongr (pow_succ 2 (n + 2)).symm).toAddEquiv).prodCongr (MulEquiv.refl _)))
  have hcard := binary_rank_two_frattini_quotient_card hpgroup A hcommutative
    (by omega : 0 < n + 3) (by decide : 0 < 1) pairCoordinates
  change Nat.log 2 (Nat.card (A ⧸ frattini A)) = 2
  rw [hcard]
  decide

theorem cyclic_two_coordinate_four_generators {S : Type*} [Group S] [Finite S]
    (hpgroup : IsPGroup 2 S) (A : Subgroup S) [A.Normal]
    (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (n : ℕ) (coordinates : Additive A ≃+ CyclicTwoSpace n) (U : Subgroup S) :
    ∃ X : Finset U, Subgroup.closure (X : Set U) = ⊤ ∧ X.card ≤ 4 := by
  let : CommGroup A := { (inferInstance : Group A) with mul_comm := @mul_comm' _ _ hcommutative }
  let e := cyclicTwoAutomorphismEquiv hcommutative n coordinates
  let ambient := e.toMonoidHom.comp (MulAut.conjNormal (H := A))
  let action := ambient.comp U.subtype
  let H := action.range
  let quotient := action.rangeRestrict
  let B := quotient.ker
  have hkernel : ambient.ker = A := by
    ext s
    change e (MulAut.conjNormal (H := A) s) = 1 ↔ s ∈ A
    rw [← map_one e, e.injective.eq_iff]
    exact Subgroup.ext_iff.mp ((conjNormal_ker_eq_centralizer A).trans hselfCentralizing) s
  have hBkernel : B = A.comap U.subtype := by
    change action.rangeRestrict.ker = A.comap U.subtype
    rw [MonoidHom.ker_rangeRestrict]
    change ambient.ker.comap U.subtype = A.comap U.subtype
    rw [hkernel]
  let embedding : B →* A := {
    toFun := fun b => ⟨b.val.val, by
      have hmem : b.val ∈ A.comap U.subtype := hBkernel ▸ b.property
      exact hmem⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hinjective : Function.Injective embedding := by
    intro x y h
    have hvals : x.val.val = y.val.val := congrArg (fun a : A => a.val) h
    exact Subtype.ext (Subtype.ext hvals)
  have hBcommutative : IsMulCommutative B := by
    apply IsMulCommutative.of_comm
    intro x y
    apply hinjective
    simp only [map_mul]
    exact mul_comm _ _
  let : CommGroup B := { (inferInstance : Group B) with mul_comm := @mul_comm' _ _ hBcommutative }
  have hpU := hpgroup.to_subgroup U
  have hpA := hpgroup.to_subgroup A
  have hArank := cyclicTwo_coordinate_generator_rank hpgroup A hcommutative n coordinates
  have hBrank : pGeneratorRank 2 B ≤ 2 := by
    exact (commutative_pGeneratorRank_embedding_le Nat.prime_two hpA embedding hinjective).trans hArank.le
  have hHrank : pGeneratorRank 2 H ≤ 4 := cyclicTwo_subgroup_generator_bound n H
  let quotientEquiv := QuotientGroup.quotientKerEquivOfSurjective quotient action.rangeRestrict_surjective
  have hquotient := pGeneratorRank_mulEquiv Nat.prime_two (hpU.to_quotient B) quotientEquiv
  change pGeneratorRank 2 (U ⧸ B) = pGeneratorRank 2 H at hquotient
  have hUrk : pGeneratorRank 2 U ≤ 4 := by
    by_cases hsmall : pGeneratorRank 2 H ≤ 2
    · have hbound := pGeneratorRank_extension_le Nat.prime_two hpU B
      rw [hquotient] at hbound
      omega
    have hdelta : cyclicTwoDelta n ∈ H := cyclicTwo_three_generators_contains_delta n H (by omega)
    obtain ⟨t, ht⟩ := hdelta
    have htNative : ambient t.val = cyclicTwoDelta n := ht
    obtain ⟨a, ha, _, hprimitive⟩ := cyclicTwo_coordinate_top_scalar_square hpgroup A
      hcommutative hselfCentralizing hnoEight n coordinates t.val htNative
    have htmem : t ^ 2 ∈ B := by
      rw [hBkernel]
      change t.val ^ 2 ∈ A
      rw [← ha]
      exact a.property
    let b₁ : B := ⟨t ^ 2, htmem⟩
    have hfrattini₁ : b₁.val ∈ frattini U := pGroup_pow_mem_frattini Nat.prime_two hpU t
    have hnotPower : ¬∃ b : B, b ^ 2 = b₁ := by
      rintro ⟨b, hb⟩
      have hsquare : embedding b₁ = a := Subtype.ext ha.symm
      have hpow := congrArg embedding hb
      rw [map_pow, hsquare] at hpow
      exact hprimitive (embedding b) hpow.symm
    by_cases hthree : pGeneratorRank 2 H ≤ 3
    · have hsave := pGeneratorRank_normal_square_saving Nat.prime_two hpU B hBcommutative b₁ hfrattini₁ hnotPower
      rw [hquotient] at hsave
      omega
    have hfour : pGeneratorRank 2 H = 4 := by omega
    obtain ⟨_, k, hk, hH⟩ := cyclicTwo_rank_four_subgroup_classification n H hfour
    have hg (g : CyclicTwoAut n)
        (hmem : g ∈ ({cyclicTwoTau n, cyclicTwoRho n, cyclicTwoZ n, cyclicTwoC n ^ (2 ^ k)} : Set _)) :
        ∃ u : U, ambient u.val = g := by
      have hinH : g ∈ H := hH ▸ Subgroup.subset_closure hmem
      exact hinH
    obtain ⟨v, hv⟩ := hg (cyclicTwoTau n) (by simp)
    obtain ⟨w, hw⟩ := hg (cyclicTwoRho n) (by simp)
    obtain ⟨c, hc⟩ := hg (cyclicTwoC n ^ (2 ^ k)) (by simp)
    obtain ⟨a₀, ha₀, hbinary₀⟩ := cyclicTwo_tau_lift_primitive_square hpgroup A hcommutative
      hselfCentralizing hnoEight n k (by omega) coordinates v.val w.val c.val hv hw hc
    let r := 2 ^ (n - k)
    let t₁ := c ^ r
    have ht₁ : ambient t₁.val = cyclicTwoDelta n := by
      change ambient (c.val ^ r) = _
      rw [map_pow, hc, ← pow_mul, ← pow_add, Nat.add_sub_of_le (by omega : k ≤ n), cyclicTwoC_half_power]
    obtain ⟨a₁, ha₁, hbinary₁, _⟩ := cyclicTwo_coordinate_top_scalar_square hpgroup A hcommutative
      hselfCentralizing hnoEight n coordinates t₁.val ht₁
    have h₀mem : v ^ 2 ∈ B := by
      rw [hBkernel]
      change v.val ^ 2 ∈ A
      rw [← ha₀]
      exact a₀.property
    have h₁mem : t₁ ^ 2 ∈ B := by
      rw [hBkernel]
      change t₁.val ^ 2 ∈ A
      rw [← ha₁]
      exact a₁.property
    let b₀ : B := ⟨v ^ 2, h₀mem⟩
    let b₂ : B := ⟨t₁ ^ 2, h₁mem⟩
    let binary := (cyclicTwoBinaryHom n coordinates).comp embedding
    have hbinary0 : binary b₀ = Multiplicative.ofAdd (1, 0) := by
      have hrep : embedding b₀ = a₀ := Subtype.ext ha₀.symm
      change Multiplicative.ofAdd (cyclicTwoBinaryCoordinates n (coordinates (Additive.ofMul (embedding b₀)))) = _
      rw [hrep, hbinary₀]
    have hbinary1 : binary b₂ = Multiplicative.ofAdd (0, 1) := by
      have hrep : embedding b₂ = a₁ := Subtype.ext ha₁.symm
      change Multiplicative.ofAdd (cyclicTwoBinaryCoordinates n (coordinates (Additive.ofMul (embedding b₂)))) = _
      rw [hrep, hbinary₁]
    have hsave := normal_binary_basis_frattini_saving hpU B hBcommutative binary b₀ b₂ hbinary0 hbinary1
      (pGroup_pow_mem_frattini Nat.prime_two hpU v) (pGroup_pow_mem_frattini Nat.prime_two hpU t₁)
    rw [hquotient] at hsave
    omega
  obtain ⟨X, hX, hcard⟩ := pGeneratorRank_generators Nat.prime_two hpU
  exact ⟨X, hX, hcard.trans_le hUrk⟩

theorem rank_two_cyclic_times_two_four_generators {S : Type*} [Group S] [Finite S]
    (hpgroup : IsPGroup 2 S) (A : Subgroup S) [A.Normal]
    (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (n : ℕ) (coordinates : A ≃* Multiplicative (ZMod (2 ^ (n + 3))) × Multiplicative (ZMod 2))
    (U : Subgroup S) :
    ∃ X : Finset U, Subgroup.closure (X : Set U) = ⊤ ∧ X.card ≤ 4 := by
  let : CommGroup A := { (inferInstance : Group A) with mul_comm := @mul_comm' _ _ hcommutative }
  let nativeCoordinates : Additive A ≃+ CyclicTwoSpace n :=
    (rankTwoAddCoordinates (lower := 1) coordinates).trans
      ((ZMod.ringEquivCongr (pow_succ 2 (n + 2))).toAddEquiv.prodCongr (AddEquiv.refl _))
  exact cyclic_two_coordinate_four_generators hpgroup A hcommutative hselfCentralizing hnoEight n
    nativeCoordinates U

theorem rank_two_cyclic_times_two_ambient_four_generators {S : Type*} [Group S] [Finite S]
    (hpgroup : IsPGroup 2 S) (A : Subgroup S) [A.Normal]
    (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (n : ℕ) (coordinates : A ≃* Multiplicative (ZMod (2 ^ (n + 3))) × Multiplicative (ZMod 2))
    (U : Subgroup S) :
    ∃ X : Finset S, X.card ≤ 4 ∧ Subgroup.closure (X : Set S) = U := by
  classical
  obtain ⟨X, hX, hcard⟩ := rank_two_cyclic_times_two_four_generators hpgroup A hcommutative
    hselfCentralizing hnoEight n coordinates U
  refine ⟨X.image U.subtype, Finset.card_image_le.trans hcard, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hX, Subgroup.map_top]
  exact U.range_subtype

end CFSG.LargeEvenClassification.Helpers
