module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryTwoFieldData
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryNorm
public import CFSG.CharacterTheory.Wreathed.OddLinearThreeCentralizerCore

public noncomputable section

namespace CFSG.Wreathed.OddUnitaryThreeCentralizerCore
open CFSG.ComponentClassification
open CatalogueBUnitaryIsometry
universe u v
variable {E : Type u} [Field E] {V : Type v} [AddCommGroup V] [Module E V]
variable {sigma : E ≃+* E} (h : V →ₛₗ[sigma.toRingHom] V →ₗ[E] E)

@[expose] def scalarAction : Eˣ →* (V ≃ₗ[E] V) where
  toFun := LinearEquiv.smulOfUnit
  map_one' := by ext v; simp [LinearEquiv.smulOfUnit]
  map_mul' a b := by ext v; simp [LinearEquiv.smulOfUnit, mul_smul]

theorem scalarAction_apply (a : Eˣ) (v : V) :
    scalarAction a v = (a : E) • v := rfl

@[expose] def normOneUnits : Subgroup Eˣ where
  carrier := {a | sigma (a : E) * (a : E) = 1}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    change sigma ((a : E) * (b : E)) * ((a : E) * (b : E)) = 1
    rw [map_mul]
    calc
      sigma (a : E) * sigma (b : E) * ((a : E) * (b : E)) =
        (sigma (a : E) * (a : E)) * (sigma (b : E) * (b : E)) := by ring
      _ = 1 := by rw [ha, hb, one_mul]
  inv_mem' {a} ha := by
    change sigma ((a⁻¹ : Eˣ) : E) * ((a⁻¹ : Eˣ) : E) = 1
    rw [Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv_rev, mul_comm (a : E), ha, inv_one]

@[expose] def scalarIsometry : normOneUnits (sigma := sigma) →* isometryGroup h :=
  (scalarAction (V := V)).comp (normOneUnits (sigma := sigma)).subtype |>.codRestrict _ (by
    intro a x y
    change h ((a.val : E) • x) ((a.val : E) • y) = h x y
    rw [CatalogueBHermitian.smul_left, map_smul, smul_eq_mul, ← mul_assoc, a.property, one_mul])

theorem scalarIsometry_apply (a : normOneUnits (sigma := sigma)) (v : V) :
    (scalarIsometry h a).val v = (a.val : E) • v := rfl

theorem scalarIsometry_mem_center (a : normOneUnits (sigma := sigma)) :
    scalarIsometry h a ∈ Subgroup.center (isometryGroup h) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  ext v
  exact g.val.map_smul (a.val : E) v

theorem orthogonal_restriction_nondegenerate (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (P Q : Submodule E V) (hPQ : IsCompl P Q)
    (horth : ∀ x ∈ P, ∀ y ∈ Q, h x y = 0) :
    (h.domRestrict₁₂ P P).Nondegenerate := by
  have hleft : (h.domRestrict₁₂ P P).SeparatingLeft := by
    intro x hx
    apply Subtype.ext
    change (x : V) = 0
    apply hnd.1
    intro y
    let e := P.prodEquivOfIsCompl Q hPQ
    obtain ⟨⟨a, b⟩, rfl⟩ := e.surjective y
    change h (x : V) ((a : V) + (b : V)) = 0
    rw [map_add]
    exact (congrArg₂ (· + ·) (hx a) (horth x x.property b b.property)).trans (zero_add 0)
  constructor
  · exact hleft
  · intro y hy
    exact hleft y (fun x => hsym.eq_iff.mpr (hy x))

theorem involution_eigenspaces_orthogonal (h2 : (2 : E) ≠ 0)
    (f : V ≃ₗ[E] V) (hisometry : f ∈ isometryGroup h)
    (x y : V) (hx : x ∈ Module.End.eigenspace f.toLinearMap (-1))
    (hy : y ∈ Module.End.eigenspace f.toLinearMap 1) : h x y = 0 := by
  have hx' : f x = -x := by simpa using Module.End.mem_eigenspace_iff.mp hx
  have hy' : f y = y := by simpa using Module.End.mem_eigenspace_iff.mp hy
  have he := hisometry x y
  rw [hx', hy'] at he
  have hneg : h (-x) y = -h x y := by
    rw [map_neg, LinearMap.neg_apply]
  rw [hneg] at he
  have hz : (2 : E) * h x y = 0 := by linear_combination -he
  exact (mul_eq_zero.mp hz).resolve_left h2


section SpecialScalars
variable [FiniteDimensional E V]

theorem scalarAction_determinant (a : Eˣ) :
    LinearEquiv.det (scalarAction (V := V) a) = a ^ Module.finrank E V := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  have ha : (scalarAction (V := V) a).toLinearMap = (a : E) • LinearMap.id := by
    ext x
    rfl
  rw [ha, LinearMap.det_smul, LinearMap.det_id, mul_one]
  rfl

@[expose] def cubicUnits : Subgroup (normOneUnits (sigma := sigma)) := (powMonoidHom 3).ker

@[expose] def scalarSpecial (hdim : Module.finrank E V = 3) :
    cubicUnits (sigma := sigma) →* specialIsometry h :=
  ((scalarIsometry h).comp (cubicUnits (sigma := sigma)).subtype).codRestrict _ (by
    intro a
    rw [MonoidHom.mem_ker]
    change LinearEquiv.det (scalarAction (V := V) a.val.val) = 1
    rw [scalarAction_determinant, hdim]
    exact congrArg (fun b : normOneUnits (sigma := sigma) => b.val)
      (MonoidHom.mem_ker.mp a.property))

@[expose] def scalarCenter (hdim : Module.finrank E V = 3) : Subgroup (specialIsometry h) :=
  (scalarSpecial h hdim).range

theorem scalarSpecial_apply (hdim : Module.finrank E V = 3)
    (a : cubicUnits (sigma := sigma)) (v : V) :
    (scalarSpecial h hdim a).val.val v = (a.val.val : E) • v := rfl

theorem scalarCenter_le_center (hdim : Module.finrank E V = 3) :
    scalarCenter h hdim ≤ Subgroup.center (specialIsometry h) := by
  rintro g ⟨a, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro b
  apply Subtype.ext
  apply Subtype.ext
  ext v
  exact b.val.val.map_smul (a.val.val : E) v

theorem scalarCenter_cube_eq_one (hdim : Module.finrank E V = 3)
    (g : specialIsometry h) (hg : g ∈ scalarCenter h hdim) : g ^ 3 = 1 := by
  obtain ⟨a, rfl⟩ := hg
  rw [← map_pow]
  have ha : a ^ 3 = 1 := Subtype.ext (MonoidHom.mem_ker.mp a.property)
  rw [ha, map_one]

theorem isometryGroup_finite [Finite E] : Finite (isometryGroup h) := by
  let : Finite V := Module.finite_of_finite E
  exact Finite.of_injective (fun g : isometryGroup h => (g.val : V → V)) (by
    intro g k heq
    apply Subtype.ext
    ext x
    exact congrFun heq x)

theorem scalar_kernel_odd [Finite E] (hdim : Module.finrank E V = 3)
    (D : Subgroup (specialIsometry h)) (hD : D ≤ scalarCenter h hdim) :
    Odd (Nat.card D) := by
  let : Finite (isometryGroup h) := isometryGroup_finite h
  apply Nat.not_even_iff_odd.mp
  intro heven
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := D) 2 heven.two_dvd
  have hc : d ^ 3 = 1 := Subtype.ext (scalarCenter_cube_eq_one h hdim d (hD d.property))
  have hdiv : orderOf d ∣ 3 := orderOf_dvd_of_pow_eq_one hc
  rw [hd] at hdiv
  omega

theorem unique_involution_lift [Finite E] (hdim : Module.finrank E V = 3)
    (D : Subgroup (specialIsometry h)) [D.Normal] (hD : D ≤ scalarCenter h hdim)
    (t : specialIsometry h ⧸ D) (ht : orderOf t = 2) :
    ∃! z : specialIsometry h, orderOf z = 2 ∧ QuotientGroup.mk' D z = t := by
  let : Finite (isometryGroup h) := isometryGroup_finite h
  have hodd := scalar_kernel_odd h hdim D hD
  obtain ⟨z, hz, hzt⟩ := OddNormalQuotientInvolutions.exists_involution_lift D hodd t ht
  refine ⟨z, ⟨hz, hzt⟩, ?_⟩
  intro w hw
  obtain ⟨d, hd⟩ := OddNormalQuotientInvolutions.exists_kernel_conjugator D hodd
    z w hz hw.1 (hw.2.trans hzt.symm)
  have hcomm := Subgroup.mem_center_iff.mp (scalarCenter_le_center h hdim (hD d.property)) z
  rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one] at hd
  exact hd.symm
end SpecialScalars


section OriginalInvolution
variable [FiniteDimensional E V]

theorem involution_finrank (h2 : (2 : E) ≠ 0) (hdim : Module.finrank E V = 3)
    (z : specialIsometry h) (hz : orderOf z = 2) :
    Module.finrank E (OddLinearThreeCentralizerCore.minusSpace z.val.val.toLinearMap) = 2 ∧
      Module.finrank E (OddLinearThreeCentralizerCore.plusSpace z.val.val.toLinearMap) = 1 := by
  have hz2 : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
  have hf : Function.Involutive z.val.val := by
    intro x
    exact congrArg (fun g : specialIsometry h => g.val.val x) (by
      simpa only [pow_two] using hz2)
  apply OddLinearThreeCentralizerCore.involution_finrank_three h2 _ hf hdim
  · exact (mem_specialIsometry_iff h z.val).mp z.property
  · intro he
    have hz1 : z = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      ext x
      exact congrArg (fun f : Module.End E V => f x) he
    rw [hz1, orderOf_one] at hz
    omega

omit [FiniteDimensional E V] in
theorem involution_restrictions (h2 : (2 : E) ≠ 0)
    (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (z : specialIsometry h) (hz : orderOf z = 2) :
    let P := OddLinearThreeCentralizerCore.minusSpace z.val.val.toLinearMap
    let Q := OddLinearThreeCentralizerCore.plusSpace z.val.val.toLinearMap
    (h.domRestrict₁₂ P P).Nondegenerate ∧ (h.domRestrict₁₂ Q Q).Nondegenerate ∧
      (∀ x ∈ P, ∀ y ∈ Q, h x y = 0) := by
  dsimp only
  let P := OddLinearThreeCentralizerCore.minusSpace z.val.val.toLinearMap
  let Q := OddLinearThreeCentralizerCore.plusSpace z.val.val.toLinearMap
  have hzpow : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
  have hz2 : z * z = 1 := by simpa only [pow_two] using hzpow
  have hf : Function.Involutive z.val.val := fun x =>
    congrArg (fun g : specialIsometry h => g.val.val x) hz2
  have hPQ := OddLinearThreeCentralizerCore.involution_spaces_isCompl h2
    z.val.val.toLinearMap hf
  have horth : ∀ x ∈ P, ∀ y ∈ Q, h x y = 0 := fun x hx y hy =>
    involution_eigenspaces_orthogonal h h2 z.val.val z.val.property x y hx hy
  refine ⟨orthogonal_restriction_nondegenerate h hsym hnd P Q hPQ horth,
    orthogonal_restriction_nondegenerate h hsym hnd Q P hPQ.symm ?_, horth⟩
  intro y hy x hx
  exact hsym.eq_iff.mpr (horth x hx y hy)

theorem isometryDeterminant_norm_one [Finite E] (hsym : h.IsSymm)
    (hnd : h.Nondegenerate) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (g : isometryGroup h) : isometryDeterminant h g ∈ normOneUnits (sigma := sigma) := by
  obtain ⟨b, hb⟩ := CatalogueBHermitian.exists_orthonormal_basis h hsym hnd hsigma hne
  let A := isometryMatrixEquiv h b hb g
  have he := (mem_Uid_iff sigma (Module.finrank E V) A.val).mp A.property
  have hd := congrArg Matrix.det he
  rw [Matrix.det_mul, Matrix.det_one] at hd
  have hc : (CFSG.LieType.Universal.Unitary.conjTr sigma A.val.val).det =
      sigma A.val.val.det := by
    rw [CFSG.LieType.Universal.Unitary.conjTr, Matrix.det_transpose]
    exact (sigma.toRingHom.map_det A.val.val).symm
  rw [hc] at hd
  change sigma (isometryDeterminant h g : E) * (isometryDeterminant h g : E) = 1
  rw [← isometryMatrixEquiv_determinant h b hb g]
  exact hd
end OriginalInvolution


section OriginalFieldGeometry
variable [Finite E] [FiniteDimensional E V]

omit [Finite E] in
theorem scalar_subgroup_normal (hdim : Module.finrank E V = 3)
    (D : Subgroup (specialIsometry h)) (hD : D ≤ scalarCenter h hdim) : D.Normal :=
  Subgroup.normal_of_le_center (hD.trans (scalarCenter_le_center h hdim))

omit [FiniteDimensional E V] in
theorem unitaryField_two_ne_zero (p f : ℕ) (hpodd : Odd p)
    (hE : Nat.card E = (p ^ f) ^ 2) : (2 : E) ≠ 0 :=
  OddLinearThreeCentralizerCore.two_ne_zero E (by rw [hE]; exact hpodd.pow.pow)

theorem original_involution_geometry (p f : ℕ) [Fact p.Prime] (hpodd : Odd p)
    (hE : Nat.card E = (p ^ f) ^ 2)
    (h : V →ₛₗ[(CatalogueBUnitaryTwo.unitaryFieldConjugation p f hE).toRingHom] V →ₗ[E] E)
    (hsym : h.IsSymm) (hnd : h.Nondegenerate) (hdim : Module.finrank E V = 3)
    (D : Subgroup (specialIsometry h)) (hD : D ≤ scalarCenter h hdim) :
    letI : D.Normal := scalar_subgroup_normal h hdim D hD
    ∀ (t : specialIsometry h ⧸ D), orderOf t = 2 →
      ∃! z : specialIsometry h,
        orderOf z = 2 ∧ QuotientGroup.mk' D z = t ∧
          Module.finrank E (OddLinearThreeCentralizerCore.minusSpace z.val.val.toLinearMap) = 2 ∧
          Module.finrank E (OddLinearThreeCentralizerCore.plusSpace z.val.val.toLinearMap) = 1 ∧
          (h.domRestrict₁₂
            (OddLinearThreeCentralizerCore.minusSpace z.val.val.toLinearMap)
            (OddLinearThreeCentralizerCore.minusSpace z.val.val.toLinearMap)).Nondegenerate ∧
          (h.domRestrict₁₂
            (OddLinearThreeCentralizerCore.plusSpace z.val.val.toLinearMap)
            (OddLinearThreeCentralizerCore.plusSpace z.val.val.toLinearMap)).Nondegenerate ∧
          (∀ x ∈ OddLinearThreeCentralizerCore.minusSpace z.val.val.toLinearMap,
            ∀ y ∈ OddLinearThreeCentralizerCore.plusSpace z.val.val.toLinearMap, h x y = 0) := by
  let : D.Normal := scalar_subgroup_normal h hdim D hD
  intro t ht
  obtain ⟨z, hz, huniq⟩ := unique_involution_lift h hdim D hD t ht
  have h2 := unitaryField_two_ne_zero p f hpodd hE
  obtain ⟨hm, hp⟩ := involution_finrank h h2 hdim z hz.1
  obtain ⟨hP, hQ, ho⟩ := involution_restrictions h h2 hsym hnd z hz.1
  exact ⟨z, ⟨hz.1, hz.2, hm, hp, hP, hQ, ho⟩, fun w hw => huniq w ⟨hw.1, hw.2.1⟩⟩
end OriginalFieldGeometry

section UnitaryCentralizer
open OddLinearThreeCentralizerCore

theorem involution_complement (h2 : (2 : E) ≠ 0)
    (z : specialIsometry h) (hz : orderOf z = 2) :
    IsCompl (minusSpace z.val.val.toLinearMap) (plusSpace z.val.val.toLinearMap) := by
  have hzpow : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
  have hz2 : z * z = 1 := by simpa only [pow_two] using hzpow
  exact involution_spaces_isCompl h2 z.val.val.toLinearMap
    (fun x => congrArg (fun g : specialIsometry h => g.val.val x) hz2)

theorem orthogonal_sum_pairing (hsym : h.IsSymm)
    (P Q : Submodule E V) (horth : ∀ x ∈ P, ∀ y ∈ Q, h x y = 0)
    (x x' : P) (y y' : Q) :
    h ((x : V) + y) ((x' : V) + y') = h x x' + h y y' := by
  rw [CatalogueBHermitian.add_left, map_add, map_add, horth x x.property y' y'.property,
    hsym.eq_iff.mpr (horth x' x'.property y y.property)]
  simp only [add_zero, zero_add]

variable [Finite E] [FiniteDimensional E V]

theorem unitary_block_isometry (hsym : h.IsSymm) (hsigma : sigma ^ 2 = 1)
    (hne : sigma ≠ 1) (P Q : Submodule E V) (hPQ : IsCompl P Q)
    (hndP : (h.domRestrict₁₂ P P).Nondegenerate)
    (horth : ∀ x ∈ P, ∀ y ∈ Q, h x y = 0)
    (a : isometryGroup (h.domRestrict₁₂ P P)) :
    blockExtension (P.prodEquivOfIsCompl Q hPQ) a.val ∈ isometryGroup h := by
  let e := P.prodEquivOfIsCompl Q hPQ
  have hd := isometryDeterminant_norm_one (h.domRestrict₁₂ P P)
    (hsym.domRestrict P) hndP hsigma hne a
  have hdinv := (normOneUnits (sigma := sigma)).inv_mem hd
  change sigma ((a.val.det⁻¹ : Eˣ) : E) * ((a.val.det⁻¹ : Eˣ) : E) = 1 at hdinv
  intro v w
  obtain ⟨⟨x, y⟩, rfl⟩ := e.surjective v
  obtain ⟨⟨x', y'⟩, rfl⟩ := e.surjective w
  change h (blockExtension e a.val (e (x, y)))
    (blockExtension e a.val (e (x', y'))) = h (e (x, y)) (e (x', y'))
  simp only [blockExtension, LinearEquiv.trans_apply, e.symm_apply_apply,
    LinearEquiv.prodCongr_apply]
  change h ((a.val x : V) + ((a.val.det⁻¹ : Eˣ) : E) • (y : V))
    ((a.val x' : V) + ((a.val.det⁻¹ : Eˣ) : E) • (y' : V)) =
      h ((x : V) + y) ((x' : V) + y')
  rw [orthogonal_sum_pairing h hsym P Q horth x x' y y']
  have hsum := orthogonal_sum_pairing h hsym P Q horth (a.val x) (a.val x')
    (((a.val.det⁻¹ : Eˣ) : E) • y) (((a.val.det⁻¹ : Eˣ) : E) • y')
  change h ((a.val x : V) + ((a.val.det⁻¹ : Eˣ) : E) • (y : V))
    ((a.val x' : V) + ((a.val.det⁻¹ : Eˣ) : E) • (y' : V)) =
      h (a.val x) (a.val x') +
        h (((a.val.det⁻¹ : Eˣ) : E) • (y : V))
          (((a.val.det⁻¹ : Eˣ) : E) • (y' : V)) at hsum
  rw [hsum]
  have ha : h (a.val x) (a.val x') = h x x' := a.property x x'
  rw [ha, CatalogueBHermitian.smul_left, map_smul, smul_eq_mul,
    ← mul_assoc, hdinv, one_mul]

@[expose] def specialAction : specialIsometry h →* _root_.SpecialLinearGroup E V where
  toFun g := ⟨g.val.val, g.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

omit [Finite E] [FiniteDimensional E V] in
theorem specialAction_apply (g : specialIsometry h) (v : V) :
    specialAction h g v = g.val.val v := rfl

omit [Finite E] [FiniteDimensional E V] in
theorem unitary_centralizer_commutes (z : specialIsometry h)
    (g : Subgroup.centralizer ({z} : Set (specialIsometry h))) :
    ∀ v, z.val.val (g.val.val.val v) = g.val.val.val (z.val.val v) := by
  have hc := Subgroup.mem_centralizer_singleton_iff.mp g.property
  intro v
  exact (congrArg (fun a : specialIsometry h => a.val.val v) hc).symm

@[expose] def unitaryCentralizerRestriction (z : specialIsometry h) :
    Subgroup.centralizer ({z} : Set (specialIsometry h)) →*
      isometryGroup (h.domRestrict₁₂
        (minusSpace z.val.val.toLinearMap) (minusSpace z.val.val.toLinearMap)) where
  toFun g := ⟨eigenspaceRestriction z.val.val.toLinearMap (-1) g.val.val.val
    (unitary_centralizer_commutes h z g), by
      intro x y
      change h (eigenspaceRestriction z.val.val.toLinearMap (-1) g.val.val.val
        (unitary_centralizer_commutes h z g) x)
          (eigenspaceRestriction z.val.val.toLinearMap (-1) g.val.val.val
            (unitary_centralizer_commutes h z g) y) = h x y
      dsimp only [minusSpace] at x y ⊢
      rw [eigenspaceRestriction_apply, eigenspaceRestriction_apply]
      exact g.val.val.property x y⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    dsimp only [minusSpace] at x ⊢
    exact eigenspaceRestriction_apply z.val.val.toLinearMap (-1) _ _ x
  map_mul' a b := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    rfl


omit [Finite E] [FiniteDimensional E V] in
theorem unitaryCentralizerRestriction_apply (z : specialIsometry h)
    (g : Subgroup.centralizer ({z} : Set (specialIsometry h)))
    (x : minusSpace z.val.val.toLinearMap) :
    ((unitaryCentralizerRestriction h z g).val x : V) = g.val.val.val x := rfl

@[expose] def unitaryBlock (hsym : h.IsSymm) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (P Q : Submodule E V) (hPQ : IsCompl P Q) (hQ : Module.finrank E Q = 1)
    (hndP : (h.domRestrict₁₂ P P).Nondegenerate)
    (horth : ∀ x ∈ P, ∀ y ∈ Q, h x y = 0) :
    isometryGroup (h.domRestrict₁₂ P P) →* specialIsometry h where
  toFun a := ⟨⟨blockExtension (P.prodEquivOfIsCompl Q hPQ) a.val,
    unitary_block_isometry h hsym hsigma hne P Q hPQ hndP horth a⟩,
      blockExtension_det hQ (P.prodEquivOfIsCompl Q hPQ) a.val⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    obtain ⟨⟨x, y⟩, rfl⟩ := (P.prodEquivOfIsCompl Q hPQ).surjective v
    simp [blockExtension, LinearEquiv.smulOfUnit]
  map_mul' a b := by
    apply Subtype.ext
    apply Subtype.ext
    exact blockExtension_mul (P.prodEquivOfIsCompl Q hPQ) a.val b.val

@[expose] def unitaryCentralizerBlock (h2 : (2 : E) ≠ 0) (hsym : h.IsSymm)
    (hnd : h.Nondegenerate) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hdim : Module.finrank E V = 3) (z : specialIsometry h) (hz : orderOf z = 2) :
    isometryGroup (h.domRestrict₁₂
      (minusSpace z.val.val.toLinearMap) (minusSpace z.val.val.toLinearMap)) →*
        Subgroup.centralizer ({z} : Set (specialIsometry h)) :=
  (unitaryBlock h hsym hsigma hne _ _ (involution_complement h h2 z hz)
    (involution_finrank h h2 hdim z hz).2
    (involution_restrictions h h2 hsym hnd z hz).1
    (involution_restrictions h h2 hsym hnd z hz).2.2).codRestrict _ (by
      intro a
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      apply Subtype.ext
      apply LinearEquiv.ext
      intro v
      exact (blockExtension_commutes z.val.val.toLinearMap
        (involution_complement h h2 z hz) a.val v).symm)

theorem unitaryCentralizerBlock_apply (h2 : (2 : E) ≠ 0) (hsym : h.IsSymm)
    (hnd : h.Nondegenerate) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hdim : Module.finrank E V = 3) (z : specialIsometry h) (hz : orderOf z = 2)
    (a : isometryGroup (h.domRestrict₁₂
      (minusSpace z.val.val.toLinearMap) (minusSpace z.val.val.toLinearMap))) (v : V) :
    (unitaryCentralizerBlock h h2 hsym hnd hsigma hne hdim z hz a).val.val.val v =
      blockExtension (Submodule.prodEquivOfIsCompl
        (minusSpace z.val.val.toLinearMap) (plusSpace z.val.val.toLinearMap)
        (involution_complement h h2 z hz)) a.val v := rfl

theorem unitaryCentralizerBlock_minus (h2 : (2 : E) ≠ 0) (hsym : h.IsSymm)
    (hnd : h.Nondegenerate) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hdim : Module.finrank E V = 3) (z : specialIsometry h) (hz : orderOf z = 2)
    (a : isometryGroup (h.domRestrict₁₂
      (minusSpace z.val.val.toLinearMap) (minusSpace z.val.val.toLinearMap)))
    (x : minusSpace z.val.val.toLinearMap) :
    (unitaryCentralizerBlock h h2 hsym hnd hsigma hne hdim z hz a).val.val.val x =
      (a.val x : V) := by
  rw [unitaryCentralizerBlock_apply]
  have hx := blockExtension_left (Submodule.prodEquivOfIsCompl
    (minusSpace z.val.val.toLinearMap) (plusSpace z.val.val.toLinearMap)
    (involution_complement h h2 z hz)) a.val x
  change blockExtension _ a.val ((x : V) + (0 : V)) = (a.val x : V) + 0 at hx
  simpa only [add_zero] using hx

theorem unitaryCentralizerBlock_plus (h2 : (2 : E) ≠ 0) (hsym : h.IsSymm)
    (hnd : h.Nondegenerate) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hdim : Module.finrank E V = 3) (z : specialIsometry h) (hz : orderOf z = 2)
    (a : isometryGroup (h.domRestrict₁₂
      (minusSpace z.val.val.toLinearMap) (minusSpace z.val.val.toLinearMap)))
    (y : plusSpace z.val.val.toLinearMap) :
    (unitaryCentralizerBlock h h2 hsym hnd hsigma hne hdim z hz a).val.val.val y =
      ((a.val.det⁻¹ : Eˣ) : E) • (y : V) := by
  rw [unitaryCentralizerBlock_apply]
  have hy := blockExtension_right (Submodule.prodEquivOfIsCompl
    (minusSpace z.val.val.toLinearMap) (plusSpace z.val.val.toLinearMap)
    (involution_complement h h2 z hz)) a.val y
  change blockExtension _ a.val ((0 : V) + (y : V)) =
    (0 : V) + ((a.val.det⁻¹ : Eˣ) : E) • (y : V) at hy
  simpa only [zero_add] using hy

theorem unitaryCentralizerRestriction_block (h2 : (2 : E) ≠ 0) (hsym : h.IsSymm)
    (hnd : h.Nondegenerate) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hdim : Module.finrank E V = 3) (z : specialIsometry h) (hz : orderOf z = 2)
    (a : isometryGroup (h.domRestrict₁₂
      (minusSpace z.val.val.toLinearMap) (minusSpace z.val.val.toLinearMap))) :
    unitaryCentralizerRestriction h z
      (unitaryCentralizerBlock h h2 hsym hnd hsigma hne hdim z hz a) = a := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  rw [unitaryCentralizerRestriction_apply]
  exact unitaryCentralizerBlock_minus h h2 hsym hnd hsigma hne hdim z hz a x

theorem unitaryCentralizerBlock_restriction (h2 : (2 : E) ≠ 0) (hsym : h.IsSymm)
    (hnd : h.Nondegenerate) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hdim : Module.finrank E V = 3) (z : specialIsometry h) (hz : orderOf z = 2)
    (g : Subgroup.centralizer ({z} : Set (specialIsometry h))) :
    unitaryCentralizerBlock h h2 hsym hnd hsigma hne hdim z hz
      (unitaryCentralizerRestriction h z g) = g := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact (commuting_det_one_eq_block z.val.val.toLinearMap
    (involution_complement h h2 z hz) (involution_finrank h h2 hdim z hz).2
    g.val.val.val (unitary_centralizer_commutes h z g) g.val.property).symm

@[expose] def unitaryCentralizerEquiv (h2 : (2 : E) ≠ 0) (hsym : h.IsSymm)
    (hnd : h.Nondegenerate) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hdim : Module.finrank E V = 3) (z : specialIsometry h) (hz : orderOf z = 2) :
    isometryGroup (h.domRestrict₁₂
      (minusSpace z.val.val.toLinearMap) (minusSpace z.val.val.toLinearMap)) ≃*
        Subgroup.centralizer ({z} : Set (specialIsometry h)) where
  toFun := unitaryCentralizerBlock h h2 hsym hnd hsigma hne hdim z hz
  invFun := unitaryCentralizerRestriction h z
  left_inv := unitaryCentralizerRestriction_block h h2 hsym hnd hsigma hne hdim z hz
  right_inv := unitaryCentralizerBlock_restriction h h2 hsym hnd hsigma hne hdim z hz
  map_mul' := (unitaryCentralizerBlock h h2 hsym hnd hsigma hne hdim z hz).map_mul


@[expose] def specialScalarCentralizer (hdim : Module.finrank E V = 3) (z : specialIsometry h) :
    cubicUnits (sigma := sigma) →*
      Subgroup.centralizer ({z} : Set (specialIsometry h)) :=
  (scalarSpecial h hdim).codRestrict _ (by
    intro c
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_center_iff.mp
      (scalarCenter_le_center h hdim (show scalarSpecial h hdim c ∈ scalarCenter h hdim from
        ⟨c, rfl⟩)) z).symm)

omit [Finite E] in
theorem unitaryCentralizerRestriction_scalar (hdim : Module.finrank E V = 3)
    (z : specialIsometry h) (c : cubicUnits (sigma := sigma)) :
    unitaryCentralizerRestriction h z (specialScalarCentralizer h hdim z c) =
      scalarIsometry (h.domRestrict₁₂
        (minusSpace z.val.val.toLinearMap) (minusSpace z.val.val.toLinearMap)) c.val := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  rfl

theorem unitaryCentralizerBlock_scalar (h2 : (2 : E) ≠ 0) (hsym : h.IsSymm)
    (hnd : h.Nondegenerate) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hdim : Module.finrank E V = 3) (z : specialIsometry h) (hz : orderOf z = 2)
    (c : cubicUnits (sigma := sigma)) :
    unitaryCentralizerBlock h h2 hsym hnd hsigma hne hdim z hz
      (scalarIsometry (h.domRestrict₁₂
        (minusSpace z.val.val.toLinearMap) (minusSpace z.val.val.toLinearMap)) c.val) =
          specialScalarCentralizer h hdim z c := by
  rw [← unitaryCentralizerRestriction_scalar h hdim z c]
  exact unitaryCentralizerBlock_restriction h h2 hsym hnd hsigma hne hdim z hz _

@[expose] def unitaryQuotientCentralizer (h2 : (2 : E) ≠ 0) (hsym : h.IsSymm)
    (hnd : h.Nondegenerate) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hdim : Module.finrank E V = 3) (D : Subgroup (specialIsometry h)) [D.Normal]
    (z : specialIsometry h) (hz : orderOf z = 2) :
    isometryGroup (h.domRestrict₁₂
      (minusSpace z.val.val.toLinearMap) (minusSpace z.val.val.toLinearMap)) →*
        Subgroup.centralizer ({QuotientGroup.mk' D z} : Set (specialIsometry h ⧸ D)) :=
  (OddNormalQuotientInvolutions.centralizerQuotient D z).comp
    (unitaryCentralizerBlock h h2 hsym hnd hsigma hne hdim z hz)

theorem unitaryQuotientCentralizer_coe (h2 : (2 : E) ≠ 0) (hsym : h.IsSymm)
    (hnd : h.Nondegenerate) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hdim : Module.finrank E V = 3) (D : Subgroup (specialIsometry h)) [D.Normal]
    (z : specialIsometry h) (hz : orderOf z = 2)
    (a : isometryGroup (h.domRestrict₁₂
      (minusSpace z.val.val.toLinearMap) (minusSpace z.val.val.toLinearMap))) :
    (unitaryQuotientCentralizer h h2 hsym hnd hsigma hne hdim D z hz a :
      specialIsometry h ⧸ D) = QuotientGroup.mk' D
        (unitaryCentralizerBlock h h2 hsym hnd hsigma hne hdim z hz a).val := rfl

theorem unitaryQuotientCentralizer_surjective (h2 : (2 : E) ≠ 0) (hsym : h.IsSymm)
    (hnd : h.Nondegenerate) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hdim : Module.finrank E V = 3) (D : Subgroup (specialIsometry h)) [D.Normal]
    (hD : D ≤ scalarCenter h hdim) (z : specialIsometry h) (hz : orderOf z = 2) :
    Function.Surjective (unitaryQuotientCentralizer h h2 hsym hnd hsigma hne hdim D z hz) := by
  let : Finite (isometryGroup h) := isometryGroup_finite h
  exact (OddNormalQuotientInvolutions.centralizerQuotient_surjective D
    (scalar_kernel_odd h hdim D hD) z hz).comp
      (unitaryCentralizerEquiv h h2 hsym hnd hsigma hne hdim z hz).surjective

variable {h} in
theorem unitaryQuotientCentralizer_mem_ker {h2 : (2 : E) ≠ 0} {hsym : h.IsSymm}
    {hnd : h.Nondegenerate} {hsigma : sigma ^ 2 = 1} {hne : sigma ≠ 1}
    {hdim : Module.finrank E V = 3} {D : Subgroup (specialIsometry h)} [D.Normal]
    {z : specialIsometry h} {hz : orderOf z = 2}
    {a : isometryGroup (h.domRestrict₁₂
      (minusSpace z.val.val.toLinearMap) (minusSpace z.val.val.toLinearMap))} :
    a ∈ (unitaryQuotientCentralizer h h2 hsym hnd hsigma hne hdim D z hz).ker ↔
      (unitaryCentralizerBlock h h2 hsym hnd hsigma hne hdim z hz a).val ∈ D := by
  rw [MonoidHom.mem_ker, ← Subtype.coe_inj, unitaryQuotientCentralizer_coe]
  exact QuotientGroup.eq_one_iff _

variable {h} in
theorem unitaryQuotientCentralizer_mem_ker_iff (h2 : (2 : E) ≠ 0) (hsym : h.IsSymm)
    (hnd : h.Nondegenerate) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    {hdim : Module.finrank E V = 3} {D : Subgroup (specialIsometry h)} [D.Normal]
    (hD : D ≤ scalarCenter h hdim) {z : specialIsometry h} (hz : orderOf z = 2)
    {a : isometryGroup (h.domRestrict₁₂
      (minusSpace z.val.val.toLinearMap) (minusSpace z.val.val.toLinearMap))} :
    a ∈ (unitaryQuotientCentralizer h h2 hsym hnd hsigma hne hdim D z hz).ker ↔
      ∃ c : cubicUnits (sigma := sigma), scalarSpecial h hdim c ∈ D ∧
        a = scalarIsometry (h.domRestrict₁₂
          (minusSpace z.val.val.toLinearMap) (minusSpace z.val.val.toLinearMap)) c.val := by
  rw [unitaryQuotientCentralizer_mem_ker]
  constructor
  · intro ha
    obtain ⟨c, hc⟩ := hD ha
    refine ⟨c, hc.symm ▸ ha, ?_⟩
    have he : unitaryCentralizerBlock h h2 hsym hnd hsigma hne hdim z hz a =
        specialScalarCentralizer h hdim z c := Subtype.ext hc.symm
    have hr := congrArg (unitaryCentralizerRestriction h z) he
    rw [unitaryCentralizerRestriction_block, unitaryCentralizerRestriction_scalar] at hr
    exact hr
  · rintro ⟨c, hc, rfl⟩
    rw [unitaryCentralizerBlock_scalar]
    exact hc

@[expose] def unitaryQuotientKernelEquiv (h2 : (2 : E) ≠ 0) (hsym : h.IsSymm)
    (hnd : h.Nondegenerate) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hdim : Module.finrank E V = 3) (D : Subgroup (specialIsometry h)) [D.Normal]
    (hD : D ≤ scalarCenter h hdim) (z : specialIsometry h) (hz : orderOf z = 2) :
    (unitaryQuotientCentralizer h h2 hsym hnd hsigma hne hdim D z hz).ker ≃* D where
  toFun a := ⟨(unitaryCentralizerBlock h h2 hsym hnd hsigma hne hdim z hz a.val).val,
    unitaryQuotientCentralizer_mem_ker.mp a.property⟩
  invFun d := ⟨unitaryCentralizerRestriction h z ⟨d.val, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_center_iff.mp (scalarCenter_le_center h hdim (hD d.property)) z).symm⟩,
    unitaryQuotientCentralizer_mem_ker.mpr (by
      rw [unitaryCentralizerBlock_restriction]
      exact d.property)⟩
  left_inv a := Subtype.ext
    (unitaryCentralizerRestriction_block h h2 hsym hnd hsigma hne hdim z hz a.val)
  right_inv d := by
    apply Subtype.ext
    exact congrArg (fun c : Subgroup.centralizer ({z} : Set (specialIsometry h)) => c.val)
      (unitaryCentralizerBlock_restriction h h2 hsym hnd hsigma hne hdim z hz _)
  map_mul' a b := by
    apply Subtype.ext
    exact congrArg (fun c : Subgroup.centralizer ({z} : Set (specialIsometry h)) => c.val)
      (map_mul (unitaryCentralizerBlock h h2 hsym hnd hsigma hne hdim z hz) a.val b.val)

theorem unitaryQuotientCentralizer_ker_card (h2 : (2 : E) ≠ 0) (hsym : h.IsSymm)
    (hnd : h.Nondegenerate) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hdim : Module.finrank E V = 3) (D : Subgroup (specialIsometry h)) [D.Normal]
    (hD : D ≤ scalarCenter h hdim) (z : specialIsometry h) (hz : orderOf z = 2) :
    Nat.card (unitaryQuotientCentralizer h h2 hsym hnd hsigma hne hdim D z hz).ker =
      Nat.card D := Nat.card_congr
        (unitaryQuotientKernelEquiv h h2 hsym hnd hsigma hne hdim D hD z hz).toEquiv

end UnitaryCentralizer

section NormOrder
open CFSG.LocalAnalysis.ComponentInitial

theorem originalFieldData [Finite E] (p f : ℕ) [Fact p.Prime]
    (hE : Nat.card E = (p ^ f) ^ 2) : UnitaryFieldData p f E where
  prime := Fact.out
  one_le := by
    have hcard := Finite.one_lt_card (α := E)
    by_contra hf
    have hf0 : f = 0 := by omega
    rw [hf0, pow_zero, one_pow] at hE
    omega
  card := by rw [Nat.mul_comm 2 f, pow_mul]; exact hE

theorem originalFieldData_bar [Finite E] (p f : ℕ) [Fact p.Prime]
    (hE : Nat.card E = (p ^ f) ^ 2) :
    (CatalogueBUnitaryTwo.unitaryFieldConjugation p f hE).toRingHom =
      (originalFieldData p f hE).bar := by
  ext x
  change CatalogueBUnitaryTwo.unitaryFieldConjugation p f hE x =
    (originalFieldData p f hE).bar x
  rw [CatalogueBUnitaryTwo.unitaryFieldConjugation_apply, UnitaryFieldData.bar_apply]

theorem normOneUnits_eq_norm_ker [Finite E] (p f : ℕ) [Fact p.Prime]
    (hE : Nat.card E = (p ^ f) ^ 2) :
    normOneUnits (sigma := CatalogueBUnitaryTwo.unitaryFieldConjugation p f hE) =
      (Units.map (originalFieldData p f hE).normHom).ker := by
  ext a
  rw [UnitaryFieldData.mem_ker_normUnits]
  change CatalogueBUnitaryTwo.unitaryFieldConjugation p f hE (a : E) * (a : E) = 1 ↔
    (a : E) * (originalFieldData p f hE).bar (a : E) = 1
  rw [← originalFieldData_bar p f hE]
  rw [mul_comm]
  rfl

theorem normOneUnits_card [Finite E] (p f : ℕ) [Fact p.Prime]
    (hE : Nat.card E = (p ^ f) ^ 2) :
    Nat.card (normOneUnits (sigma := CatalogueBUnitaryTwo.unitaryFieldConjugation p f hE)) =
      p ^ f + 1 := by
  rw [normOneUnits_eq_norm_ker]
  exact (originalFieldData p f hE).card_ker_normUnits_and_surjective.1

end NormOrder

theorem scalarIsometry_injective [Nontrivial V] : Function.Injective (scalarIsometry h) := by
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  intro a b hab
  apply Subtype.ext
  apply Units.ext
  exact smul_left_injective E hx
    (congrArg (fun g : isometryGroup h => g.val x) hab)

theorem scalar_norm_one_of_isometry [Nontrivial V] (hnd : h.Nondegenerate)
    (a : Eˣ) (ha : scalarAction (V := V) a ∈ isometryGroup h) :
    a ∈ normOneUnits (sigma := sigma) := by
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have hex : ∃ y, h x y ≠ 0 := by
    by_contra hn
    have hall : ∀ y, h x y = 0 := by simpa only [not_exists, not_not] using hn
    exact hx (hnd.1 x hall)
  obtain ⟨y, hy⟩ := hex
  have he := ha x y
  change h ((a : E) • x) ((a : E) • y) = h x y at he
  rw [CatalogueBHermitian.smul_left, map_smul, smul_eq_mul, ← mul_assoc] at he
  change sigma (a : E) * (a : E) = 1
  exact (mul_right_cancel₀ hy (he.trans (one_mul (h x y)).symm))

theorem scalarIsometry_range_le_center :
    (scalarIsometry h).range ≤ Subgroup.center (isometryGroup h) := by
  rintro a ⟨c, rfl⟩
  exact scalarIsometry_mem_center h c

@[expose] def planeCoordinates (B : (Fin 2 → E) ≃ₗ[E] V) :
    (V ≃ₗ[E] V) ≃* Matrix.GeneralLinearGroup (Fin 2) E :=
  CatalogueBAlternatingIsometry.basisMatrixEquiv (Module.Basis.ofEquivFun B.symm)

theorem planeCoordinates_val (B : (Fin 2 → E) ≃ₗ[E] V) (g : V ≃ₗ[E] V) :
    (planeCoordinates B g).val =
      LinearMap.toMatrix' ((B.trans g).trans B.symm).toLinearMap := by
  rw [planeCoordinates, CatalogueBAlternatingIsometry.basisMatrixEquiv_val,
    LinearMap.toMatrix, Module.Basis.equivFun_ofEquivFun]
  rfl


theorem planeCoordinates_special_inverse
    (B : (Fin 2 → E) ≃ₗ[E] V) (t : Eˣ)
    (e : specialIsometry h ≃*
      Matrix.SpecialLinearGroup (Fin 2) (CatalogueBLinearTwoDescent.fixedSubfield E sigma))
    (hinverse : ∀ N, LinearMap.toMatrix'
      ((B.trans (e.symm N).val.val).trans B.symm).toLinearMap =
        (CatalogueBUnitaryTwo.diagonalGL t).val *
          (CatalogueBUnitaryTwo.fixedSLMap sigma N).val *
            (CatalogueBUnitaryTwo.diagonalGL t)⁻¹.val)
    (N : Matrix.SpecialLinearGroup (Fin 2)
      (CatalogueBLinearTwoDescent.fixedSubfield E sigma)) :
    planeCoordinates B (e.symm N).val.val =
      CFSG.Semidihedral.OddLinearNormals.conjugatedEntrywiseSL
        (CatalogueBLinearTwoDescent.fixedSubfield E sigma).subtype
        (CatalogueBUnitaryTwo.diagonalGL t) N := by
  apply Units.ext
  rw [planeCoordinates_val, hinverse]
  rfl

theorem planeCoordinates_special_range
    (B : (Fin 2 → E) ≃ₗ[E] V) (t : Eˣ)
    (e : specialIsometry h ≃*
      Matrix.SpecialLinearGroup (Fin 2) (CatalogueBLinearTwoDescent.fixedSubfield E sigma))
    (hinverse : ∀ N, LinearMap.toMatrix'
      ((B.trans (e.symm N).val.val).trans B.symm).toLinearMap =
        (CatalogueBUnitaryTwo.diagonalGL t).val *
          (CatalogueBUnitaryTwo.fixedSLMap sigma N).val *
            (CatalogueBUnitaryTwo.diagonalGL t)⁻¹.val) :
    CFSG.Semidihedral.OddLinearNormals.conjugatedImageSL
      (CatalogueBLinearTwoDescent.fixedSubfield E sigma).subtype
      (CatalogueBUnitaryTwo.diagonalGL t) =
        ((planeCoordinates B).toMonoidHom.comp
          ((isometryGroup h).subtype.comp (specialIsometry h).subtype)).range := by
  rw [CFSG.Semidihedral.OddLinearNormals.conjugatedImageSL_eq_range]
  ext A
  constructor
  · rintro ⟨N, rfl⟩
    exact ⟨e.symm N, planeCoordinates_special_inverse h B t e hinverse N⟩
  · rintro ⟨g, rfl⟩
    refine ⟨e g, ?_⟩
    have he := planeCoordinates_special_inverse h B t e hinverse (e g)
    rw [e.symm_apply_apply] at he
    exact he.symm


theorem unitaryPlane_normal_odd_scalar [Finite E] [FiniteDimensional E V]
    (p f : ℕ) [Fact p.Prime] (hpodd : Odd p)
    (hE : Nat.card E = (p ^ f) ^ 2)
    (h : V →ₛₗ[(CatalogueBUnitaryTwo.unitaryFieldConjugation p f hE).toRingHom] V →ₗ[E] E)
    (hsym : h.IsSymm) (hnd : h.Nondegenerate) (hdim : Module.finrank E V = 2)
    (R : Subgroup (isometryGroup h)) (hRnormal : R.Normal) (hRodd : Odd (Nat.card R)) :
    R ≤ (scalarIsometry h).range := by
  let sigma := CatalogueBUnitaryTwo.unitaryFieldConjugation p f hE
  let F := CatalogueBLinearTwoDescent.fixedSubfield E sigma
  obtain ⟨hFcard, B, t, e, hB, hgram, ht, hforward, hinverse⟩ :=
    CatalogueBUnitaryTwo.unitary_field_two_special_linear_isomorphism
      p f hE h hsym hnd hdim
  let c := planeCoordinates B
  let M := (isometryGroup h).map c.toMonoidHom
  let eM := c.subgroupMap (isometryGroup h)
  let S := CFSG.Semidihedral.OddLinearNormals.conjugatedImageSL F.subtype
    (CatalogueBUnitaryTwo.diagonalGL t)
  have hS : S = ((c.toMonoidHom.comp (isometryGroup h).subtype).comp
      (specialIsometry h).subtype).range :=
    planeCoordinates_special_range h B t e hinverse
  have hSM : S ≤ M := by
    rw [hS]
    rintro A ⟨g, rfl⟩
    exact ⟨g.val.val, g.val.property, rfl⟩
  have hSrestrict : S.subgroupOf M = (specialIsometry h).map eM.toMonoidHom := by
    ext A
    constructor
    · intro hA
      change A.val ∈ S at hA
      rw [hS] at hA
      obtain ⟨g, hg⟩ := hA
      exact ⟨g.val, g.property, Subtype.ext hg⟩
    · rintro ⟨g, hg, rfl⟩
      change c g.val ∈ S
      rw [hS]
      exact ⟨⟨g, hg⟩, rfl⟩
  have hSnormal : (S.subgroupOf M).Normal := by
    rw [hSrestrict]
    exact (show (specialIsometry h).Normal from inferInstance).map
      eM.toMonoidHom eM.surjective
  let T := R.map eM.toMonoidHom
  have hTnormal : T.Normal := hRnormal.map eM.toMonoidHom eM.surjective
  have hTcard : Nat.card T = Nat.card R :=
    (Nat.card_congr (eM.subgroupMap R).toEquiv).symm
  have hFodd : Odd (Nat.card F) := by rw [hFcard]; exact hpodd.pow
  have hFge : 3 ≤ Nat.card F := by
    have hf1 := (originalFieldData p f hE).one_le
    have hpge : 3 ≤ p := by
      have hpprime : Nat.Prime p := Fact.out
      have hp2 := hpprime.two_le
      have hpne : p ≠ 2 := by intro he; subst p; norm_num at hpodd
      omega
    rw [hFcard]
    exact hpge.trans (Nat.le_self_pow (by omega) p)
  intro r hr
  have hmr : eM r ∈ T := ⟨r, hr, rfl⟩
  have hscalar := CFSG.Semidihedral.OddLinearNormals.normal_odd_conjugated_matrix_overgroup_scalar
    hFodd hFge F.subtype F.subtype.injective (CatalogueBUnitaryTwo.diagonalGL t)
    M hSM hSnormal T hTnormal (hTcard ▸ hRodd) (eM r) hmr
  have hc : c r.val ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) E) :=
    Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr hscalar
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hc
  obtain ⟨a, ha⟩ := hc
  have har : scalarAction (V := V) a = r.val := by
    apply c.injective
    rw [← ha]
    apply Units.ext
    rw [planeCoordinates_val]
    have he : ((B.trans (scalarAction (V := V) a)).trans B.symm).toLinearMap =
        (a : E) • LinearMap.id := by
      apply LinearMap.ext
      intro x
      change B.symm ((a : E) • B x) = (a : E) • x
      rw [map_smul, B.symm_apply_apply]
    rw [he, map_smul, LinearMap.toMatrix'_id]
    ext i j
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal,
      Matrix.one_apply]
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (R := E) (by rw [hdim]; decide)
  have hanorm := scalar_norm_one_of_isometry h hnd a (har.symm ▸ r.property)
  exact ⟨⟨a, hanorm⟩, Subtype.ext har⟩


section ExactCore
open OddLinearThreeCentralizerCore
open scoped Nat
variable [Finite E] [FiniteDimensional E V]

theorem unitaryQuotientKernel_le_scalars (h2 : (2 : E) ≠ 0) (hsym : h.IsSymm)
    (hnd : h.Nondegenerate) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hdim : Module.finrank E V = 3) (D : Subgroup (specialIsometry h)) [D.Normal]
    (hD : D ≤ scalarCenter h hdim) (z : specialIsometry h) (hz : orderOf z = 2) :
    (unitaryQuotientCentralizer h h2 hsym hnd hsigma hne hdim D z hz).ker ≤
      (scalarIsometry (h.domRestrict₁₂
        (minusSpace z.val.val.toLinearMap) (minusSpace z.val.val.toLinearMap))).range := by
  intro a ha
  obtain ⟨c, _, rfl⟩ := (unitaryQuotientCentralizer_mem_ker_iff
    h2 hsym hnd hsigma hne hD hz).mp ha
  exact ⟨c.val, rfl⟩

theorem unitaryQuotientCentralizer_core_structure (p f : ℕ) [Fact p.Prime]
    (hpodd : Odd p) (hE : Nat.card E = (p ^ f) ^ 2)
    (h : V →ₛₗ[(CatalogueBUnitaryTwo.unitaryFieldConjugation p f hE).toRingHom] V →ₗ[E] E)
    (hsym : h.IsSymm) (hnd : h.Nondegenerate) (hdim : Module.finrank E V = 3)
    (D : Subgroup (specialIsometry h)) [D.Normal] (hD : D ≤ scalarCenter h hdim)
    (z : specialIsometry h) (hz : orderOf z = 2) :
    let h2 := unitaryField_two_ne_zero p f hpodd hE
    let hsigma := (CatalogueBUnitaryTwo.unitaryFieldConjugation_data p f hE).1
    let hne := (CatalogueBUnitaryTwo.unitaryFieldConjugation_data p f hE).2.1
    let P := minusSpace z.val.val.toLinearMap
    let phi := unitaryQuotientCentralizer h h2 hsym hnd hsigma hne hdim D z hz
    let A := normOneUnits (sigma := CatalogueBUnitaryTwo.unitaryFieldConjugation p f hE)
    CFSG.oddCore (Subgroup.centralizer
      ({QuotientGroup.mk' D z} : Set (specialIsometry h ⧸ D))) =
        ((CyclicOddScalarQuotient.oddElements A).map
          (scalarIsometry (h.domRestrict₁₂ P P))).map phi ∧
      CFSG.oddCore (Subgroup.centralizer
        ({QuotientGroup.mk' D z} : Set (specialIsometry h ⧸ D))) ≤
          Subgroup.center (Subgroup.centralizer
            ({QuotientGroup.mk' D z} : Set (specialIsometry h ⧸ D))) ∧
      IsCyclic (CFSG.oddCore (Subgroup.centralizer
        ({QuotientGroup.mk' D z} : Set (specialIsometry h ⧸ D)))) ∧
      Nat.card (CFSG.oddCore (Subgroup.centralizer
        ({QuotientGroup.mk' D z} : Set (specialIsometry h ⧸ D)))) =
          ordCompl[2] (p ^ f + 1) / Nat.card D := by
  let h2 := unitaryField_two_ne_zero p f hpodd hE
  let hsigma := (CatalogueBUnitaryTwo.unitaryFieldConjugation_data p f hE).1
  let hne := (CatalogueBUnitaryTwo.unitaryFieldConjugation_data p f hE).2.1
  let P := minusSpace z.val.val.toLinearMap
  let hP := h.domRestrict₁₂ P P
  let phi := unitaryQuotientCentralizer h h2 hsym hnd hsigma hne hdim D z hz
  have hPdim : Module.finrank E P = 2 := (involution_finrank h h2 hdim z hz).1
  have hPnd : hP.Nondegenerate := (involution_restrictions h h2 hsym hnd z hz).1
  let : Nontrivial P := Module.nontrivial_of_finrank_pos (R := E) (by rw [hPdim]; decide)
  let : Finite (isometryGroup h) := isometryGroup_finite h
  let : Finite (isometryGroup hP) := isometryGroup_finite hP
  have hkerodd : Odd (Nat.card phi.ker) := by
    rw [unitaryQuotientCentralizer_ker_card h h2 hsym hnd hsigma hne hdim D hD z hz]
    exact scalar_kernel_odd h hdim D hD
  have hc := CyclicOddScalarQuotient.quotient_oddCore_structure
    (scalarIsometry hP) (scalarIsometry_injective hP) (scalarIsometry_range_le_center hP)
    phi (unitaryQuotientCentralizer_surjective h h2 hsym hnd hsigma hne hdim D hD z hz)
    hkerodd (unitaryQuotientKernel_le_scalars h h2 hsym hnd hsigma hne hdim D hD z hz)
    (unitaryPlane_normal_odd_scalar p f hpodd hE hP (hsym.domRestrict P) hPnd hPdim)
  refine ⟨hc.1, hc.2.1, hc.2.2.1, ?_⟩
  calc
    Nat.card (CFSG.oddCore (Subgroup.centralizer
      ({QuotientGroup.mk' D z} : Set (specialIsometry h ⧸ D)))) =
        ordCompl[2] (Nat.card (normOneUnits
          (sigma := CatalogueBUnitaryTwo.unitaryFieldConjugation p f hE))) /
            Nat.card phi.ker := hc.2.2.2
    _ = ordCompl[2] (p ^ f + 1) / Nat.card D := by
      rw [normOneUnits_card p f hE,
        unitaryQuotientCentralizer_ker_card h h2 hsym hnd hsigma hne hdim D hD z hz]
end ExactCore


section TargetCentralizer
open OddLinearThreeCentralizerCore
open scoped Nat
variable [Finite E] [FiniteDimensional E V]

@[expose] def unitaryTargetCentralizerEquiv (D : Subgroup (specialIsometry h)) [D.Normal]
    (z : specialIsometry h) (t : specialIsometry h ⧸ D) (hzt : QuotientGroup.mk' D z = t) :
    Subgroup.centralizer ({QuotientGroup.mk' D z} : Set (specialIsometry h ⧸ D)) ≃*
      Subgroup.centralizer ({t} : Set (specialIsometry h ⧸ D)) :=
  MulEquiv.subgroupCongr (congrArg (fun x : specialIsometry h ⧸ D =>
    Subgroup.centralizer ({x} : Set (specialIsometry h ⧸ D))) hzt)

omit [Finite E] [FiniteDimensional E V] in
theorem unitaryTargetCentralizerEquiv_coe (D : Subgroup (specialIsometry h)) [D.Normal]
    (z : specialIsometry h) (t : specialIsometry h ⧸ D) (hzt : QuotientGroup.mk' D z = t)
    (g : Subgroup.centralizer ({QuotientGroup.mk' D z} : Set (specialIsometry h ⧸ D))) :
    (unitaryTargetCentralizerEquiv h D z t hzt g : specialIsometry h ⧸ D) = g :=
  MulEquiv.subgroupCongr_apply _ g

@[expose] def unitaryTargetQuotientCentralizer (h2 : (2 : E) ≠ 0) (hsym : h.IsSymm)
    (hnd : h.Nondegenerate) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hdim : Module.finrank E V = 3) (D : Subgroup (specialIsometry h)) [D.Normal]
    (z : specialIsometry h) (hz : orderOf z = 2) (t : specialIsometry h ⧸ D)
    (hzt : QuotientGroup.mk' D z = t) :
    isometryGroup (h.domRestrict₁₂
      (minusSpace z.val.val.toLinearMap) (minusSpace z.val.val.toLinearMap)) →*
        Subgroup.centralizer ({t} : Set (specialIsometry h ⧸ D)) :=
  (unitaryTargetCentralizerEquiv h D z t hzt).toMonoidHom.comp
    (unitaryQuotientCentralizer h h2 hsym hnd hsigma hne hdim D z hz)

theorem unitaryTargetQuotientCentralizer_coe (h2 : (2 : E) ≠ 0) (hsym : h.IsSymm)
    (hnd : h.Nondegenerate) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hdim : Module.finrank E V = 3) (D : Subgroup (specialIsometry h)) [D.Normal]
    (z : specialIsometry h) (hz : orderOf z = 2) (t : specialIsometry h ⧸ D)
    (hzt : QuotientGroup.mk' D z = t)
    (a : isometryGroup (h.domRestrict₁₂
      (minusSpace z.val.val.toLinearMap) (minusSpace z.val.val.toLinearMap))) :
    (unitaryTargetQuotientCentralizer h h2 hsym hnd hsigma hne hdim D z hz t hzt a :
      specialIsometry h ⧸ D) = QuotientGroup.mk' D
        (unitaryCentralizerBlock h h2 hsym hnd hsigma hne hdim z hz a).val :=
  (unitaryTargetCentralizerEquiv_coe h D z t hzt _).trans
    (unitaryQuotientCentralizer_coe h h2 hsym hnd hsigma hne hdim D z hz a)

theorem unitaryTargetQuotientCentralizer_surjective (h2 : (2 : E) ≠ 0) (hsym : h.IsSymm)
    (hnd : h.Nondegenerate) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hdim : Module.finrank E V = 3) (D : Subgroup (specialIsometry h)) [D.Normal]
    (hD : D ≤ scalarCenter h hdim) (z : specialIsometry h) (hz : orderOf z = 2)
    (t : specialIsometry h ⧸ D) (hzt : QuotientGroup.mk' D z = t) :
    Function.Surjective
      (unitaryTargetQuotientCentralizer h h2 hsym hnd hsigma hne hdim D z hz t hzt) :=
  (unitaryTargetCentralizerEquiv h D z t hzt).surjective.comp
    (unitaryQuotientCentralizer_surjective h h2 hsym hnd hsigma hne hdim D hD z hz)

theorem unitaryTargetQuotientCentralizer_ker (h2 : (2 : E) ≠ 0) (hsym : h.IsSymm)
    (hnd : h.Nondegenerate) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hdim : Module.finrank E V = 3) (D : Subgroup (specialIsometry h)) [D.Normal]
    (z : specialIsometry h) (hz : orderOf z = 2) (t : specialIsometry h ⧸ D)
    (hzt : QuotientGroup.mk' D z = t) :
    (unitaryTargetQuotientCentralizer h h2 hsym hnd hsigma hne hdim D z hz t hzt).ker =
      (unitaryQuotientCentralizer h h2 hsym hnd hsigma hne hdim D z hz).ker :=
  MonoidHom.ker_comp_of_injective _ _ (unitaryTargetCentralizerEquiv h D z t hzt).injective

theorem unitaryTargetQuotientCentralizer_core_structure (p f : ℕ) [Fact p.Prime]
    (hpodd : Odd p) (hE : Nat.card E = (p ^ f) ^ 2)
    (h : V →ₛₗ[(CatalogueBUnitaryTwo.unitaryFieldConjugation p f hE).toRingHom] V →ₗ[E] E)
    (hsym : h.IsSymm) (hnd : h.Nondegenerate) (hdim : Module.finrank E V = 3)
    (D : Subgroup (specialIsometry h)) [D.Normal] (hD : D ≤ scalarCenter h hdim)
    (z : specialIsometry h) (hz : orderOf z = 2) (t : specialIsometry h ⧸ D)
    (hzt : QuotientGroup.mk' D z = t) :
    let h2 := unitaryField_two_ne_zero p f hpodd hE
    let hsigma := (CatalogueBUnitaryTwo.unitaryFieldConjugation_data p f hE).1
    let hne := (CatalogueBUnitaryTwo.unitaryFieldConjugation_data p f hE).2.1
    let P := minusSpace z.val.val.toLinearMap
    let phi := unitaryTargetQuotientCentralizer h h2 hsym hnd hsigma hne hdim D z hz t hzt
    let A := normOneUnits (sigma := CatalogueBUnitaryTwo.unitaryFieldConjugation p f hE)
    CFSG.oddCore (Subgroup.centralizer ({t} : Set (specialIsometry h ⧸ D))) =
        ((CyclicOddScalarQuotient.oddElements A).map
          (scalarIsometry (h.domRestrict₁₂ P P))).map phi ∧
      CFSG.oddCore (Subgroup.centralizer ({t} : Set (specialIsometry h ⧸ D))) ≤
        Subgroup.center (Subgroup.centralizer ({t} : Set (specialIsometry h ⧸ D))) ∧
      IsCyclic (CFSG.oddCore (Subgroup.centralizer ({t} : Set (specialIsometry h ⧸ D)))) ∧
      Nat.card (CFSG.oddCore (Subgroup.centralizer ({t} : Set (specialIsometry h ⧸ D)))) =
        ordCompl[2] (p ^ f + 1) / Nat.card D := by
  let h2 := unitaryField_two_ne_zero p f hpodd hE
  let hsigma := (CatalogueBUnitaryTwo.unitaryFieldConjugation_data p f hE).1
  let hne := (CatalogueBUnitaryTwo.unitaryFieldConjugation_data p f hE).2.1
  let P := minusSpace z.val.val.toLinearMap
  let hP := h.domRestrict₁₂ P P
  let phi := unitaryTargetQuotientCentralizer h h2 hsym hnd hsigma hne hdim D z hz t hzt
  have hPdim : Module.finrank E P = 2 := (involution_finrank h h2 hdim z hz).1
  have hPnd : hP.Nondegenerate := (involution_restrictions h h2 hsym hnd z hz).1
  let : Nontrivial P := Module.nontrivial_of_finrank_pos (R := E) (by rw [hPdim]; decide)
  let : Finite (isometryGroup h) := isometryGroup_finite h
  let : Finite (isometryGroup hP) := isometryGroup_finite hP
  have hk := unitaryTargetQuotientCentralizer_ker h h2 hsym hnd hsigma hne hdim D z hz t hzt
  have hkerodd : Odd (Nat.card phi.ker) := by
    rw [hk, unitaryQuotientCentralizer_ker_card h h2 hsym hnd hsigma hne hdim D hD z hz]
    exact scalar_kernel_odd h hdim D hD
  have hc := CyclicOddScalarQuotient.quotient_oddCore_structure
    (scalarIsometry hP) (scalarIsometry_injective hP) (scalarIsometry_range_le_center hP)
    phi (unitaryTargetQuotientCentralizer_surjective
      h h2 hsym hnd hsigma hne hdim D hD z hz t hzt) hkerodd
    (by rw [hk]; exact unitaryQuotientKernel_le_scalars
          h h2 hsym hnd hsigma hne hdim D hD z hz)
    (unitaryPlane_normal_odd_scalar p f hpodd hE hP (hsym.domRestrict P) hPnd hPdim)
  refine ⟨hc.1, hc.2.1, hc.2.2.1, ?_⟩
  calc
    Nat.card (CFSG.oddCore (Subgroup.centralizer ({t} : Set (specialIsometry h ⧸ D)))) =
        ordCompl[2] (Nat.card (normOneUnits
          (sigma := CatalogueBUnitaryTwo.unitaryFieldConjugation p f hE))) /
            Nat.card phi.ker := hc.2.2.2
    _ = ordCompl[2] (p ^ f + 1) / Nat.card D := by
      rw [normOneUnits_card p f hE, hk,
        unitaryQuotientCentralizer_ker_card h h2 hsym hnd hsigma hne hdim D hD z hz]
end TargetCentralizer


section FullNode
open OddLinearThreeCentralizerCore
open scoped Nat
variable [Finite E] [FiniteDimensional E V]

set_option maxHeartbeats 1000000 in
theorem odd_unitary_three_involution_centralizer_core (p f : ℕ) [Fact p.Prime]
    (hpodd : Odd p) (hE : Nat.card E = (p ^ f) ^ 2)
    (h : V →ₛₗ[(CatalogueBUnitaryTwo.unitaryFieldConjugation p f hE).toRingHom] V →ₗ[E] E)
    (hsym : h.IsSymm) (hnd : h.Nondegenerate) (hdim : Module.finrank E V = 3)
    (D : Subgroup (specialIsometry h)) (hD : D ≤ scalarCenter h hdim) :
    letI : D.Normal := scalar_subgroup_normal h hdim D hD
    let h2 := unitaryField_two_ne_zero p f hpodd hE
    let hsigma := (CatalogueBUnitaryTwo.unitaryFieldConjugation_data p f hE).1
    let hne := (CatalogueBUnitaryTwo.unitaryFieldConjugation_data p f hE).2.1
    let A := normOneUnits (sigma := CatalogueBUnitaryTwo.unitaryFieldConjugation p f hE)
    ∀ t : specialIsometry h ⧸ D, orderOf t = 2 →
      ∃ (z : specialIsometry h) (hz : orderOf z = 2) (hzt : QuotientGroup.mk' D z = t),
        let P := minusSpace z.val.val.toLinearMap
        let Q := plusSpace z.val.val.toLinearMap
        let hP := h.domRestrict₁₂ P P
        let j := unitaryCentralizerEquiv h h2 hsym hnd hsigma hne hdim z hz
        let phi := unitaryTargetQuotientCentralizer h h2 hsym hnd hsigma hne hdim D z hz t hzt
        (∀ w : specialIsometry h, orderOf w = 2 → QuotientGroup.mk' D w = t → w = z) ∧
          Module.finrank E P = 2 ∧ Module.finrank E Q = 1 ∧
          hP.Nondegenerate ∧ (h.domRestrict₁₂ Q Q).Nondegenerate ∧
          (∀ x ∈ P, ∀ y ∈ Q, h x y = 0) ∧
          Function.Bijective j ∧
          (∀ a : isometryGroup hP,
            (∀ x : P, (j a).val.val.val x = (a.val x : V)) ∧
            (∀ y : Q, (j a).val.val.val y = ((a.val.det⁻¹ : Eˣ) : E) • (y : V))) ∧
          (∀ a : isometryGroup hP,
            (phi a : specialIsometry h ⧸ D) = QuotientGroup.mk' D (j a).val) ∧
          Function.Surjective phi ∧
          (∀ a : isometryGroup hP,
            a ∈ phi.ker ↔ ∃ c : cubicUnits
              (sigma := CatalogueBUnitaryTwo.unitaryFieldConjugation p f hE),
              scalarSpecial h hdim c ∈ D ∧ a = scalarIsometry hP c.val) ∧
          Nat.card phi.ker = Nat.card D ∧
          CFSG.oddCore (Subgroup.centralizer ({t} : Set (specialIsometry h ⧸ D))) =
            ((CyclicOddScalarQuotient.oddElements A).map (scalarIsometry hP)).map phi ∧
          CFSG.oddCore (Subgroup.centralizer ({t} : Set (specialIsometry h ⧸ D))) ≤
            Subgroup.center (Subgroup.centralizer ({t} : Set (specialIsometry h ⧸ D))) ∧
          IsCyclic (CFSG.oddCore (Subgroup.centralizer ({t} : Set (specialIsometry h ⧸ D)))) ∧
          Nat.card (CFSG.oddCore (Subgroup.centralizer ({t} : Set (specialIsometry h ⧸ D)))) =
            ordCompl[2] (p ^ f + 1) / Nat.card D := by
  let : D.Normal := scalar_subgroup_normal h hdim D hD
  let h2 := unitaryField_two_ne_zero p f hpodd hE
  let hsigma := (CatalogueBUnitaryTwo.unitaryFieldConjugation_data p f hE).1
  let hne := (CatalogueBUnitaryTwo.unitaryFieldConjugation_data p f hE).2.1
  dsimp only
  intro t ht
  obtain ⟨z, ⟨hz, hzt⟩, huniq⟩ := unique_involution_lift h hdim D hD t ht
  obtain ⟨hm, hp⟩ := involution_finrank h h2 hdim z hz
  obtain ⟨hPnd, hQnd, horth⟩ := involution_restrictions h h2 hsym hnd z hz
  obtain ⟨hcore, hcenter, hcyclic, horder⟩ :=
    unitaryTargetQuotientCentralizer_core_structure p f hpodd hE h hsym hnd hdim D hD z hz t hzt
  refine ⟨z, hz, hzt, ?_, hm, hp, hPnd, hQnd, horth,
    (unitaryCentralizerEquiv h h2 hsym hnd hsigma hne hdim z hz).bijective, ?_,
    unitaryTargetQuotientCentralizer_coe h h2 hsym hnd hsigma hne hdim D z hz t hzt,
    unitaryTargetQuotientCentralizer_surjective h h2 hsym hnd hsigma hne hdim D hD z hz t hzt,
    ?_, ?_, hcore, hcenter, hcyclic, horder⟩
  · intro w hw hwt
    exact huniq w ⟨hw, hwt⟩
  · intro a
    exact ⟨unitaryCentralizerBlock_minus h h2 hsym hnd hsigma hne hdim z hz a,
      unitaryCentralizerBlock_plus h h2 hsym hnd hsigma hne hdim z hz a⟩
  · intro a
    rw [unitaryTargetQuotientCentralizer_ker]
    exact unitaryQuotientCentralizer_mem_ker_iff h2 hsym hnd hsigma hne hD hz
  · rw [unitaryTargetQuotientCentralizer_ker]
    exact unitaryQuotientCentralizer_ker_card h h2 hsym hnd hsigma hne hdim D hD z hz
end FullNode

end CFSG.Wreathed.OddUnitaryThreeCentralizerCore
