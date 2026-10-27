module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBUOrderThreeHermitianSplitting
public import CFSG.RankThree.PartTwo.Sec21.Item228Census2ProofU4Lin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentPlane
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentFix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentPos
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoBasic
public import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoBlocks
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate9130

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

open Module QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
  CFSG.LinearAlgebra CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.GorensteinLyons CFSG.LocalAnalysis.GorensteinLyons.OrderThreeSplitting
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC

open CFSG.LocalAnalysis.GorensteinLyons.OrderThreeHermitian (MovedSpace toV movedSpace
  unitaryFieldData_omegaField toV_injective toV_omega_smul)

section Restriction

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem finrank_omega_movedSpace {c : V ≃ₗ[ZMod 2] V} (hc3 : orderOf c = 3)
    {hc : c.toLinearMap ^ 3 = 1} (hdim : finrank (ZMod 2) V = 10)
    (hfix : finrank (ZMod 2) (fixedSpace c) = 2) :
    finrank OmegaField (MovedSpace c.toLinearMap hc) = 4 := by
  have h1 := Submodule.finrank_add_eq_of_isCompl (isCompl_fixed_moved hc)
  have h2 : finrank (ZMod 2) (movedSpace c.toLinearMap) = 8 := by
    have : finrank (ZMod 2) (OrderThreeHermitian.fixedSpace c.toLinearMap) = 2 := hfix
    omega
  haveI : IsScalarTower (ZMod 2) OmegaField (MovedSpace c.toLinearMap hc) :=
    IsScalarTower.of_algebraMap_smul fun a x => OrderThreeHermitian.algebraMap_smul' a x
  have h3 := Module.finrank_mul_finrank (ZMod 2) OmegaField (MovedSpace c.toLinearMap hc)
  rw [finrank_omegaField] at h3
  change 2 * finrank OmegaField (MovedSpace c.toLinearMap hc) = finrank (ZMod 2) (movedSpace c.toLinearMap)
    at h3
  omega

theorem not_isScalar_of_not_mem_zpowers {c e : V ≃ₗ[ZMod 2] V} (hc3 : orderOf c = 3)
    {hc : c.toLinearMap ^ 3 = 1} (hefix : ∀ v ∈ fixedSpace c, e v = v)
    (hnot : e ∉ Subgroup.zpowers c)
    {eL : LinearMap.GeneralLinearGroup OmegaField (MovedSpace c.toLinearMap hc)}
    (heL : ∀ x, toV c.toLinearMap hc ((eL : Module.End OmegaField _) x) = e (toV c.toLinearMap hc x))
    (μ : OmegaField) :
    (eL : Module.End OmegaField (MovedSpace c.toLinearMap hc)) ≠ μ • 1 := by
  intro hμ
  apply hnot
  have hex : ∀ x, e (toV c.toLinearMap hc x) = toV c.toLinearMap hc (μ • x) := fun x => by
    rw [← heL, hμ]
    rfl
  have hsup : OrderThreeHermitian.fixedSpace c.toLinearMap ⊔ movedSpace c.toLinearMap = ⊤ :=
    (isCompl_fixed_moved hc).sup_eq_top
  have key : ∃ i : ℕ, ∀ w ∈ movedSpace c.toLinearMap, e w = (c ^ i) w := by
    by_cases hμ0 : μ = 0
    · refine ⟨0, fun w hw => ?_⟩
      obtain ⟨x, hx⟩ : ∃ x : MovedSpace c.toLinearMap hc, toV c.toLinearMap hc x = w := ⟨⟨w, hw⟩, rfl⟩
      have h1 := hex x
      rw [hx, hμ0, zero_smul, map_zero] at h1
      have h2 : w = 0 := e.injective (by rw [map_zero]; exact h1)
      rw [h2, map_zero, map_zero]
    · rcases OrderThreeHermitian.eq_one_or_omega μ hμ0 with h | h | h
      · refine ⟨0, fun w hw => ?_⟩
        obtain ⟨x, hx⟩ : ∃ x : MovedSpace c.toLinearMap hc, toV c.toLinearMap hc x = w :=
          ⟨⟨w, hw⟩, rfl⟩
        have h1 := hex x
        rw [hx, h, one_smul, hx] at h1
        exact h1
      · refine ⟨1, fun w hw => ?_⟩
        obtain ⟨x, hx⟩ : ∃ x : MovedSpace c.toLinearMap hc, toV c.toLinearMap hc x = w :=
          ⟨⟨w, hw⟩, rfl⟩
        have h1 := hex x
        rw [hx, h, toV_omega_smul, hx] at h1
        exact h1
      · refine ⟨2, fun w hw => ?_⟩
        obtain ⟨x, hx⟩ : ∃ x : MovedSpace c.toLinearMap hc, toV c.toLinearMap hc x = w :=
          ⟨⟨w, hw⟩, rfl⟩
        have h1 := hex x
        rw [hx, h, OrderThreeSplitting.toV_omega_sq_smul, hx] at h1
        rw [pow_two, LinearEquiv.mul_apply]
        exact h1
  obtain ⟨i, hi⟩ := key
  refine Subgroup.mem_zpowers_iff.2 ⟨i, LinearEquiv.ext fun v => ?_⟩
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : v ∈ _)
  have hu' : c u = u := (OrderThreeSplitting.mem_fixedSpace_iff (c := c.toLinearMap)).1 hu
  rw [map_add, map_add, hefix u hu, hi w hw, zpow_natCast, pow_apply_eq_of_apply_eq hu' i]

private theorem omega_pow_five_eq_one (μ : OmegaField) (hμ : μ ^ 5 = 1) : μ = 1 := by
  have h2 : (2 : OmegaField) = 0 := omegaField_two_eq_zero
  have hsq : CFSG.LinearAlgebra.omega ^ 2 = CFSG.LinearAlgebra.omega + 1 := omega_sq
  have hω3 : CFSG.LinearAlgebra.omega ^ 3 = 1 := by
    linear_combination (CFSG.LinearAlgebra.omega + 1) * hsq + CFSG.LinearAlgebra.omega * h2
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    norm_num at hμ
  rcases OrderThreeHermitian.eq_one_or_omega μ hμ0 with h | h | h
  · exact h
  · exfalso
    rw [h] at hμ
    have h5' : CFSG.LinearAlgebra.omega ^ 2 = 1 := by
      linear_combination hμ - CFSG.LinearAlgebra.omega ^ 2 * hω3
    exact OrderThreeHermitian.omega_ne_zero (by linear_combination h5' - hsq)
  · exfalso
    rw [h] at hμ
    exact OrderThreeHermitian.omega_ne_one
      (by linear_combination hμ - CFSG.LinearAlgebra.omega *
        (CFSG.LinearAlgebra.omega ^ 6 + CFSG.LinearAlgebra.omega ^ 3 + 1) * hω3)

private theorem eq_one_of_pow_five_of_commute_nonscalar {W : Type} [AddCommGroup W]
    [Module OmegaField W] [FiniteDimensional OmegaField W] (hW : finrank OmegaField W = 4)
    {B : W →ₛₗ[unitaryFieldData_omegaField.bar] W →ₗ[OmegaField] OmegaField} (hBs : B.IsSymm)
    (hBl : B.SeparatingLeft) {a b : LinearMap.GeneralLinearGroup OmegaField W}
    (ha : a ∈ sesqUnitaryGroup B) (hb : b ∈ sesqUnitaryGroup B) (hab : a * b = b * a)
    (ha3 : a ^ 3 = 1) (hasc : ∀ μ : OmegaField, (a : Module.End OmegaField W) ≠ μ • 1)
    (hbr : b ^ 5 = 1) : b = 1 := by
  classical
  by_contra hb1
  haveI : CharP OmegaField 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) OmegaField).injective 2
  have h2 : (2 : OmegaField) = 0 := omegaField_two_eq_zero
  have hsq : CFSG.LinearAlgebra.omega ^ 2 = CFSG.LinearAlgebra.omega + 1 := omega_sq
  have hω : CFSG.LinearAlgebra.omega ^ 2 + CFSG.LinearAlgebra.omega + 1 = 0 := by
    linear_combination hsq + (CFSG.LinearAlgebra.omega + 1) * h2
  have hnd : ∀ x, (∀ y, B y x = 0) → x = 0 := fun x hx => hBl x fun y => by
    have h := hBs.eq x y
    rw [hx y] at h
    exact (map_eq_zero _).1 h
  have hbr5 : ((b : LinearMap.GeneralLinearGroup OmegaField W) : Module.End OmegaField W) ^ 5 = 1 := by
    have := congrArg Units.val hbr
    simpa using this
  have ha3' : ((a : LinearMap.GeneralLinearGroup OmegaField W) : Module.End OmegaField W) ^ 3 = 1 := by
    have := congrArg Units.val ha3
    simpa using this
  exact CFSG.RankThree.PartTwo.Sec21.Item228Census2Proof.no_commuting_unitary_three_five B hW
    (q := 2) (fun x => by rw [UnitaryFieldData.bar_apply, pow_one]) (Or.inl rfl)
    omega_pow_five_eq_one hω hnd
    (fun x y => mem_sesqUnitaryGroup.1 ha x y) (fun x y => mem_sesqUnitaryGroup.1 hb x y)
    (congrArg Units.val hab) ha3' hasc hbr5 (fun h => hb1 (Units.ext h))

private theorem card_sesqUnitaryGroup {W : Type} [AddCommGroup W] [Module OmegaField W]
    [FiniteDimensional OmegaField W] (hW : finrank OmegaField W = 4)
    {B : W →ₛₗ[unitaryFieldData_omegaField.bar] W →ₗ[OmegaField] OmegaField} (hBs : B.IsSymm)
    (hBl : B.SeparatingLeft) : Nat.card ↥(sesqUnitaryGroup B) = 77760 := by
  haveI : Finite OmegaField := unitaryFieldData_omegaField.finite
  haveI : Finite W := Module.finite_of_finite OmegaField
  have hcard := (CFSG.LinearGroups.unitary_full_group_order unitaryFieldData_omegaField hBs hBl hW
    (by norm_num)).1
  have h : ((Nat.card ↥(sesqUnitaryGroup B) : ℕ) : ℤ) = 77760 := by
    rw [hcard]
    decide
  exact_mod_cast h

private theorem le_five_of_prime_dvd_77760 {r : ℕ} (hr : r.Prime) (hdvd : r ∣ 77760) : r ≤ 5 := by
  have h77 : (77760 : ℕ) = 2 ^ 6 * 3 ^ 5 * 5 := by norm_num
  rw [h77] at hdvd
  rcases (Nat.Prime.dvd_mul hr).1 hdvd with h | h
  · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
    · have := Nat.le_of_dvd (by norm_num) (hr.dvd_of_dvd_pow h)
      omega
    · have := Nat.le_of_dvd (by norm_num) (hr.dvd_of_dvd_pow h)
      omega
  · exact Nat.le_of_dvd (by norm_num) h

theorem eq_one_of_pow_eq_one_of_commute_nonscalar {W : Type} [AddCommGroup W] [Module OmegaField W]
    [FiniteDimensional OmegaField W] (hW : finrank OmegaField W = 4)
    {B : W →ₛₗ[unitaryFieldData_omegaField.bar] W →ₗ[OmegaField] OmegaField} (hBs : B.IsSymm)
    (hBl : B.SeparatingLeft) {a b : LinearMap.GeneralLinearGroup OmegaField W}
    (ha : a ∈ sesqUnitaryGroup B) (hb : b ∈ sesqUnitaryGroup B) (hab : a * b = b * a)
    (ha3 : a ^ 3 = 1) (hasc : ∀ μ : OmegaField, (a : Module.End OmegaField W) ≠ μ • 1) {r : ℕ}
    (hr : r.Prime) (hr5 : 5 ≤ r) (hbr : b ^ r = 1) : b = 1 := by
  classical
  by_contra hb1
  have hord : orderOf b = r :=
    ((Nat.dvd_prime hr).1 (orderOf_dvd_of_pow_eq_one hbr)).resolve_left fun h =>
      hb1 (orderOf_eq_one_iff.1 h)
  by_cases hr5' : r = 5
  · subst hr5'
    exact hb1 (eq_one_of_pow_five_of_commute_nonscalar hW hBs hBl ha hb hab ha3 hasc hbr)
  · have hdvd : r ∣ Nat.card ↥(sesqUnitaryGroup B) := by
      have := orderOf_dvd_natCard (⟨b, hb⟩ : ↥(sesqUnitaryGroup B))
      rwa [Subgroup.orderOf_mk, hord] at this
    rw [card_sesqUnitaryGroup hW hBs hBl] at hdvd
    exact hr5' (le_antisymm (le_five_of_prime_dvd_77760 hr hdvd) hr5)

theorem exists_unitary_restrict {c : V ≃ₗ[ZMod 2] V} (hc3 : orderOf c = 3) {hc : c.toLinearMap ^ 3 = 1}
    (hq : ∀ v, Q (c.toLinearMap v) = Q v) {x : V ≃ₗ[ZMod 2] V}
    (hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hxc : x * c = c * x) :
    ∃ xL : LinearMap.GeneralLinearGroup OmegaField (MovedSpace c.toLinearMap hc),
      xL ∈ sesqUnitaryGroup (hermForm Q c.toLinearMap hc hq) ∧
        ∀ w, toV c.toLinearMap hc ((xL : Module.End OmegaField _) w) = x (toV c.toLinearMap hc w) := by
  have hnorm : x ∈ Subgroup.normalizer (Subgroup.zpowers c : Set (V ≃ₗ[ZMod 2] V)) := by
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    rintro h ⟨k, rfl⟩
    exact (Commute.zpow_right (show Commute x c from hxc) k).eq.symm
  obtain ⟨-, -, gW, hgW, -, hgL, -⟩ := restrict_normalizer hc3 hc hq
    (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hxO) hnorm
  obtain ⟨-, xL, hxL, hxU⟩ := hgL (by rw [hxc, mul_inv_cancel_right])
  exact ⟨xL, hxU, fun w => by rw [hxL, hgW]⟩

theorem toV_pow_apply {c : V ≃ₗ[ZMod 2] V} {hc : c.toLinearMap ^ 3 = 1} {x : V ≃ₗ[ZMod 2] V}
    {xL : LinearMap.GeneralLinearGroup OmegaField (MovedSpace c.toLinearMap hc)}
    (hx : ∀ w, toV c.toLinearMap hc ((xL : Module.End OmegaField _) w) = x (toV c.toLinearMap hc w))
    (k : ℕ) (w : MovedSpace c.toLinearMap hc) :
    toV c.toLinearMap hc (((xL ^ k : LinearMap.GeneralLinearGroup OmegaField _) :
      Module.End OmegaField _) w) = (x ^ k) (toV c.toLinearMap hc w) := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, Units.val_mul, Module.End.mul_apply, ih, hx, pow_succ, LinearEquiv.mul_apply]

theorem pow_eq_one_of_restrict {c : V ≃ₗ[ZMod 2] V} {hc : c.toLinearMap ^ 3 = 1} {x : V ≃ₗ[ZMod 2] V}
    {xL : LinearMap.GeneralLinearGroup OmegaField (MovedSpace c.toLinearMap hc)}
    (hx : ∀ w, toV c.toLinearMap hc ((xL : Module.End OmegaField _) w) = x (toV c.toLinearMap hc w))
    {k : ℕ} (hk : x ^ k = 1) : xL ^ k = 1 := by
  refine Units.ext (LinearMap.ext fun w => toV_injective ?_)
  rw [toV_pow_apply hx k w, hk]
  rfl

private theorem eq_one_of_fixes_fixed_moved {c g : V ≃ₗ[ZMod 2] V} {hc : c.toLinearMap ^ 3 = 1}
    (hfix : ∀ v ∈ fixedSpace c, g v = v)
    (hmov : ∀ v ∈ movedSpace c.toLinearMap, g v = v) : g = 1 := by
  refine LinearEquiv.ext fun v => ?_
  have hsup : OrderThreeHermitian.fixedSpace c.toLinearMap ⊔ movedSpace c.toLinearMap = ⊤ :=
    (isCompl_fixed_moved hc).sup_eq_top
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : v ∈ _)
  rw [map_add, hfix u hu, hmov w hw]
  rfl

private theorem fixes_movedSpace_of_commute (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : finrank (ZMod 2) V = 10) {c e g : V ≃ₗ[ZMod 2] V}
    (hcO : c ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hc3 : orderOf c = 3)
    (hcfix : finrank (ZMod 2) (fixedSpace c) = 2)
    (heO : e ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hec : e * c = c * e) (hgc : g * c = c * g)
    (hge : g * e = e * g) (he3 : e ^ 3 = 1) (hefix : ∀ v ∈ fixedSpace c, e v = v)
    (hnot : e ∉ Subgroup.zpowers c) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hgr : g ^ r = 1) :
    ∀ v ∈ movedSpace c.toLinearMap, g v = v := by
  have hc3' : c.toLinearMap ^ 3 = 1 := by
    have h := pow_orderOf_eq_one c
    rw [hc3] at h
    have := congrArg LinearEquiv.automorphismGroup.toLinearMapMonoidHom h
    rwa [map_pow, map_one] at this
  have hq : ∀ v, Q (c.toLinearMap v) = Q v := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hcO
  obtain ⟨eL, heU, heL⟩ := exists_unitary_restrict (hc := hc3') hc3 hq heO hec
  obtain ⟨gL, hgU, hgL⟩ := exists_unitary_restrict (hc := hc3') hc3 hq hgO hgc
  have hW := finrank_omega_movedSpace (hc := hc3') hc3 hdim hcfix
  haveI : FiniteDimensional OmegaField (MovedSpace c.toLinearMap hc3') :=
    Module.finite_of_finrank_pos (by rw [hW]; norm_num)
  have hBs := hermForm_isSymm (c := c) (hc := hc3') hq
  have hBl := hermForm_separatingLeft (c := c.toLinearMap) (hc := hc3') hQ hq
  have hcomm : eL * gL = gL * eL := by
    refine Units.ext (LinearMap.ext fun w => toV_injective ?_)
    rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, heL, hgL, hgL, heL]
    exact (DFunLike.congr_fun hge _).symm
  have hgLr : gL ^ r = 1 := pow_eq_one_of_restrict hgL hgr
  have heL3 : eL ^ 3 = 1 := pow_eq_one_of_restrict heL he3
  have hgL1 : gL = 1 :=
    eq_one_of_pow_eq_one_of_commute_nonscalar hW hBs hBl heU hgU hcomm heL3
      (fun μ => not_isScalar_of_not_mem_zpowers hc3 hefix hnot heL μ) hr hr5 hgLr
  intro v hv
  have := hgL ⟨v, hv⟩
  rw [hgL1] at this
  exact this.symm

theorem eq_one_of_pow_eq_one_of_commute_two (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : finrank (ZMod 2) V = 10) {c e g : V ≃ₗ[ZMod 2] V}
    (hcO : c ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hc3 : orderOf c = 3)
    (hcfix : finrank (ZMod 2) (fixedSpace c) = 2)
    (heO : e ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hec : e * c = c * e) (hgc : g * c = c * g)
    (hge : g * e = e * g) (he3 : e ^ 3 = 1) (hefix : ∀ v ∈ fixedSpace c, e v = v)
    (hnot : e ∉ Subgroup.zpowers c) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hgr : g ^ r = 1) :
    g = 1 := by
  have hc3' : c.toLinearMap ^ 3 = 1 := by
    have h := pow_orderOf_eq_one c
    rw [hc3] at h
    have := congrArg LinearEquiv.automorphismGroup.toLinearMapMonoidHom h
    rwa [map_pow, map_one] at this
  refine eq_one_of_fixes_fixed_moved (c := c) (hc := hc3') ?_
    (fixes_movedSpace_of_commute hQ hdim hcO hc3 hcfix heO hgO hec hgc hge he3 hefix hnot hr hr5 hgr)
  have hgI : g ∈ isometryCentralizer Q c :=
    mem_isometryCentralizer.2 ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hgO,
      fun v => DFunLike.congr_fun hgc v⟩
  have hg₀r : (isometryRestrictFixed Q c ⟨g, hgI⟩) ^ r = 1 := by
    rw [← map_pow]
    have : (⟨g, hgI⟩ : ↥(isometryCentralizer Q c)) ^ r = 1 := Subtype.ext (by simpa using hgr)
    rw [this, map_one]
  have hg₀ := eq_one_of_pow_eq_one_of_finrank_two hcfix hr hr5 hg₀r
  intro u hu
  have := congrArg Subtype.val (DFunLike.congr_fun hg₀ (⟨u, hu⟩ : fixedSpace c))
  simpa [coe_isometryRestrictFixed] using this

end Restriction

section Burnside

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

private theorem fixes_fixedSpace_of_mem_torus {l : List (V × V)} (hl : IsFrame Q l)
    {d e : V ≃ₗ[ZMod 2] V} (hdt : d ∈ torus Q l) (hfull : ∀ p ∈ l, d p.1 ≠ p.1)
    (het : e ∈ torus Q l) : ∀ v ∈ fixedSpace d, e v = v := by
  intro v hv
  rw [fixedSpace_eq_perpL hl hdt hfull] at hv
  have hx' : ∀ p ∈ l, polar Q v p.1 = 0 ∧ polar Q v p.2 = 0 := fun p hp => by
    have := (mem_perpL_iff l v).1 hv p hp
    rw [polar_comm Q v p.1, polar_comm Q v p.2]
    exact this
  exact torus_fixes hl hx' _ het

private theorem eq_one_of_prime_order_of_mem_centralizer (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : finrank (ZMod 2) V = 10) {Bb : Subgroup ↥(orthDerived Q)} {l : List (V × V)}
    (hF : FrameOf Q Bb 4 l) {d e g : ↥(orthDerived Q)} (hd : d ∈ Bb) (he : e ∈ Bb)
    (hfull : ∀ p ∈ l, (d : V ≃ₗ[ZMod 2] V) p.1 ≠ p.1) (hed : e ∉ Subgroup.zpowers d)
    (hgd : d * g = g * d) (hge : e * g = g * e) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hgr : ((g : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) ^ r = 1) : g = 1 := by
  have hl := hF.isFrame
  have hdt : (d : V ≃ₗ[ZMod 2] V) ∈ torus Q l := hF.mem_torus hd
  have het : (e : V ≃ₗ[ZMod 2] V) ∈ torus Q l := hF.mem_torus he
  obtain ⟨p₀, hp₀⟩ : ∃ p₀, p₀ ∈ l := by
    have hne : l ≠ [] := by
      intro h
      have := hF.length_eq
      rw [h] at this
      simp at this
    exact List.exists_mem_of_ne_nil l hne
  have hd1 : (d : V ≃ₗ[ZMod 2] V) ≠ 1 := fun h => hfull p₀ hp₀ (by rw [h]; rfl)
  have hd3 : orderOf (d : V ≃ₗ[ZMod 2] V) = 3 := orderOf_eq_prime (torus_pow_three hl _ hdt) hd1
  have hfs : fixedSpace (d : V ≃ₗ[ZMod 2] V) = perpL Q l := fixedSpace_eq_perpL hl hdt hfull
  have hcfix : finrank (ZMod 2) (fixedSpace (d : V ≃ₗ[ZMod 2] V)) = 2 := by
    rw [hfs]
    exact finrank_perpL_eq_two hl (n := 5) (by omega) (by rw [hF.length_eq]) (by norm_num)
  have hefix := fixes_fixedSpace_of_mem_torus hl hdt hfull het
  have hnot : (e : V ≃ₗ[ZMod 2] V) ∉ Subgroup.zpowers (d : V ≃ₗ[ZMod 2] V) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    exact hed (Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩)
  have h1 := eq_one_of_pow_eq_one_of_commute_two hQ hdim
    (orthDerived_le_orthogonalGroup d.2) hd3 hcfix (orthDerived_le_orthogonalGroup e.2)
    (orthDerived_le_orthogonalGroup g.2)
    (torus_commute hl het hdt).eq (congrArg Subtype.val hgd).symm
    (congrArg Subtype.val hge).symm (torus_pow_three hl _ het) hefix hnot hr hr5 hgr
  exact Subtype.ext h1

theorem isSolvable_centralizer_pair_of_fullSupport (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : finrank (ZMod 2) V = 10) {Bb : Subgroup ↥(orthDerived Q)} {l : List (V × V)}
    (hF : FrameOf Q Bb 4 l) {d e : ↥(orthDerived Q)} (hd : d ∈ Bb) (he : e ∈ Bb)
    (hfull : ∀ p ∈ l, (d : V ≃ₗ[ZMod 2] V) p.1 ≠ p.1) (hed : e ∉ Subgroup.zpowers d) :
    Group.IsSolvable ↥(Subgroup.centralizer ({d, e} : Set ↥(orthDerived Q))) := by
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  haveI : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.ComponentClassification.Burgoyne.C.isSolvable_of_prime_dvd_two_three fun r hr hdvd => ?_
  by_contra hne
  have hr5 : 5 ≤ r := by
    have h2 := hr.two_le
    have h4 : r ≠ 4 := by
      rintro rfl
      exact absurd hr (by norm_num)
    omega
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' r hdvd
  have hgd : (d : ↥(orthDerived Q)) * (g : ↥(orthDerived Q)) = (g : ↥(orthDerived Q)) * d :=
    Subgroup.mem_centralizer_iff.1 g.2 d (by simp)
  have hge : (e : ↥(orthDerived Q)) * (g : ↥(orthDerived Q)) = (g : ↥(orthDerived Q)) * e :=
    Subgroup.mem_centralizer_iff.1 g.2 e (by simp)
  have hgr : ((g : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V) ^ r = 1 := by
    have := pow_orderOf_eq_one g
    rw [hg] at this
    exact congrArg (fun x : ↥(Subgroup.centralizer ({d, e} : Set ↥(orthDerived Q))) =>
      ((x : ↥(orthDerived Q)) : V ≃ₗ[ZMod 2] V)) this
  have hg1 : g = 1 :=
    Subtype.ext (eq_one_of_prime_order_of_mem_centralizer hQ hdim hF hd he hfull hed hgd hge hr hr5 hgr)
  rw [hg1, orderOf_one] at hg
  exact hr.one_lt.ne hg

end Burnside

end CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

end
