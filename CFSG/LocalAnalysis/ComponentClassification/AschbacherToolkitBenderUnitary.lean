module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderCount
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderUnitaryCoord
public import CFSG.StronglyEmbedded.BenderUnitaryBorel
import CFSG.Models.BenderSuzuki

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

namespace Bender

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI

theorem sylowCenter_le_commutator {X : Type*} [Group X] {T : Subgroup X}
    (h : Subgroup.center T ≤ commutator T) : sylowCenter T ≤ ⁅T, T⁆ := by
  intro g hg
  rw [← map_center_eq_sylowCenter] at hg
  obtain ⟨w, hw, rfl⟩ := hg
  have h2 : (commutator T).map T.subtype = ⁅T, T⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  rw [← h2]
  exact ⟨w, h hw, rfl⟩

theorem numeric (f : ℕ) (hf : 2 ≤ f) :
    2 * (2 ^ f) ^ 2 < ((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1) * 2 ^ f ∧
      (2 ^ f) ^ 3 < 4 * (((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1) * 2 ^ f) := by
  rcases (show f = 2 ∨ 3 ≤ f by omega) with hf2 | hf3
  · subst hf2
    norm_num
  obtain ⟨q, hq⟩ : ∃ q, q = 2 ^ f := ⟨_, rfl⟩
  rw [← hq]
  have hq8 : 8 ≤ q := by
    rw [hq]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
  set d := Nat.gcd 3 (q + 1) with hd
  set m := (q ^ 2 - 1) / d with hm
  have hdvd : d ∣ q ^ 2 - 1 := by
    rw [show q ^ 2 - 1 = (q + 1) * (q - 1) by simpa using Nat.sq_sub_sq q 1]
    exact dvd_mul_of_dvd_left (Nat.gcd_dvd_right 3 (q + 1)) _
  have hdm : d * m = q ^ 2 - 1 := Nat.mul_div_cancel' hdvd
  have hd3 : d ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 (q + 1))
  have h3m : q ^ 2 - 1 ≤ 3 * m := by
    rw [← hdm]
    exact Nat.mul_le_mul_right m hd3
  have hqq : q ^ 2 = q * q := sq q
  have hqqq : q ^ 3 = q * q * q := by ring
  have h8q : 8 * q ≤ q * q := Nat.mul_le_mul_right q hq8
  have hm2 : 2 * q + 1 ≤ m := by omega
  have hm4 : q * q + 1 ≤ 4 * m := by omega
  have e1 : (2 * q + 1) * q ≤ m * q := Nat.mul_le_mul_right q hm2
  have e2 : (q * q + 1) * q ≤ 4 * m * q := Nat.mul_le_mul_right q hm4
  have e3 : (2 * q + 1) * q = 2 * (q * q) + q := by ring
  have e4 : (q * q + 1) * q = q * q * q + q := by ring
  have e5 : 4 * m * q = 4 * (m * q) := by ring
  constructor
  · rw [hqq]
    omega
  · rw [hqqq]
    omega

theorem nestedAt_projectiveSpecialUnitary {K : Type*} [Field K] [Finite K] [CharP K 2]
    (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f) (hKcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    NestedAt (T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  classical
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite G := Finite.of_injective Subtype.val Subtype.coe_injective
  let U := hermitianUnipotentPSU J hJ
  have hU : Function.Injective U := CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ
  let S0 := unitaryCoverSylow J f hf hKcard hfixed hJ
  have hB := bender_projectiveSpecialUnitary_borel J f hf hKcard hfixed hJ
  obtain ⟨hSE, hZ2, -, hTcard⟩ := benderBorel_sylowCenter hB S0
  have hR2 : IsPGroup 2 (S0 : Subgroup G) := S0.isPGroup'
  apply nestedAt_of_one_sylow S0 _ T
  have hS0 : (S0 : Subgroup G) = U.range := unitaryCoverSylow_coe J f hf hKcard hfixed hJ
  rw [hS0] at hSE hZ2 hTcard hR2 ⊢
  have hcen0 : ∀ z : hermitianUnipotentCoord J, z.1.1 = 0 → U z ∈ sylowCenter U.range := by
    intro z hz
    refine mem_sylowCenter.mpr ⟨⟨z, rfl⟩, ?_⟩
    rintro _ ⟨w, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    rw [UnitaryCoord.mul_comm_iff, hz, map_zero, mul_zero, zero_mul]
  have hnoncen : ∀ z : hermitianUnipotentCoord J, U z ∉ sylowCenter U.range → z.1.1 ≠ 0 :=
    fun z hz h0 => hz (hcen0 z h0)
  have hZT : sylowCenter U.range ≤ ⁅U.range, U.range⁆ := by
    apply sylowCenter_le_commutator
    have h := (unitaryCoverRoot_nativeStructure J (2 ^ f) hKcard hfixed hJ).2.1
    exact h.symm.le
  have hcent : ∀ x ∈ U.range, x ∉ sylowCenter U.range →
      Nat.card (U.range ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) ≤ (2 ^ f) ^ 2 := by
    rintro _ ⟨z, rfl⟩ hxZ
    have hz := hnoncen z hxZ
    have hmap : U.range ⊓ Subgroup.centralizer ({U z} : Set G) =
        (Subgroup.centralizer ({z} : Set (hermitianUnipotentCoord J))).map U := by
      ext y
      constructor
      · rintro ⟨⟨w, rfl⟩, hy⟩
        refine ⟨w, ?_, rfl⟩
        have hy' : U w * U z = U z * U w := Subgroup.mem_centralizer_singleton_iff.mp hy
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        apply hU
        rw [map_mul, map_mul]
        exact hy'
      · rintro ⟨w, hw, rfl⟩
        refine ⟨⟨w, rfl⟩, ?_⟩
        have hw' : w * z = z * w := Subgroup.mem_centralizer_singleton_iff.mp hw
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        rw [← map_mul, ← map_mul, hw']
    rw [hmap, Subgroup.card_map_of_injective hU]
    exact UnitaryCoord.card_centralizer_le J (2 ^ f) hfixed z hz
  let Sc := unitaryCoverScalarImage J
  have hScard : Nat.card Sc = ((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1) :=
    unitaryCoverScalarImage_card J (2 ^ f) hKcard hfixed hJ
  let Z0 := (unitaryCoverFirstCoord J).ker
  have hZ0card : Nat.card Z0 = 2 ^ f := UnitaryCoord.card_firstCoord_ker J (2 ^ f) hfixed
  have horbit : ∀ x ∈ U.range, x ∉ sylowCenter U.range →
      Nat.card Sc * 2 ^ f ≤
        Set.ncard {y : G | ∃ n ∈ Subgroup.normalizer (U.range : Set G), y = n⁻¹ * x * n} := by
    rintro _ ⟨z, rfl⟩ hxZ
    have hz := hnoncen z hxZ
    have hks : ∀ s : Sc, ∃ k : Kˣ, unitaryCoverScalar J k = s := fun s => s.2
    choose ks hks using hks
    let ι : Sc × Z0 → G := fun p =>
      U (hermitianTorusAction J (ks p.1) z * (p.2 : hermitianUnipotentCoord J))
    have hι : Function.Injective ι := by
      rintro ⟨s, y⟩ ⟨s', y'⟩ h
      have h1 : hermitianTorusAction J (ks s) z * (y : hermitianUnipotentCoord J) =
          hermitianTorusAction J (ks s') z * (y' : hermitianUnipotentCoord J) := hU h
      have hy1 : (y : hermitianUnipotentCoord J).1.1 = 0 := y.2
      have hy1' : (y' : hermitianUnipotentCoord J).1.1 = 0 := y'.2
      have hfst := congrArg (fun v : hermitianUnipotentCoord J => v.1.1) h1
      change (hermitianTorusAction J (ks s) z).1.1 + (y : hermitianUnipotentCoord J).1.1 =
        (hermitianTorusAction J (ks s') z).1.1 + (y' : hermitianUnipotentCoord J).1.1 at hfst
      rw [hy1, hy1', add_zero, add_zero, UnitaryCoord.hermitianTorusAction_fst_eq,
        UnitaryCoord.hermitianTorusAction_fst_eq] at hfst
      have h2 : unitaryCoverScalar J (ks s) = unitaryCoverScalar J (ks s') :=
        Units.ext (mul_left_cancel₀ hz hfst)
      rw [hks, hks] at h2
      have hss : s = s' := Subtype.ext h2
      subst hss
      have hyy : y = y' := Subtype.ext (mul_left_cancel h1)
      rw [hyy]
    have hmem : ∀ p, ι p ∈
        {y : G | ∃ n ∈ Subgroup.normalizer (U.range : Set G), y = n⁻¹ * U z * n} := by
      rintro ⟨s, y⟩
      let v := hermitianTorusAction J (ks s) z
      have hv : v.1.1 ≠ 0 := by
        change (hermitianTorusAction J (ks s) z).1.1 ≠ 0
        rw [UnitaryCoord.hermitianTorusAction_fst_eq]
        exact mul_ne_zero hz (Units.ne_zero _)
      have hy1 : (y : hermitianUnipotentCoord J).1.1 = 0 := y.2
      have hvy : v.1.1 = (v * (y : hermitianUnipotentCoord J)).1.1 := by
        change v.1.1 = v.1.1 + (y : hermitianUnipotentCoord J).1.1
        rw [hy1, add_zero]
      obtain ⟨c, hc⟩ :=
        UnitaryCoord.exists_inv_mul_mul_eq J (2 ^ f) hKcard hfixed hJ v _ hvy hv
      let τ := hermitianTorusPSU J hJ (ks s)
      have hτ : τ ∈ Subgroup.normalizer (U.range : Set G) :=
        unitaryCoverTorus_le_normalizer J hJ ⟨ks s, rfl⟩
      have hconj : τ * U z * τ⁻¹ = U v := unitaryCoverTorus_conj_root J hJ (ks s) z
      refine ⟨τ⁻¹ * U c,
        Subgroup.mul_mem _ (Subgroup.inv_mem _ hτ) (Subgroup.le_normalizer ⟨c, rfl⟩), ?_⟩
      have hιv : ι (s, y) = U (v * (y : hermitianUnipotentCoord J)) := rfl
      calc ι (s, y) = U (c⁻¹ * v * c) := by rw [hιv, hc]
        _ = (U c)⁻¹ * (τ * U z * τ⁻¹) * U c := by rw [hconj, map_mul, map_mul, map_inv]
        _ = (τ⁻¹ * U c)⁻¹ * U z * (τ⁻¹ * U c) := by group
    calc Nat.card Sc * 2 ^ f = Nat.card (Sc × Z0) := by rw [Nat.card_prod, hZ0card]
      _ = (Set.range ι).ncard := (Set.ncard_range_of_injective hι).symm
      _ ≤ _ := Set.ncard_le_ncard (by rintro _ ⟨p, rfl⟩; exact hmem p) (Set.toFinite _)
  obtain ⟨hco, hoT⟩ := numeric f hf
  rw [← hScard] at hco hoT
  exact nestedAt_of_counting hSE hZ2 hZT hR2 hcent horbit hco (hTcard ▸ hoT)

theorem nestedAt_of_mulEquiv_psu3 {X : Type*} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (e : X ≃* PSU3 2 f) (T : Sylow 2 X) : NestedAt (T : Subgroup X) := by
  let k := GaloisField 2 f
  let K := FiniteField.Extension k 2 2
  let J := binaryQuadraticHermitian f (by omega)
  let : CharP K 2 := CharP.of_ringHom_of_ne_zero (algebraMap k K) 2 (by norm_num)
  have hKcard : Nat.card K = (2 ^ f) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 f (by omega)]
  have hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f :=
    quadraticBinaryFrobenius_fixed_card f (by omega)
  have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  let e₁ := (projectiveSpecialUnitary_equiv_PSU3Model J f hf hJ hKcard hfixed).some
  have hmodel : PSU3Model f = PSU3 2 f := CFSG.Models.benderPSU3Model_eq_psu3 f
  let e₂ : ProjectiveSpecialUnitaryMatrixGroup J ≃* PSU3 2 f :=
    e₁.trans (MulEquiv.subgroupCongr hmodel)
  let e₃ : X ≃* ProjectiveSpecialUnitaryMatrixGroup J := e.trans e₂.symm
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_surjective e₃ e₃.surjective
  exact nestedAt_of_mulEquiv e₃ (nestedAt_projectiveSpecialUnitary J f hf hKcard hfixed hJ) T

end Bender

end CFSG.ComponentClassification.AschbacherToolkit
