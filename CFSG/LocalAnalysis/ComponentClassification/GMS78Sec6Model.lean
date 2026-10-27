module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitarySublineTorusCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutUnitaryModel

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.ShultStronglyClosedTI
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism CFSG.ShultStronglyClosedTI.TwoCoreGrowth
open CFSG.ComponentClassification.AschbacherToolkit.Bender
open CFSG.ComponentClassification.AschbacherToolkit.Bender.UnitaryAut
open Matrix

theorem centralizer_map_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (A : Subgroup G) :
    centralizer ((A.map e.toMonoidHom : Subgroup H) : Set H) =
      (centralizer (A : Set G)).map e.toMonoidHom := by
  ext x
  constructor
  · intro hx
    refine ⟨e.symm x, mem_centralizer_iff.mpr fun a ha => e.injective ?_, by simp⟩
    have := (mem_centralizer_iff.mp hx) (e a) ⟨a, ha, rfl⟩
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact this
  · rintro ⟨g, hg, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, (mem_centralizer_iff.mp hg) a ha]

variable {K : Type} [Field K] (J : HermitianForm 3 K) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

instance u3_scalarCenter_normal : (scalarCenter J).Normal :=
  ⟨fun n hn g => by
    have hc := (mem_center_iff.mp (scalarCenter_le_center J hn)) g
    have e : g * n * g⁻¹ = n := by rw [hc, mul_inv_cancel_right]
    rw [e]
    exact hn⟩

theorem u3_coverToPSU_injective :
    Function.Injective (coverToPSU J (scalarCenter J) hJ le_rfl) := by
  intro x y h
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective y
  rw [coverToPSU_mk, coverToPSU_mk] at h
  rw [QuotientGroup.eq, scalarCenter_eq_ker J hJ, MonoidHom.mem_ker, map_mul, map_inv, h,
    inv_mul_cancel]

@[expose] noncomputable def u3CoverEquiv :
    J.specialSubgroup ⧸ scalarCenter J ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
  MulEquiv.ofBijective (coverToPSU J (scalarCenter J) hJ le_rfl)
    ⟨u3_coverToPSU_injective J hJ, coverToPSU_surjective hJ le_rfl⟩

@[expose] noncomputable def u3TorusK : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (torusL J (scalarCenter J) hJ).map (u3CoverEquiv J hJ).toMonoidHom

theorem mem_u3TorusK {x : ProjectiveSpecialUnitaryMatrixGroup J} :
    x ∈ u3TorusK J hJ ↔ ∃ c : normOne J, psuMk J (torusHom J hJ c) = x := by
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, ⟨c, rfl⟩, rfl⟩

theorem u3_psuMk_torusHom (c : normOne J) :
    psuMk J (torusHom J hJ c) = hermitianTorusPSU J hJ (c : Kˣ) := by
  have hc : J.conj ((c : Kˣ) : K) = ((c : Kˣ) : K)⁻¹ := conj_eq_inv_of_mem_normOne J c.2
  apply Subtype.ext
  rw [coe_psuMk, hermitianTorusPSU_val]
  congr 1
  rw [coe_torusHom]
  apply Units.ext
  rw [coe_diag3, hermitianTorusGL_val, hermitianTorusMatrix_eq, hc, inv_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sq]

theorem u3_torusK_le_torus : u3TorusK J hJ ≤ unitaryCoverTorus J hJ := by
  intro x hx
  obtain ⟨c, rfl⟩ := (mem_u3TorusK J hJ).mp hx
  rw [u3_psuMk_torusHom]
  exact ⟨_, rfl⟩

theorem u3_torusK_le_normalizer :
    u3TorusK J hJ ≤ normalizer ((unitaryCoverRoot J hJ : Subgroup _) : Set _) :=
  (u3_torusK_le_torus J hJ).trans (unitaryCoverTorus_le_normalizer J hJ)

theorem u3_torusAction_eq {k : Kˣ} (hk : (k : K) * J.conj k = 1) {z : hermitianUnipotentCoord J}
    (hz : z.1.1 = 0) : hermitianTorusAction J k z = z := by
  have hk0 : (k : K) ≠ 0 := k.ne_zero
  have hc : (J.conj (k : K))⁻¹ * (k : K)⁻¹ = 1 := by
    rw [← mul_inv, mul_comm, hk, inv_one]
  apply Subtype.ext
  apply Prod.ext
  · rw [hermitianTorusAction_fst, hz, zero_mul, zero_mul]
  · rw [hermitianTorusAction_snd, mul_assoc, hc, mul_one]

theorem u3_mem_torusK_of_commute [CharP K 2] {k : Kˣ}
    (hk : hermitianTorusPSU J hJ k * hermitianUnipotentPSU J hJ
      ⟨(0, 1), by simp [CharTwo.add_self_eq_zero]⟩ =
      hermitianUnipotentPSU J hJ ⟨(0, 1), by simp [CharTwo.add_self_eq_zero]⟩ *
        hermitianTorusPSU J hJ k) :
    hermitianTorusPSU J hJ k ∈ u3TorusK J hJ := by
  rw [hermitianTorusPSU_mul_unipotent] at hk
  have h := CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ (mul_right_cancel hk)
  have h2 := congrArg (fun z : hermitianUnipotentCoord J => z.1.2) h
  simp only [hermitianTorusAction_snd, one_mul] at h2
  have hk0 : (k : K) ≠ 0 := k.ne_zero
  have hc0 : J.conj (k : K) ≠ 0 := (map_ne_zero J.conj).2 hk0
  have hn : (k : K) * J.conj k = 1 := by
    field_simp at h2
    rw [mul_comm]
    exact h2.symm
  rw [mem_u3TorusK]
  exact ⟨⟨k, hn⟩, u3_psuMk_torusHom J hJ ⟨k, hn⟩⟩

section Finite

variable [Finite K] [CharP K 2] {f : ℕ} (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
  (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
include hf hcard hfixed

theorem u3_torusK_le_centralizer :
    u3TorusK J hJ ≤ centralizer ((sylowCenter (unitaryCoverRoot J hJ) : Subgroup _) : Set _) := by
  have hq : 2 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right two_pos hf)
  intro x hx
  obtain ⟨c, rfl⟩ := (mem_u3TorusK J hJ).mp hx
  rw [u3_psuMk_torusHom, mem_centralizer_iff]
  intro y hy
  obtain ⟨z, rfl⟩ := (mem_sylowCenter.mp hy).1
  have hz : z.1.1 = 0 := (mem_sylowCenter_root J (2 ^ f) hcard hfixed hq hJ z).mp hy
  have h := hermitianTorusPSU_mul_unipotent J hJ (c : Kˣ) z
  rw [u3_torusAction_eq J c.2 hz] at h
  exact h.symm

theorem u3_exists_eq_mul_of_mem_normalizer {g : ProjectiveSpecialUnitaryMatrixGroup J}
    (hg : g ∈ normalizer ((unitaryCoverRoot J hJ : Subgroup _) : Set _))
    (hgc : g ∈ centralizer ((sylowCenter (unitaryCoverRoot J hJ) : Subgroup _) : Set _)) :
    ∃ r ∈ unitaryCoverRoot J hJ, ∃ a ∈ u3TorusK J hJ, g = r * a := by
  obtain ⟨r, hr, h, ⟨k, rfl⟩, rfl⟩ := (normalizer_and_card_sylow J f hf hcard hfixed hJ).1 g hg
  refine ⟨r, hr, _, u3_mem_torusK_of_commute J hJ ?_, rfl⟩
  set z : hermitianUnipotentCoord J := ⟨(0, 1), by simp [CharTwo.add_self_eq_zero]⟩ with hzdef
  have hz : hermitianUnipotentPSU J hJ z ∈ sylowCenter (unitaryCoverRoot J hJ) :=
    mem_sylowCenter_root_of_fst J hJ rfl
  have hrz : r * hermitianUnipotentPSU J hJ z = hermitianUnipotentPSU J hJ z * r :=
    (mem_sylowCenter.mp hz).2 r hr
  have hgz := (mem_centralizer_iff.mp hgc) _ hz
  set u := hermitianUnipotentPSU J hJ z
  set t := hermitianTorusPSU J hJ k
  calc t * u = r⁻¹ * (u * (r * t)) := by
        rw [hgz]
        calc t * u = r⁻¹ * (r * t * u) := by group
          _ = r⁻¹ * (r * t * u) := rfl
    _ = r⁻¹ * (u * r * t) := by group
    _ = r⁻¹ * (r * u * t) := by rw [hrz]
    _ = u * t := by group

omit [CharP K 2] in
theorem u3_odd_card_torusK : Odd (Nat.card (u3TorusK J hJ)) := by
  have hq : 2 < 2 ^ f := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right two_pos hf)
  have h1 := card_torusL_mul_card hJ (le_rfl : scalarCenter J ≤ scalarCenter J)
  rw [card_normOne (J := J) Nat.prime_two hq hcard hfixed] at h1
  have h2 : Nat.card (u3TorusK J hJ) = Nat.card (torusL J (scalarCenter J) hJ) :=
    Subgroup.card_map_of_injective (u3CoverEquiv J hJ).injective
  have hodd : Odd (2 ^ f + 1) := (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  rw [h2]
  exact Odd.of_dvd_nat hodd ⟨_, h1.symm⟩

@[expose] noncomputable def u3SubLine : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (sublineL J (scalarCenter J) hJ).map (u3CoverEquiv J hJ).toMonoidHom

omit hf hcard hfixed in
noncomputable def u3SubLineEquiv :
    u3SubLine J hJ ≃* SpecialLinearGroup (Fin 2) (unitaryCoverFixedField J) :=
  ((sublineL J (scalarCenter J) hJ).equivMapOfInjective _
    (u3CoverEquiv J hJ).injective).symm.trans (sublineEquiv hJ le_rfl).symm

omit [Finite K] hf hcard hfixed in
theorem u3_commute_subLine_torusK {x y : ProjectiveSpecialUnitaryMatrixGroup J}
    (hx : x ∈ u3SubLine J hJ) (hy : y ∈ u3TorusK J hJ) : x * y = y * x := by
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  simp only [MulEquiv.coe_toMonoidHom]
  rw [← map_mul, ← map_mul, sublineL_commute_torusL hJ x' hx' y' hy']

omit [Finite K] hf hcard hfixed in
theorem u3_subLine_inf_torusK : u3SubLine J hJ ⊓ u3TorusK J hJ = ⊥ := by
  rw [u3SubLine, u3TorusK, ← Subgroup.map_inf_eq _ _ (u3CoverEquiv J hJ).toMonoidHom
    (u3CoverEquiv J hJ).injective,
    sublineL_inf_torusL hJ le_rfl, Subgroup.map_bot]

theorem u3_centralizer_torusK :
    centralizer ((u3TorusK J hJ : Subgroup _) : Set _) = u3SubLine J hJ ⊔ u3TorusK J hJ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, -, -, -, -, -, -, -, c, hc3, -⟩, -⟩ :=
    unitary_central_cover_subline_torus_centralizer J f hf hcard hfixed hJ (scalarCenter J) le_rfl
  have hcT : ((torusHom J hJ c : J.specialSubgroup) : J.specialSubgroup ⧸ scalarCenter J) ∈
      torusL J (scalarCenter J) hJ := ⟨c, rfl⟩
  have h := centralizer_eq_sublineL_sup_torusL hJ le_rfl le_rfl hc3 hcT
  rw [u3TorusK, centralizer_map_mulEquiv, h, Subgroup.map_sup]
  rfl

theorem u3_center_root_le :
    sylowCenter (unitaryCoverRoot J hJ) ≤ u3SubLine J hJ := by
  have hq : 2 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right two_pos hf)
  intro x hx
  obtain ⟨z, rfl⟩ := (mem_sylowCenter.mp hx).1
  have hz1 : z.1.1 = 0 := (mem_sylowCenter_root J (2 ^ f) hcard hfixed hq hJ z).mp hx
  have hz2 : J.conj z.1.2 = z.1.2 := by
    have h := z.2
    rw [hz1, zero_mul, add_zero] at h
    exact (CharTwo.add_eq_zero.mp h).symm
  refine ⟨_, ⟨upperSL _ (Multiplicative.ofAdd ⟨z.1.2, hz2⟩), rfl⟩, ?_⟩
  apply Subtype.ext
  change ProjGenLinGroup.mk
      (((sublineHom J hJ (upperSL _ (Multiplicative.ofAdd ⟨z.1.2, hz2⟩)) :
        J.specialSubgroup) : GL (Fin 3) K)) = ProjGenLinGroup.mk (hermitianUnipotentGL J z)
  congr 1
  apply Units.ext
  rw [coe_sublineHom_upperSL, hermitianUnipotentGL_val, hermitianUnipotentMatrix_eq, hz1, map_zero,
    neg_zero]
  rfl

end Finite

end CFSG.ComponentClassification.GMS78
