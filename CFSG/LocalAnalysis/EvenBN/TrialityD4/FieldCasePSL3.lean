module

public import CFSG.Blueprint.Catalog
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
import CFSG.LocalAnalysis.ComponentInitial.FieldFourCoverMatrices
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSylowNormalizer

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup

section Proof

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open CFSG.LieType.Chevalley (HSL coe_HSL)

section Transport

variable {G G' : Type*} [Group G] [Group G']

private theorem mem_normalizer_map_equiv_iff_D4 (θ : G ≃* G') (H : Subgroup G) (g : G) :
    θ g ∈ normalizer ((H.map θ.toMonoidHom : Subgroup G') : Set G') ↔
      g ∈ normalizer (H : Set G) := by
  rw [← Subgroup.map_equiv_normalizer_eq H θ, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

private theorem mem_inf_centralizer_map_equiv_iff_D4 (θ : G ≃* G') (H : Subgroup G) (z : G) :
    θ z ∈ H.map θ.toMonoidHom ⊓ centralizer ((H.map θ.toMonoidHom : Subgroup G') : Set G') ↔
      z ∈ H ⊓ centralizer (H : Set G) := by
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply,
    mem_centralizer_iff, mem_centralizer_iff]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h y hy
    apply θ.injective
    rw [map_mul, map_mul]
    exact h _ ⟨y, hy, rfl⟩
  · rintro h _ ⟨y, hy, rfl⟩
    change θ y * θ z = θ z * θ y
    rw [← map_mul, ← map_mul, h y hy]

private theorem card_inf_centralizer_map_equiv_D4 (θ : G ≃* G') (H : Subgroup G) :
    Nat.card ↥(H.map θ.toMonoidHom ⊓ centralizer ((H.map θ.toMonoidHom : Subgroup G') : Set G')) =
      Nat.card ↥(H ⊓ centralizer (H : Set G)) := by
  have h : H.map θ.toMonoidHom ⊓ centralizer ((H.map θ.toMonoidHom : Subgroup G') : Set G') =
      (H ⊓ centralizer (H : Set G)).map θ.toMonoidHom := by
    ext y
    obtain ⟨z, rfl⟩ := θ.surjective y
    rw [mem_inf_centralizer_map_equiv_iff_D4, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  rw [h]
  exact Subgroup.card_map_of_injective θ.injective

end Transport

private theorem matrix_conj_unipU_center_D4 {F : Type} [Field F] (M N : Matrix (Fin 3) (Fin 3) F)
    (m10 : M 1 0 = 0) (m20 : M 2 0 = 0) (m21 : M 2 1 = 0)
    (n10 : N 1 0 = 0) (n20 : N 2 0 = 0) (n21 : N 2 1 = 0) (hMN : M * N = 1) (c : F) :
    M * !![1, 0, c; 0, 1, 0; 0, 0, 1] * N = !![1, 0, M 0 0 * N 2 2 * c; 0, 1, 0; 0, 0, 1] := by
  have e00 := congrFun (congrFun hMN 0) 0
  have e01 := congrFun (congrFun hMN 0) 1
  have e02 := congrFun (congrFun hMN 0) 2
  have e11 := congrFun (congrFun hMN 1) 1
  have e12 := congrFun (congrFun hMN 1) 2
  have e22 := congrFun (congrFun hMN 2) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, m10, m20, m21, n10, n20, n21] at e00 e01 e02
  simp [Matrix.mul_apply, Fin.sum_univ_three, m10, m20, m21, n10, n20, n21] at e11 e12 e22
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, m10, m20, m21, n10, n20, n21]
  · exact e00
  · exact e01
  · linear_combination e02
  · exact e11
  · exact e12
  · exact e22

private theorem conj_unipU_center_of_mem_upperTriangular_D4 {F : Type} [Field F]
    {b : Matrix.SpecialLinearGroup (Fin 3) F} (hb : b ∈ upperTriangular 3 F) (c : F) :
    b * unipU F 0 0 c * b⁻¹ = unipU F 0 0
      ((b : Matrix (Fin 3) (Fin 3) F) 0 0 *
        ((b⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 * c) := by
  have hN : ((b⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F).IsUpperTriangular :=
    coe_inv_isUpperTriangular (mem_upperTriangular_iff_isUpperTriangular.1 hb)
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_unipU, coe_unipU]
  exact matrix_conj_unipU_center_D4 _ _ (hb 1 0 (by decide)) (hb 2 0 (by decide))
    (hb 2 1 (by decide)) (hN (show (0 : Fin 3) < 1 by decide))
    (hN (show (0 : Fin 3) < 2 by decide)) (hN (show (1 : Fin 3) < 2 by decide))
    (by rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]) c

private theorem projUnitriangular_inf_centralizer_D4 {F : Type} [Field F] :
    projUnitriangular 3 F ⊓
      centralizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) =
        projCenterW F := by
  rw [← projUnip_eq_projUnitriangular]
  ext z
  constructor
  · rintro ⟨hz, hzc⟩
    refine mem_projCenterW_of_commute hz ?_ ?_
    · exact (mem_centralizer_iff.1 hzc _ (mem_projUnip.2 ⟨1, 0, 0, rfl⟩)).symm
    · exact (mem_centralizer_iff.1 hzc _ (mem_projUnip.2 ⟨0, 1, 0, rfl⟩)).symm
  · intro hz
    obtain ⟨c, rfl⟩ := mem_projCenterW.1 hz
    refine ⟨mem_projUnip.2 ⟨0, 0, c, rfl⟩, mem_centralizer_iff.2 fun y hy => ?_⟩
    obtain ⟨a, b, c', rfl⟩ := mem_projUnip.1 hy
    rw [← map_mul, ← map_mul, unipU_mul, unipU_mul]
    congr 2 <;> ring

private theorem card_projUnitriangular_inf_centralizer_D4 {F : Type} [Field F] [Finite F] :
    Nat.card ↥(projUnitriangular 3 F ⊓
      centralizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) :
        Set (projectiveSL 3 F))) = Nat.card F := by
  rw [projUnitriangular_inf_centralizer_D4]
  exact card_projCenterW

private theorem exists_proj_conj_unipU_center_D4 {F : Type} [Field F]
    {b : Matrix.SpecialLinearGroup (Fin 3) F} (hb : b ∈ upperTriangular 3 F) :
    ∃ t : F, ∀ c : F, proj 3 F b * proj 3 F (unipU F 0 0 c) * (proj 3 F b)⁻¹ =
      proj 3 F (unipU F 0 0 (t * c)) :=
  ⟨(b : Matrix (Fin 3) (Fin 3) F) 0 0 *
    ((b⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2, fun c => by
    rw [← map_inv, ← map_mul, ← map_mul, conj_unipU_center_of_mem_upperTriangular_D4 hb,
      mul_assoc]⟩

private theorem projUnitriangular_center_comm_D4 {F : Type} [Field F] [Finite F] [CharP F 2]
    {g h z : projectiveSL 3 F}
    (hg : g ∈ normalizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F)))
    (hh : h ∈ normalizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F)))
    (hz : z ∈ projUnitriangular 3 F ⊓ centralizer ((projUnitriangular 3 F :
      Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F))) :
    g * (h * z * h⁻¹) * g⁻¹ = h * (g * z * g⁻¹) * h⁻¹ := by
  rw [normalizer_projUnitriangular 2] at hg hh
  rw [projUnitriangular_inf_centralizer_D4] at hz
  obtain ⟨b, hb, rfl⟩ := hg
  obtain ⟨b', hb', rfl⟩ := hh
  obtain ⟨c, rfl⟩ := mem_projCenterW.1 hz
  obtain ⟨t, ht⟩ := exists_proj_conj_unipU_center_D4 hb
  obtain ⟨t', ht'⟩ := exists_proj_conj_unipU_center_D4 hb'
  rw [ht' c, ht (t' * c), ht c, ht' (t * c)]
  congr 2
  ring

private theorem projUnitriangular_center_transitive_D4 {F : Type} [Field F] [Finite F] [CharP F 2]
    {z z' : projectiveSL 3 F}
    (hz : z ∈ projUnitriangular 3 F ⊓
      centralizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)))
    (hz' : z' ∈ projUnitriangular 3 F ⊓
      centralizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)))
    (h1 : z ≠ 1) (h1' : z' ≠ 1) :
    ∃ g ∈ normalizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F)), g * z * g⁻¹ = z' := by
  rw [projUnitriangular_inf_centralizer_D4] at hz hz'
  obtain ⟨c, rfl⟩ := mem_projCenterW.1 hz
  obtain ⟨c', rfl⟩ := mem_projCenterW.1 hz'
  have hc : c ≠ 0 := by
    rintro rfl
    exact h1 (by rw [unipU_zero, map_one])
  have hc' : c' ≠ 0 := by
    rintro rfl
    exact h1' (by rw [unipU_zero, map_one])
  have ht : c' * c⁻¹ ≠ 0 := mul_ne_zero hc' (inv_ne_zero hc)
  refine ⟨proj 3 F (leviOne F (HSL (Units.mk0 _ ht))), ?_, ?_⟩
  · rw [normalizer_projUnitriangular 2]
    refine Subgroup.mem_map_of_mem _ ?_
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [coe_leviOne, coe_HSL] at hij ⊢
  · rw [← map_inv, ← map_mul, ← map_mul,
      mul_inv_eq_iff_eq_mul.2 (leviOne_mul_unipU (HSL (Units.mk0 _ ht)) 0 c)]
    congr 2
    · simp [coe_HSL]
    · simp [coe_HSL]
      field_simp

private theorem exists_mulEquiv_map_sylow_eq_projUnitriangular_D4 {K : Type} [Group K] [Finite K]
    {F : Type} [Field F] [Finite F] [CharP F 2] (ψ : K ≃* projectiveSL 3 F) (T : Sylow 2 K) :
    ∃ θ : K ≃* projectiveSL 3 F,
      (T : Subgroup K).map θ.toMonoidHom = projUnitriangular 3 F := by
  obtain ⟨U, hU⟩ := exists_sylow_projUnitriangular (K := F) 2 (n := 3) (by norm_num)
  set S' : Sylow 2 (projectiveSL 3 F) := T.mapSurjective (f := ψ.toMonoidHom) ψ.surjective
  obtain ⟨x, hx⟩ : ∃ x : projectiveSL 3 F, x • U = S' := MulAction.exists_smul_eq _ U S'
  have key : ∀ a : projectiveSL 3 F,
      a ∈ (S' : Subgroup (projectiveSL 3 F)) ↔ x⁻¹ * a * x ∈ projUnitriangular 3 F := by
    intro a
    rw [← hx, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← hU,
      ← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv]
  refine ⟨ψ.trans (MulAut.conj x⁻¹), ?_⟩
  ext y
  rw [Subgroup.mem_map_equiv]
  have e : (ψ.trans (MulAut.conj x⁻¹)).symm y = ψ.symm (x * y * x⁻¹) := by
    simp [MulAut.conj_symm_apply]
  rw [e, ← Subgroup.mem_map_equiv (f := ψ)]
  change x * y * x⁻¹ ∈ (S' : Subgroup (projectiveSL 3 F)) ↔ _
  rw [key]
  simp [mul_assoc]

theorem pslThreeSylowCenterAction :
    ∀ (K : Type) [Group K] [Finite K] (m : ℕ), CFSG.Blueprint.LieModel K .PSL 3 2 m →
      ∀ T : Sylow 2 K,
        Nat.card ↥((T : Subgroup K) ⊓ centralizer ((T : Subgroup K) : Set K)) = 2 ^ m ∧
        (∀ g ∈ normalizer ((T : Subgroup K) : Set K), ∀ h ∈ normalizer ((T : Subgroup K) : Set K),
          ∀ z ∈ (T : Subgroup K) ⊓ centralizer ((T : Subgroup K) : Set K),
            g * (h * z * h⁻¹) * g⁻¹ = h * (g * z * g⁻¹) * h⁻¹) ∧
        (∀ z ∈ (T : Subgroup K) ⊓ centralizer ((T : Subgroup K) : Set K),
          ∀ z' ∈ (T : Subgroup K) ⊓ centralizer ((T : Subgroup K) : Set K), z ≠ 1 → z' ≠ 1 →
            ∃ g ∈ normalizer ((T : Subgroup K) : Set K), g * z * g⁻¹ = z') := by
  intro K _ _ m hK T
  have hm : 1 ≤ m := (CFSG.Blueprint.LieModel.admissible hK).2.1
  obtain ⟨F, hFf, hFfin, hF, ⟨ψ⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hK
  haveI : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two hm hF
  obtain ⟨θ, hθ⟩ := exists_mulEquiv_map_sylow_eq_projUnitriangular_D4 ψ T
  have hθZ : ∀ z : K, θ z ∈ projUnitriangular 3 F ⊓
      centralizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) ↔
        z ∈ (T : Subgroup K) ⊓ centralizer ((T : Subgroup K) : Set K) := by
    intro z
    have := mem_inf_centralizer_map_equiv_iff_D4 θ (T : Subgroup K) z
    rwa [hθ] at this
  have hθN : ∀ g : K, θ g ∈ normalizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F)) ↔ g ∈ normalizer ((T : Subgroup K) : Set K) := by
    intro g
    have := mem_normalizer_map_equiv_iff_D4 θ (T : Subgroup K) g
    rwa [hθ] at this
  refine ⟨?_, ?_, ?_⟩
  · have h1 := card_inf_centralizer_map_equiv_D4 θ (T : Subgroup K)
    rw [hθ] at h1
    rw [← h1, card_projUnitriangular_inf_centralizer_D4, hF]
  · intro g hg h hh z hz
    apply θ.injective
    simp only [map_mul, map_inv]
    exact projUnitriangular_center_comm_D4 ((hθN g).2 hg) ((hθN h).2 hh) ((hθZ z).2 hz)
  · intro z hz z' hz' h1 h1'
    obtain ⟨g', hg', hgz⟩ := projUnitriangular_center_transitive_D4 ((hθZ z).2 hz)
      ((hθZ z').2 hz') (fun h => h1 (θ.injective (by rw [h, map_one])))
      (fun h => h1' (θ.injective (by rw [h, map_one])))
    refine ⟨θ.symm g', (hθN _).1 (by simpa using hg'), ?_⟩
    apply θ.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hgz

end Proof

end CFSG.LocalAnalysis.EvenBN.TrialityD4
