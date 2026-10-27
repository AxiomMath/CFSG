module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzQuat
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY12
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.CtxData
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzShape

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open CFSG.ComponentClassification.StandardRecognition
open CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

@[expose] def FzSylowOfClosure : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (T Y R : Subgroup G), orderOf z = 2 → FzSylow T →
    T ≤ centralizer ({z} : Set G) → Nonempty (R ≃* QuaternionGroup 2) → z ∈ R → R ≤ T →
    T = Y ⊔ R → Y ≤ centralizer (R : Set G) → Y ⊓ R ≤ zpowers z →
    (∀ a ∈ R, ∀ g ∈ centralizer ({z} : Set G), g * a * g⁻¹ ∈ T → g * a * g⁻¹ ∈ R) →
    ¬ 2 ∣ R.relIndex (fzCClosure z R)

theorem fz_commute_t (h : Ctx0 t L S x₁ x₂ lam rho) : Commute t x₁ ∧ Commute t x₂ := by
  have hT : wreathGrp x₁ x₂ lam ≤ L := h.inf_eq ▸ inf_le_right
  have hx₁ : x₁ ∈ wreathGrp x₁ x₂ lam := subset_closure (by simp)
  have hx₂ : x₂ ∈ wreathGrp x₁ x₂ lam := subset_closure (by simp)
  have hcent : t ∈ Subgroup.centralizer (L : Set G) := h.hyp.mem_centralizer
  exact ⟨(Subgroup.mem_centralizer_iff.mp hcent x₁ (hT hx₁)).symm,
    (Subgroup.mem_centralizer_iff.mp hcent x₂ (hT hx₂)).symm⟩

theorem fz_orderOf_z (h : Ctx0 t L S x₁ x₂ lam rho) : orderOf ((x₁ * x₂) ^ 2) = 2 :=
  orderOf_eq_prime (by rw [sq]; exact h.wreath.sq_x₁x₂_mul_self) h.wreath.sq_x₁x₂_ne_one

theorem fz_sq_a31 (h : Ctx0 t L S x₁ x₂ lam rho) : ((x₁ * x₂)⁻¹ * t) ^ 2 = (x₁ * x₂) ^ 2 := by
  obtain ⟨h1, h2⟩ := fz_commute_t h
  have hu : Commute t (x₁ * x₂) := h1.mul_right h2
  have ht2 : t ^ 2 = 1 := (orderOf_eq_prime_iff.mp h.hyp.ord_t).1
  rw [(hu.symm.inv_left).mul_pow, ht2, mul_one, inv_pow]
  exact inv_eq_of_mul_eq_one_right h.wreath.sq_x₁x₂_mul_self

theorem fz_closure_le_centralizer {s s' : Set G} (h : ∀ u ∈ s, ∀ v ∈ s', v * u = u * v) :
    closure s ≤ centralizer ((closure s' : Subgroup G) : Set G) := by
  rw [centralizer_closure, closure_le]
  intro u hu
  exact mem_centralizer_iff.mpr fun v hv => h u hu v hv

theorem fz_catalog_of_shape (hCI : ClassicalInvolutionTheoremModels)
    (hGlue : FzSylowOfClosure) [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (h : Ctx0 t L S x₁ x₂ lam rho) {T₂ : Subgroup G} (hT : FzSylow T₂) {a₁₂ a₂₂ a₃₂ : G}
    (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂)
    (hcl : ∀ a ∈ fzR3 t x₁ x₂ a₃₂, ∀ g ∈ centralizer ({(x₁ * x₂) ^ 2} : Set G),
      g * a * g⁻¹ ∈ T₂ → g * a * g⁻¹ ∈ fzR3 t x₁ x₂ a₃₂) : Blueprint.Catalog G := by
  have hq3 : IsQ8Pair ((x₁ * x₂)⁻¹ * t) a₃₂ := hsh.quat₃
  have hz2 : ((x₁ * x₂)⁻¹ * t) ^ 2 = (x₁ * x₂) ^ 2 := fz_sq_a31 h
  have hzR : (x₁ * x₂) ^ 2 ∈ fzR3 t x₁ x₂ a₃₂ := by
    rw [← hz2]
    exact pow_mem (subset_closure (by simp)) 2
  have hRz : fzR3 t x₁ x₂ a₃₂ ≤ centralizer ({(x₁ * x₂) ^ 2} : Set G) := by
    rw [fzR3, closure_le]
    rintro g (rfl | rfl)
    · rw [SetLike.mem_coe, mem_centralizer_singleton_iff, ← hz2]
      exact (Commute.refl _).pow_right 2 |>.eq
    · rw [SetLike.mem_coe, mem_centralizer_singleton_iff, ← hz2]
      exact hq3.mul_comm_sq
  have hRq : Nonempty (fzR3 t x₁ x₂ a₃₂ ≃* QuaternionGroup 2) := fz_q8_nonempty_equiv hq3
  have hTYR : T₂ = closure ({x₁ * t, a₁₂, x₂ * t, a₂₂, lam} : Set G) ⊔ fzR3 t x₁ x₂ a₃₂ := by
    rw [hsh.gen, fzR3, ← Subgroup.closure_union]
    congr 1
    ext g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    tauto
  have hYR : closure ({x₁ * t, a₁₂, x₂ * t, a₂₂, lam} : Set G) ≤
      centralizer ((fzR3 t x₁ x₂ a₃₂ : Subgroup G) : Set G) := by
    refine fz_closure_le_centralizer ?_
    intro u hu v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl
    · exact (hsh.comm₁₃ _ (by simp) v hv).symm.eq
    · exact (hsh.comm₁₃ _ (by simp) v hv).symm.eq
    · exact (hsh.comm₂₃ _ (by simp) v hv).symm.eq
    · exact (hsh.comm₂₃ _ (by simp) v hv).symm.eq
    · rcases hv with rfl | rfl
      · exact hsh.lam_comm₃.1.symm.eq
      · exact hsh.lam_comm₃.2.symm.eq
  have hYRz : closure ({x₁ * t, a₁₂, x₂ * t, a₂₂, lam} : Set G) ⊓ fzR3 t x₁ x₂ a₃₂ ≤
      zpowers ((x₁ * x₂) ^ 2) := by
    rintro g ⟨hgY, hgR⟩
    rw [← hz2]
    refine fz_q8_mem_zpowers_sq_of_central hq3 hgR fun r hr => ?_
    exact (mem_centralizer_iff.mp (hYR hgY) r hr).symm
  have hTz : T₂ ≤ centralizer ({(x₁ * x₂) ^ 2} : Set G) := by
    rw [hTYR]
    refine sup_le ?_ hRz
    exact hYR.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzR))
  have hsyl := hGlue G ((x₁ * x₂) ^ 2) T₂ _ _ (fz_orderOf_z h) hT hTz hRq hzR
    (hTYR ▸ le_sup_right) hTYR hYR hYRz hcl
  exact fz_catalog_of_quaternion hCI hnonab (fz_orderOf_z h) hzR hRz hRq hsyl

end CFSG.OddStandard.SmallF3.FritzII
