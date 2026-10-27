module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Model
public import CFSG.GH74.Uniqueness.SU.KI1r4F61L216
public import Certificates.Certificate23201

public section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open CFSG Subgroup Sporadic.SmallOddCore GH74.Uniqueness.SU.K.R4.L216M GH74.KGroups

theorem autModel_of_gh74 {K X : Type*} [Group K] [Group X] (M : GH74.KGroups.AutModel K X)
    (hle : M.P ≤ M.A) : Sporadic.SmallOddCore.AutModel M.P M.A where
  le := hle
  conj_mem := fun x hx p hp => by
    obtain ⟨φ, hφ⟩ := M.Φ.surjective ⟨x, hx⟩
    obtain ⟨k, hk⟩ := M.e.surjective ⟨p, hp⟩
    have h := M.spec φ k
    rw [hk, hφ] at h
    rw [← h]
    exact (M.e (φ k)).2
  surj α := by
    refine ⟨M.Φ (MulAut.congr M.e.symm α), (M.Φ _).2, fun p => ?_⟩
    have h := M.spec (MulAut.congr M.e.symm α) (M.e.symm p)
    rw [MulEquiv.apply_symm_apply] at h
    rw [← h]
    show ((α p : M.P) : X) = ((M.e (M.e.symm (α (M.e (M.e.symm p)))) : M.P) : X)
    rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  inj x hx hc := by
    obtain ⟨φ, hφ⟩ := M.Φ.surjective ⟨x, hx⟩
    have h1 : φ = 1 := MulEquiv.ext fun k => M.e.injective (Subtype.ext (by
      rw [M.spec φ k, hφ]
      show x * (M.e k : X) * x⁻¹ = (M.e k : X)
      rw [hc _ (M.e k).2, mul_inv_cancel_right]))
    rw [h1, map_one] at hφ
    exact (congrArg Subtype.val hφ).symm

theorem QA_closure : QA.originalSubgroup = Subgroup.closure {pa, pb, sg} := by
  rw [QA, Sporadic.Schreier.certificate_originalSubgroup]
  congr 1
  ext g
  simp

theorem QP_le_QA : QP.originalSubgroup ≤ QA.originalSubgroup := by
  rw [QP_closure, QA_closure]
  exact closure_mono (by simp [Set.insert_subset_iff])


theorem l216_coset : ∀ t ∈ QA.originalSubgroup, orderOf t = 2 →
    ∀ s ∈ QP.originalSubgroup, orderOf (t * s) = 2 →
      ∃ c ∈ QP.originalSubgroup, c⁻¹ * t * c = t * s := by
  have hcheck := Certificates.certificate23201
  simp only [L216.l216CosetOK, Bool.and_eq_true, Bool.not_eq_true'] at hcheck
  obtain ⟨hsift, hall⟩ := hcheck
  have hsg : sg * sg ∉ QP.originalSubgroup := by
    rw [mem_iff_sift QP QP_ok]
    simp [hsift]
  have hpa : pa ∈ QP.originalSubgroup := by
    rw [QP_closure]
    exact subset_closure (by simp)
  refine coset_of_table QP_le_QA (fun b : Bool => bif b then sg * sg else pa)
    (fun t ht ht2 => ?_) (fun i j hij => ?_)
  · have h := forall_of_all QA QA_ok hall t ht
    have ht2' : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
    have ht1 : t ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ht2; omega
    simp only [ht2', ht1, decide_true, decide_false, Bool.not_true, Bool.false_or,
      List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨c, hc, hct⟩ := h
    have hcP := (mem_elemsT QP QP_ok c).1 hc
    rcases hct with hct | hct
    · refine ⟨false, c⁻¹, inv_mem hcP, ?_⟩
      show t = c⁻¹ * pa * c⁻¹⁻¹
      rw [← hct]
      group
    · refine ⟨true, c⁻¹, inv_mem hcP, ?_⟩
      show t = c⁻¹ * (sg * sg) * c⁻¹⁻¹
      rw [← hct]
      group
  · cases i <;> cases j <;> simp_all

theorem l216 : CF23InnerFusionFor fun Y _ => Blueprint.LieModel Y .PSL 2 2 4 := by
  intro G _ _ N hN hC hY α J hα hJN hJα _ _ _ hZ _
  have := hN
  obtain ⟨M, hMP, hMA⟩ := GH74.Uniqueness.SU.K.R4.L216M.autModel hY
  have hle : M.P ≤ M.A := by
    rw [hMP, hMA]
    exact QP_le_QA
  have hM := autModel_of_gh74 M hle
  obtain ⟨hmem, hord⟩ := embed_mem_orderOf hM hC M.e hα
  have hA : ∀ y, y ∈ M.A → y ∈ QA.originalSubgroup := fun y hy => hMA ▸ hy
  have hP : ∀ y, y ∈ M.P ↔ y ∈ QP.originalSubgroup := fun y => by rw [hMP]
  refine concl_of_coset hα hJN hJα hZ (coset_of_autModel hM hC M.e fun s hs hts => ?_)
  obtain ⟨c, hc, hct⟩ := l216_coset _ (hA _ hmem) hord s ((hP s).1 hs) hts
  exact ⟨c, (hP c).2 hc, hct⟩

end CFSG.ComponentClassification.GSThmB.CF23I
