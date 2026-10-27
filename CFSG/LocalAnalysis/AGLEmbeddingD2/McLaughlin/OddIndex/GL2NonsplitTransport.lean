module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.GL2NonsplitAlg
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.PSL2

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3

variable {F : Type} [Field F]

abbrev projPSL (F : Type) [Field F] : SpecialLinearGroup (Fin 2) F →* PSL2MatrixGroup F :=
  QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) F))

theorem projPSL_eq_one_iff {z : SpecialLinearGroup (Fin 2) F} :
    projPSL F z = 1 ↔ z ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) :=
  QuotientGroup.eq_one_iff z

theorem cSL_pow_three : (cSL (F := F)) ^ 3 = 1 := by
  have := pow_orderOf_eq_one (cSL (F := F))
  rwa [orderOf_cSL] at this

theorem orderOf_projPSL_cSL : orderOf (projPSL F (cSL (F := F))) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (by rw [← map_pow, cSL_pow_three, map_one]) ?_
  intro h
  have hc := eq_one_of_mem_center_of_pow_three (projPSL_eq_one_iff.mp h) cSL_pow_three
  have := orderOf_cSL (F := F)
  rw [hc, orderOf_one] at this
  omega

variable [Finite F]

theorem toGL_mem_Nt_of_projPSL {g : SpecialLinearGroup (Fin 2) F}
    (hg : projPSL F g * projPSL F cSL * (projPSL F g)⁻¹ ∈
      Subgroup.zpowers (projPSL F (cSL (F := F)))) :
    Matrix.SpecialLinearGroup.toGL g ∈ (Nt : Subgroup (GL (Fin 2) F)) := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
  set c : SpecialLinearGroup (Fin 2) F := cSL with hc
  set z : SpecialLinearGroup (Fin 2) F := g * c * g⁻¹ * (c ^ k)⁻¹ with hz
  have hzc : z ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
    rw [← projPSL_eq_one_iff]
    simp only [hz, map_mul, map_inv, map_zpow]
    rw [← hk]
    exact mul_inv_cancel _
  have hcomm : Commute z (c ^ k) := (Subgroup.mem_center_iff.mp hzc (c ^ k)).symm
  have hgcg : g * c * g⁻¹ = z * c ^ k := by rw [hz, inv_mul_cancel_right]
  have hck3 : (c ^ k) ^ 3 = 1 := by
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hc, cSL_pow_three, _root_.one_zpow]
  have hz3 : z ^ 3 = 1 := by
    have h1 : (g * c * g⁻¹) ^ 3 = 1 := by
      rw [conj_pow, hc, cSL_pow_three]
      simp
    rw [hgcg, hcomm.mul_pow, hck3, mul_one] at h1
    exact h1
  have hz1 : z = 1 := eq_one_of_mem_center_of_pow_three hzc hz3
  rw [hz1, one_mul] at hgcg
  have hgl : Matrix.SpecialLinearGroup.toGL g * cGL * (Matrix.SpecialLinearGroup.toGL g)⁻¹ =
      cGL ^ k := by
    have := congrArg (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := F)) hgcg
    simpa [map_mul, map_inv, map_zpow, hc, toGL_cSL] using this
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
  have : Matrix.SpecialLinearGroup.toGL g * cGL ^ j * (Matrix.SpecialLinearGroup.toGL g)⁻¹ =
      cGL ^ (k * j) := by
    rw [← conj_zpow, hgl, ← _root_.zpow_mul]
  rw [this]
  exact Subgroup.zpow_mem_zpowers _ _

theorem mem_Nt_of_inv {s : GL (Fin 2) F} (hs : s * cGL * s⁻¹ = cGL⁻¹) :
    s ∈ (Nt : Subgroup (GL (Fin 2) F)) := by
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
  rw [← conj_zpow, hs, _root_.inv_zpow]
  exact Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers _ _)

omit [Finite F] in
theorem cGL_mem_Nt : (cGL : GL (Fin 2) F) ∈ (Nt : Subgroup (GL (Fin 2) F)) :=
  Subgroup.le_normalizer (Subgroup.mem_zpowers _)

omit [Finite F] in
theorem toGL_mem_Nt_of_mem_center {z : SpecialLinearGroup (Fin 2) F}
    (hz : z ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F)) :
    Matrix.SpecialLinearGroup.toGL z ∈ (Nt : Subgroup (GL (Fin 2) F)) := by
  apply mem_Nt_of_comm
  have := congrArg (fun A : SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F))
    (Subgroup.mem_center_iff.mp hz cSL)
  simp only [Matrix.SpecialLinearGroup.coe_mul] at this
  exact this.symm

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
