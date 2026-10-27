module

public import CFSG.LinearAlgebra.RootGroupSL.ModelPDecomp
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.LinearAlgebra.RootGroupSL.SLFacts
public import CFSG.LinearAlgebra.RootGroupSL.ModelStructure

public section

namespace CFSG.LinearAlgebra.RootGroupSL

open CFSG.Open

variable {k E VJ V₀ : Type} [Field k] [Field E] [Algebra k E]
  [AddCommGroup VJ] [Module k VJ] [Module E VJ] [IsScalarTower k E VJ]
  [AddCommGroup V₀] [Module k V₀]
  [Module.Finite k E] [Module.Finite E VJ] [Module.Finite k VJ] [Module.Finite k V₀]


private lemma add_self_eq_zero_of_charTwo_aux (K : Type*) [Field K] [CharP K 2]
    {A : Type*} [AddCommGroup A] [Module K A] (x : A) : x + x = 0 := by
  calc x + x = (1 : K) • x + (1 : K) • x := by rw [one_smul]
    _ = ((1 : K) + 1) • x := (add_smul _ _ _).symm
    _ = 0 := by rw [CharTwo.add_self_eq_zero (1 : K), zero_smul]

private theorem le_pCore_of_normal_aux {G : Type*} [Group G] {p : ℕ} {N : Subgroup G}
    (hN : N.Normal) (hp : IsPGroup p N) : N ≤ CFSG.pCore p G := by
  rw [CFSG.pCore_eq_iSup]
  exact le_iSup_of_le N (le_iSup_of_le hN (le_iSup_of_le hp le_rfl))

private theorem le_pCoreOf_of_normal_aux {G : Type*} [Group G] {p : ℕ} {N H : Subgroup G}
    (hNH : N ≤ H) (hN : (N.subgroupOf H).Normal) (hp : IsPGroup p N) :
    N ≤ pCoreOf p H := by
  have hsub : IsPGroup p (N.subgroupOf H) :=
    hp.of_equiv (Subgroup.subgroupOfEquivOfLe hNH).symm
  have hcore : N.subgroupOf H ≤ CFSG.pCore p ↥H := by
    rw [CFSG.pCore_eq_iSup]
    exact le_iSup_of_le (N.subgroupOf H) (le_iSup_of_le hN (le_iSup_of_le hsub le_rfl))
  intro x hx
  refine Subgroup.mem_map.mpr ⟨⟨x, hNH hx⟩, ?_, rfl⟩
  exact hcore (Subgroup.mem_subgroupOf.mpr hx)

private lemma isPGroup_modelA1 [CharP k 2] : IsPGroup 2 (modelA1 k VJ V₀) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, show (2 : ℕ) ^ 1 = 2 by norm_num]
  obtain ⟨φ, hφ⟩ := (mem_modelA1_iff (g : SpecialLinearGroup k (VJ × V₀))).mp g.2
  rw [← hφ, pow_two, ← modelA1Elt_add]
  have hzero : φ + φ = 0 := by
    ext w
    exact add_self_eq_zero_of_charTwo_aux k (φ w)
  rw [hzero]
  apply SpecialLinearGroup.ext
  intro p
  obtain ⟨v, w⟩ := p
  simp [modelA1Elt_apply]

private lemma normal_modelA1_subgroupOf_modelP1 :
    ((modelA1 k VJ V₀).subgroupOf (modelP1 k VJ V₀)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff modelA1_le_modelP1]
  intro a g ha hg
  obtain ⟨φa, rfl⟩ := (mem_modelA1_iff a).mp ha
  obtain ⟨φ, hφ⟩ := exists_decomp_modelP1 g hg
  set B := modelBOfP1 g hg with hB
  rw [← hφ]
  have hb : blockSLk k V₀ B ∈ modelK1 k VJ V₀ := by
    rw [modelK1_eq_range]
    exact MonoidHom.mem_range.mpr ⟨B, rfl⟩
  have hconj : blockSLk k V₀ B * modelA1Elt φa * (blockSLk k V₀ B)⁻¹ ∈ modelA1 k VJ V₀ :=
    modelK1_conj_mem_modelA1 hb ((mem_modelA1_iff _).mpr ⟨φa, rfl⟩)
  have hcomm : modelA1Elt φ *
        (blockSLk k V₀ B * modelA1Elt φa * (blockSLk k V₀ B)⁻¹) =
      (blockSLk k V₀ B * modelA1Elt φa * (blockSLk k V₀ B)⁻¹) * modelA1Elt φ :=
    modelA1_mul_comm ((mem_modelA1_iff _).mpr ⟨φ, rfl⟩) hconj
  have heq : (modelA1Elt φ * blockSLk k V₀ B) * modelA1Elt φa *
        (modelA1Elt φ * blockSLk k V₀ B)⁻¹ =
      blockSLk k V₀ B * modelA1Elt φa * (blockSLk k V₀ B)⁻¹ := by
    calc (modelA1Elt φ * blockSLk k V₀ B) * modelA1Elt φa *
          (modelA1Elt φ * blockSLk k V₀ B)⁻¹
        = modelA1Elt φ * (blockSLk k V₀ B * modelA1Elt φa *
            (blockSLk k V₀ B)⁻¹) * (modelA1Elt φ)⁻¹ := by group
      _ = (blockSLk k V₀ B * modelA1Elt φa * (blockSLk k V₀ B)⁻¹) *
            modelA1Elt φ * (modelA1Elt φ)⁻¹ := by rw [hcomm]
      _ = blockSLk k V₀ B * modelA1Elt φa * (blockSLk k V₀ B)⁻¹ := by group
  rw [heq]
  exact hconj

theorem pCoreOf_modelP1 [Finite k] [CharP k 2] (hVJ : 2 ≤ Module.finrank k VJ) :
    pCoreOf 2 (modelP1 k VJ V₀) = modelA1 k VJ V₀ := by
  apply le_antisymm
  · intro x hx
    have hOle : pCoreOf 2 (modelP1 k VJ V₀) ≤ modelP1 k VJ V₀ :=
      Subgroup.map_subtype_le (CFSG.pCore 2 ↥(modelP1 k VJ V₀))
    have hOsub : (pCoreOf 2 (modelP1 k VJ V₀)).subgroupOf (modelP1 k VJ V₀) =
        CFSG.pCore 2 ↥(modelP1 k VJ V₀) := by
      change ((CFSG.pCore 2 ↥(modelP1 k VJ V₀)).map
          (modelP1 k VJ V₀).subtype).comap (modelP1 k VJ V₀).subtype =
        CFSG.pCore 2 ↥(modelP1 k VJ V₀)
      exact Subgroup.comap_map_eq_self_of_injective
        (modelP1 k VJ V₀).subtype_injective _
    have hnorm : ((pCoreOf 2 (modelP1 k VJ V₀)).subgroupOf (modelP1 k VJ V₀)).Normal := by
      rw [hOsub]
      exact CFSG.pCore_normal (p := 2) (G := ↥(modelP1 k VJ V₀))
    have hmapnorm : (((pCoreOf 2 (modelP1 k VJ V₀)).subgroupOf
        (modelP1 k VJ V₀)).map resP1).Normal :=
      hnorm.map resP1 resP1_surjective
    have hpO : IsPGroup 2 ((pCoreOf 2 (modelP1 k VJ V₀)).subgroupOf
        (modelP1 k VJ V₀)) := by
      rw [hOsub]
      exact CFSG.pCore_isPGroup (p := 2) (G := ↥(modelP1 k VJ V₀))
    have hmapP : IsPGroup 2 (((pCoreOf 2 (modelP1 k VJ V₀)).subgroupOf
        (modelP1 k VJ V₀)).map resP1) := hpO.map resP1
    have hle_core : (((pCoreOf 2 (modelP1 k VJ V₀)).subgroupOf
        (modelP1 k VJ V₀)).map resP1) ≤ CFSG.pCore 2 (SpecialLinearGroup k VJ) :=
      le_pCore_of_normal_aux hmapnorm hmapP
    have hbot : (((pCoreOf 2 (modelP1 k VJ V₀)).subgroupOf
        (modelP1 k VJ V₀)).map resP1) = ⊥ := by
      rw [pCore_two_specialLinearGroup_eq_bot' (k := k) (X := VJ)] at hle_core
      exact le_bot_iff.mp hle_core
    have hker_le : (pCoreOf 2 (modelP1 k VJ V₀)).subgroupOf (modelP1 k VJ V₀) ≤
        resP1.ker := by
      intro y hy
      rw [MonoidHom.mem_ker]
      have hy' : resP1 y ∈ (((pCoreOf 2 (modelP1 k VJ V₀)).subgroupOf
          (modelP1 k VJ V₀)).map resP1) := Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
      rw [hbot] at hy'
      exact Subgroup.mem_bot.mp hy'
    have hxP : x ∈ modelP1 k VJ V₀ := hOle hx
    have hxker : (⟨x, hxP⟩ : ↥(modelP1 k VJ V₀)) ∈ resP1.ker :=
      hker_le (Subgroup.mem_subgroupOf.mpr hx)
    rw [resP1_ker] at hxker
    exact Subgroup.mem_subgroupOf.mp hxker
  · exact le_pCoreOf_of_normal_aux modelA1_le_modelP1
      normal_modelA1_subgroupOf_modelP1 isPGroup_modelA1

private lemma isPGroup_modelA2 [CharP k 2] : IsPGroup 2 (modelA2 k VJ V₀) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, show (2 : ℕ) ^ 1 = 2 by norm_num]
  obtain ⟨ψ, hψ⟩ := (mem_modelA2_iff (g : SpecialLinearGroup k (VJ × V₀))).mp g.2
  rw [← hψ, pow_two, ← modelA2Elt_add]
  have hzero : ψ + ψ = 0 := by
    ext v
    exact add_self_eq_zero_of_charTwo_aux k (ψ v)
  rw [hzero]
  apply SpecialLinearGroup.ext
  intro p
  obtain ⟨v, w⟩ := p
  simp [modelA2Elt_apply]

private lemma normal_modelA2_subgroupOf_modelP2 :
    ((modelA2 k VJ V₀).subgroupOf (modelP2 k VJ V₀)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff modelA2_le_modelP2]
  intro a g ha hg
  obtain ⟨ψa, rfl⟩ := (mem_modelA2_iff a).mp ha
  obtain ⟨ψ, hψ⟩ := exists_decomp_modelP2 g hg
  set B := modelBOfP2 g hg with hB
  rw [← hψ]
  have hb : blockSLk k V₀ B ∈ modelK1 k VJ V₀ := by
    rw [modelK1_eq_range]
    exact MonoidHom.mem_range.mpr ⟨B, rfl⟩
  have hconj : blockSLk k V₀ B * modelA2Elt ψa * (blockSLk k V₀ B)⁻¹ ∈ modelA2 k VJ V₀ :=
    modelK1_conj_mem_modelA2 hb ((mem_modelA2_iff _).mpr ⟨ψa, rfl⟩)
  have hcomm : modelA2Elt ψ *
        (blockSLk k V₀ B * modelA2Elt ψa * (blockSLk k V₀ B)⁻¹) =
      (blockSLk k V₀ B * modelA2Elt ψa * (blockSLk k V₀ B)⁻¹) * modelA2Elt ψ :=
    modelA2_mul_comm ((mem_modelA2_iff _).mpr ⟨ψ, rfl⟩) hconj
  have heq : (modelA2Elt ψ * blockSLk k V₀ B) * modelA2Elt ψa *
        (modelA2Elt ψ * blockSLk k V₀ B)⁻¹ =
      blockSLk k V₀ B * modelA2Elt ψa * (blockSLk k V₀ B)⁻¹ := by
    calc (modelA2Elt ψ * blockSLk k V₀ B) * modelA2Elt ψa *
          (modelA2Elt ψ * blockSLk k V₀ B)⁻¹
        = modelA2Elt ψ * (blockSLk k V₀ B * modelA2Elt ψa *
            (blockSLk k V₀ B)⁻¹) * (modelA2Elt ψ)⁻¹ := by group
      _ = (blockSLk k V₀ B * modelA2Elt ψa * (blockSLk k V₀ B)⁻¹) *
            modelA2Elt ψ * (modelA2Elt ψ)⁻¹ := by rw [hcomm]
      _ = blockSLk k V₀ B * modelA2Elt ψa * (blockSLk k V₀ B)⁻¹ := by group
  rw [heq]
  exact hconj

theorem pCoreOf_modelP2 [Finite k] [CharP k 2] (hVJ : 2 ≤ Module.finrank k VJ) :
    pCoreOf 2 (modelP2 k VJ V₀) = modelA2 k VJ V₀ := by
  apply le_antisymm
  · intro x hx
    have hOle : pCoreOf 2 (modelP2 k VJ V₀) ≤ modelP2 k VJ V₀ :=
      Subgroup.map_subtype_le (CFSG.pCore 2 ↥(modelP2 k VJ V₀))
    have hOsub : (pCoreOf 2 (modelP2 k VJ V₀)).subgroupOf (modelP2 k VJ V₀) =
        CFSG.pCore 2 ↥(modelP2 k VJ V₀) := by
      change ((CFSG.pCore 2 ↥(modelP2 k VJ V₀)).map
          (modelP2 k VJ V₀).subtype).comap (modelP2 k VJ V₀).subtype =
        CFSG.pCore 2 ↥(modelP2 k VJ V₀)
      exact Subgroup.comap_map_eq_self_of_injective
        (modelP2 k VJ V₀).subtype_injective _
    have hnorm : ((pCoreOf 2 (modelP2 k VJ V₀)).subgroupOf (modelP2 k VJ V₀)).Normal := by
      rw [hOsub]
      exact CFSG.pCore_normal (p := 2) (G := ↥(modelP2 k VJ V₀))
    have hmapnorm : (((pCoreOf 2 (modelP2 k VJ V₀)).subgroupOf
        (modelP2 k VJ V₀)).map resP2).Normal :=
      hnorm.map resP2 resP2_surjective
    have hpO : IsPGroup 2 ((pCoreOf 2 (modelP2 k VJ V₀)).subgroupOf
        (modelP2 k VJ V₀)) := by
      rw [hOsub]
      exact CFSG.pCore_isPGroup (p := 2) (G := ↥(modelP2 k VJ V₀))
    have hmapP : IsPGroup 2 (((pCoreOf 2 (modelP2 k VJ V₀)).subgroupOf
        (modelP2 k VJ V₀)).map resP2) := hpO.map resP2
    have hle_core : (((pCoreOf 2 (modelP2 k VJ V₀)).subgroupOf
        (modelP2 k VJ V₀)).map resP2) ≤ CFSG.pCore 2 (SpecialLinearGroup k VJ) :=
      le_pCore_of_normal_aux hmapnorm hmapP
    have hbot : (((pCoreOf 2 (modelP2 k VJ V₀)).subgroupOf
        (modelP2 k VJ V₀)).map resP2) = ⊥ := by
      rw [pCore_two_specialLinearGroup_eq_bot' (k := k) (X := VJ)] at hle_core
      exact le_bot_iff.mp hle_core
    have hker_le : (pCoreOf 2 (modelP2 k VJ V₀)).subgroupOf (modelP2 k VJ V₀) ≤
        resP2.ker := by
      intro y hy
      rw [MonoidHom.mem_ker]
      have hy' : resP2 y ∈ (((pCoreOf 2 (modelP2 k VJ V₀)).subgroupOf
          (modelP2 k VJ V₀)).map resP2) := Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
      rw [hbot] at hy'
      exact Subgroup.mem_bot.mp hy'
    have hxP : x ∈ modelP2 k VJ V₀ := hOle hx
    have hxker : (⟨x, hxP⟩ : ↥(modelP2 k VJ V₀)) ∈ resP2.ker :=
      hker_le (Subgroup.mem_subgroupOf.mpr hx)
    rw [resP2_ker] at hxker
    exact Subgroup.mem_subgroupOf.mp hxker
  · exact le_pCoreOf_of_normal_aux modelA2_le_modelP2
      normal_modelA2_subgroupOf_modelP2 isPGroup_modelA2

end CFSG.LinearAlgebra.RootGroupSL
