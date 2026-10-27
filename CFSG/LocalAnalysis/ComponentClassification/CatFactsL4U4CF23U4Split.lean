module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EUCase

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open CFSG Subgroup Module CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.CatalogueBUnitaryB CFSG.LinearGroups
open CFSG.ComponentClassification.GSThmB.Catalog7L4EU
open CFSG.ComponentClassification.OddClassSelector (NoTightWitness)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem u4_split_false (hp : p ≠ 2)
    {X' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))} (hXq : CFSG.IsQuasisimple X')
    (hnt : NoTightWitness X')
    {Y Y₂ : Subgroup (sesqUnitaryGroup (stdHermForm h 4))}
    {T : sesqUnitaryGroup (stdHermForm h 4)}
    (hYX : Y.map (QuotientGroup.mk' (sesqNormOneScalars h (stdHermForm h 4))) = X'.map (ιU h))
    (hY₂p : ⁅Y₂, Y₂⁆ = Y₂) (hTY₂ : T ∈ Y₂) (hcomm : ∀ y ∈ Y, ∀ w ∈ Y₂, y * w = w * y)
    (hTT : unitaryOp T * unitaryOp T = -1)
    (hTZ : T ∉ sesqNormOneScalars h (stdHermForm h 4)) : False := by
  classical
  have : Finite K := h.finite
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp
  obtain ⟨T', hT'⟩ := le_range_toSesqUnitary h hY₂p hTY₂
  have hιt : ιU h (QuotientGroup.mk T') =
      QuotientGroup.mk' (sesqNormOneScalars h (stdHermForm h 4)) T := by
    rw [ιU_mk, hT']
    rfl
  have hTTZ : T * T ∈ sesqNormOneScalars h (stdHermForm h 4) := by
    refine ⟨-1, ?_, ?_⟩
    · rw [UnitaryFieldData.norm, map_neg, map_one, neg_one_mul, neg_neg]
    · rw [show ((T * T : sesqUnitaryGroup (stdHermForm h 4)) : LinearMap.GeneralLinearGroup K
        (Fin 4 → K)) = unitaryOp T * unitaryOp T from rfl, hTT]
      exact (neg_one_smul K (1 : Module.End K (Fin 4 → K))).symm
  have hπT : QuotientGroup.mk' (sesqNormOneScalars h (stdHermForm h 4)) T ≠ 1 := fun h1 =>
    hTZ ((QuotientGroup.eq_one_iff T).mp h1)
  have hπTT : QuotientGroup.mk' (sesqNormOneScalars h (stdHermForm h 4)) T *
      QuotientGroup.mk' (sesqNormOneScalars h (stdHermForm h 4)) T = 1 := by
    rw [← map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr hTTZ
  have ht1 : (QuotientGroup.mk T' : StatedProj (StatedSU 4 (p ^ f) K)) ≠ 1 := fun h1 =>
    hπT (by rw [← hιt, h1, map_one])
  have htt : (QuotientGroup.mk T' : StatedProj (StatedSU 4 (p ^ f) K)) *
      QuotientGroup.mk T' = 1 := ιU_injective h (by rw [map_mul, hιt, hπTT, map_one])
  have hto : orderOf (QuotientGroup.mk T' : StatedProj (StatedSU 4 (p ^ f) K)) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
  have hu : orderOf (QuotientGroup.mk' (sesqNormOneScalars h (stdHermForm h 4)) T) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hπTT) hπT
  have hXι : ∀ x ∈ X', ∃ y ∈ Y,
      QuotientGroup.mk' (sesqNormOneScalars h (stdHermForm h 4)) y = ιU h x := fun x hx => by
    have hm : ιU h x ∈ Y.map (QuotientGroup.mk' (sesqNormOneScalars h (stdHermForm h 4))) :=
      hYX ▸ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hm
    exact ⟨y, hy, hyx⟩
  have htX : ∀ x ∈ X', x * QuotientGroup.mk T' = QuotientGroup.mk T' * x := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hXι x hx
    apply ιU_injective h
    rw [map_mul, map_mul, hιt, ← hyx, ← map_mul, ← map_mul, hcomm y hy T hTY₂]
  set C := centralizer
    ({QuotientGroup.mk' (sesqNormOneScalars h (stdHermForm h 4)) T} :
      Set (sesqProjUnitary h (stdHermForm h 4))) with hC
  have hmemC : ∀ x : StatedProj (StatedSU 4 (p ^ f) K), ιU h x ∈ C ↔
      x * QuotientGroup.mk T' = QuotientGroup.mk T' * x := by
    intro x
    rw [hC, mem_centralizer_singleton_iff, ← hιt, ← map_mul, ← map_mul]
    exact (ιU_injective h).eq_iff
  have hXC : X'.map (ιU h) ≤ C := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hmemC x).mpr (htX x hx)
  have hBq : CFSG.IsQuasisimple ((X'.map (ιU h)).subgroupOf C) :=
    (isQuasisimple_congr ((Subgroup.subgroupOfEquivOfLe hXC).trans
      (X'.equivMapOfInjective _ (ιU_injective h)).symm)).mpr hXq
  have : (ιU h).range.Normal := ιU_range_normal h
  have hBM : (X'.map (ιU h)).subgroupOf C ≤ (ιU h).range.subgroupOf C := fun x hx =>
    mem_subgroupOf.mpr (map_le_range _ _ (mem_subgroupOf.mp hx))
  have hBn : (((X'.map (ιU h)).subgroupOf C).subgroupOf
      ((ιU h).range.subgroupOf C)).Normal := by
    rw [normal_subgroupOf_iff hBM]
    intro a b ha hb
    rw [mem_subgroupOf] at ha hb ⊢
    obtain ⟨x, hx, hxa⟩ := ha
    obtain ⟨g, hg⟩ := hb
    have hgt : g * QuotientGroup.mk T' = QuotientGroup.mk T' * g := by
      rw [← hmemC, hg]
      exact b.2
    have hgN := mem_normalizer_iff.mp (hnt _ g hto htX hgt) x
    refine ⟨g * x * g⁻¹, hgN.mp hx, ?_⟩
    rw [map_mul, map_mul, map_inv, hg, hxa]
    rfl
  have hBc : CFSG.IsComponent ((X'.map (ιU h)).subgroupOf C) :=
    ⟨hBq, IsSubnormal.step _ _ hBM (Normal.isSubnormal inferInstance) hBn⟩
  have hBmap : (((X'.map (ιU h)).subgroupOf C).map C.subtype : Subgroup _) = X'.map (ιU h) := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hXC]
  have hQB : Y₂.map (QuotientGroup.mk' (sesqNormOneScalars h (stdHermForm h 4))) ≤
      centralizer ((((X'.map (ιU h)).subgroupOf C).map C.subtype : Subgroup _) :
        Set (sesqProjUnitary h (stdHermForm h 4))) := by
    rw [hBmap]
    rintro _ ⟨w, hw, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hXι x hx
    rw [← hyx, ← map_mul, ← map_mul, hcomm y hy w hw]
  have hQ1 : Y₂.map (QuotientGroup.mk' (sesqNormOneScalars h (stdHermForm h 4))) ≠ ⊥ := by
    intro hb
    apply hπT
    have hm : QuotientGroup.mk' (sesqNormOneScalars h (stdHermForm h 4)) T ∈
        Y₂.map (QuotientGroup.mk' (sesqNormOneScalars h (stdHermForm h 4))) :=
      mem_map_of_mem _ hTY₂
    rw [hb, mem_bot] at hm
    exact hm
  have hQp : ⁅Y₂.map (QuotientGroup.mk' (sesqNormOneScalars h (stdHermForm h 4))),
      Y₂.map (QuotientGroup.mk' (sesqNormOneScalars h (stdHermForm h 4)))⁆ =
      Y₂.map (QuotientGroup.mk' (sesqNormOneScalars h (stdHermForm h 4))) := by
    rw [← Subgroup.map_commutator, hY₂p]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, A, -, -, hA2, -, -, hfix⟩ :=
    odd_projective_unitary_local_component_supported_on_eigenspace h hp
      (by rw [Module.finrank_fin_fun]; norm_num) (stdHermForm_isSymm h 4)
      (stdHermForm_separatingLeft h 4) hu rfl hBc hQB hQ1 hQp
  have hTQ : T ∈ ⁅(Y₂.map (QuotientGroup.mk' (sesqNormOneScalars h (stdHermForm h 4)))).comap
      (QuotientGroup.mk' (sesqNormOneScalars h (stdHermForm h 4))),
      (Y₂.map (QuotientGroup.mk' (sesqNormOneScalars h (stdHermForm h 4)))).comap
      (QuotientGroup.mk' (sesqNormOneScalars h (stdHermForm h 4)))⁆ := by
    have hle : Y₂ ≤ (Y₂.map (QuotientGroup.mk' (sesqNormOneScalars h (stdHermForm h 4)))).comap
        (QuotientGroup.mk' (sesqNormOneScalars h (stdHermForm h 4))) :=
      le_comap_map _ _
    rw [← hY₂p] at hTY₂
    exact commutator_mono hle hle hTY₂
  have hA0 : A ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at hA2
    omega
  obtain ⟨a, haA, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA0
  have hTa := hfix T hTQ a haA
  have h1 := LinearMap.congr_fun hTT a
  rw [Module.End.mul_apply, hTa, hTa, LinearMap.neg_apply, Module.End.one_apply] at h1
  apply ha0
  have h3 : (2 : K) • a = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h1]
    exact neg_add_cancel a
  exact (smul_eq_zero.mp h3).resolve_left h2

end CFSG.ComponentClassification.GSThmB.CF23I
