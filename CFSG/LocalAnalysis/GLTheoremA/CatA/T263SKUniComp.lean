module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SKUniBlock
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SK

open Polynomial Module Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCPrimary CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LocalAnalysis.GLTheoremA.T263.DX

variable {n d : ℕ} {K : Type} [Field K] [Finite K] (h : UnitaryFieldData 2 n K)
  {A : primeFormUnitary h (idGram K d)}

local notation "𝒜" => Matrix.GeneralLinearGroup.toLin ((A : GL (Fin d) K))
local notation "𝒳" => ((Matrix.GeneralLinearGroup.toLin ((A : GL (Fin d) K)) :
  LinearMap.GeneralLinearGroup K (Fin d → K)) : Module.End K (Fin d → K))

omit [Finite K] in
theorem mk_mem_fix_of_mem_fix {g : ↥(gramSU h (idGram K d))}
    (hg : g ∈ fixSubgroup (primeFormConjSU h (idGram K d) A)) :
    (g : primeFormP h (idGram K d)) ∈ fixSubgroup (primeFormConjHom h (idGram K d) A) := by
  rw [mem_fixSubgroup, ← mk_primeFormConjSU h A g, mem_fixSubgroup.1 hg]

omit [Finite K] in
theorem map_fix_le_fix_uni :
    (fixSubgroup (primeFormConjSU h (idGram K d) A)).map
        (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K d)) d)) ≤
      fixSubgroup (primeFormConjHom h (idGram K d) A) := by
  rintro _ ⟨g, hg, rfl⟩
  exact mk_mem_fix_of_mem_fix h hg

omit [Finite K] in
theorem unitaryPreimageBlock_le_fix (a : K[X]) :
    KD264Lie.unitaryPreimageBlock h (x := 𝒜) a ≤ fixSubgroup (primeFormConjSU h (idGram K d) A) :=
  fun g hg => (mem_fixSubgroup_primeFormConjSU_iff A rfl g).mpr
    (specialBlock_le_unitaryCentralizer (Subgroup.mem_comap.mp hg)).2

omit [Finite K] in
theorem unitaryBlockComponent_le_map_fix (a : K[X]) :
    KD264Lie.unitaryBlockComponent h (x := 𝒜) a ≤
      (fixSubgroup (primeFormConjSU h (idGram K d) A)).map
        (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K d)) d)) :=
  Subgroup.map_mono (unitaryPreimageBlock_le_fix h a)

omit [Finite K] in
theorem conj_mem_map_fix_uni {w : primeFormP h (idGram K d)}
    (hw : w ∈ fixSubgroup (primeFormConjHom h (idGram K d) A)) {c : primeFormP h (idGram K d)}
    (hc : c ∈ (fixSubgroup (primeFormConjSU h (idGram K d) A)).map
      (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K d)) d))) :
    w * c * w⁻¹ ∈ (fixSubgroup (primeFormConjSU h (idGram K d) A)).map
      (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K d)) d)) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (normOneScalars h (gramSU h (idGram K d)) d) w
  obtain ⟨c₀, hc₀, rfl⟩ := hc
  refine ⟨g * c₀ * g⁻¹, ?_, by simp only [map_mul, map_inv]⟩
  have h1 : ((primeFormConjSU h (idGram K d) A g : ↥(gramSU h (idGram K d))) : primeFormP h (idGram K d)) =
      (g : primeFormP h (idGram K d)) := by
    rw [mk_primeFormConjSU]
    exact mem_fixSubgroup.1 hw
  have hs : g⁻¹ * primeFormConjSU h (idGram K d) A g ∈ normOneScalars h (gramSU h (idGram K d)) d :=
    QuotientGroup.eq.1 h1.symm
  set s := g⁻¹ * primeFormConjSU h (idGram K d) A g with hsdef
  have hσg : primeFormConjSU h (idGram K d) A g = g * s := by rw [hsdef, mul_inv_cancel_left]
  have hc0 : primeFormConjSU h (idGram K d) A c₀ = c₀ := mem_fixSubgroup.1 hc₀
  rw [SetLike.mem_coe, mem_fixSubgroup, map_mul, map_mul, map_inv, hσg, hc0]
  have hsc : s * c₀ * s⁻¹ = c₀ := mul_inv_eq_iff_eq_mul.2 (normOne_commute h hs c₀).eq
  calc g * s * c₀ * (g * s)⁻¹ = g * (s * c₀ * s⁻¹) * g⁻¹ := by group
    _ = g * c₀ * g⁻¹ := by rw [hsc]

theorem isQuasisimple_unitaryPreimageBlock (H : UnitaryPrimaryData h.bar (idForm h d) 𝒜) (hq : 2 ≤ 2 ^ n)
    (a : primaryFactors 𝒳) (ha : IsGoodBlock h 𝒜 a) :
    CFSG.IsQuasisimple ↥(KD264Lie.unitaryPreimageBlock h (x := 𝒜) (a : K[X])) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (KD264Lie.specialBlockEquiv h H a hq ha).symm
    ((specialBlockFacts_of_good H hq a ha).quasisimple ha.1)

theorem isQuasisimple_unitaryBlockComponent (H : UnitaryPrimaryData h.bar (idForm h d) 𝒜) (hq : 2 ≤ 2 ^ n)
    (a : primaryFactors 𝒳) (ha : IsGoodBlock h 𝒜 a) :
    CFSG.IsQuasisimple ↥(KD264Lie.unitaryBlockComponent h (x := 𝒜) (a : K[X])) := by
  have hFq := isQuasisimple_unitaryPreimageBlock h H hq a ha
  refine CFSG.LocalCores.isQuasisimple_map hFq _ fun hle => ?_
  have hZF : Subgroup.center ↥(KD264Lie.unitaryPreimageBlock h (x := 𝒜) (a : K[X])) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    rw [Subgroup.mem_center_iff]
    intro g'
    have hg : (g : ↥(gramSU h (idGram K d))) ∈ normOneScalars h (gramSU h (idGram K d)) d := by
      have := hle g.2
      rwa [QuotientGroup.ker_mk'] at this
    exact Subtype.ext (normOne_commute h hg g').eq.symm
  obtain ⟨u, w, huw⟩ := hFq.2.2
  apply huw
  induction u using QuotientGroup.induction_on with
  | H u =>
    induction w using QuotientGroup.induction_on with
    | H w =>
      rw [(QuotientGroup.eq_one_iff u).mpr (by rw [hZF]; exact Subgroup.mem_top u),
        (QuotientGroup.eq_one_iff w).mpr (by rw [hZF]; exact Subgroup.mem_top w)]

theorem isComponentOf_unitaryBlockComponent (H : UnitaryPrimaryData h.bar (idForm h d) 𝒜) (hq : 2 ≤ 2 ^ n)
    (a : primaryFactors 𝒳) (ha : IsGoodBlock h 𝒜 a) :
    CFSG.Open.IsComponentOf (KD264Lie.unitaryBlockComponent h (x := 𝒜) (a : K[X]))
      (fixSubgroup (primeFormConjHom h (idGram K d) A)) := by
  refine ⟨(unitaryBlockComponent_le_map_fix h (a : K[X])).trans (map_fix_le_fix_uni h), ?_,
    open_of_native_dx (isQuasisimple_unitaryBlockComponent h H hq a ha)⟩
  have hJn : ((KD264Lie.unitaryBlockComponent h (x := 𝒜) (a : K[X])).subgroupOf
      ((fixSubgroup (primeFormConjSU h (idGram K d) A)).map
        (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K d)) d)))).Normal :=
    SD.Lin.normal_map_subgroupOf _ fun c hc g hg => by
      have hcU := toLinSU_mem_unitaryCentralizer A rfl hc
      have := conj_mem_specialBlock hcU (Subgroup.mem_comap.mp hg)
      rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
      exact this
  have hCn : (((fixSubgroup (primeFormConjSU h (idGram K d) A)).map
      (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K d)) d))).subgroupOf
        (fixSubgroup (primeFormConjHom h (idGram K d) A))).Normal := by
    refine ⟨fun x hx y => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using conj_mem_map_fix_uni h y.2 hx
  exact CFSG.Open.IsSubnormal.step (unitaryBlockComponent_le_map_fix h (a : K[X])) hJn
    (CFSG.Open.IsSubnormal.step (map_fix_le_fix_uni h) hCn (CFSG.Open.IsSubnormal.refl _))

theorem dvd_card_centerQuot_unitaryBlockComponent (H : UnitaryPrimaryData h.bar (idForm h d) 𝒜)
    (hq : 2 ≤ 2 ^ n) (a : primaryFactors 𝒳) (ha : IsGoodBlock h 𝒜 a) {p : ℕ} (hp : p.Prime)
    (hpF : p ∣ Nat.card (specialBlock (idForm h d) 𝒜 (a : K[X]))) :
    p ∣ Nat.card (↥(KD264Lie.unitaryBlockComponent h (x := 𝒜) (a : K[X])) ⧸
      Subgroup.center ↥(KD264Lie.unitaryBlockComponent h (x := 𝒜) (a : K[X]))) := by
  have hFq := isQuasisimple_unitaryPreimageBlock h H hq a ha
  have hperf : commutator ↥(KD264Lie.unitaryPreimageBlock h (x := 𝒜) (a : K[X])) = ⊤ :=
    (open_of_native_dx hFq).1
  obtain ⟨hsurj, hker⟩ := KD264Lie.subgroupMap_mk'_surjective_ker_le_center h (x := 𝒜) a
  obtain ⟨e⟩ := LieComp.nonempty_centralQuotient_mulEquiv hperf _ hsurj hker
  rw [← Nat.card_congr e.toEquiv]
  refine CFSG.dvd_card_quotient_center_of_quasisimple hFq hp ?_
  rw [Nat.card_congr (KD264Lie.specialBlockEquiv h H a hq ha).toEquiv]
  exact hpF

end CFSG.LocalAnalysis.GLTheoremA.T263.SK

end
