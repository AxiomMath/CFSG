module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167TriAmbInputs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167TriK
public import CFSG.LocalAnalysis.GLTheoremA.S12.Compl123

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut)
open CFSG.LocalAnalysis.GLTheoremA.Y10F (centerQuotAut centerQuotAut_mk)

set_option linter.unusedSectionVars false


private theorem tri_isPGroup_zpowers {Ω : Type} [Group Ω] {x : Ω} (hx : x ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers x) := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 g.2
  show (g : Ω) ^ 3 ^ 1 = 1
  rw [← hm, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

private theorem tri_chevAut_eq {Ω : Type} [Group Ω] [Finite Ω] (X : Subgroup Ω) {a : Ω}
    (ha : a ∈ Subgroup.normalizer (X : Set Ω)) :
    chevAut 3 X ⟨a, ha⟩ = centerQuotAut (PQuot 3 X) (barAut 3 X ⟨a, ha⟩) := by
  ext s
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective s
  rw [centerQuotAut_mk]
  exact CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk
    (barAut 3 X ⟨a, ha⟩) k

private theorem tri_inducesInnerMod_of_mem_cs {Ω : Type} [Group Ω] {p : ℕ} {X : Subgroup Ω}
    {x : Ω} (hc : x ∈ cs X) : InducesInnerMod p X x := by
  refine ⟨1, X.one_mem, fun y hy => ?_⟩
  have h : x⁻¹ * y * x = y := by
    rw [mul_assoc, Subgroup.mem_centralizer_iff.1 hc y hy, inv_mul_cancel_left]
  rw [h]
  simp [(GLAPPrimeCoreOf p X).one_mem]

theorem tri_not_mem_cs {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {X : Subgroup Ω} {x : Ω}
    (hself : GLAPComponent p X X) (hchev : IsChevSimple 2 (PSimple p X))
    (hxN : x ∈ Subgroup.normalizer (X : Set Ω))
    (hnon : ¬ InnDiagOn p (Subgroup.zpowers x) X) : x ∉ cs X := fun hc =>
  hnon (MI.inner_innDiag_any hself hchev hxN (tri_inducesInnerMod_of_mem_cs hc))

theorem false_of_triality_amb {Ω : Type} [Group Ω] [Finite Ω] {X J : Subgroup Ω} {x : Ω}
    (hX : CFSG.Open.IsQuasisimple ↥X) (hchev : IsChevSimple 2 (PSimple 3 X))
    (hxN : x ∈ Subgroup.normalizer (X : Set Ω)) (hx3 : x ^ 3 = 1) (hnf : ¬ FieldOn 3 x X)
    (hnon : ¬ InnDiagOn 3 (Subgroup.zpowers x) X) (hJ : GLAPComponent 3 (X ⊓ cx x) J)
    (htype : Type167J 3 J) : False := by
  have hself : GLAPComponent 3 X X := tri_glaPComponent_self hX hchev
  have hxi : x⁻¹ ∈ Subgroup.normalizer (X : Set Ω) := Subgroup.inv_mem _ hxN
  have hK : CFSG.Open.IsQuasisimple (PQuot 3 X) := MI.isQuasisimple_pQuot_any hself
  have hα3 : barAut 3 X ⟨x⁻¹, hxi⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have h1 : (⟨x⁻¹, hxi⟩ : ↥(Subgroup.normalizer (X : Set Ω))) ^ 3 = 1 :=
      Subtype.ext (by simp [inv_pow, hx3])
    rw [h1, map_one]
  have hnInn : ¬ K144.I144Inner (PQuot 3 X) (barAut 3 X ⟨x⁻¹, hxi⟩) := fun h =>
    hnon (tri_innDiagOn_of_i144Inner hxN h)
  have hnFld : ¬ GLAMarking (PQuot 3 X) (fun lab _ _ I F θ =>
      GLAPrimeField 3 lab I F (GLAInduces θ fun a b => barAut 3 X ⟨x⁻¹, hxi⟩ a = b)) := by
    intro h
    refine hnf ⟨hxN, ?_⟩
    have hrel : indRel 3 X x = fun a b => barAut 3 X ⟨x⁻¹, hxi⟩ a = b := by
      funext a b
      exact propext (FP.indRel_iff_barAut hxN a b)
    rw [hrel]
    exact h
  have hap : IsPGroup 3 (Subgroup.zpowers x⁻¹) := tri_isPGroup_zpowers (by rw [inv_pow, hx3, inv_one])
  have hJ' : GLAPComponent 3 (X ⊓ Subgroup.centralizer ({x⁻¹} : Set Ω)) J := by
    rw [K144.centralizer_inv_eq]
    exact hJ
  have hT := glaPComponent_chevTransfer Nat.prime_three hxi hap hJ'
  rw [tri_chevAut_eq] at hT
  obtain ⟨e⟩ := nonempty_pSimple_equiv_chevTransfer Nat.prime_three hxi hap hJ'
  exact false_of_triality_K hK hchev hα3 hnInn hnFld hT ((type167Grp_congr e).1 htype)

end CFSG.LocalAnalysis.GLTheoremA.I167

end
