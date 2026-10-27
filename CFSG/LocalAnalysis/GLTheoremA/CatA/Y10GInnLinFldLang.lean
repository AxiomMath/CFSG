module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinFldGrp
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma52
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.LieType.SemisimpleCentralizers.HeldLangPSL

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GInnLinFld

open CFSG.Open CFSG.Assembly CFSG.LieType.SemisimpleCentralizers.HeldLang
open CFSG.HardMathSupport.Foote.ModuleExclusions
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

theorem lang_fixed {d : ℕ} {K : Type} [Field K] [Finite K] (hd : 3 ≤ d) (A : GL (Fin d) K) (σ : K ≃+* K)
    (c : K)
    (hg : Ai σ (A : Matrix (Fin d) (Fin d) K) (orderOf σ) = c • (1 : Matrix (Fin d) (Fin d) K))
    (β : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K)))
    (hβ : ∀ x : ↥(slGL (Fin d) K),
      β (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) x) =
        LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) (slTwist σ A x)) :
    ∃ Y : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin d) K)),
      Y ≤ fixSubgroup β ∧ (Y.subgroupOf (fixSubgroup β)).Normal ∧
        ⁅fixSubgroup β, fixSubgroup β⁆ ≤ Y ∧
        Nonempty (↥Y ≃* StatedProj (StatedSL d ↥(fixField σ))) := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨Y₀, hY₀F, hY₀n, hFY₀, ⟨e₀⟩⟩ := exists_psl_fix_equiv σ A c hg
  obtain ⟨eP⟩ := nonempty_psl_equiv_statedProj d ↥(fixField σ)
  have hcomp : ∀ y : PSL (Fin d) K,
      β (pslEquivLarge d y) = pslEquivLarge d (slTwistBar σ A y) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    rw [slTwistBar_mk, pslEquivLarge_mk, pslEquivLarge_mk]
    exact hβ g
  have hC : fixSubgroup β = (fixHom (slTwistBar σ A)).map (pslEquivLarge d).toMonoidHom := by
    ext x
    rw [mem_fixSubgroup, Subgroup.mem_map]
    constructor
    · intro hx
      refine ⟨(pslEquivLarge d).symm x, ?_, (pslEquivLarge d).apply_symm_apply x⟩
      rw [mem_fixHom]
      have h1 : pslEquivLarge d (slTwistBar σ A ((pslEquivLarge d).symm x)) =
          pslEquivLarge d ((pslEquivLarge d).symm x) := by
        rw [← hcomp, MulEquiv.apply_symm_apply]
        exact hx
      exact (pslEquivLarge d).injective h1
    · rintro ⟨y, hy, hyx⟩
      rw [← hyx]
      show β (pslEquivLarge d y) = pslEquivLarge d y
      rw [hcomp, mem_fixHom.1 hy]
  have hYC : Y₀.map (pslEquivLarge d).toMonoidHom ≤ fixSubgroup β := by
    rw [hC]
    exact Subgroup.map_mono hY₀F
  have hYn : ((Y₀.map (pslEquivLarge d).toMonoidHom).subgroupOf (fixSubgroup β)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hYC]
    intro h k hh hk
    rw [hC] at hk
    obtain ⟨f₀, hf₀, rfl⟩ := Subgroup.mem_map.1 hk
    obtain ⟨h₀, hh₀, rfl⟩ := Subgroup.mem_map.1 hh
    refine Subgroup.mem_map.2 ⟨f₀ * h₀ * f₀⁻¹, ?_, by simp⟩
    exact (Subgroup.normal_subgroupOf_iff hY₀F).1 hY₀n h₀ f₀ hh₀ hf₀
  have hCY : ⁅fixSubgroup β, fixSubgroup β⁆ ≤ Y₀.map (pslEquivLarge d).toMonoidHom := by
    rw [hC, ← Subgroup.map_commutator]
    exact Subgroup.map_mono hFY₀
  refine ⟨Y₀.map (pslEquivLarge d).toMonoidHom, hYC, hYn, hCY, ⟨?_⟩⟩
  exact (Subgroup.equivMapOfInjective Y₀ (pslEquivLarge d).toMonoidHom (pslEquivLarge d).injective).symm.trans
    (e₀.trans eP)

theorem component_eq_of_fixed {P : Type} [Group P] [Finite P] {C Y J : Subgroup P} {p : ℕ}
    (hJ : CFSG.Open.GLAPComponent p C J) (hYC : Y ≤ C) (hYn : (Y.subgroupOf C).Normal)
    (hCY : ⁅C, C⁆ ≤ Y) [IsSimpleGroup ↥Y] [Group.IsPerfect ↥Y] : J = Y := by
  have hperf : ⁅J, J⁆ = J := Lemma53Ns.glaPComponent_perfect hJ
  have hne : J ≠ ⊥ := glaPComponent_ne_bot hJ
  obtain ⟨hJC, hJsub, -, -⟩ := hJ
  have hJY : J ≤ Y := by
    calc J = ⁅J, J⁆ := hperf.symm
      _ ≤ ⁅C, C⁆ := Subgroup.commutator_mono hJC hJC
      _ ≤ Y := hCY
  have hsub : CFSG.Open.IsSubnormal J Y := by
    have h := CFSG.Fischer.Classification.Recognition.IsSubnormal.inf_normal hJsub hYC hYn
    rwa [inf_eq_left.2 hJY] at h
  have hq : CFSG.Open.IsQuasisimple ↥Y := isQuasisimple_of_simple_perfect inferInstance
  rcases CFSG.Fischer.Classification.Recognition.IsSubnormal.eq_or_le_center hsub hq with h | h
  · exact h
  · exfalso
    rw [center_eq_bot_of_simple_perfect (inferInstance : Group.IsPerfect ↥Y), Subgroup.map_bot,
      le_bot_iff] at h
    exact hne h

end CFSG.LocalAnalysis.GLTheoremA.Y10GInnLinFld

end
