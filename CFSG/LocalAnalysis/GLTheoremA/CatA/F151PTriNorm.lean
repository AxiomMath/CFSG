module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151DiagDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PExcNormCore
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenInner

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F151

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator (PerfectInLayer)
open CFSG.ComponentClassification.OuterAutomorphisms (inner_le_innAutDerived)
open CFSG.LocalAnalysis.GLTheoremA.S267.Gen (CompNormal)


private theorem shapeModelNormAt_trialityD4 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    (hPL : ∀ x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom), x ≠ 1 → x ^ p = 1 →
      PerfectInLayer (MulAut.conj x)) :
    ShapeModelNormAt ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) p := by
  intro x y hx1 hxp _hyp hxy J hJ
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hCN : CompNormal (MulAut.conj x) :=
    S267.Gen.compNormal_trialityD4 (ℓ := ℓ) (f := f) hℓ hf hK σ hσ hp hp2 hpℓ
      (MulAut.conj x) (inner_le_innAutDerived _ ⟨x, rfl⟩)
      (by rw [← map_pow, hxp, map_one])
      (fun h => hx1 (CFSG.mulAutConj_injective_of_center_eq_bot hZ h))
  exact mem_normalizer_glaPComponent_of_compNormal hxy (hPL x hx1 hxp) hCN hJ

theorem triNorm_of (hL : CatLayer) (hI : ShapeModelNormIso) :
    SimpleNormModel (CharTwoOf KD264Lie.isTrialityIdx) := by
  intro S _ _ p hp hp2 hcat hshape
  obtain ⟨i, hi, ⟨eCat⟩⟩ := hcat
  cases i with
  | cyclic _ _ => exact absurd hi (by simp [onLie])
  | alternating _ _ => exact absurd hi (by simp [onLie])
  | sporadic _ => exact absurd hi (by simp [onLie])
  | lie dd =>
    obtain ⟨idx, hv⟩ := dd
    obtain ⟨hPtri, hPchar⟩ := hi
    cases idx with
    | trialityD4 q =>
      have hq2 : q.p = 2 := by
        rw [← TauCeti.LieTypeIndex.characteristic_trialityD4]; exact hPchar
      obtain ⟨K, hKf, hKfin, σ, hK, hσ, -, ⟨eB⟩⟩ :=
        CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
      letI := hKf
      letI := hKfin
      have hcatM : catalogIs ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
          (onLie fun d => d.characteristic = 2) :=
        ⟨.lie ⟨.trialityD4 q, hv⟩, hPchar, ⟨eB.symm⟩⟩
      have hPL : ∀ x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
          x ≠ 1 → x ^ p = 1 → PerfectInLayer (MulAut.conj x) :=
        fun x hx1 hxp => hL _ p hp hp2 hcatM x hx1 hxp
      have hnorm := shapeModelNormAt_trialityD4 q.prime_p q.exponent_pos hK σ hσ hp hp2
        (by rw [hq2]; exact hp2) hPL
      exact hI _ _ (eB.symm.trans eCat.symm) p hnorm
    | _ => exact hPtri.elim

end CFSG.LocalAnalysis.GLTheoremA.F151

end
