module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTits
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSpinMinus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted Matrix

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem exists_conj_borelQuotient (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hn : 4 ≤ n)
    (T : Sylow 2 (StatedProj (StatedOmega (StatedQuadMinus n F b c))))
    (J : Subgroup (StatedProj (StatedOmega (StatedQuadMinus n F b c))))
    (hNJ : Subgroup.normalizer (T : Set (StatedProj (StatedOmega (StatedQuadMinus n F b c)))) ≤ J) :
    ∃ (g : StatedProj (StatedOmega (StatedQuadMinus n F b c)))
      (π' : spinGroup (quadMinus n F b c) →*
        StatedProj (StatedOmega (StatedQuadMinus n F b c))),
      (∀ k, π' k = g * spinToStatedProj (quadMinus n F b c)
        (range_spinMatrix_quadMinus hn hirr) k * g⁻¹) ∧
      BorelQuotient (minusDatum n hirr) (minusWeyl n hirr) (minusTorus n hirr) π'
        (Nat.card F ^ 2 - 1) ∧
      (borel (minusDatum n hirr) (minusTorus n hirr)).map π' ≤ J := by
  have : Finite (spinGroup (quadMinus n F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  set π₀ := spinToStatedProj (quadMinus n F b c) (range_spinMatrix_quadMinus hn hirr) with hπ₀
  have hB := borelQuotient_spinMinus hirr hn
    (MulEquiv.refl (StatedProj (StatedOmega (StatedQuadMinus n F b c))))
  have hπ : ((MulEquiv.refl (StatedProj (StatedOmega (StatedQuadMinus n F b c)))).symm.toMonoidHom.comp
      π₀) = π₀ := MonoidHom.ext fun _ => rfl
  rw [hπ] at hB
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2 : IsPGroup 2 (posUnipotent (minusDatum n hirr)) := isPGroup_iSup_pos hB.extras hB.pGroup
  have hidx : ¬ 2 ∣ ((posUnipotent (minusDatum n hirr)).map π₀).index := fun hd =>
    hB.not_dvd_index (hd.trans (Subgroup.index_map_dvd _ hB.surj))
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (StatedProj (StatedOmega (StatedQuadMinus n F b c)))
    ((hU2.map π₀).toSylow hidx) T
  set π' : spinGroup (quadMinus n F b c) →*
      StatedProj (StatedOmega (StatedQuadMinus n F b c)) :=
    (MulAut.conj g).toMonoidHom.comp π₀ with hπ'
  have hπ'surj : Function.Surjective π' := (MulAut.conj g).surjective.comp hB.surj
  have hker : π'.ker = π₀.ker := by
    ext z
    simp [hπ', MonoidHom.mem_ker]
  have hT : (T : Subgroup _) = (posUnipotent (minusDatum n hirr)).map π' := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    change Subgroup.map (MulAut.conj g).toMonoidHom ((posUnipotent _).map π₀) = _
    rw [Subgroup.map_map]
  have hQ : BorelQuotient (minusDatum n hirr) (minusWeyl n hirr) (minusTorus n hirr) π'
      (Nat.card F ^ 2 - 1) :=
    { ct := hB.ct, extras := hB.extras, pGroup := hB.pGroup, surj := hπ'surj, odd := hB.odd
      torus_pow := hB.torus_pow
      ker_central := fun z hz => hB.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => hB.ker_pow z (hker ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  refine ⟨g, π', fun k => rfl, hQ, ?_⟩
  rw [← hNπ]
  exact hNJ

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
