module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltPlusD.Reduction
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltPlusD.FlagLink
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltPlusD.Center
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltPlusD.NaturalModule
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.StatedOmegaScalars

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding CFSG.LieType.Universal.Spin
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg Matrix CFSG.AGLEmbedding.LieOut
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal.Spin.Twisted

section

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem eq_one_of_mem_statedScalars_statedOmega (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hn : 2 ≤ n) {A : StatedOmega (StatedQuadMinus n F b c)}
    (hA : (A : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) ∈
      StatedScalars (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) : A = 1 :=
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.eq_one_of_mem_statedScalars_statedQuadMinus_omega hirr hn hA

end


theorem altPlusCellD4 (hGA : CFSG.Open.GriessAllModelsStatement) : AltPlusCellD4 := by
  intro Y _ _ L J p x hC hp hAlt hxL hxp hxC hfix n hmodel
  subst hp
  have hperf : Group.IsPerfect ↥L := ⟨hC.comp.2.2.1⟩
  have hZ1 := card_center_eq_one_of_pomegaMinus_four hGA hmodel
  have hZ : Subgroup.center ↥L = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ1
  obtain ⟨⟨-, hf, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e⟩⟩ := hmodel
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hn4 : 4 ≤ n := by omega
  obtain ⟨hJL, T, hT, hNT⟩ := hC.parab
  have hNJ := normalizer_barSylow_le_quotImage hT hNT
  have hshort : ∀ π' : spinGroup (quadMinus n F b c) →* ↥L ⧸ Subgroup.center ↥L,
      π'.ker = (e.symm.toMonoidHom.comp (spinToStatedProj (quadMinus n F b c)
        (range_spinMatrix_quadMinus hn4 hirr))).ker →
      ∀ k : Fin (n - 1), ¬ k.val + 1 < n - 1 →
        ¬ (CFSG.LieType.CurtisTits.rankOne (minusDatum n hirr).rootGroup k).map π' ≤
          quotImage L J :=
    fun π' hker k hk hle => false_of_altPlus_shortNode hC (Or.inl rfl) hAlt hirr hn4 hcard
      le_rfl (by norm_num) e π' hker k hk hle
  obtain ⟨W, hWQ, hWdim, hWstab⟩ :=
    exists_stab_of_overgroup hirr hn4 e (barSylow hT) (quotImage L J) hNJ hshort
  have hxJ : x ∈ J := hfix x hxL (by simp)
  have hxbJ : (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : ↥L ⧸ Subgroup.center ↥L) ∈ quotImage L J :=
    mem_quotImage.2 ⟨⟨x, hxL⟩, hxJ, rfl⟩
  obtain ⟨M0, hM0⟩ := QuotientGroup.mk_surjective
    (e (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : ↥L ⧸ Subgroup.center ↥L))
  have hMW := fun w hw => hWstab _ hxbJ M0 hM0 w hw
  have hMQ := preserves_of_mem_statedOmega (Q₀ := StatedQuadMinus n F b c) M0.2
  have hM5 : (M0 : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) ^ 5 = 1 := by
    have h1 : (QuotientGroup.mk (M0 ^ 5) :
        StatedProj (StatedOmega (StatedQuadMinus n F b c))) = 1 := by
      rw [QuotientGroup.mk_pow, hM0, ← map_pow, ← QuotientGroup.mk_pow]
      have : (⟨x, hxL⟩ : ↥L) ^ 5 = 1 := Subtype.ext hxp
      rw [this]
      simp
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    have := eq_one_of_mem_statedScalars_statedOmega hirr (by omega) h1
    simpa using congrArg Subtype.val this
  have hC' : ∀ g ∈ StatedOmega (StatedQuadMinus n F b c),
      g * (M0 : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) =
        (M0 : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) * g →
      ∀ w ∈ W, (g : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) *ᵥ w ∈ W := by
    intro g hg hcomm w hw
    set gΩ : ↥(StatedOmega (StatedQuadMinus n F b c)) := ⟨g, hg⟩ with hgΩ
    set y : ↥L ⧸ Subgroup.center ↥L := e.symm (QuotientGroup.mk gΩ) with hydef
    have hy : y ∈ quotImage L J := by
      obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective y
      have hcomm' : (QuotientGroup.mk gΩ : StatedProj (StatedOmega (StatedQuadMinus n F b c))) *
          e (QuotientGroup.mk (⟨x, hxL⟩ : ↥L)) = e (QuotientGroup.mk (⟨x, hxL⟩ : ↥L)) *
          QuotientGroup.mk gΩ := by
        rw [← hM0, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        exact Subtype.ext hcomm
      have hy' : y * QuotientGroup.mk (⟨x, hxL⟩ : ↥L) = QuotientGroup.mk (⟨x, hxL⟩ : ↥L) * y := by
        apply e.injective
        rw [map_mul, map_mul, hydef, MulEquiv.apply_symm_apply]
        exact hcomm'
      rw [← hl, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at hy'
      have hmem := QuotientGroup.eq.1 hy'
      rw [hZ, Subgroup.mem_bot] at hmem
      have hlx : l * ⟨x, hxL⟩ = ⟨x, hxL⟩ * l := by
        exact inv_mul_eq_one.1 hmem
      have hfl : x * (l : Y) * x⁻¹ = l := by
        have := congrArg Subtype.val hlx
        simp only [Subgroup.coe_mul] at this
        rw [← this, mul_assoc, mul_inv_cancel, mul_one]
      exact mem_quotImage.2 ⟨l, hfix l l.2 hfl, hl⟩
    exact hWstab y hy gΩ (by simp [hydef]) w hw
  refine false_of_invariant_totSingular (K := F) (ι := Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
    (by rw [hcard]; norm_num) (quadMinusForm n F b c hirr) ?_ W hWQ ?_
    (M0 : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) hMQ hM5 hMW hC'
  · simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  · rw [hWdim]
    omega

theorem altPlusCellD (hGA : CFSG.Open.GriessAllModelsStatement) : AltPlusCellD :=
  altPlusCellD_of_four (altPlusCellD4 hGA)

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
