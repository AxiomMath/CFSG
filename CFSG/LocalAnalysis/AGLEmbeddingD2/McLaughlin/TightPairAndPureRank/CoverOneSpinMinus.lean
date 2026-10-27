module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverOneChain
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverOneFamilies
public import CFSG.Timmesfeld.RankTwo.LevisBRankOne

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.Universal.Spin.OddCT CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.CentralExt
  CFSG.LieType.CurtisTits CFSG.QuasithinUnique CFSG.AGLEmbedding.BlockCyc
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.SectionRank.EvenCover
open scoped commutatorElement

section Pkg

variable
  {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem hasTorusSL2_spinMinus_short (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] [Finite (ShortField b c)] [CharP (ShortField b c) 2]
    (h4 : 4 ≤ Nat.card (ShortField b c)) {k : Fin (n - 1)} (hk : ¬ k.val + 1 < n - 1) :
    HasTorusSL2 (minusDatum n hirr) (minusTorus n hirr) k (ShortField b c) := by
  obtain ⟨φ, hx, hy⟩ := CFSG.Timmesfeld.RankTwo.exists_hom_of_rankOneRels (shortRels n hirr k)
  have hS := sl2_isSimpleGroup (k := ShortField b c) h4
  have hx0 : (shortRels n hirr k).x 0 = 1 := RankOneRels.x_zero _
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with hb | ht
    · exact hb
    · exfalso
      have hmem : sl2Upper (1 : ShortField b c) ∈ φ.ker := by rw [ht]; exact Subgroup.mem_top _
      have h1 : φ (sl2Upper (1 : ShortField b c)) = 1 := MonoidHom.mem_ker.1 hmem
      rw [hx] at h1
      exact one_ne_zero (shortRels_x_injective hirr k (h1.trans hx0.symm))
  have hL : rankOne (minusDatum n hirr).rootGroup k ≤ φ.range := by
    refine sup_le (fun g hg => ?_) (fun g hg => ?_)
    · obtain ⟨t, rfl⟩ := (mem_minusRootGroup_single_iff hirr hk g).1 hg
      exact ⟨sl2Upper t, hx t⟩
    · obtain ⟨t, rfl⟩ := (mem_minusRootGroup_neg_single_iff hirr hk g).1 hg
      exact ⟨sl2Lower t, hy t⟩
  obtain ⟨ω, hω0, hω2⟩ := CFSG.ClassicalModels.exists_ne_zero_sq_ne_one_of_four_le_card
    (ShortField b c) h4
  have hφh : φ ((sl2Rels (ShortField b c)).h ω) = (shortRels n hirr k).h ω := by
    simp only [RankOneRels.h_def, RankOneRels.w_def, map_mul, map_inv, sl2Rels_x, sl2Rels_y, hx, hy]
  have hnc : (sl2Rels (ShortField b c)).h ω * sl2Upper 1 ≠
      sl2Upper 1 * (sl2Rels (ShortField b c)).h ω := by
    intro hc
    have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) (ShortField b c) =>
      (A : Matrix (Fin 2) (Fin 2) (ShortField b c)) 0 1) hc
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Rels_h hω0, coe_sl2Upper, Matrix.mul_apply,
      Fin.sum_univ_two] at this
    apply hω2
    field_simp at this
    linear_combination this
  refine ⟨φ, hinj, fun a => ?_, fun a => ?_, hL, (sl2Rels (ShortField b c)).h ω, sl2Upper 1, hnc, ?_⟩
  · rw [hx a]
    exact (mem_minusRootGroup_single_iff hirr hk _).2 ⟨a, rfl⟩
  · rw [hy a]
    exact (mem_minusRootGroup_neg_single_iff hirr hk _).2 ⟨a, rfl⟩
  · rw [hφh, minusTorus_of_not_lt n hirr hk]
    exact shortRels_h_mem n hirr k hω0

end Pkg


section Long

variable {K : Type*} [Group K] {D : UniversalRootDatum K}

theorem noncomm_of_hasSL2Node {i : Fin D.rank} {E : Type} [Field E] [CharP E 2]
    (h : HasSL2Node D i E) :
    ∃ a ∈ rankOne D.rootGroup i, ∃ b ∈ rankOne D.rootGroup i, a * b ≠ b * a := by
  obtain ⟨φ, hinj, hU, hL⟩ := h
  have hu : φ (sl2Upper (1 : E)) ∈ rankOne D.rootGroup i :=
    le_sup_left (a := D.rootGroup (Pi.single i 1)) (hU 1)
  have hl : φ (sl2Lower (1 : E)) ∈ rankOne D.rootGroup i :=
    le_sup_right (b := D.rootGroup (-Pi.single i 1)) (hL 1)
  refine ⟨φ (sl2Upper 1 * sl2Lower 1), ?_, φ (sl2Upper 1), hu, fun hc => ?_⟩
  · rw [map_mul]
    exact mul_mem hu hl
  · apply sl2_upper_lower_not_commute (F := E)
    apply hinj
    simp only [map_mul, mul_assoc] at hc ⊢
    exact hc

end Long

section Main

variable {W : Type} [Group W] [Finite W] {L S₀ A₁ A₂ : Subgroup W} {F : Type} [Field F] [Finite F]
  [CharP F 2] {b c : F}

theorem CoverCtxOne.false_spinMinus_five (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (ctx : CoverCtxOne L S₀ A₁ A₂) {n : ℕ} (hF : Nat.card F = 2) (hn : 5 ≤ n)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedOmega (StatedQuadMinus n F b c))) :
    False := by
  have : Finite (spinGroup (quadMinus n F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  have hq := borelQuotient_spinMinus hirr (by omega : 4 ≤ n) e
  have hM : Nat.card F ^ 2 - 1 = 3 := by rw [hF]; norm_num
  rw [hM] at hq
  obtain ⟨π', h', hcov⟩ := ctx.cover hq
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  have : CharP (ShortField b c) 2 :=
    charP_of_injective_algebraMap (algebraMap F (ShortField b c)).injective 2
  have hF2 : 2 ≤ Nat.card F := by
    have := Finite.one_lt_card (α := F)
    omega
  have h4 : 4 ≤ Nat.card (ShortField b c) := by
    rw [SpinMinusClosed.card_shortField]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ Nat.card F ^ 2 := Nat.pow_le_pow_left hF2 2
  let s : Fin (n - 1) := ⟨n - 2, by omega⟩
  have hs : ¬ s.val + 1 < n - 1 := by simp only [s]; omega
  have hTS := hasTorusSL2_spinMinus_short hirr h4 hs
  have hlong : ∀ k : Fin (n - 1), k ≠ s → k.val + 1 < n - 1 := fun k hk => by
    have h1 := k.2
    have : k.val ≠ n - 2 := fun e => hk (Fin.ext e)
    omega
  have h6 : ∀ k : Fin (n - 1), k ≠ s →
      Nat.card (rankOne (minusDatum n hirr).rootGroup k) = 6 ∧
        ∃ a ∈ rankOne (minusDatum n hirr).rootGroup k,
          ∃ b ∈ rankOne (minusDatum n hirr).rootGroup k, a * b ≠ b * a := fun k hk =>
    ⟨spinMinus_long_card hirr hF (hlong k hk),
      noncomm_of_hasSL2Node (hasSL2Node_spinMinus_long hirr (hlong k hk))⟩
  let j₀ : Fin (n - 1) := ⟨0, by omega⟩
  let j₁ : Fin (n - 1) := ⟨1, by omega⟩
  let j₂ : Fin (n - 1) := ⟨2, by omega⟩
  have hj₀ : j₀.val + 1 < n - 1 := by simp only [j₀]; omega
  have hj₁ : j₁.val + 1 < n - 1 := by simp only [j₁]; omega
  have hj₂ : j₂.val + 1 < n - 1 := by simp only [j₂]; omega
  have hne : ∀ x y : Fin (n - 1), x.val ≠ y.val → x ≠ y := fun x y h e => h (by rw [e])
  have h0s : j₀ ≠ s := hne _ _ (by simp only [j₀, s]; omega)
  have h1s : j₁ ≠ s := hne _ _ (by simp only [j₁, s]; omega)
  have h2s : j₂ ≠ s := hne _ _ (by simp only [j₂, s]; omega)
  have h01 : j₀ ≠ j₁ := hne _ _ (by simp only [j₀, j₁]; omega)
  have h02 : j₀ ≠ j₂ := hne _ _ (by simp only [j₀, j₂]; omega)
  have hA01 : (minusDatum n hirr).cartan j₀ j₁ = -1 := cartanB_of_succ rfl
  have hA10 : (minusDatum n hirr).cartan j₁ j₀ = -1 := by
    change cartanB (n - 1) j₁ j₀ = -1
    rw [cartanB_of_pred (by rfl)]
    split_ifs with h
    · exfalso
      change 1 + 1 = n - 1 at h
      omega
    · rfl
  have hc02 : (minusDatum n hirr).cartan j₀ j₂ = 0 :=
    cartanB_of_far h02 (by simp only [j₀, j₂]; omega) (by simp only [j₀, j₂]; omega)
  have hc0s : (minusDatum n hirr).cartan j₀ s = 0 :=
    cartanB_of_far h0s (by simp only [j₀, s]; omega) (by simp only [j₀, s]; omega)
  have hc1s : (minusDatum n hirr).cartan j₁ s = 0 :=
    cartanB_of_far h1s (by simp only [j₁, s]; omega) (by simp only [j₁, s]; omega)
  have hperf := spinMinus_pair_perfect hirr h'.ct h'.extras hF
    (i := j₀) (j := j₁) (by simp only [j₀, j₁]) hj₁
  exact false_short_chain h' h4 hTS h6 (hasSL2Node_spinMinus_long hirr hj₀).hasOrderThree
    (hasSL2Node_spinMinus_long hirr hj₁).hasOrderThree
    (hasSL2Node_spinMinus_long hirr hj₂).hasOrderThree
    (hasSL2Node_spinMinus_long hirr hj₂).hasOrderThreeNC h0s h1s h2s h01 h02 hA01 hA10 hc02 hc0s
    hc1s hperf ctx.solv₁ ctx.solv₂ hcov

end Main

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
