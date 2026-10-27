module

public import CFSG.LocalAnalysis.RankThreeUC.K518HAFam
public import CFSG.Timmesfeld.RankTwo.LevisBRankOne

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K518H

open CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbedding.ParabHub CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.CentralExt CFSG.LieType.CurtisTits CFSG.AGLEmbeddingD2.Tits.GN516

section SpinMinus

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
  (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

include hirr in
private theorem spinMinus_node_sl2
    (k : Fin (n - 1)) :
    ∃ (F' : Type) (_ : Field F') (_ : Finite F') (_ : CharP F' 2),
      Nonempty (Matrix.SpecialLinearGroup (Fin 2) F' ≃*
        ↥(rankOne (minusDatum n hirr).rootGroup k)) ∧
        Nat.card F ^ 2 - 1 ∣ Nat.card F' ^ 2 - 1 := by
  by_cases hk : k.val + 1 < n - 1
  · let e : Matrix.SpecialLinearGroup (Fin 2) F ≃*
        ↥(rankOne (minusDatum n hirr).rootGroup k) :=
      (MonoidHom.ofInjective
        (SpinFrame.longSL2_injective _ (succ_ne_of_lt n hk) true false)).trans
        (MulEquiv.subgroupCongr (rankOne_minusRootGroup_of_lt n hirr hk).symm)
    exact ⟨F, inferInstance, inferInstance, inferInstance, ⟨e⟩, dvd_rfl⟩
  · have := fact_shortField hirr
    have := finite_shortField (b := b) (c := c)
    have : CharP (ShortField b c) 2 :=
      charP_of_injective_algebraMap (algebraMap F (ShortField b c)).injective 2
    have h4 : 4 ≤ Nat.card (ShortField b c) := by
      rw [SpinMinusClosed.card_shortField]
      have h2 : 2 ≤ Nat.card F := Finite.one_lt_card
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ Nat.card F ^ 2 := Nat.pow_le_pow_left h2 2
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
    have hr : rankOne (minusDatum n hirr).rootGroup k = φ.range := by
      refine le_antisymm (sup_le (fun g hg => ?_) (fun g hg => ?_)) ?_
      · obtain ⟨t, rfl⟩ := (mem_minusRootGroup_single_iff hirr hk g).1 hg
        exact ⟨sl2Upper t, hx t⟩
      · obtain ⟨t, rfl⟩ := (mem_minusRootGroup_neg_single_iff hirr hk g).1 hg
        exact ⟨sl2Lower t, hy t⟩
      · rintro _ ⟨A, rfl⟩
        have hle : Subgroup.closure
            (Set.range (sl2Upper (k := ShortField b c)) ∪ Set.range sl2Lower) ≤
            (rankOne (minusDatum n hirr).rootGroup k).comap φ := by
          rw [Subgroup.closure_le]
          rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩)
          · exact le_sup_left (a := (minusDatum n hirr).rootGroup (Pi.single k 1))
              ((mem_minusRootGroup_single_iff hirr hk _).2 ⟨t, (hx t).symm⟩)
          · exact le_sup_right (b := (minusDatum n hirr).rootGroup (-Pi.single k 1))
              ((mem_minusRootGroup_neg_single_iff hirr hk _).2 ⟨t, (hy t).symm⟩)
        exact hle (Sp.mem_closure_sl2 A)
    refine ⟨ShortField b c, inferInstance, inferInstance, inferInstance,
      sl2_equiv_rankOne_of_range hinj hr, ?_⟩
    rw [SpinMinusClosed.card_shortField]
    exact sub_one_dvd_sq_sub_one _

end SpinMinus

theorem hasRkModel_of_model_pomegaMinus
    {Y : Type} [Group Y] {n f : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel Y .POmegaMinus n 2 f) : HasRkModel Y := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have : Finite (spinGroup (quadMinus n F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  exact hasRkModel_of_sl2_nodes (borelQuotient_spinMinus hirr (by omega) e) fun i =>
    spinMinus_node_sl2 hirr i

end CFSG.LocalAnalysis.RankThreeUC.S15.K518H

end
