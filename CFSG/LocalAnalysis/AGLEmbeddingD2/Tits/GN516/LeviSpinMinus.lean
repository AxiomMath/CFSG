module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviNode
public import CFSG.Timmesfeld.RankTwo.LevisBRankOne

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.Steinberg CFSG.LieType.Steinberg.CentralExt
  CFSG.LieType.CurtisTits

section SpinMinus

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
  (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

include hirr in
theorem nodeLevi_spinMinus_long {k : Fin (n - 1)} (hk : k.val + 1 < n - 1) :
    NodeLevi (minusDatum n hirr) k := by
  let e : Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥(rankOne (minusDatum n hirr).rootGroup k) :=
    (MonoidHom.ofInjective (SpinFrame.longSL2_injective _ (succ_ne_of_lt n hk) true false)).trans
      (MulEquiv.subgroupCongr (rankOne_minusRootGroup_of_lt n hirr hk).symm)
  exact nodeLevi_of_equiv_sl2 e

include hirr in
theorem nodeLevi_spinMinus_short
    {k : Fin (n - 1)} (hk : ¬k.val + 1 < n - 1) :
    NodeLevi (minusDatum n hirr) k := by
  have := fact_shortField hirr
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
  exact nodeLevi_of_range_sl2 hinj hr

theorem nodeLevi_spinMinus
    (i : Fin (n - 1)) : NodeLevi (minusDatum n hirr) i := by
  by_cases hk : i.val + 1 < n - 1
  · exact nodeLevi_spinMinus_long hirr hk
  · exact nodeLevi_spinMinus_short hirr hk

end SpinMinus

end CFSG.AGLEmbeddingD2.Tits.GN516
