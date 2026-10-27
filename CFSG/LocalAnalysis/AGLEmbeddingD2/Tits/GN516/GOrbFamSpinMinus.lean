module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbEdgeLevi
public import CFSG.ClassicalInvolution.WeakCT.Standard
public import CFSG.ClassicalInvolution.WeakCT.TwistedSpinModel
public import CFSG.RankThree.PartOne.CTP.SpinMinusEven

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516.Fam

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.WeakCT CFSG.RankThree.PartOne.CTP

local instance finite_spinGroup_quadMinus_spinMinus {F : Type} [Field F] [Finite F] (n : ℕ)
    (b c : F) : Finite (spinGroup (quadMinus n F b c)) := by
  have : FiniteDimensional F (CliffordAlgebra (quadMinus n F b c)) :=
    finiteDimensional_cliffordAlgebra' _
  have : Finite (CliffordAlgebra (quadMinus n F b c)) := Module.finite_of_finite F
  infer_instance

private theorem cartanB_ne_zero_iff {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    cartanB m i j ≠ 0 ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  unfold cartanB
  simp only [Matrix.of_apply, if_neg hij]
  by_cases h : i.val + 1 = j.val ∨ j.val + 1 = i.val
  · rw [if_pos h]
    split_ifs <;> simp [h]
  · rw [if_neg h]
    simp [h]

private theorem minusDatum_cartan_path {n : ℕ} {F : Type} [Field F] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    ∀ i j : Fin (minusDatum n hirr).rank, i ≠ j →
      ((minusDatum n hirr).cartan i j ≠ 0 ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val) :=
  fun _ _ hij => cartanB_ne_zero_iff hij

private theorem edgeCond_comm {K : Type} [Group K] [Finite K] {D : UniversalRootDatum K}
    {H : Fin D.rank → Subgroup K} {u v : Fin D.rank} (h : Core.EdgeCond D H u v) :
    Core.EdgeCond D H v u := by
  unfold Core.EdgeCond at h ⊢
  rcases h with h | h | h
  · exact Or.inl (EdgeLev.edgeLevi_symm h)
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr h.symm)

private theorem edgeCond_of_succ {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hn : 4 ≤ n)
    (H : Fin (minusDatum n hirr).rank → Subgroup (spinGroup (quadMinus n F b c)))
    {u v : Fin (minusDatum n hirr).rank} (huv : u.val + 1 = v.val) :
    Core.EdgeCond (minusDatum n hirr) H u v := by
  have hvlt : v.val < n - 1 := v.isLt
  have hu : u.val + 1 < n - 1 := by omega
  by_cases hv : v.val + 1 < n - 1
  · obtain ⟨emb, hinj, h0, h1⟩ := exists_sl3_minus_even (n := n) b c huv hu hv
    have hgen : (blk F 0).range ⊔ (blk F 1).range = ⊤ := B12_sup_B23 (K := F)
    have key : emb.range = (emb.comp (blk F 0)).range ⊔ (emb.comp (blk F 1)).range := by
      rw [MonoidHom.range_comp, MonoidHom.range_comp, ← Subgroup.map_sup, hgen,
        MonoidHom.range_eq_map]
    have hr : emb.range = CFSG.LieType.CurtisTits.rankOne (minusDatum n hirr).rootGroup u ⊔
        CFSG.LieType.CurtisTits.rankOne (minusDatum n hirr).rootGroup v := by
      rw [key, h0, h1, rankOne_minusDatum_long hirr hu, rankOne_minusDatum_long hirr hv]
    exact Or.inl (EdgeLev.edgeLevi_of_sl3 emb hinj hr)
  · have hvt : v.val + 1 = (minusDatum n hirr).rank := by
      show v.val + 1 = n - 1
      omega
    have hut : u.val + 2 = (minusDatum n hirr).rank := by
      show u.val + 2 = n - 1
      omega
    have hdeg := EdgeLev.degree_ne_of_path (by show 3 ≤ n - 1; omega)
      (minusDatum n hirr).isFiniteType (minusDatum_cartan_path (n := n) hirr) hvt hut
    exact Or.inr (Or.inl hdeg.symm)

theorem edgeCond_spinMinus {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hn : 4 ≤ n)
    (H : Fin (minusDatum n hirr).rank → Subgroup (spinGroup (quadMinus n F b c)))
    (hrank : 3 ≤ (minusDatum n hirr).rank) (u v : Fin (minusDatum n hirr).rank)
    (hadj : (TauCeti.diagramGraph (minusDatum n hirr).cartan).Adj u v) :
    Core.EdgeCond (minusDatum n hirr) H u v := by
  obtain ⟨hne, hc⟩ := (minusDatum n hirr).isFiniteType.diagramGraph_adj_iff.1 hadj
  rcases (minusDatum_cartan_path (n := n) hirr u v hne).1 hc with h | h
  · exact edgeCond_of_succ hirr hn H h
  · exact edgeCond_comm (edgeCond_of_succ hirr hn H h)

end CFSG.AGLEmbeddingD2.Tits.GN516.Fam
