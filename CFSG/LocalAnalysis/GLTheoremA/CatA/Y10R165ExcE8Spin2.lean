module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Spin

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Spin

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Steinberg.Adjoint CFSG.Blueprint.Chevalley CFSG.LieType.CurtisTits
  CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.RankThree.Classical2
open scoped MatrixGroups

@[expose] def spinFixW1 (K : Type) [Field K] : Subgroup (spinGroup (quadPlus 8 K)) where
  carrier := {g | ∀ v ∈ e8SpinW1 K, spinAction (quadPlus 8 K) g v = v}
  one_mem' := by intro v _; rw [map_one]; rfl
  mul_mem' := by
    intro a b ha hb v hv
    rw [map_mul, LinearEquiv.mul_apply, hb v hv, ha v hv]
  inv_mem' := by
    intro a ha v hv
    have h1 : spinAction (quadPlus 8 K) a (spinAction (quadPlus 8 K) a⁻¹ v) = v := by
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    exact (spinAction (quadPlus 8 K) a).injective (h1.trans (ha v hv).symm)

theorem longSL2_range_le_spinFixW1 {K : Type} [Field K] {i j : Fin 8} (hij : i ≠ j)
    (hi : (i : ℕ) < 4) (hj : (j : ℕ) < 4) (s t : Bool) :
    ((plusFrame 8 K (by norm_num)).longSL2 hij s t).range ≤ spinFixW1 K := by
  rw [CFSG.ClassicalInvolution.RouteD.Gaps.longSL2_range_eq_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨c, rfl⟩ v hv
    exact spinAction_longRoot_fixes_W1 hij hi hj s t (Multiplicative.toAdd c) hv
  · rintro _ ⟨c, rfl⟩ v hv
    exact spinAction_longRoot_fixes_W1 hij.symm hj hi (!t) (!s) (Multiplicative.toAdd c) hv

private theorem lt_four_rootIdxD {k : Fin 8} (hk : (k : ℕ) < 3) : (rootIdxD 8 k : ℕ) < 4 := by
  unfold rootIdxD
  rw [if_pos (show k.val + 1 < 8 by omega)]
  omega

private theorem lt_four_rootIdxD' {k : Fin 8} (hk : (k : ℕ) < 3) : (rootIdxD' 8 k : ℕ) < 4 := by
  unfold rootIdxD'
  rw [dif_pos (show k.val + 1 < 8 by omega)]
  simp only [Fin.val_mk]
  omega

private theorem rootD_le_spinFixW1 {K : Type} [Field K] {k : Fin 8} (hk : (k : ℕ) < 3) :
    (rootD (n := 8) K (by norm_num) k).range ≤ spinFixW1 K := by
  have h := longSL2_range_le_spinFixW1 (K := K) (rootIdxD_ne 8 (by omega) k)
    (lt_four_rootIdxD hk) (lt_four_rootIdxD' hk) true (rootSignD 8 k)
  rw [CFSG.ClassicalInvolution.RouteD.Gaps.longSL2_range_eq_sup] at h
  exact le_trans le_sup_left h

private theorem negRootD_le_spinFixW1 {K : Type} [Field K] {k : Fin 8} (hk : (k : ℕ) < 3) :
    (negRootD (n := 8) K (by norm_num) k).range ≤ spinFixW1 K := by
  have h := longSL2_range_le_spinFixW1 (K := K) (rootIdxD_ne 8 (by omega) k).symm
    (lt_four_rootIdxD' hk) (lt_four_rootIdxD hk) (!rootSignD 8 k) false
  rw [CFSG.ClassicalInvolution.RouteD.Gaps.longSL2_range_eq_sup] at h
  exact le_trans le_sup_left h

theorem e8D8Chain_le_spinFixW1 {K : Type} [Field K] [Finite K] {k : Fin 8}
    (hk : (k : ℕ) < 3) :
    e8D8Chain K k ≤ (spinFixW1 K).map (e8D8SpinHom K) := by
  rw [← e8D8SpinHom_rankOne K k]
  refine Subgroup.map_mono ?_
  change CFSG.LieType.CurtisTits.rankOne (plusDatum 8 K (by norm_num)).rootGroup k ≤ spinFixW1 K
  refine sup_le ?_ ?_
  · change plusRootGroup 8 K (by norm_num) (Pi.single k 1) ≤ spinFixW1 K
    rw [plusRootGroup_single (by norm_num) k]
    exact rootD_le_spinFixW1 hk
  · change plusRootGroup 8 K (by norm_num) (-Pi.single k 1) ≤ spinFixW1 K
    rw [plusRootGroup_neg_single (by norm_num) k]
    exact negRootD_le_spinFixW1 hk

private theorem e8D4Root_four_eq : e8D4Root 4 = e8D8Root := by decide
private theorem e8D4Root_five_eq : e8D4Root 5 = Pi.single (e8D8Node 1) 1 := by decide
private theorem e8D4Root_six_eq : e8D4Root 6 = Pi.single (e8D8Node 2) 1 := by decide

theorem e8D4Perp_rootCorrespondence (K : Type) [Field K] [Finite K] [CharP K 2] :
    ((plusFrame 8 K (by norm_num)).longSL2 (i := 2) (j := 3) (by decide) true true).range.map
        (e8D8SpinHom K) = CFSG.HardMathSupport.Lang.AnisoE8.rootPairE8 K (e8D4Root 7) := by
  classical
  set c : Fin (Tag.rank .E8) → ℤ := Pi.single (e8D8Node 7) 1 with hcdef
  have hcroot : IsRoot .E8 c := isRoot_single _ _
  have hchain : e8D8Chain K 7 = (e8Datum K).rootGroup c ⊔ (e8Datum K).rootGroup (-c) :=
    e8D8Chain_ne_zero_eq (by decide)
  have hβ : wordReflect .E8 ([3, 2, 4, 3, 5, 4, 6, 5].map e8D8Node) c = e8D4Root 7 := by
    rw [hcdef]
    decide +kernel
  have hle : ((plusFrame 8 K (by norm_num)).longSL2 (i := 2) (j := 3) (by decide)
        true true).range.map (e8D8SpinHom K) ≤
      CFSG.HardMathSupport.Lang.AnisoE8.rootPairE8 K (e8D4Root 7) :=
    map_longSL2_le_of_word (K := K) (by norm_num) (fun k => e8D8SpinHom_rankOne K k)
      (fun k hk => e8D8SpinHom_weylD K hk) [3, 2, 4, 3, 5, 4, 6, 5] (by decide) 7 (by decide)
      true true (by decide +kernel) hcroot hchain hβ
  have hcardL : Nat.card ↥(((plusFrame 8 K (by norm_num)).longSL2 (i := 2) (j := 3)
        (by decide) true true).range.map (e8D8SpinHom K)) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [Subgroup.card_map_of_injective (e8D8SpinHom_injective K), MonoidHom.range_eq_map,
      Subgroup.card_map_of_injective
        (CFSG.LieType.Steinberg.SpinFrame.longSL2_injective (plusFrame 8 K (by norm_num))
          (by decide) true true),
      Subgroup.card_top]
  have hcardR : Nat.card ↥(CFSG.HardMathSupport.Lang.AnisoE8.rootPairE8 K (e8D4Root 7)) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
    have hconj := map_conj_weylWordElt_rootPair (K := K) (τ := .E8)
      ([3, 2, 4, 3, 5, 4, 6, 5].map e8D8Node) hcroot
    rw [hβ] at hconj
    rw [show CFSG.HardMathSupport.Lang.AnisoE8.rootPairE8 K (e8D4Root 7) =
        (e8Datum K).rootGroup (e8D4Root 7) ⊔ (e8Datum K).rootGroup (-e8D4Root 7) from rfl,
      ← hconj, Subgroup.card_map_of_injective (MulEquiv.injective _), ← hchain]
    obtain ⟨ρ, hρ, -⟩ := exists_e8D8_family_param K
    rw [← (hρ 7).2, MonoidHom.range_eq_map, Subgroup.card_map_of_injective (hρ 7).1,
      Subgroup.card_top]
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [hcardR, hcardL]))

theorem e8D4Perp_le_map_spinFixW1 (K : Type) [Field K] [Finite K] [CharP K 2] :
    e8D4Perp K ≤ (spinFixW1 K).map (e8D8SpinHom K) := by
  rw [e8D4Perp_eq]
  refine iSup_le fun j => ?_
  fin_cases j
  · show CFSG.HardMathSupport.Lang.AnisoE8.rootPairE8 K (e8D4Root 4) ≤ _
    rw [e8D4Root_four_eq, ← e8D8Chain_zero_eq]
    exact e8D8Chain_le_spinFixW1 (by decide)
  · show CFSG.HardMathSupport.Lang.AnisoE8.rootPairE8 K (e8D4Root 5) ≤ _
    rw [e8D4Root_five_eq, ← e8D8Chain_ne_zero_eq (by decide)]
    exact e8D8Chain_le_spinFixW1 (by decide)
  · show CFSG.HardMathSupport.Lang.AnisoE8.rootPairE8 K (e8D4Root 6) ≤ _
    rw [e8D4Root_six_eq, ← e8D8Chain_ne_zero_eq (by decide)]
    exact e8D8Chain_le_spinFixW1 (by decide)
  · show CFSG.HardMathSupport.Lang.AnisoE8.rootPairE8 K (e8D4Root 7) ≤ _
    rw [← e8D4Perp_rootCorrespondence K]
    exact Subgroup.map_mono
      (longSL2_range_le_spinFixW1 (i := 2) (j := 3) (by decide) (by decide) (by decide) true true)

theorem e8D4Perp_fixes_e8SpinW1 (K : Type) [Field K] [Finite K] [CharP K 2]
    {y : ↥(⨆ k, e8D8Chain K k)} (hy : (y : adjointGroup .E8 K) ∈ e8D4Perp K)
    {v : Fin 8 ⊕ Fin 8 → K} (hv : v ∈ e8SpinW1 K) :
    ((e8D8Theta K y : ↥(orthDerived (quadPlus 8 K))) :
      (Fin 8 ⊕ Fin 8 → K) ≃ₗ[K] (Fin 8 ⊕ Fin 8 → K)) v = v := by
  have hx' : (y : adjointGroup .E8 K) ∈ (spinFixW1 K).map (e8D8SpinHom K) :=
    e8D4Perp_le_map_spinFixW1 K hy
  obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.mp hx'
  have hsub : y = e8D8Equiv K w := Subtype.ext (by rw [coe_e8D8Equiv]; exact hwy.symm)
  rw [hsub, coe_e8D8Theta_e8D8Equiv]
  exact hw v hv

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Spin
