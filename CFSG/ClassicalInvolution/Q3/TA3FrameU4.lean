module

public import CFSG.ClassicalInvolution.Q3.TA3FrameL4
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5U4Cls
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5U4Pairc
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L5U5

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Frame

open CFSG CFSG.ClassicalInvolution CFSG.Blueprint
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.CatFactsL4U4
  CFSG.Assembly.LowTwoRank StabU HBlocks TBlocks UnitaryOut UnitaryConj
open scoped MatrixGroups

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {R : GL (Fin 4) K} {t : K}
  (hR : uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) = t • bJ 1 1)

namespace FU4

theorem eq_one_of_bdK_smul {a b : SL(2, h.fixedField)} {c : K} (e : bdK h (a, b) = c • 1)
    (hb : b = 1 ∨ a = 1) : a = 1 ∧ b = 1 := by
  have hinj := Matrix.map_injective (h.fixedField.subtype).injective (m := Fin 2) (n := Fin 2)
  have ea := congrArg ul e
  have eb := congrArg lr e
  rw [bdK, ul_bd] at ea
  rw [bdK, lr_bd] at eb
  have hc1 : c = 1 := by
    rcases hb with rfl | rfl
    · have := congrFun (congrFun eb 0) 0
      simp [lr] at this
      exact this.symm
    · have := congrFun (congrFun ea 0) 0
      simp [ul] at this
      exact this.symm
  rw [hc1, one_smul] at ea eb
  have e1 : ∀ w : SL(2, h.fixedField), (w : Matrix (Fin 2) (Fin 2) h.fixedField).map
      h.fixedField.subtype = ul (1 : Matrix (Fin 4) (Fin 4) K) → w = 1 := fun w hw => by
    have h2 : (w : Matrix (Fin 2) (Fin 2) h.fixedField).map h.fixedField.subtype =
        ((1 : SL(2, h.fixedField)) : Matrix (Fin 2) (Fin 2) h.fixedField).map
          h.fixedField.subtype := by
      rw [hw, Matrix.SpecialLinearGroup.coe_one, Matrix.map_one _ (map_zero _) (map_one _)]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ul]
    exact Subtype.ext (hinj h2)
  refine ⟨e1 a ea, e1 b ?_⟩
  rw [eb]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ul, lr]

theorem bdK_eq_smul_of_mem {x : SL(2, h.fixedField) × SL(2, h.fixedField)}
    (hx : bdHomU h hR x ∈ scal p f K) : ∃ c : K, bdK h x = c • 1 := by
  obtain ⟨c, hc⟩ := val_of_mem_scal hx
  refine ⟨c, ?_⟩
  rw [← cP_bdHomU h hR x, cP, hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    ← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem injective_inlU :
    Function.Injective (((QuotientGroup.mk' (scal p f K)).comp (bdHomU h hR)).comp
      (MonoidHom.inl _ _)) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hx : bdHomU h hR (a, 1) ∈ scal p f K := (QuotientGroup.eq_one_iff _).mp ha
  obtain ⟨c, hc⟩ := bdK_eq_smul_of_mem h hR hx
  exact (eq_one_of_bdK_smul h hc (Or.inl rfl)).1

theorem injective_inrU :
    Function.Injective (((QuotientGroup.mk' (scal p f K)).comp (bdHomU h hR)).comp
      (MonoidHom.inr _ _)) := by
  rw [injective_iff_map_eq_one]
  intro b hb
  have hx : bdHomU h hR (1, b) ∈ scal p f K := (QuotientGroup.eq_one_iff _).mp hb
  obtain ⟨c, hc⟩ := bdK_eq_smul_of_mem h hR hx
  exact (eq_one_of_bdK_smul h hc (Or.inr rfl)).2

theorem isSimpleGroup_psu4 [Finite K] (hp : p.Prime) (hK : Nat.card K = (p ^ f) ^ 2) :
    IsSimpleGroup (StatedProj (StatedSU 4 (p ^ f) K)) := by
  have : Fact p.Prime := ⟨hp⟩
  exact ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p f hK 4 (by norm_num)
    (by simp)

end FU4

include hR in
theorem layerExcludesQ8_psu4_t2 (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (ht0 : t ≠ 0)
    {Y : unitarySU p f K 4}
    (hYR : ((Y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) =
      (R : Matrix (Fin 4) (Fin 4) K) * X1 (1 : K)) :
    LayerExcludesQ8 (StatedProj (StatedSU 4 (p ^ f) K)) (QuotientGroup.mk Y) := by
  have : Finite K := h.finite
  have h4 : 4 ≤ Nat.card h.fixedField := by rw [h.card_fixedField]; omega
  have := FU4.isSimpleGroup_psu4 h.prime (by rw [h.card, ← pow_mul, mul_comm])
  exact FL4.layerExcludesQ8_of_block
    (FL4.center_eq_bot_of_sl2 h4 _ (FU4.injective_inlU h hR)) h4
    ((QuotientGroup.mk' (scal p f K)).comp (bdHomU h hR)) (FU4.injective_inlU h hR)
    (FU4.injective_inrU h hR) (Q5U4.range_bdHomU_le_centralizer h hR hYR)
    (Subgroup.isPerfect_iff.mp (Q5U4.isPerfect_range_bdHomU h hR (by omega)))
    (fun M hM hMp => Q5U4.le_range_bdHomU_of_perfect h hR hp2 ht0 hYR hM hMp)
    (Q5U4.noQ8Fix_t2 h hp2 ht0 hR)

include h in
theorem layerExcludesQ8_psu4_pair (hp2 : p ≠ 2) {P : GL (Fin 4) K}
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)
    {Y : unitarySU p f K 4} {l : K} (hl0 : l ≠ 0) (hYP : cP P Y = X1 l) :
    LayerExcludesQ8 (StatedProj (StatedSU 4 (p ^ f) K)) (QuotientGroup.mk Y) := by
  have : Finite K := h.finite
  let H₀ : Subgroup (StatedProj (StatedSU 4 (p ^ f) K)) :=
    ((QuotientGroup.mk' (scal p f K)).comp (Q5U4.pairHom h hP)).range
  have : IsSimpleGroup H₀ := Q5U4.isSimpleGroup_range_pairHom h hP
  have : Group.IsPerfect H₀ := Q5U4.isPerfect_range_pairHom h hP
  have := FU4.isSimpleGroup_psu4 h.prime (by rw [h.card, ← pow_mul, mul_comm])
  exact FL4.layerExcludesQ8_of_simple (FL4.center_eq_bot_of_perfect H₀)
    (Q5U4.range_pairHom_le_centralizer h hP hYP)
    (fun M hM hMp => Q5U4.le_range_pairHom_of_perfect h hP hp2 hl0 hYP hM hMp)
    (Q5U4.noQ8Fix_pair h hP hp2)

omit h in
theorem layerExcludesQ8_u4 {X : Type} [Group X] (hp : p.Prime) (hp2 : p ≠ 2)
    (h8 : p ^ f % 8 ≠ 7) (h5 : 5 ≤ p ^ f) (hm : LieModel X .PSU 4 p f) (x : X)
    (hx : orderOf x = 2) : LayerExcludesQ8 X x := by
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := Q5L5U5.statedClassicalModel_of_lieModel_psu hm
  have hf : 1 ≤ f := Nat.pos_of_ne_zero fun h0 => by rw [h0, pow_zero] at h5; omega
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  refine LayerExcludesQ8.of_mulEquiv e₀ ?_
  have hz : orderOf (e₀ x) = 2 := by rw [MulEquiv.orderOf_eq]; exact hx
  rcases Q5U4.inv_split h hp2 h8 hz with ⟨Y, hY, hYY, h1, hm1⟩ | ⟨hq, Y, hY, hYY⟩
  · obtain ⟨R, s, hs0, -, hR, hYR⟩ := Q5U4.exists_frame_t2 h hp2 Y hYY h1 hm1
    rw [← hY]
    exact layerExcludesQ8_psu4_t2 h hR hp2 h5 hs0 hYR
  · obtain ⟨P, l, hP, hl, -, hYP⟩ := Q5U4.exists_pair_frame h hp2 hq Y hYY
    have hl0 : l ≠ 0 := by
      rintro rfl
      norm_num at hl
    rw [← hY]
    exact layerExcludesQ8_psu4_pair h hp2 hP hl0 hYP

end CFSG.ClassicalInvolution.Q3.TA3.Frame
