module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusResGroup
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinData
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGenArith

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

@[expose] def orthMinusBlockOrders (q : ℕ) : Set ℕ :=
  {N | (∃ k : ℕ, 2 ≤ k ∧ N = ordA (k - 1) q) ∨ ∃ m : ℕ, 2 ≤ m ∧ N = ordTwistedD m q}

namespace LeviBlock

theorem u38_not_mem_orthMinusBlockOrders {f : ℕ} :
    5515776 ∉ orthMinusBlockOrders (2 ^ f) := by
  rintro (⟨k, -, hk⟩ | ⟨m, -, hm⟩)
  · exact ordA_ne_u38 rfl hk.symm
  · exact ordTwistedD_ne_u38 rfl hm.symm

theorem u42_not_mem_orthMinusBlockOrders {f : ℕ} (hq : 2 ^ f ≠ 2) :
    25920 ∉ orthMinusBlockOrders (2 ^ f) := by
  rintro (⟨k, -, hk⟩ | ⟨m, -, hm⟩)
  · exact ordA_ne_u42 rfl hk.symm
  · exact hq ((ordTwistedD_eq_u42_iff rfl).1 hm.symm).2

theorem orthMinus_isQuasisimple_of_simple {S : Type} [Group S] [IsSimpleGroup S]
    (h : ∃ x y : S, x * y ≠ y * x) :
    CFSG.Open.IsQuasisimple S ∧ Subgroup.center S = ⊥ := by
  obtain ⟨⟨hP, hs, -⟩, hZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup h
  exact ⟨⟨hP.commutator_eq_top, hs⟩, hZ⟩

theorem orthMinus_not_isQuasisimple_of_comm {S : Type} [Group S] (h : ∀ x y : S, x * y = y * x) :
    ¬ CFSG.Open.IsQuasisimple S := by
  rintro ⟨-, hs⟩
  obtain ⟨a, b, hab⟩ := (IsSimpleGroup.toNontrivial (G := S ⧸ Subgroup.center S)).exists_pair_ne
  induction a using QuotientGroup.induction_on with | H x => ?_
  induction b using QuotientGroup.induction_on with | H y => ?_
  exact hab (QuotientGroup.eq.2 (Subgroup.mem_center_iff.2 fun z => h z _))

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

theorem comm_orthResDer_zero (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (x y : ↥(orthResDer K b c 0)) : x * y = y * x := by
  set e := orthMinusCommutatorCongr (minusTailZeroIsometry (b := b) (c := c))
  refine e.injective ?_
  rw [map_mul, map_mul]
  exact Subtype.ext (commute_of_mem_commutator_minusTailForm hirr (e x).2 (e y).2)

theorem isQuasisimple_or_isSolvable_orthResDer (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (m : ℕ) : CFSG.Open.IsQuasisimple ↥(orthResDer K b c m) ∨
      Group.IsSolvable ↥(orthResDer K b c m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact Or.inr (isSolvable_orthResDer_zero hirr)
  · obtain ⟨f, hK⟩ : ∃ f, Nat.card K = 2 ^ f := by
      have := Fintype.ofFinite K
      obtain ⟨n, -, hn⟩ := FiniteField.card K 2
      exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩
    obtain ⟨hs, hna, -⟩ := orthResDer_facts hK hm hirr
    exact Or.inl (orthMinus_isQuasisimple_of_simple hna).1

theorem card_orthResDer_quotient_center {f m : ℕ} (hK : Nat.card K = 2 ^ f)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hq : CFSG.Open.IsQuasisimple ↥(orthResDer K b c m)) :
    1 ≤ m ∧ Nat.card ↥(orthResDer K b c m) = ordTwistedD (m + 1) (2 ^ f) ∧
      Nat.card (↥(orthResDer K b c m) ⧸ Subgroup.center ↥(orthResDer K b c m)) =
        ordTwistedD (m + 1) (2 ^ f) := by
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · exact absurd hq (orthMinus_not_isQuasisimple_of_comm (comm_orthResDer_zero hirr))
    · exact h
  obtain ⟨hs, hna, hcard⟩ := orthResDer_facts hK hm hirr
  have hZ := (orthMinus_isQuasisimple_of_simple hna).2
  refine ⟨hm, hcard, ?_⟩
  rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot).toEquiv, hcard]

theorem card_orthResDer_of_sixty {m : ℕ} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hq : CFSG.Open.IsQuasisimple ↥(orthResDer K b c m))
    (h60 : Nat.card (↥(orthResDer K b c m) ⧸ Subgroup.center ↥(orthResDer K b c m)) = 60) :
    Nat.card ↥(orthResDer K b c m) = 60 := by
  obtain ⟨f, hK⟩ : ∃ f, Nat.card K = 2 ^ f := by
    have := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩
  obtain ⟨-, h1, h2⟩ := card_orthResDer_quotient_center hK hirr hq
  rw [h1, ← h2, h60]

omit [CharP K 2] in
theorem card_specialLinear_range_of_sixty {f k : ℕ} (hK : Nat.card K = 2 ^ f)
    (hq : CFSG.Open.IsQuasisimple ↥(Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin k) K →* GL (Fin k) K).range)
    (h60 : Nat.card (↥(Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin k) K →* GL (Fin k) K).range ⧸ Subgroup.center
        ↥(Matrix.SpecialLinearGroup.toGL :
          Matrix.SpecialLinearGroup (Fin k) K →* GL (Fin k) K).range) = 60) :
    Nat.card ↥(Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin k) K →* GL (Fin k) K).range = 60 := by
  have h2 := two_le_of_isQuasisimple_specialLinear
    (isQuasisimple_of_mulEquiv (slEquivToGLRange (K := K) k).symm hq)
  rw [card_range_toGL_quotient_center (by omega)] at h60
  obtain ⟨h1, h4⟩ := (ordA_eq_sixty_iff hK).1 h60
  obtain rfl : k = 2 := by omega
  rw [← Nat.card_congr (slEquivToGLRange (K := K) 2).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by omega), h4]
  decide

end LeviBlock

end CFSG.AGLEmbedding
