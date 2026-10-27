module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverModel
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinData
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGenArith
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups
import CFSG.Timmesfeld.Orders.ClassicalOmega
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitMaximalFamilyCharacter

public section

namespace CFSG.AGLEmbedding

open Matrix QuadraticMap CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LieType.Universal.Spin

@[expose] def plusBlockOrders (q : ℕ) : Set ℕ :=
  {N | (∃ k, 2 ≤ k ∧ N = ordA (k - 1) q) ∨ ∃ m, 3 ≤ m ∧ N = ordD m q}

theorem u38_not_mem_plusBlockOrders {q f : ℕ} (hq : q = 2 ^ f) : 5515776 ∉ plusBlockOrders q := by
  rintro (⟨k, -, hk⟩ | ⟨m, -, hm⟩)
  · exact ordA_ne_u38 hq hk.symm
  · exact ordD_ne_u38 hq hm.symm

theorem u42_not_mem_plusBlockOrders {q f : ℕ} (hq : q = 2 ^ f) : 25920 ∉ plusBlockOrders q := by
  rintro (⟨k, -, hk⟩ | ⟨m, -, hm⟩)
  · exact ordA_ne_u42 hq hk.symm
  · exact ordD_ne_u42 hq hm.symm

theorem eq_four_of_sixty_mem_plusBlockOrders {q f : ℕ} (hq : q = 2 ^ f)
    (h : 60 ∈ plusBlockOrders q) : q = 4 := by
  rcases h with ⟨k, -, hk⟩ | ⟨m, -, hm⟩
  · exact ((ordA_eq_sixty_iff hq).1 hk.symm).2
  · exact absurd hm.symm (ordD_ne_sixty hq)

namespace LeviBlock

variable {K : Type} [Field K]

theorem isQuasisimple_or_isSolvable_rangeSL [Finite K] (k : ℕ) :
    CFSG.Open.IsQuasisimple ↥(SpecialLinearGroup.toGL : SpecialLinearGroup (Fin k) K →*
      GL (Fin k) K).range ∨
    Group.IsSolvable ↥(SpecialLinearGroup.toGL : SpecialLinearGroup (Fin k) K →*
      GL (Fin k) K).range := by
  rcases isQuasisimple_or_isSolvable_specialLinear (K := K) k with h | h
  · exact Or.inl (isQuasisimple_of_mulEquiv (slEquivToGLRange _) h)
  · exact Or.inr (Group.isSolvable_of_surjective (f := (slEquivToGLRange (K := K) k).toMonoidHom)
      (slEquivToGLRange _).surjective)

theorem card_rangeSL_quotient_center [Finite K] {k : ℕ}
    (h : CFSG.Open.IsQuasisimple ↥(SpecialLinearGroup.toGL : SpecialLinearGroup (Fin k) K →*
      GL (Fin k) K).range) :
    Nat.card (↥(SpecialLinearGroup.toGL : SpecialLinearGroup (Fin k) K →* GL (Fin k) K).range ⧸
      Subgroup.center ↥(SpecialLinearGroup.toGL : SpecialLinearGroup (Fin k) K →*
        GL (Fin k) K).range) ∈ plusBlockOrders (Nat.card K) := by
  have h2 := two_le_of_isQuasisimple_specialLinear
    (isQuasisimple_of_mulEquiv (slEquivToGLRange (K := K) k).symm h)
  exact Or.inl ⟨k, h2, card_range_toGL_quotient_center (by omega)⟩

theorem card_plusElementary [Finite K] [CharP K 2] {n : ℕ} (hn : 3 ≤ n) :
    (Nat.card (orthElementaryGroup (quadPlus n K)) : ℤ) =
      (Nat.card K : ℤ) ^ (n * (n - 1)) * ((Nat.card K : ℤ) ^ n - 1) *
        ∏ i ∈ Finset.Icc 1 (n - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hn0 : 0 < m + 1 := by omega
  have hnd := nondegenerate_polarBilin_quadPlus (m + 1) K
  have hidx := CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_eq_two_mul hnd
    (plusPair_orth (K := K) (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (by simp [Fin.ext_iff]))
    (regular_quadPlus (by omega)).2
    (orthogonalGroup_le_closure_of_two_eq_zero (plusFamily_orth hn0) hnd CharTwo.two_eq_zero
      (fun x hx _ => eq_zero_of_mem_tailSpace_plusFamily hn0 hx)
      (fun x hx hx0 => absurd (eq_zero_of_mem_tailSpace_plusFamily hn0 hx) hx0) (by omega))
  have hO := (CFSG.Timmesfeld.ClassicalOrders.card_quadPlus (K := K) m).2
  rw [hidx] at hO
  push_cast at hO
  change (Nat.card (elementaryGroup (quadPlus (m + 1) K)) : ℤ) = _
  rw [Nat.add_sub_cancel, show (m + 1) * m = m * (m + 1) by ring]
  linarith

theorem isQuasisimple_plusElementary [CharP K 2] {m : ℕ} (hm : 3 ≤ m) :
    CFSG.Open.IsQuasisimple ↥(orthElementaryGroup (quadPlus m K)) ∧
      Subgroup.center ↥(orthElementaryGroup (quadPlus m K)) = ⊥ := by
  have : IsSimpleGroup (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedOmega
      (CFSG.Assembly.LowTwoRank.StatedQuadPlus m K))) :=
    isSimpleGroup_statedProj_statedOmega_quadPlus hm
  have hs : IsSimpleGroup ↥(orthElementaryGroup (quadPlus m K)) :=
    (statedProjOmegaPlusEquiv (K := K) hm).symm.isSimpleGroup
  have htop : (⊤ : Subgroup ↥(orthElementaryGroup (quadPlus m K))).map
      (orthElementaryGroup (quadPlus m K)).subtype = orthElementaryGroup (quadPlus m K) := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hperf : commutator ↥(orthElementaryGroup (quadPlus m K)) = ⊤ := by
    apply Subgroup.map_injective (orthElementaryGroup (quadPlus m K)).subtype_injective
    rw [commutator_def, Subgroup.map_commutator, htop, commutator_orthElementaryGroup hm]
  have hZ : Subgroup.center ↥(orthElementaryGroup (quadPlus m K)) = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(orthElementaryGroup (quadPlus m K)))
        with h | h
    · exact h
    · exfalso
      have hc : commutator ↥(orthElementaryGroup (quadPlus m K)) = ⊥ := by
        rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        exact Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top x) y
      rw [hperf] at hc
      exact top_ne_bot hc
  refine ⟨⟨hperf, ?_⟩, hZ⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup

theorem card_plusElementary_quotient_center [Finite K] [CharP K 2] {m f : ℕ} (hm : 3 ≤ m)
    (hK : Nat.card K = 2 ^ f) :
    Nat.card (↥(orthElementaryGroup (quadPlus m K)) ⧸
      Subgroup.center ↥(orthElementaryGroup (quadPlus m K))) = ordD m (Nat.card K) := by
  rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq (isQuasisimple_plusElementary hm).2).trans
    QuotientGroup.quotientBot).toEquiv]
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · have := (Finite.one_lt_card : 1 < Nat.card K); rw [hK] at this; simp at this
    · exact h
  have hev : Even (Nat.card K) := by rw [hK]; exact (Nat.even_pow' (by omega)).mpr even_two
  have hodd : Odd (Nat.card K ^ m - 1) := by
    have h1 : 1 ≤ Nat.card K ^ m := Nat.one_le_pow _ _ hq1
    have h2 : Even (Nat.card K ^ m) := (Nat.even_pow' (by omega)).mpr hev
    exact Nat.Even.sub_odd h1 h2 odd_one
  have hgcd : Nat.gcd 4 (Nat.card K ^ m - 1) = 1 :=
    Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd) |>.gcd_eq_one
  rw [ordD, hgcd, Nat.div_one]
  have h := card_plusElementary (K := K) hm
  have hcast : ((Nat.card K ^ (m * (m - 1)) * (Nat.card K ^ m - 1) *
      ∏ i ∈ Finset.Icc 1 (m - 1), (Nat.card K ^ (2 * i) - 1) : ℕ) : ℤ) =
      (Nat.card K : ℤ) ^ (m * (m - 1)) * ((Nat.card K : ℤ) ^ m - 1) *
        ∏ i ∈ Finset.Icc 1 (m - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
    push_cast [Nat.cast_sub (Nat.one_le_pow _ _ hq1)]
    congr 1
  exact_mod_cast h.trans hcast.symm

end LeviBlock

end CFSG.AGLEmbedding
