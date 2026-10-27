module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinCuts
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.Timmesfeld.Orders.ClassicalLinear
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall

public section

namespace CFSG.AGLEmbedding

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial

@[expose] def linBlockOrders (K : Type) : Set ℕ :=
  {N | ∃ m : ℕ, 2 ≤ m ∧ N = ordA (m - 1) (Nat.card K)}

variable {K : Type} [Field K]

namespace LeviBlock

theorem subsingleton_specialLinear_of_lt_two {m : ℕ} (hm : m < 2) :
    Subsingleton (SpecialLinearGroup (Fin m) K) := by
  refine ⟨fun A B => Subtype.ext (Matrix.ext fun i j => ?_)⟩
  have hi := i.isLt
  obtain rfl : m = 1 := by omega
  have hA := A.2
  have hB := B.2
  rw [Matrix.det_unique] at hA hB
  rw [Subsingleton.elim i default, Subsingleton.elim j default, hA, hB]

theorem isQuasisimple_or_isSolvable_specialLinear [Finite K] (m : ℕ) :
    CFSG.Open.IsQuasisimple (SpecialLinearGroup (Fin m) K) ∨
      Group.IsSolvable (SpecialLinearGroup (Fin m) K) := by
  classical
  by_cases hq : 2 ≤ m ∧ (3 ≤ m ∨ ∃ s : Finset K, s.card = 4)
  · left
    exact ⟨(CFSG.LinearGroups.special_linear_isPerfect hq.1 hq.2).commutator_eq_top,
      (CFSG.LinearGroups.linear_projective_simple hq.1 hq.2).2.1⟩
  · right
    rcases Nat.lt_or_ge m 2 with hm | hm
    · have := subsingleton_specialLinear_of_lt_two (K := K) hm
      infer_instance
    · have hm2 : m = 2 := by
        by_contra hne
        exact hq ⟨hm, Or.inl (by omega)⟩
      subst hm2
      have := Fintype.ofFinite K
      have hlt : Nat.card K < 4 := by
        by_contra hge
        obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
          (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
        exact hq ⟨le_rfl, Or.inr ⟨s, hs⟩⟩
      have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
      have := CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable
        K (by omega)
      exact Group.isSolvable_of_isSolvable_injective (f := SpecialLinearGroup.toGL)
        SpecialLinearGroup.toGL_injective

theorem two_le_of_isQuasisimple_specialLinear {m : ℕ}
    (h : CFSG.Open.IsQuasisimple (SpecialLinearGroup (Fin m) K)) : 2 ≤ m := by
  by_contra hm
  have := subsingleton_specialLinear_of_lt_two (K := K) (by omega : m < 2)
  have : IsSimpleGroup (SpecialLinearGroup (Fin m) K ⧸
    Subgroup.center (SpecialLinearGroup (Fin m) K)) := h.2
  obtain ⟨a, b, hab⟩ := (IsSimpleGroup.toNontrivial (G := SpecialLinearGroup (Fin m) K ⧸
    Subgroup.center (SpecialLinearGroup (Fin m) K))).exists_pair_ne
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (congrArg _ (Subsingleton.elim a b))

theorem card_specialLinear_quotient_center [Finite K] {m : ℕ} (hm : 1 ≤ m) :
    Nat.card (SpecialLinearGroup (Fin m) K ⧸ Subgroup.center (SpecialLinearGroup (Fin m) K)) =
      ordA (m - 1) (Nat.card K) := by
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := K) hm
  rw [← Nat.card_congr
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj m K).toEquiv] at h
  rw [h, ordA, Nat.sub_add_cancel hm, mul_comm (m - 1) m]

@[expose] noncomputable def slEquivToGLRange (m : ℕ) :
    SpecialLinearGroup (Fin m) K ≃*
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range :=
  MonoidHom.ofInjective SpecialLinearGroup.toGL_injective

theorem card_range_toGL_quotient_center [Finite K] {m : ℕ} (hm : 1 ≤ m) :
    Nat.card (↥(SpecialLinearGroup.toGL : SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range ⧸
      Subgroup.center ↥(SpecialLinearGroup.toGL :
        SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range) = ordA (m - 1) (Nat.card K) := by
  rw [← Nat.card_congr (QuotientGroup.congr _ _ (slEquivToGLRange (K := K) m)
    (map_center_mulEquiv (slEquivToGLRange m))).toEquiv,
    card_specialLinear_quotient_center hm]

theorem isQuasisimple_or_isSolvable_linBlockSL [Finite K] {n : ℕ} (I : Set ℕ) (a : Fin n) :
    CFSG.Open.IsQuasisimple ↥(linBlockSL K n I a) ∨ Group.IsSolvable ↥(linBlockSL K n I a) := by
  rcases isQuasisimple_or_isSolvable_specialLinear (K := K) (linBlockLen n I a) with h | h
  · exact Or.inl (isQuasisimple_of_mulEquiv (slEquivToGLRange _) h)
  · exact Or.inr (Group.isSolvable_of_surjective (f := (slEquivToGLRange (K := K)
      (linBlockLen n I a)).toMonoidHom) (slEquivToGLRange _).surjective)

end LeviBlock

open LeviBlock

theorem hasLeviBlocks_flagStabilizer [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n) (I : Set ℕ) :
    HasLeviBlocks ↥(LinearFlag.flagStabilizer n K I) (linBlockOrders K) := by
  refine ⟨n, fun a => GL (Fin (linBlockLen n I a)) K, fun _ => inferInstance,
    fun _ => inferInstance, linBlockSL K n I, linLeviHom K n I,
    isPGroup_ker_linLeviHom hn, pi_le_range_linLeviHom, commutator_range_linLeviHom_le,
    isQuasisimple_or_isSolvable_linBlockSL I, fun a ha => ?_⟩
  have h2 := two_le_of_isQuasisimple_specialLinear
    (isQuasisimple_of_mulEquiv (slEquivToGLRange (K := K) (linBlockLen n I a)).symm ha)
  exact ⟨linBlockLen n I a, h2, card_range_toGL_quotient_center (by omega)⟩

end CFSG.AGLEmbedding
