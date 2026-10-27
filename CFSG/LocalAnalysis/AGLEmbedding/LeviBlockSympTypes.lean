module

import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall
import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionTypeExceptions
import CFSG.Monster.Existence.Compat.Sp8
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Universal.Symplectic
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherParabolicData

public section

namespace CFSG.AGLEmbedding.LeviBlock

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.Open
open SymplecticHigher (flagStabilizer)

variable {K : Type} [Field K]

theorem spFlag_card_eq_two_pow [Finite K] [CharP K 2] : ∃ f, 1 ≤ f ∧ Nat.card K = 2 ^ f := by
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem spFlag_card_eq_two_or_four_le [Finite K] [CharP K 2] :
    Nat.card K = 2 ∨ 4 ≤ Nat.card K := by
  obtain ⟨f, hf, hq⟩ := spFlag_card_eq_two_pow (K := K)
  rcases Nat.lt_or_ge f 2 with h | h
  · left
    rw [hq, show f = 1 by omega, pow_one]
  · right
    rw [hq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h

omit [Field K] in
theorem spFlag_exists_finset_four [Finite K] (h : 4 ≤ Nat.card K) :
    ∃ s : Finset K, s.card = 4 := by
  have := Fintype.ofFinite K
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h)
  exact ⟨s, hs⟩

theorem spFlag_isQuasisimple_SL [Finite K] {k : ℕ} (hk : 2 ≤ k) (h : 3 ≤ k ∨ 4 ≤ Nat.card K) :
    CFSG.Open.IsQuasisimple (SpecialLinearGroup (Fin k) K) := by
  have h' : 3 ≤ k ∨ ∃ s : Finset K, s.card = 4 := h.imp_right spFlag_exists_finset_four
  exact ⟨Group.isPerfect_def.mp (CFSG.LinearGroups.special_linear_isPerfect hk h'),
    (CFSG.LinearGroups.linear_projective_simple hk h').2.1⟩

theorem spFlag_card_SL_center [Finite K] {k : ℕ} (hk : 1 ≤ k) :
    Nat.card (SpecialLinearGroup (Fin k) K ⧸ Subgroup.center (SpecialLinearGroup (Fin k) K)) =
      ordA (k - 1) (Nat.card K) := by
  rw [Nat.card_congr (projectiveSpecialLinearGroupEquivStatedProj k K).toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL hk, ordA, Nat.sub_add_cancel hk,
    mul_comm (k - 1) k]

theorem spFlag_isSolvable_SL [Finite K] {k : ℕ} (h : k ≤ 1 ∨ (k = 2 ∧ Nat.card K = 2)) :
    Group.IsSolvable (SpecialLinearGroup (Fin k) K) := by
  rcases h with h | ⟨rfl, hK⟩
  · refine Group.isSolvable_of_comm fun a b => Subtype.ext ?_
    rcases Nat.lt_or_ge k 1 with h0 | h1
    · ext i j
      exact absurd i.isLt (by omega)
    · obtain rfl : k = 1 := by omega
      ext i j
      rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_one]
      ring
  · have : Group.IsSolvable (GL (Fin 2) K) :=
      CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable K
        (Or.inl hK)
    exact Group.isSolvable_of_isSolvable_injective Matrix.SpecialLinearGroup.toGL_injective

theorem spFlag_isQuasisimple_Sp [Finite K] [CharP K 2] {m : ℕ} (hm : 1 ≤ m)
    (h : 4 ≤ Nat.card K ∨ 3 ≤ m) : CFSG.Open.IsQuasisimple (StatedSp m K) := by
  have hK : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ m) ∨
      (Nat.card K = 2 ∧ 3 ≤ m) := by
    rcases h with h | h
    · exact Or.inl (Or.inr h)
    · rcases spFlag_card_eq_two_or_four_le (K := K) with h2 | h4
      · exact Or.inr (Or.inr ⟨h2, h⟩)
      · exact Or.inl (Or.inr h4)
  have hq := CFSG.LieType.Universal.Symplectic.isQuasisimple m K hm hK
  exact ⟨Group.isPerfect_def.mp hq.1, hq.2.1⟩

theorem spFlag_card_Sp_center [Finite K] [CharP K 2] (m : ℕ) :
    Nat.card (StatedSp m K ⧸ Subgroup.center (StatedSp m K)) = ordBC m (Nat.card K) := by
  obtain ⟨f, hf, hq⟩ := spFlag_card_eq_two_pow (K := K)
  have hgcd : Nat.gcd 2 (Nat.card K - 1) = 1 := by
    rw [hq]
    have : 2 ≤ 2 ^ f := le_self_pow₀ (by norm_num) (by omega)
    obtain ⟨c, hc⟩ : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    exact Nat.coprime_two_left.mpr ⟨c - 1, by omega⟩
  rw [Nat.card_congr (CFSG.LieType.Universal.Symplectic.centerQuotientEquiv m K).toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo, ordBC, hgcd, Nat.div_one,
    sq]

theorem spFlag_isSolvable_Sp [Finite K] {m : ℕ} (h : m = 0 ∨ (m = 1 ∧ Nat.card K = 2)) :
    Group.IsSolvable (StatedSp m K) := by
  rcases h with rfl | ⟨rfl, hK⟩
  · refine Group.isSolvable_of_comm fun a b => Subtype.ext (Units.ext ?_)
    ext i
    exact i.elim (fun i => i.elim0) fun i => i.elim0
  · let e : Fin 1 ⊕ Fin 1 ≃ Fin 2 := finSumFinEquiv
    let φ : StatedSp 1 K →* GL (Fin 2) K :=
      (Units.mapEquiv (Matrix.reindexAlgEquiv K K e).toMulEquiv).toMonoidHom.comp
        (StatedSp 1 K).subtype
    have hφ : Function.Injective φ := fun x y h =>
      Subtype.ext ((Units.mapEquiv (Matrix.reindexAlgEquiv K K e).toMulEquiv).injective h)
    have : Group.IsSolvable (GL (Fin 2) K) :=
      CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable K
        (Or.inl hK)
    exact Group.isSolvable_of_isSolvable_injective hφ

theorem spFlag_spFour_comm [Finite K] (hK : Nat.card K = 2) :
    CFSG.Open.IsQuasisimple (commutator (StatedSp 2 K)) ∧
      Nat.card (commutator (StatedSp 2 K) ⧸ Subgroup.center (commutator (StatedSp 2 K))) =
        360 := by
  let e : StatedSp 2 K ≃* CFSG.ComponentClassification.PresentationLocal.sympFour :=
    (CFSG.Monster.Existence.Compat.statedSpEquiv 2 K).trans
      ((CFSG.Monster.Existence.Compat.sympMapEquiv
        (CFSG.Monster.Existence.Compat.ringEquivZMod2 hK)).trans
        (MulEquiv.ofBijective CFSG.ComponentClassification.StandardRecognition.symplecticToSympFour
          CFSG.ComponentClassification.StandardRecognition.symplecticToSympFour_bijective))
  have hmap : (commutator (StatedSp 2 K)).map e.toMonoidHom = commutator _ := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr e.surjective]
  let e6 : commutator (StatedSp 2 K) ≃* alternatingGroup (Fin 6) :=
    (e.subgroupMap _).trans ((MulEquiv.subgroupCongr hmap).trans
      CFSG.ComponentClassification.PresentationLocal.commutatorEquivAlternating)
  have h6 : 5 ≤ Nat.card (Fin 6) := by simp
  have hA := CFSG.ComponentClassification.CatalogueBAlternating.alternating_quasisimple h6
  refine ⟨isQuasisimple_of_mulEquiv e6.symm hA, ?_⟩
  rw [Nat.card_congr (QuotientGroup.congr _ _ e6 (map_center_mulEquiv e6)).toEquiv]
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup h6
  have hZ : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (alternatingGroup (Fin 6))) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := exists_noncomm_centerQuotient hA
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
      rw [(QuotientGroup.eq_one_iff g).mpr (h ▸ Subgroup.mem_top g), one_mul, mul_one] at hab
      exact hab rfl
  rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hZ).toEquiv,
    Nat.card_congr (QuotientGroup.quotientBot).toEquiv, nat_card_alternatingGroup]
  simp [Nat.factorial]

end CFSG.AGLEmbedding.LeviBlock
