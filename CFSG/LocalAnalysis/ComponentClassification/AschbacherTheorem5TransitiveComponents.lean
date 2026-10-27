module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveQuotient

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped MatrixGroups

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace SectionSix

variable {G : Type} [Group G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem bar_D_normal (D : Subgroup G) : (bar D D).Normal := by
  have h : (D.subgroupOf (Subgroup.normalizer (D : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl
  exact h.map _ (toBar_surjective D)

theorem bar_le_bar_D_of_le {Y : Subgroup G} (hY : Y ≤ D) : bar D Y ≤ bar D D :=
  bar_mono D hY

theorem bar_D_le_normalizer {Y : Subgroup G} (hY : Y ≤ D)
    (hDY : D ≤ Subgroup.normalizer (Y : Set G)) :
    bar D D ≤ Subgroup.normalizer (bar D Y : Set (Bar D)) :=
  bar_le_normalizer hDY (hY.trans Subgroup.le_normalizer)

theorem map_quotientEmbedding_le_bar (D : Subgroup G)
    {K : Subgroup (D ⧸ aschbacherThm5OddCore D)} {Ā : Subgroup (D ⧸ aschbacherThm5OddCore D)}
    (hK : K ≤ Ā) : K.map (quotientEmbedding D) ≤ bar D (aschbacherThm5Preimage D Ā) := by
  rw [← map_quotientEmbedding]
  exact Subgroup.map_mono hK

theorem bar_factor_components [Finite G] (hyp : Hyp61 G D r Abar) (k : Fin r) :
    ∃ (m : ℕ) (K : Fin m → Subgroup (Bar D)), 0 < m ∧
      (∀ l, IsComponentOf (K l) ⊤ ∧ K l ≤ bar D (aschbacherThm5Preimage D (Abar k))) ∧
      (∀ l l', l ≠ l' → ∀ x ∈ K l, ∀ y ∈ K l', x * y = y * x) ∧
      ⨆ l, K l = bar D (aschbacherThm5Preimage D (Abar k)) := by
  obtain ⟨m, K, hm, hK, hcomm, hgen⟩ := hyp.hsemisimple k
  set ι := quotientEmbedding D
  have hι := quotientEmbedding_injective D
  set K' : Fin m → Subgroup (Bar D) := fun l => (K l).map ι
  have hK'le : ∀ l, K' l ≤ bar D (aschbacherThm5Preimage D (Abar k)) :=
    fun l => map_quotientEmbedding_le_bar D (hK l).1
  have hcomm' : ∀ l l', l ≠ l' → ∀ x ∈ K' l, ∀ y ∈ K' l', x * y = y * x := by
    rintro l l' hll' _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm l l' hll' x hx y hy]
  have hgen' : ⨆ l, K' l = bar D (aschbacherThm5Preimage D (Abar k)) := by
    rw [← map_quotientEmbedding, ← hgen, Subgroup.map_iSup]
  have hnormK : ∀ l, bar D (aschbacherThm5Preimage D (Abar k)) ≤
      Subgroup.normalizer (K' l : Set (Bar D)) := by
    intro l
    rw [← hgen']
    refine iSup_le fun l' => ?_
    by_cases hll' : l' = l
    · subst hll'
      exact Subgroup.le_normalizer
    · refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hcomm' l' l hll' x hx y hy).symm
  have hAD : aschbacherThm5Preimage D (Abar k) ≤ D := preimage_le D _
  have hDA : D ≤ Subgroup.normalizer (aschbacherThm5Preimage D (Abar k) : Set G) := by
    have hn := canonical_preimage_normal D Abar hyp.hcomm hyp.hgen k
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hAD).mp hn
  refine ⟨m, K', hm, fun l => ⟨⟨le_top, ?_, ?_⟩, hK'le l⟩, hcomm', hgen'⟩
  · refine IsSubnormal.step (hK'le l)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (hK'le l)).mpr (hnormK l)) ?_
    refine IsSubnormal.step (bar_mono D hAD)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (bar_mono D hAD)).mpr
        (bar_D_le_normalizer hAD hDA)) ?_
    have hDn := bar_D_normal D
    refine IsSubnormal.step le_top ?_ (IsSubnormal.refl ⊤)
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mpr
      (Subgroup.normalizer_eq_top_iff.mpr hDn).ge
  · exact Components.quasisimple_of_equiv
      ((K l).equivMapOfInjective ι hι).symm (hK l).2

theorem component_centralizes_twoGroup {X : Type*} [Group X] [Finite X] {L W : Subgroup X}
    (hL : IsComponentOf L ⊤) (hW : IsPGroup 2 W)
    (hLW : L ≤ Subgroup.normalizer (W : Set X)) : ⁅L, W⁆ = ⊥ := by
  rcases AschbacherComponentAction.component_arbitrary_action L W hL with hle | hbot
  · exfalso
    have hLW' : L ≤ W := hle.trans (Subgroup.le_normalizer_iff_commutator_le_right.mp hLW)
    have hL2 : IsPGroup 2 L := hW.to_le hLW'
    have : Group.IsPerfect L := ⟨hL.2.2.1⟩
    have : Nontrivial L := Quasisimple.nontrivial hL.2.2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact Group.IsPerfect.not_isNilpotent L hL2.isNilpotent
  · exact hbot

theorem thm3_one_or_three {X : Type} [Group X] [Finite X] {Q T S L : Subgroup X}
    (hT2 : IsPGroup 2 T) (hTS : T ≤ S) (hS2 : IsPGroup 2 S)
    (hL : IsComponentOf L ⊤) (hLQ : L ≤ Q) (hLT : ⁅L, T⁆ ≠ ⊥)
    (h : AschbacherTheorem3.Thm3Conclusion Q T S) :
    (IsCyclic T ∧
      (IsCyclic (S ⊓ Q : Subgroup X) ∨ AschbacherTheorem3.IsQuaternionTwoGroup (S ⊓ Q) ∨
        AschbacherTheorem3.IsDihedralTwoGroup (S ⊓ Q)) ∧
      (AschbacherTheorem3.IsDihedralTwoGroup S ∨ AschbacherTheorem3.IsSemidihedralTwoGroup S ∨
        AschbacherTheorem3.IsWreathedTwoGroup S)) ∨
    (∃ n : ℕ, 2 ≤ n ∧
      AschbacherTheorem3.oTwoPrime (Q ⊔ T) =
        pCoreOf 2 (Q ⊔ T) ⊔ AschbacherTheorem3.oTwoPrime Q ∧
      pCoreOf 2 (Q ⊔ T) ⊓ AschbacherTheorem3.oTwoPrime Q = ⊥ ∧
      ⁅pCoreOf 2 (Q ⊔ T), AschbacherTheorem3.oTwoPrime Q⁆ = ⊥ ∧
      IsElemAbelian 2 (pCoreOf 2 (Q ⊔ T)) ∧ Nat.card (pCoreOf 2 (Q ⊔ T)) = 2 ^ n ∧
      Nonempty (AschbacherTheorem3.oTwoPrime Q ≃* PSL(2, GaloisField 2 n))) := by
  have hW : ∀ W : Subgroup X, IsPGroup 2 W → T ≤ W →
      Q ⊔ T ≤ Subgroup.normalizer (W : Set X) → False := by
    intro W hW2 hTW hWN
    apply hLT
    have hbot := component_centralizes_twoGroup hL hW2 (hLQ.trans (le_sup_left.trans hWN))
    rw [eq_bot_iff, ← hbot]
    exact Subgroup.commutator_mono le_rfl hTW
  have hWS : CFSG.SignalizerFunctor.Helpers.relativeWeakClosure Q T S ≤ S :=
    CFSG.SignalizerFunctor.Helpers.relative_weak_closure_le Q T S
  have hTW : T ≤ CFSG.SignalizerFunctor.Helpers.relativeWeakClosure Q T S :=
    CFSG.SignalizerFunctor.Helpers.subgroup_le_relative_weak_closure Q T S hTS
  rcases h with h1 | h2 | h3 | h4 | h5
  · exact Or.inl h1
  · exact (hW T hT2 le_rfl h2).elim
  · exact Or.inr h3
  · obtain ⟨-, -, -, -, -, -, hWN, -, -⟩ := h4
    exact (hW _ (hS2.to_le hWS) hTW hWN).elim
  · exact (hW _ (hS2.to_le hWS) hTW h5.1).elim

end SectionSix

end CFSG.ComponentClassification.AschbacherTheorem5
