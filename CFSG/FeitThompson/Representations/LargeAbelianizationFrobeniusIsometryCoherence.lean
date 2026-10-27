module

public import CFSG.FeitThompson.Representations.CentralLayerCoherenceExtension
import CFSG.FeitThompson.Local.ChiefSectionsCentralNilpotent
public import CFSG.FeitThompson.Local.ChiefFactorCentralizationCentralSeries
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup
import CFSG.FeitThompson.Representations.SolvableFrobeniusKernelInducedIndexDegree

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open NormalInducedFamily
open scoped Pointwise

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G] {H E : Subgroup L}

omit [Fintype L] [Group G] [Fintype G] in
theorem relIndex_le_relIndex_of_le [Finite L] {A B : Subgroup L} (hBA : B ≤ A) :
    A.relIndex H ≤ B.relIndex H :=
  Subgroup.relIndex_le_of_le_left hBA
    (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := B.subgroupOf H))).ne'

theorem isCoherent_of_isCoherent_restrictBaseline_self {S : Set (L → ℂ)}
    (τ : charSpanZero S →+ virtualChars G)
    (h : IsCoherent S (restrictBaseline (subset_refl S) τ)) : IsCoherent S τ := by
  refine IsCoherent.congr_baseline (fun f => ?_) h
  rw [restrictBaseline_apply]
  congr 1

private theorem isCoherent_kerLayerIndFam_bot_aux [H.Normal] [Group.IsNilpotent ↥H]
    (hodd : Odd (Nat.card L)) (hH : H ≠ ⊥)
    (hmul : (H : Set L) * (E : Set L) = Set.univ) (hinf : H ⊓ E = ⊥)
    (hC : ∀ u ∈ E, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥)
    (τ : charSpanZero (kerLayerIndFam (⊥ : Subgroup L) H) →+ virtualChars G)
    (hτiso : ∀ f g : charSpanZero (kerLayerIndFam (⊥ : Subgroup L) H),
      cfInner (τ f : G → ℂ) (τ g : G → ℂ) = cfInner (f : L → ℂ) (g : L → ℂ))
    (hτ1 : ∀ f : charSpanZero (kerLayerIndFam (⊥ : Subgroup L) H), (τ f : G → ℂ) 1 = 0) :
    ∀ n : ℕ, ∀ A : Subgroup L, A.Normal → Nat.card A ≤ n → A ≤ ⁅H, H⁆ →
      4 * H.index ^ 2 + 1 < A.relIndex H →
      IsCoherent (kerLayerIndFam A H)
        (restrictBaseline (kerLayerIndFam_anti_left (K := H) (bot_le : (⊥ : Subgroup L) ≤ A)) τ) →
      IsCoherent (kerLayerIndFam (⊥ : Subgroup L) H) τ := by
  intro n
  induction n with
  | zero =>
    intro A _ hcard _ _ _
    exact absurd hcard (by simpa using Nat.card_pos.ne')
  | succ n ih =>
    intro A hAn hcard hAH' hidx hcoh
    have := hAn
    rcases eq_or_ne A ⊥ with rfl | hA
    ·
      exact isCoherent_of_isCoherent_restrictBaseline_self τ hcoh
    ·
      obtain ⟨B, hchief⟩ := exists_isChiefFactor A hA
      have := hchief.normal_den
      have hAH : A ≤ H := hAH'.trans (Subgroup.commutator_le_self H)
      have hHA : ⁅H, A⁆ ≤ B :=
        commutator_le_of_isChiefFactor_of_le ‹H.Normal› ‹Group.IsNilpotent ↥H› hchief hAH
      have hcohB : IsCoherent (kerLayerIndFam B H)
          (restrictBaseline (kerLayerIndFam_anti_left (K := H)
            (bot_le : (⊥ : Subgroup L) ≤ B)) τ) :=
        isCoherent_kerLayerIndFam_of_lt_relIndex (E := E) hodd hH hmul hinf hC hchief.lt.le hAH'
          hHA hidx τ hτiso hτ1 hcoh
      refine ih B hchief.normal_den ?_ (hchief.lt.le.trans hAH') ?_ hcohB
      ·
        have := natCard_lt_natCard_of_lt hchief.lt
        omega
      ·
        exact lt_of_lt_of_le hidx (relIndex_le_relIndex_of_le hchief.lt.le)

theorem isCoherent_kerLayerIndFam_bot_of_lt_relIndex_commutator [H.Normal]
    [Group.IsNilpotent ↥H] (hodd : Odd (Nat.card L)) (hH : H ≠ ⊥)
    (hmul : (H : Set L) * (E : Set L) = Set.univ) (hinf : H ⊓ E = ⊥)
    (hC : ∀ u ∈ E, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥)
    (hidx : 4 * H.index ^ 2 + 1 < (⁅H, H⁆ : Subgroup L).relIndex H)
    (τ : charSpanZero (kerLayerIndFam (⊥ : Subgroup L) H) →+ virtualChars G)
    (hτiso : ∀ f g : charSpanZero (kerLayerIndFam (⊥ : Subgroup L) H),
      cfInner (τ f : G → ℂ) (τ g : G → ℂ) = cfInner (f : L → ℂ) (g : L → ℂ))
    (hτ1 : ∀ f : charSpanZero (kerLayerIndFam (⊥ : Subgroup L) H), (τ f : G → ℂ) 1 = 0) :
    IsCoherent (kerLayerIndFam (⊥ : Subgroup L) H) τ :=
  isCoherent_kerLayerIndFam_bot_aux (E := E) hodd hH hmul hinf hC τ hτiso hτ1
    (Nat.card (⁅H, H⁆ : Subgroup L)) ⁅H, H⁆ inferInstance le_rfl le_rfl hidx
    (isCoherent_kerLayerIndFam_commutator (E := E) hH hmul hinf hC τ hτiso hτ1)

theorem isCoherent_kerLayerIndFam_bot_of_lt_card_sq [H.Normal]
    [Group.IsNilpotent ↥H] (hodd : Odd (Nat.card L)) (hH : H ≠ ⊥)
    (hmul : (H : Set L) * (E : Set L) = Set.univ) (hinf : H ⊓ E = ⊥)
    (hC : ∀ u ∈ E, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥)
    (hidx : 4 * Nat.card E ^ 2 + 1 < (⁅H, H⁆ : Subgroup L).relIndex H)
    (τ : charSpanZero (kerLayerIndFam (⊥ : Subgroup L) H) →+ virtualChars G)
    (hτiso : ∀ f g : charSpanZero (kerLayerIndFam (⊥ : Subgroup L) H),
      cfInner (τ f : G → ℂ) (τ g : G → ℂ) = cfInner (f : L → ℂ) (g : L → ℂ))
    (hτ1 : ∀ f : charSpanZero (kerLayerIndFam (⊥ : Subgroup L) H), (τ f : G → ℂ) 1 = 0) :
    IsCoherent (kerLayerIndFam (⊥ : Subgroup L) H) τ :=
  isCoherent_kerLayerIndFam_bot_of_lt_relIndex_commutator (E := E) hodd hH hmul hinf hC
    (by rwa [index_eq_card_of_isComplement'
      (isComplement'_of_mul_eq_univ_of_inf_eq_bot hmul hinf)]) τ hτiso hτ1

end CFSG.FeitThompson
