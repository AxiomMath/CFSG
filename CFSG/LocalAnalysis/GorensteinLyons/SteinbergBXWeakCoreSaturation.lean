module

public import CFSG.Assembly.LargeEvenDefs
public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreAbsorption
public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreInternal
public import CFSG.GH74.EvenRank

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.LargeEvenClassification.Helpers
open scoped Pointwise

variable {G : Type*} [Group G]

theorem largeEvenWeakCore_eq_weakTwoGeneratedPCore [Finite G] (p : ℕ) (P : Subgroup G) :
    CFSG.Assembly.LargeEvenWeakCore p P = weakTwoGeneratedPCore p P := by
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨Q, hQP, hQ2, hQ3, rfl⟩
    exact eligible_normalizer_le_weak_core P Q ⟨hQP, hQ2, hQ3⟩
  · apply iSup_le
    rintro ⟨Q, hQP, hQ2, hQ3⟩
    exact le_sSup ⟨Q, hQP, hQ2, hQ3, rfl⟩

theorem largeEvenWeakCoreLocal_iff (X : Type*) [Group X] [Finite X] (p : ℕ) :
    CFSG.Assembly.LargeEvenWeakCoreLocal X p ↔ WeakCoreLocal p X := by
  unfold CFSG.Assembly.LargeEvenWeakCoreLocal WeakCoreLocal
  simp only [largeEvenWeakCore_eq_weakTwoGeneratedPCore]

theorem isCharacteristicP_two_iff (W : Subgroup G) :
    CFSG.IsCharacteristicP 2 W ↔ IsCharacteristicTwoLocal W := by
  unfold CFSG.IsCharacteristicP IsCharacteristicTwoLocal
  exact (CFSG.GH74.inf_centralizer_map_subtype_le_iff W _).symm

theorem weak_core_sylow_saturation_and_locality [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hrank : 3 ≤ CFSG.Assembly.pRank p (⊤ : Subgroup G)) (P : Sylow p G) {W : Subgroup G}
    (hW : W = CFSG.Assembly.LargeEvenWeakCore p (P : Subgroup G)) :
    (P : Subgroup G) ≤ W ∧
      (∃ Q : Sylow p W, (Q : Subgroup W) = (P : Subgroup G).subgroupOf W) ∧
      CFSG.Assembly.pRank p W = CFSG.Assembly.pRank p (⊤ : Subgroup G) ∧
      CFSG.Assembly.LargeEvenWeakCore p ((P : Subgroup G).subgroupOf W) = ⊤ ∧
      normalizer ((P : Subgroup G) : Set G) ≤ normalizer (W : Set G) ∧
      ((normalizer (W : Set G) : Subgroup G) : Set G) =
        (W : Set G) * (normalizer ((P : Subgroup G) : Set G) : Set G) ∧
      (∀ U : Subgroup G, U ≤ W → IsPGroup p U → 2 ≤ CFSG.Assembly.pRank p U →
        3 ≤ CFSG.Assembly.pRank p (W ⊓ centralizer (U : Set G)) → normalizer (U : Set G) ≤ W) ∧
      (∀ (E K : Subgroup G) (k : ℕ), E ≤ W → CFSG.Assembly.IsElemAbelian p E →
        Nat.card E = p ^ k → 3 ≤ k → ¬ p ∣ Nat.card K → E ≤ normalizer (K : Set G) → K ≤ W) ∧
      (CFSG.IsCharacteristicPType G 2 →
        List.TFAE [CFSG.Assembly.LargeEvenWeakCoreLocal G p, CFSG.Assembly.pCoreOf 2 W ≠ ⊥,
          CFSG.IsCharacteristicP 2 W, CFSG.Assembly.LargeEvenWeakCoreLocal W p] ∧
        (∀ Y : Subgroup G, CFSG.IsPLocal 2 Y → W ≤ Y →
          CFSG.Assembly.pCoreOf 2 Y ≠ ⊥ ∧ CFSG.Assembly.pCoreOf 2 Y ≤ CFSG.Assembly.pCoreOf 2 W ∧
            CFSG.IsCharacteristicP 2 W) ∧
        (CFSG.Assembly.LargeEvenWeakCoreLocal G p → IsSimpleGroup G →
          (∃ a b : G, a * b ≠ b * a) → W < ⊤)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain rfl : W = weakTwoGeneratedPCore p (P : Subgroup G) := by
    rw [hW, largeEvenWeakCore_eq_weakTwoGeneratedPCore]
  have hrank' : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := hrank
  have hPrank : 3 ≤ CFSG.Open.pRank p (P : Subgroup G) := by
    rw [pRank_sylow_eq_ambient hp P]
    exact hrank'
  have hPW : (P : Subgroup G) ≤ weakTwoGeneratedPCore p (P : Subgroup G) :=
    parent_le_weak_core hp.one_lt _ hPrank
  have hNPW := normalizer_parent_le_normalizer_weak_core hp.one_lt (P : Subgroup G)
  have hfrat : ((normalizer (weakTwoGeneratedPCore p (P : Subgroup G) : Set G) : Subgroup G) :
      Set G) = (weakTwoGeneratedPCore p (P : Subgroup G) : Set G) *
        (normalizer ((P : Subgroup G) : Set G) : Set G) := by
    apply Set.Subset.antisymm
    · intro g hg
      have hgW := mem_normalizer_iff_map_conj_eq.mp hg
      have hle : (P : Subgroup G).map (MulAut.conj g).toMonoidHom ≤
          weakTwoGeneratedPCore p (P : Subgroup G) := by
        rw [← hgW]
        exact map_mono hPW
      obtain ⟨w, hw⟩ := sylow_contains_conjugate_inside hp P _
        ((P : Subgroup G).map (MulAut.conj g).toMonoidHom) hPW hle (P.isPGroup'.map _)
      have heq : ((P : Subgroup G).map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj (w : G)).toMonoidHom = P := by
        apply eq_of_le_of_card_ge hw
        rw [card_map_of_injective (MulAut.conj _).injective,
          card_map_of_injective (MulAut.conj _).injective]
      have hwg : (w : G) * g ∈ normalizer ((P : Subgroup G) : Set G) := by
        rw [mem_normalizer_iff_map_conj_eq]
        have hcomp : (P : Subgroup G).map (MulAut.conj ((w : G) * g) : G →* G) =
            ((P : Subgroup G).map (MulAut.conj g).toMonoidHom).map
              (MulAut.conj (w : G)).toMonoidHom := by
          rw [map_map]
          congr 1
          ext x
          simp [MulAut.conj_apply, mul_assoc]
        rw [hcomp, heq]
      exact Set.mem_mul.mpr ⟨(w : G)⁻¹, inv_mem w.2, (w : G) * g, hwg, by group⟩
    · rintro _ ⟨w, hw, n, hn, rfl⟩
      exact mul_mem (le_normalizer hw) (hNPW hn)
  obtain ⟨E, hEP, hE, hEcard⟩ := pRank_witness hp.one_lt (P : Subgroup G)
  have hEW : E ≤ weakTwoGeneratedPCore p (P : Subgroup G) := hEP.trans hPW
  have hWbot : weakTwoGeneratedPCore p (P : Subgroup G) ≠ ⊥ := by
    intro h
    have hE1 : E = ⊥ := le_bot_iff.mp (h ▸ hEW)
    rw [hE1, card_bot] at hEcard
    have := Nat.one_lt_pow (by omega : CFSG.Open.pRank p (P : Subgroup G) ≠ 0) hp.one_lt
    omega
  refine ⟨hPW, ⟨P.subtype hPW, Sylow.coe_subtype _ _⟩, weak_core_rank_eq_ambient hp P hPrank, ?_,
    hNPW, hfrat, ?_, ?_, ?_⟩
  · rw [largeEvenWeakCore_eq_weakTwoGeneratedPCore]
    exact weak_core_internal_eq_top hp.one_lt (P : Subgroup G) hPW
  · intro U hUW hU hU2 hU3
    exact weak_core_absorbs_pSubgroup_normalizer hp P hPrank U hUW hU hU2 hU3
  · intro E' K k hE'W hE' hE'card hk hK hE'K
    exact rank_three_normalized_coprime_le_weak_core hp P hPrank E' K hE' hE'card hk hE'W hK hE'K
  · intro hchar
    have hcharOpen : CFSG.Open.IsCharTwoType G := CFSG.GH74.isCharTwoType_iff.mpr hchar
    have hY : ∀ Y : Subgroup G, CFSG.IsPLocal 2 Y → weakTwoGeneratedPCore p (P : Subgroup G) ≤ Y →
        CFSG.Assembly.pCoreOf 2 Y ≠ ⊥ ∧
          CFSG.Assembly.pCoreOf 2 Y ≤ CFSG.Assembly.pCoreOf 2 (weakTwoGeneratedPCore p P) ∧
          CFSG.IsCharacteristicP 2 (weakTwoGeneratedPCore p (P : Subgroup G)) := by
      intro Y hYloc hWY
      obtain ⟨h1, -, h3⟩ := rank_three_two_local_intersection_characteristic hp hp2 hcharOpen P
        hPrank E Y hE hEcard hPrank hEW (hEW.trans hWY) hYloc
      rw [inf_eq_left.mpr hWY] at h1 h3
      exact ⟨twoLocal_core_ne_bot Y hYloc, h1, (isCharacteristicP_two_iff _).mpr h3⟩
    have h12 : CFSG.Assembly.LargeEvenWeakCoreLocal G p →
        CFSG.Assembly.pCoreOf 2 (weakTwoGeneratedPCore p (P : Subgroup G)) ≠ ⊥ := by
      intro hA
      obtain ⟨Y, hYloc, hWY⟩ := ((largeEvenWeakCoreLocal_iff G p).mp hA).2 P
      obtain ⟨hY1, hY2, -⟩ := hY Y hYloc hWY
      exact fun h => hY1 (le_bot_iff.mp (h ▸ hY2))
    refine ⟨?_, hY, fun hA hsimple hnonab => ?_⟩
    · tfae_have 1 → 2 := h12
      tfae_have 2 → 1 := fun hcore =>
        (largeEvenWeakCoreLocal_iff G p).mpr (nontrivial_weak_core_implies_local hp P hrank' hcore)
      tfae_have 2 → 3 := fun hcore => by
        obtain ⟨Y, hYloc, hWY⟩ := nontrivial_core_local_container _ hcore
        exact (hY Y hYloc hWY).2.2
      tfae_have 3 → 2 := fun hC =>
        characteristic_two_nontrivial_core _ ((isCharacteristicP_two_iff _).mp hC) hWbot
      tfae_have 2 ↔ 4 := by
        rw [largeEvenWeakCoreLocal_iff]
        exact (weak_core_internal_locality_iff hp P hPrank).symm
      tfae_finish
    · exact lt_top_iff_ne_top.mpr (simple_subgroup_nontrivial_core_proper hnonab _ (h12 hA))

end CFSG.LocalAnalysis.GorensteinLyons
