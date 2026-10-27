module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentM10Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentM10Alt
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentM10Spor
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.A6LieSmall

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)


theorem card_alt_le_of_le_six {n : ℕ} (h5 : 5 ≤ n) (h6 : n ≤ 6) :
    Nat.card (alternatingGroup (Fin n)) ≤ 360 := by
  interval_cases n
  · rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  · rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide

theorem seven_le_of_card_alt {n : ℕ} (h : 1440 ≤ Nat.card (alternatingGroup (Fin n))) : 7 ≤ n := by
  by_contra hn
  push Not at hn
  have h1 : Nat.card (alternatingGroup (Fin n)) ≤ n.factorial :=
    calc Nat.card (alternatingGroup (Fin n)) ≤ Nat.card (Equiv.Perm (Fin n)) :=
          Subgroup.card_le_card_group _
      _ = n.factorial := by rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  have h2 : n.factorial ≤ (6 : ℕ).factorial := Nat.factorial_le (by omega)
  have h3 : (6 : ℕ).factorial = 720 := by decide
  omega

theorem arm_inner (hI : A6InnerLieSmall) {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (hcat : Catalog S) {z : S} (hz : orderOf z = 2)
    (hcard : Nat.card ↥(centralizer ({z} : Set S)) = 1440)
    (D : Subgroup ↥(centralizer ({z} : Set S))) [D.Normal]
    (hD : Nonempty (↥D ≃* alternatingGroup (Fin 6))) : False := by
  obtain ⟨eD⟩ := hD
  rcases (CFSG.Milestones.ct_catalog_nonabelian_type_partition S hna).1 hcat with
    ⟨n, hn, ⟨θ⟩⟩ | hodd | heven | ⟨s, ⟨es⟩⟩
  ·
    have hI' : Function.Injective (MulAut.conj : S →* MulAut S) :=
      CFSG.ComponentClassification.CatLeaf.mulAut_conj_injective_of_simple hna
    have hσ : orderOf (MulAut.conj z : MulAut S) = 2 :=
      (orderOf_injective (MulAut.conj : S →* MulAut S) hI' z).trans hz
    have hfix : fixedSubgroup (MulAut.conj z : MulAut S) = centralizer ({z} : Set S) :=
      CFSG.SeitzReduction.SporadicRefine.fixedSubgroup_conj_eq_centralizerOf z
    have hfc : Nat.card ↥(fixedSubgroup (MulAut.conj z : MulAut S)) = 1440 := by
      rw [hfix]
      exact hcard
    have hS : 1440 ≤ Nat.card (alternatingGroup (Fin n)) := by
      rw [← Nat.card_congr θ.toEquiv, ← hcard]
      exact Subgroup.card_le_card_group _
    exact alt_fixed_false (seven_le_of_card_alt hS) θ hσ (Or.inr (Or.inl hfc))
  · exact hI S hodd z hz hcard.le D inferInstance ⟨eD⟩
  · exact CFSG.ComponentClassification.CatLeaf.involutionCentralizersComponentFree_of_evenLieType
      heven z hz D (isComponent_of_alt6 D eD)
  · exact spor_inner_false inferInstance hna es hz hcard D ⟨eD⟩

theorem arm_outer (hO : A6OuterLieSmall) {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (hcat : Catalog S) {σ : MulAut S} (hσ : orderOf σ = 2)
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range)
    (hcard : Nat.card ↥(fixedSubgroup σ) = 360 ∨ Nat.card ↥(fixedSubgroup σ) = 720)
    (D : Subgroup ↥(fixedSubgroup σ)) [D.Normal]
    (hD : Nonempty (↥D ≃* alternatingGroup (Fin 6)))
    (hinv : ∀ x : ↥(fixedSubgroup σ), orderOf x = 2 → x ∈ D) :
    Nonempty (S ≃* CFSG.LieType.Multipliers.U43.X₀) ∧ Nat.card ↥(fixedSubgroup σ) = 720 := by
  obtain ⟨eD⟩ := hD
  have hle : Nat.card ↥(fixedSubgroup σ) ≤ 720 := by omega
  rcases (CFSG.Milestones.ct_catalog_nonabelian_type_partition S hna).1 hcat with
    ⟨n, hn, ⟨θ⟩⟩ | hodd | heven | ⟨s, ⟨es⟩⟩
  ·
    exfalso
    by_cases hn7 : 7 ≤ n
    · have h6 := no_order_six D ⟨eD⟩ hle hinv
      rcases hcard with h | h
      · exact alt_fixed_false hn7 θ hσ (Or.inl h)
      · exact alt_fixed_false hn7 θ hσ (Or.inr (Or.inr ⟨h, h6⟩))
    ·
      have hS : Nat.card S ≤ 360 := by
        rw [Nat.card_congr θ.toEquiv]
        exact card_alt_le_of_le_six hn (by omega)
      have h360 : 360 ≤ Nat.card ↥(fixedSubgroup σ) := by omega
      have htop : fixedSubgroup σ = ⊤ := by
        rw [← Subgroup.card_eq_iff_eq_top]
        exact le_antisymm (Subgroup.card_le_card_group _) (by omega)
      have hσ1 : σ = 1 := by
        ext x
        have hx : x ∈ fixedSubgroup σ := by rw [htop]; exact Subgroup.mem_top x
        exact hx
      rw [hσ1, orderOf_one] at hσ
      omega
  · exact hO S (Or.inl hodd) σ hσ hout hle D inferInstance ⟨eD⟩ hinv
  · exact hO S (Or.inr heven) σ hσ hout hle D inferInstance ⟨eD⟩ hinv
  · exfalso
    exact spor_outer_false inferInstance hna es hσ hout hcard D ⟨eD⟩

end CFSG.ComponentClassification.CatFC
