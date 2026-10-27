module

public import CFSG.GH74.GLS.SP.Local.SPLPumpXF

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

theorem perfect_of_component {Q : Type} [Group Q] {K : Subgroup Q} (hK : IsComponent K) : ⁅K, K⁆ = K :=
  Subgroup.isPerfect_iff.mp hK.1.1

theorem conjSub_conjSub_inv {Q : Type} [Group Q] {z : Q} (hz : z * z = 1) (K : Subgroup Q) :
    conjSub z⁻¹ (conjSub z⁻¹ K) = K := by
  ext x
  rw [mem_conjSub_iff', mem_conjSub_iff']
  have hinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  simp only [hinv]
  have : z * (z * x * z) * z = x := by
    calc z * (z * x * z) * z = (z * z) * x * (z * z) := by group
      _ = x := by rw [hz]; group
  rw [this]

namespace XCtx

variable {X : Type} [Group X] [Finite X] {z t : X} {A T₁ : Subgroup X}

theorem component_le
    (hG : Generic.GenericKnownFacts) (hF : E2.E2ComponentFacts)
    (hUI : StableUniqueInvolution) (hAlt : StableDoubleCoverAlt) (hL34 : StableL34Cover)
    (hOUI : OtherUniqueInvolution) (hDiag : DiagonalImpossible)
    (hX : XCtx X z t A T₁) (hcomp : ∀ K : Subgroup X, IsComponent K → InC2 ↥K ∨ InT2 ↥K)
    {L : Subgroup X} (hL : IsComponent L)
    (hcases : (conjSub z⁻¹ L = L ∧ A ≤ L) ∨
      (conjSub z⁻¹ L ≠ L ∧ ∃ hAB : ⁅L, conjSub z⁻¹ L⁆ = ⊥, A ≤ (swapDiag hAB).range)) :
    ∀ K : Subgroup X, IsComponent K → K ≤ A := by
  rcases hcases with ⟨hst, hAL⟩ | ⟨hne, hAB, hAD⟩
  · have hz : ∀ x ∈ L, z * x * z⁻¹ ∈ L := by
      intro x hx
      have h1 : x ∈ conjSub z⁻¹ L := by rw [hst]; exact hx
      rw [mem_conjSub_iff', inv_inv] at h1
      exact h1
    have hcen := hX.stable_central hG hF hUI hAlt hL34 (hcomp L hL) hz hAL
    have hLA : L ≤ A := hX.perfect_le L (fun c hc => hcen c hc) (perfect_of_component hL)
    intro K hK
    by_cases hKL : K = L
    · rw [hKL]
      exact hLA
    have hcommKL : ⁅K, L⁆ = ⊥ := (CFSG.LocalCores.distinct_components_commute hK hL).resolve_left hKL
    have hKA : ∀ k ∈ K, ∀ a ∈ A, k * a = a * k := by
      have h1 : K ≤ centralizer (L : Set X) := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommKL
      intro k hk a ha
      exact (mem_centralizer_iff.mp (h1 hk) a (hAL ha)).symm
    by_cases hzK : conjSub z⁻¹ K = K
    · by_cases hmove : ∃ x ∈ K, z * x ≠ x * z
      · exfalso
        have hKz : ∀ x ∈ K, z * x * z⁻¹ ∈ K := by
          intro x hx
          have h1 : x ∈ conjSub z⁻¹ K := by rw [hzK]; exact hx
          rw [mem_conjSub_iff', inv_inv] at h1
          exact h1
        exact hX.other_False hG hF hOUI ⟨hKz, hKA, hmove⟩ hK.1 (hcomp K hK)
      · push Not at hmove
        exact hX.perfect_le K hmove (perfect_of_component hK)
    · exfalso
      have hz2 : z⁻¹ = z := inv_eq_of_mul_eq_one_right hX.z_sq
      have hAB' := commutator_conjSub_eq_bot hK hzK
      have hKL' : conjSub z⁻¹ K ≠ L := by
        intro h
        apply hKL
        rw [← conjSub_conjSub_inv hX.z_sq K, h, hst]
      have hK'c : IsComponent (conjSub z⁻¹ K) := isComponent_conjSub hK z⁻¹
      have hcomm' : ⁅conjSub z⁻¹ K, L⁆ = ⊥ :=
        (CFSG.LocalCores.distinct_components_commute hK'c hL).resolve_left hKL'
      have hK'A : ∀ k ∈ conjSub z⁻¹ K, ∀ a ∈ A, k * a = a * k := by
        have h1 : conjSub z⁻¹ K ≤ centralizer (L : Set X) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm'
        intro k hk a ha
        exact (mem_centralizer_iff.mp (h1 hk) a (hAL ha)).symm
      have hDq := isQuasisimple_range_swapDiag hAB' (assembly_isQuasisimple_of_isComponent hK)
      have hDperf := commutator_self_of_isQuasisimple hDq
      have hDc : ∀ c ∈ (swapDiag hAB').range, z * c = c * z := by
        rintro _ ⟨x, rfl⟩
        have := mem_centralizer_singleton_iff.mp (swapDiag_mem_centralizer hAB' hz2 x)
        exact this.symm
      have hDA : (swapDiag hAB').range ≤ A := hX.perfect_le _ hDc hDperf
      have hDbot : (swapDiag hAB').range = ⊥ := by
        rw [eq_bot_iff]
        intro c hc
        have hcA := hDA hc
        have hz' : (⟨c, hcA⟩ : ↥A) ∈ center ↥A := by
          rw [Subgroup.mem_center_iff]
          intro b
          apply Subtype.ext
          obtain ⟨x, rfl⟩ := hc
          show (b : X) * swapDiag hAB' x = swapDiag hAB' x * b
          rw [swapDiag_apply]
          have h1 := hKA (x : X) x.2 b b.2
          have h2 := hK'A (z⁻¹ * (x : X) * z) (conj_mem_conjSub x.2) b b.2
          calc (b : X) * ((x : X) * (z⁻¹ * x * z)) = (b * x) * (z⁻¹ * x * z) := by group
            _ = (x * b) * (z⁻¹ * x * z) := by rw [← h1]
            _ = x * (b * (z⁻¹ * x * z)) := by group
            _ = x * ((z⁻¹ * x * z) * b) := by rw [← h2]
            _ = (x * (z⁻¹ * x * z)) * b := by group
        rw [hX.A_quasisimple.2, Subgroup.mem_bot] at hz'
        exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hz')
      have hKle : K ≤ conjSub z⁻¹ K := by
        intro x hx
        have h1 : swapDiag hAB' ⟨x, hx⟩ = 1 := by
          have : swapDiag hAB' ⟨x, hx⟩ ∈ (swapDiag hAB').range := ⟨_, rfl⟩
          rw [hDbot, Subgroup.mem_bot] at this
          exact this
        rw [swapDiag_apply] at h1
        have h3 : (x : X) * (z⁻¹ * x * z) = 1 := h1
        have h2 : z⁻¹ * x * z = x⁻¹ := eq_inv_of_mul_eq_one_right h3
        have h4 : x⁻¹ ∈ conjSub z⁻¹ K := by
          rw [← h2]
          exact conj_mem_conjSub hx
        have := inv_mem h4
        simpa using this
      have hle2 : conjSub z⁻¹ K ≤ K := by
        have h2 : conjSub z⁻¹ K ≤ conjSub z⁻¹ (conjSub z⁻¹ K) := Subgroup.map_mono hKle
        rwa [conjSub_conjSub_inv hX.z_sq K] at h2
      exact hzK (le_antisymm hle2 hKle)
  · exact (hDiag X z t A T₁ L hX hL hne hAB hAD).elim

end XCtx

end CFSG.GH74.GLS.SP.Local
