module

public import CFSG.ClassicalInvolution.Generic.Frame
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T7U

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] [Finite G]

theorem exists_central_mod {S A T : Subgroup G} (hS : IsPGroup 2 ↥S) (hAS : A ≤ S)
    (hAn : ∀ s ∈ S, conjSub s A = A) (hTA : T ≤ A) (hTc : ∀ s ∈ S, ∀ x ∈ T, s * x = x * s)
    (hne : T ≠ A) : ∃ x ∈ A, x ∉ T ∧ ∀ s ∈ S, s * x * s⁻¹ * x⁻¹ ∈ T := by
  classical
  let N : Subgroup ↥S := T.subgroupOf S
  have hNn : N.Normal := ⟨fun n hn g => by
    have hn' : (n : G) ∈ T := hn
    show ((g * n * g⁻¹ : ↥S) : G) ∈ T
    have e : ((g * n * g⁻¹ : ↥S) : G) = n := by
      have := hTc g g.2 n hn'
      calc ((g * n * g⁻¹ : ↥S) : G) = (g : G) * n * (g : G)⁻¹ := rfl
        _ = n := by rw [this]; group
    rw [e]; exact hn'⟩
  have := hNn
  have hQ2 : IsPGroup 2 (↥S ⧸ N) := hS.to_quotient N
  have hnil : Group.IsNilpotent (↥S ⧸ N) := hQ2.isNilpotent
  have hAsn : (A.subgroupOf S).Normal := ⟨fun a ha g => by
    have ha' : (a : G) ∈ A := ha
    show ((g * a * g⁻¹ : ↥S) : G) ∈ A
    have : (g : G) * a * (g : G)⁻¹ ∈ conjSub (g : G) A := conj_mem_conjSub ha'
    rw [hAn g g.2] at this
    exact this⟩
  let H : Subgroup (↥S ⧸ N) := (A.subgroupOf S).map (QuotientGroup.mk' N)
  have hHn : H.Normal :=
    Subgroup.Normal.map hAsn (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  obtain ⟨x₁, hx₁A, hx₁T⟩ : ∃ x ∈ A, x ∉ T := by
    by_contra h
    push Not at h
    exact hne (le_antisymm hTA h)
  have hHbot : H ≠ ⊥ := by
    intro hbot
    have hmem : (QuotientGroup.mk (⟨x₁, hAS hx₁A⟩ : ↥S) : ↥S ⧸ N) ∈ H :=
      Subgroup.mem_map.mpr ⟨⟨x₁, hAS hx₁A⟩, hx₁A, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
    exact hx₁T hmem
  obtain ⟨c, hc⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hHbot)
  obtain ⟨hcH, hcc⟩ := Subgroup.mem_inf.mp c.2
  obtain ⟨x', hx'A, hx'c⟩ := Subgroup.mem_map.mp hcH
  have hc1 : (c : ↥S ⧸ N) ≠ 1 := fun h => hc (Subtype.ext h)
  refine ⟨(x' : G), hx'A, fun hxT => hc1 ?_, fun s hs => ?_⟩
  · rw [← hx'c]
    exact (QuotientGroup.eq_one_iff _).mpr hxT
  · have hcent := Subgroup.mem_center_iff.mp hcc (QuotientGroup.mk (⟨s⁻¹, S.inv_mem hs⟩ : ↥S))
    rw [← hx'c] at hcent
    simp only [QuotientGroup.mk'_apply] at hcent
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hcent
    have hT1 : (x' : G)⁻¹ * s * x' * s⁻¹ ∈ T := by
      have : (((⟨s⁻¹, S.inv_mem hs⟩ * x')⁻¹ * (x' * ⟨s⁻¹, S.inv_mem hs⟩) : ↥S) : G) ∈ T := hcent
      simpa [mul_assoc] using this
    have hxS : (x' : G) ∈ S := x'.2
    have hcomm := hTc _ hxS _ hT1
    have e : s * (x' : G) * s⁻¹ * (x' : G)⁻¹ =
        (x' : G) * ((x' : G)⁻¹ * s * x' * s⁻¹) * (x' : G)⁻¹ := by group
    rw [e, hcomm]
    have e2 : (x' : G)⁻¹ * s * x' * s⁻¹ * (x' : G) * (x' : G)⁻¹ =
        (x' : G)⁻¹ * s * x' * s⁻¹ := by group
    rw [e2]
    exact hT1

end CFSG.ClassicalInvolution.Asc77.T7U
