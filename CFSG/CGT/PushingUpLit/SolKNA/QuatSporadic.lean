module

public import CFSG.CGT.PushingUpLit.SolKNA.Quaternion
public import CFSG.CGT.PushingUpLit.SolKNA.Split
import CFSG.ClassicalInvolution.Basic

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.CGT.PushingUpLit.SolKAb (MTOutcome sylowImg)
open CFSG.ComponentClassification.AschbacherTheorem3 (IsQuaternionTwoGroup)
open CFSG.ComponentClassification.StandardRecognition (ClassicalInvolutionTheoremModels)

section Orbit

variable {P : Type*} [Group P]

theorem card_le_of_faithful_action {u : P} (hu2 : orderOf u = 2)
    (hH : ∀ H : Subgroup P, H ≠ ⊥ → u ∈ H) {Ω : Type*} [Finite Ω]
    (φ : P →* Equiv.Perm Ω) (hφ : Function.Injective φ) : Nat.card P ≤ Nat.card Ω := by
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu2
    omega
  have hφu : φ u ≠ 1 := fun h => hu1 (hφ (by rw [h, map_one]))
  obtain ⟨ω, hω⟩ : ∃ ω : Ω, φ u ω ≠ ω := by
    by_contra hcon
    push Not at hcon
    exact hφu (Equiv.ext hcon)
  have hstab : ∀ g : P, φ g ω = ω → g = 1 := by
    intro g hg
    by_contra hg1
    have hne : Subgroup.zpowers g ≠ ⊥ := by
      rwa [Ne, Subgroup.zpowers_eq_bot]
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hH _ hne)
    apply hω
    rw [← hj, map_zpow]
    exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hg j
  have hinj : Function.Injective fun g : P => φ g ω := by
    intro g g' h
    have h' : φ (g⁻¹ * g') ω = ω := by
      rw [map_mul, map_inv, Equiv.Perm.mul_apply, ← (show φ g ω = φ g' ω from h)]
      simp
    exact (inv_mul_eq_one.mp (hstab _ h'))
  exact Nat.card_le_card_of_injective _ hinj

theorem four_mul_two_pow_le_of_faithful_action {k : ℕ} (e : P ≃* QuaternionGroup (2 ^ k))
    {Ω : Type*} [Finite Ω] (φ : P →* Equiv.Perm Ω) (hφ : Function.Injective φ) :
    4 * 2 ^ k ≤ Nat.card Ω := by
  obtain ⟨u, hu2, -, hH⟩ :=
    CFSG.ClassicalInvolution.exists_unique_involution_of_mulEquiv_quaternionGroup e
  have h1 := card_le_of_faithful_action hu2 hH φ hφ
  have hcard : Nat.card P = 4 * 2 ^ k := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  omega

end Orbit

theorem nonempty_equiv_quaternionGroup_two_of_perm {G : Type} [Group G] {P : Subgroup G}
    (hP : IsQuaternionTwoGroup P) {Ω : Type} [Finite Ω] (hΩ : Nat.card Ω < 16)
    (ψ : G →* Equiv.Perm Ω) (hψ : Function.Injective ψ) :
    Nonempty (↥P ≃* QuaternionGroup 2) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hP
  have hle := four_mul_two_pow_le_of_faithful_action e (ψ.comp P.subtype)
    (hψ.comp P.subtype_injective)
  have hn3 : n = 3 := by
    by_contra hne
    have h4 : 2 ^ 2 ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  subst hn3
  exact ⟨e⟩

theorem quaternionInspectionSporadic_holds : QuaternionInspectionSporadic := by
  intro G _ _ hKP hs hna K hK hM hF R hq hspor
  have hQ8 : Nonempty (↥(sylowImg R) ≃* QuaternionGroup 2) := by
    rcases hspor with h | h
    · obtain ⟨e⟩ := h
      exact nonempty_equiv_quaternionGroup_two_of_perm hq (Ω := Fin 11) (by simp)
        ((CFSG.Blueprint.NativeSporadic.M11).subtype.comp e.toMonoidHom)
        (Subtype.val_injective.comp e.injective)
    · obtain ⟨e⟩ := h
      exact nonempty_equiv_quaternionGroup_two_of_perm hq (Ω := Fin 12) (by simp)
        ((CFSG.Blueprint.NativeSporadic.M12).subtype.comp e.toMonoidHom)
        (Subtype.val_injective.comp e.injective)
  rcases hspor with h | h
  · exact Or.inr (Or.inr (Or.inl ⟨hQ8, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨hQ8, Or.inr (Or.inr (Or.inr (Or.inr h)))⟩))

theorem quaternionInspection_of_lie (hL : QuaternionInspectionLie) : QuaternionInspection :=
  quaternionInspection_of_split quaternionInspectionSporadic_holds hL

theorem solomonTimmesfeldMainNonAbelian_of_lie_inputs (hCIT : ClassicalInvolutionTheoremModels)
    (hL : QuaternionInspectionLie) (hRank : SolomonTimmesfeldMainRankGe2) :
    CFSG.CGT.PushingUpLit.SolKAb.SolomonTimmesfeldMainNonAbelian :=
  nonAbelian_of_split (quaternion_of_cit_inspection hCIT (quaternionInspection_of_lie hL)) hRank

end CFSG.CGT.PushingUpLit.SolKNA
