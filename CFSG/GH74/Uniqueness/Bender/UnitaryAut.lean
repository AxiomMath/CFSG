module

public import CFSG.GH74.Uniqueness.Bender.CentralizesCenter
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RootCenterAutomorphismUnitaryTransport

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup

@[expose] def autCentralizer {K : Type*} [Group K] (V : Subgroup K) : Subgroup (MulAut K) where
  carrier := {σ | ∀ z ∈ V, σ z = z}
  mul_mem' {σ τ} hσ hτ z hz := by
    rw [MulAut.mul_apply, hτ z hz, hσ z hz]
  one_mem' _ _ := rfl
  inv_mem' {σ} hσ z hz := by
    rw [MulAut.inv_apply]
    exact (MulEquiv.symm_apply_eq σ).mpr (hσ z hz).symm

theorem mem_autCentralizer_iff {K : Type*} [Group K] {V : Subgroup K} {σ : MulAut K} :
    σ ∈ autCentralizer V ↔ ∀ z ∈ V, σ z = z := Iff.rfl

section Omega

variable {K : Type*} [Group K] [Finite K]

theorem BenderCore.omega₁_map_eq_rootCenter {q i e : ℕ} {P : Subgroup K} {t : K}
    (h : BenderCore q i e P t) :
    (CFSG.omega₁ (G := (P : Type _)) (p := 2)).map P.subtype = rootCenter P := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    have hx2 : x * x = 1 := by simpa [sq] using hx
    exact h.mem_rootCenter_of_mul_self x.2 (by simpa using congrArg Subtype.val hx2)
  · intro z hz
    refine ⟨⟨z, rootCenter_le P hz⟩, Subgroup.subset_closure ?_, rfl⟩
    show (⟨z, rootCenter_le P hz⟩ : P) ^ 2 ^ 1 = 1
    apply Subtype.ext
    simpa [sq] using h.center_sq z hz

theorem BenderType.rootCenterAut_eq_autCentralizer
    {n i e : ℕ} (h : BenderType K n i e)
    (Q : Sylow 2 K) :
    CFSG.ProperTwoGeneratedCore.RootCenter.rootCenterAut (Q : Subgroup K) (rootCenter (Q : Subgroup K)) =
      autCentralizer (rootCenter (Q : Subgroup K)) := by
  ext σ
  constructor
  · rintro ⟨-, hσ⟩
    exact hσ
  · intro hσ
    refine ⟨?_, hσ⟩
    have hle : (Q : Subgroup K).map σ.toMonoidHom ≤ (Q : Subgroup K) := by
      rintro _ ⟨s, hs, rfl⟩
      exact h.mem_of_centralizes_rootCenter Q σ hσ s hs
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective σ.injective]

end Omega

section Main

open CFSG.ProperTwoGeneratedCore.RootCenter

theorem BenderType.lemma_3_6_c_unitary
    {K : Type} [Group K] [Finite K] {n e : ℕ}
    (h : BenderType K n 3 e) (Q : Sylow 2 K) :
    ∃ D : Subgroup (MulAut K),
      (Subgroup.map (MulAut.conj : K →* MulAut K) (Q : Subgroup K)) ⊓ D = ⊥ ∧
      (Subgroup.map (MulAut.conj : K →* MulAut K) (Q : Subgroup K)) ⊔ D =
        autCentralizer (rootCenter (Q : Subgroup K)) ∧
      ((Subgroup.map (MulAut.conj : K →* MulAut K) (Q : Subgroup K)).subgroupOf
        (autCentralizer (rootCenter (Q : Subgroup K)))).Normal ∧
      Nat.card D = 2 * (2 ^ n + 1) ∧ Nonempty (D ≃* DihedralGroup (2 ^ n + 1)) := by
  obtain ⟨hn, ⟨e₁⟩⟩ : 2 ≤ n ∧ Nonempty (K ≃* CFSG.Theory.Comparator.PSU3Model n) := by
    cases h with
    | unitary n hn e => exact ⟨hn, ⟨e⟩⟩
  obtain ⟨E, hE, hF, J, hJ, hcard, hfixed, ⟨e'⟩⟩ := exists_psu3_concrete hn
  obtain ⟨t, hc⟩ := h.exists_benderCore Q
  have hU : rootCenter (Q : Subgroup K) =
      (CFSG.omega₁ (G := (Q : Subgroup K)) (p := 2)).map (Q : Subgroup K).subtype :=
    hc.omega₁_map_eq_rootCenter.symm
  obtain ⟨-, -, -, ⟨D, hD1, hD2, hD3, hD4, hD5⟩, -⟩ :=
    CFSG.ProperTwoGeneratedCore.RootCenter.even_unitary_root_center_automorphisms_of_mulEquiv J n
      hn hcard hfixed hJ (e₁.trans e') Q (rootCenter (Q : Subgroup K)) hU
  rw [h.rootCenterAut_eq_autCentralizer Q] at hD2 hD3
  exact ⟨D, hD1, hD2, hD3, hD4, hD5⟩

end Main

end CFSG.GH74.Uniqueness.Bender
