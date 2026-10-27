module

public import CFSG.LieType.ChevTwo.OppCl.FormsCasesBase

public section

namespace CFSG.LieType.ChevTwo.OppCl

open CFSG.Open CFSG.LieType.BorelTits

namespace FormsCases

section UradAPI

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] {H : Type} [Group H]
variable {Φ : ReflForm F V} {ρ : H →* Module.End F V} {U : Submodule F V}

theorem fw_zero :
    isoCompletion Φ (fun k => if k = 0 then (⊥ : Submodule F V) else U) 1 0 = ⊥ :=
  isoCompletion_zero (by simp) 1

theorem fw_one :
    isoCompletion Φ (fun k => if k = 0 then (⊥ : Submodule F V) else U) 1 1 = U := by
  rw [isoCompletion_of_le le_rfl]
  simp

theorem fw_two :
    isoCompletion Φ (fun k => if k = 0 then (⊥ : Submodule F V) else U) 1 2 = Φ.perp U := by
  have h := isoCompletion_perp (F := Φ)
    (X := fun k => if k = 0 then (⊥ : Submodule F V) else U) (m := 1) (k := 1) le_rfl
  simpa using h

theorem fw_of_ge {k : ℕ} (hk : 3 ≤ k) :
    isoCompletion Φ (fun k => if k = 0 then (⊥ : Submodule F V) else U) 1 k = ⊤ := by
  rcases hk.eq_or_lt with rfl | hk
  · have h := isoCompletion_top (F := Φ)
      (X := fun k => if k = 0 then (⊥ : Submodule F V) else U) (by simp) 1
    simpa using h
  · exact isoCompletion_of_lt (by omega)

theorem fw_mono (hU : Φ.IsTotallyIsotropic U) :
    Monotone (isoCompletion Φ (fun k => if k = 0 then (⊥ : Submodule F V) else U) 1) := by
  refine monotone_nat_of_le_succ (isoCompletion_le_succ (F := Φ)
    (X := fun k => if k = 0 then (⊥ : Submodule F V) else U) ?_ ?_ 1)
  · intro i j hij
    by_cases hi : i = 0
    · simp [hi]
    · simp [hi, show j ≠ 0 by omega]
  · intro k
    by_cases hk : k = 0
    · simp only [hk, if_true]
      exact bot_le
    · simpa [hk] using hU

theorem mem_Urad_iff [Finite V] (hU : Φ.IsTotallyIsotropic U) (hρ : IsIsometric Φ ρ) {u : H} :
    u ∈ Urad Φ ρ U ↔ (∀ v ∈ U, ρ u v = v) ∧ (∀ v ∈ Φ.perp U, ρ u v - v ∈ U) := by
  unfold Urad
  constructor
  · intro h
    have hlow := ((mem_flagKernel ρ).mp h).2
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · have hv' : v ∈ isoCompletion Φ (fun k => if k = 0 then (⊥ : Submodule F V) else U) 1 1 := by
        rw [fw_one]
        exact hv
      have h0 := hlow 0 v hv'
      rw [fw_zero, Submodule.mem_bot, sub_eq_zero] at h0
      exact h0
    · have hv' : v ∈ isoCompletion Φ (fun k => if k = 0 then (⊥ : Submodule F V) else U) 1 2 := by
        rw [fw_two]
        exact hv
      have h1 := hlow 1 v hv'
      rwa [fw_one] at h1
  · rintro ⟨h1, h2⟩
    refine mem_flagKernel_of_sub_mem' ρ (fw_mono hU) fw_zero ?_
    intro k v hv
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k) with rfl | rfl | rfl | hk
    · have hvU : v ∈ U := by
        rw [← fw_one (Φ := Φ) (U := U)]
        exact hv
      rw [fw_zero, Submodule.mem_bot, sub_eq_zero]
      exact h1 v hvU
    · have hvP : v ∈ Φ.perp U := by
        rw [← fw_two (Φ := Φ) (U := U)]
        exact hv
      rw [fw_one]
      exact h2 v hvP
    · rw [fw_two]
      intro w hw
      have h3 := hρ u w v
      rw [h1 w hw] at h3
      rw [Φ.β_sub_right, h3, sub_self]
    · rw [fw_of_ge (by omega)]
      exact Submodule.mem_top

theorem urad_isPGroup [CharP F 2] (hinj : Function.Injective ρ) :
    IsPGroup 2 (Urad Φ ρ U) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold Urad
  exact isPGroup_flagKernel ρ 2 hinj fw_zero (m := 3) (fw_of_ge le_rfl)

theorem mem_flagStab_Fw [Finite V] (hU : Φ.IsTotallyIsotropic U) (hρ : IsIsometric Φ ρ) {u : H} :
    u ∈ flagStab ρ (isoCompletion Φ (fun k => if k = 0 then (⊥ : Submodule F V) else U) 1) ↔
      (∀ v ∈ U, ρ u v ∈ U) ∧ (∀ v ∈ Φ.perp U, ρ u v ∈ Φ.perp U) := by
  constructor
  · intro h
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · have hv' : v ∈ isoCompletion Φ (fun k => if k = 0 then (⊥ : Submodule F V) else U) 1 1 := by
        rw [fw_one]
        exact hv
      have h1 := flagStab_apply_mem ρ h hv'
      rwa [fw_one] at h1
    · have hv' : v ∈ isoCompletion Φ (fun k => if k = 0 then (⊥ : Submodule F V) else U) 1 2 := by
        rw [fw_two]
        exact hv
      have h2 := flagStab_apply_mem ρ h hv'
      rwa [fw_two] at h2
  · rintro ⟨h1, h2⟩
    refine mem_flagStab_of_forall' ρ fun k v hv => ?_
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k) with rfl | rfl | rfl | hk
    · rw [fw_zero, Submodule.mem_bot] at hv ⊢
      rw [hv, map_zero]
    · rw [fw_one] at hv ⊢
      exact h1 v hv
    · rw [fw_two] at hv ⊢
      exact h2 v hv
    · rw [fw_of_ge hk]
      exact Submodule.mem_top

end UradAPI

end FormsCases

end CFSG.LieType.ChevTwo.OppCl
