module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Comb
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BHeartPhi

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem heart_permVec_one (v : Fin 8 → ZMod 2) : permVec (1 : Equiv.Perm (Fin 8)) v = v := by
  funext i
  rfl

theorem heart_permVec_injective (σ : Equiv.Perm (Fin 8)) {v w : Fin 8 → ZMod 2}
    (h : permVec σ v = permVec σ w) : v = w := by
  have h1 : permVec σ⁻¹ (permVec σ v) = permVec σ⁻¹ (permVec σ w) := by rw [h]
  rwa [← sec5b_permVec_mul, ← sec5b_permVec_mul, inv_mul_cancel, heart_permVec_one,
    heart_permVec_one] at h1

theorem HeartData.relabel {φ : (Fin 8 → ZMod 2) → G} {A M : Subgroup G}
    {Alt : Subgroup (Equiv.Perm (Fin 8))} (hd : HeartData φ A M Alt) {σ : Equiv.Perm (Fin 8)}
    (hσ : σ ∈ Alt) : HeartData (fun v => φ (permVec σ v)) A M Alt where
  mem v hv := hd.mem _ (isEvenVec_permVec σ hv)
  add v w hv hw := by
    show φ (permVec σ (v + w)) = φ (permVec σ v) * φ (permVec σ w)
    rw [sec5b_permVec_add]
    exact hd.add _ _ (isEvenVec_permVec σ hv) (isEvenVec_permVec σ hw)
  add_one v hv := by
    show φ (permVec σ (v + 1)) = φ (permVec σ v)
    rw [sec5b_permVec_add, sec5b_permVec_one]
    exact hd.add_one _ (isEvenVec_permVec σ hv)
  inj v w hv hw h := by
    rcases hd.inj _ _ (isEvenVec_permVec σ hv) (isEvenVec_permVec σ hw) h with h1 | h1
    · exact Or.inl (heart_permVec_injective σ h1)
    · refine Or.inr (heart_permVec_injective σ ?_)
      rw [h1, sec5b_permVec_add, sec5b_permVec_one]
  surj x hx := by
    obtain ⟨u, hu, rfl⟩ := hd.surj x hx
    refine ⟨permVec σ⁻¹ u, isEvenVec_permVec _ hu, ?_⟩
    show φ (permVec σ (permVec σ⁻¹ u)) = φ u
    rw [← sec5b_permVec_mul, mul_inv_cancel, heart_permVec_one]
  act h hh := by
    obtain ⟨ρ, hρ, hρact⟩ := hd.act h hh
    refine ⟨σ⁻¹ * ρ * σ, mul_mem (mul_mem (inv_mem hσ) hρ) hσ, fun v hv => ?_⟩
    show h * φ (permVec σ v) * h⁻¹ = φ (permVec σ (permVec (σ⁻¹ * ρ * σ) v))
    rw [hρact _ (isEvenVec_permVec σ hv), ← sec5b_permVec_mul, ← sec5b_permVec_mul]
    congr 2
    group
  lift τ hτ := by
    obtain ⟨h, hh, hact⟩ := hd.lift (σ * τ * σ⁻¹) (mul_mem (mul_mem hσ hτ) (inv_mem hσ))
    refine ⟨h, hh, fun v hv => ?_⟩
    show h * φ (permVec σ v) * h⁻¹ = φ (permVec σ (permVec τ v))
    rw [hact _ (isEvenVec_permVec σ hv), ← sec5b_permVec_mul, ← sec5b_permVec_mul]
    congr 2
    group

theorem HeartData.map_zero {φ : (Fin 8 → ZMod 2) → G} {A M : Subgroup G}
    {Alt : Subgroup (Equiv.Perm (Fin 8))} (hd : HeartData φ A M Alt) : φ 0 = 1 := by
  have h := hd.add 0 0 sec5b_isEvenVec_zero sec5b_isEvenVec_zero
  rw [add_zero] at h
  exact mul_left_cancel (a := φ 0) (by rw [mul_one]; exact h.symm)

theorem HeartData.map_one {φ : (Fin 8 → ZMod 2) → G} {A M : Subgroup G}
    {Alt : Subgroup (Equiv.Perm (Fin 8))} (hd : HeartData φ A M Alt) : φ 1 = 1 := by
  have h := hd.add_one 0 sec5b_isEvenVec_zero
  rwa [zero_add, hd.map_zero] at h

theorem HeartData.toPermModuleMod {φ : (Fin 8 → ZMod 2) → G} {A M : Subgroup G}
    {Alt : Subgroup (Equiv.Perm (Fin 8))} (hd : HeartData φ A M Alt)
    (hM : M ≤ normalizer (A : Set G)) :
    IsPermModuleMod (n := 8) IsEvenVec ({0, fun _ => 1} : Set (Fin 8 → ZMod 2)) φ A ⊥ M Alt := by
  have key : ∀ a : ZMod 2, 0 = a + 1 → a = 1 := by decide
  refine ⟨bot_le, ?_, hM, ?_, hd.mem, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.bot_subgroupOf]
    exact Subgroup.normal_bot
  · intro g _
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp only [SetLike.mem_coe, Subgroup.mem_bot]
    constructor
    · rintro rfl
      simp
    · intro h
      exact mul_eq_left.mp (mul_inv_eq_one.mp h)
  · intro v w hv hw
    rw [hd.add v w hv hw, inv_mul_cancel]
    exact Subgroup.one_mem _
  · intro v hv
    constructor
    · intro hmem
      have hφv : φ v = 1 := Subgroup.mem_bot.mp hmem
      rcases hd.inj v 0 hv sec5b_isEvenVec_zero (by rw [hφv, hd.map_zero]) with h | h
      · exact Or.inl h.symm
      · refine Or.inr ?_
        funext i
        exact key (v i) (congrFun h i)
    · rintro (h | h)
      · rw [h, hd.map_zero]
        exact Subgroup.one_mem _
      · have h1 : v = 1 := h
        rw [h1, hd.map_one]
        exact Subgroup.one_mem _
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := hd.surj x hx
    exact ⟨v, hv, by rw [inv_mul_cancel]; exact Subgroup.one_mem _⟩
  · intro h hh
    obtain ⟨σ, hσ, hact⟩ := hd.act h hh
    exact ⟨σ, hσ, fun v hv => by rw [hact v hv, inv_mul_cancel]; exact Subgroup.one_mem _⟩
  · intro σ hσ
    obtain ⟨h, hh, hact⟩ := hd.lift σ hσ
    exact ⟨h, hh, fun v hv => by rw [hact v hv, inv_mul_cancel]; exact Subgroup.one_mem _⟩

end CFSG.OddStandard.SmallF3.Omega
