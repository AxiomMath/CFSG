
module

public import CFSG.GF2Type.Smith1979.GammaU.StepABase

public section

namespace CFSG.GF2Type.Smith1979.GammaU.StepA

open CFSG.GF2Type.Smith1979.GammaU Module

theorem mem_map_conj_inv' {g l : V12 ≃ₗ[ZMod 2] V12} {L : Subgroup (V12 ≃ₗ[ZMod 2] V12)} :
    l ∈ L.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * l * g⁻¹ ∈ L := by
  rw [mem_map_conj]
  constructor
  · rintro ⟨l₀, hl₀, rfl⟩
    rw [show g * (g⁻¹ * l₀ * g⁻¹⁻¹) * g⁻¹ = l₀ by group]
    exact hl₀
  · intro h
    exact ⟨g * l * g⁻¹, h, by group⟩

theorem saMonoid_perm {m : ℕ} (T : ℕ → V12 ≃ₗ[ZMod 2] V12)
    (hsa : ∀ r ∈ saGens, ∀ j < m, ∃ j' < m,
      ((spanOf d0).map (T j : V12 →ₗ[ZMod 2] V12)).map (linOfRows r) =
        (spanOf d0).map (T j' : V12 →ₗ[ZMod 2] V12))
    {h : V12 ≃ₗ[ZMod 2] V12} (hh : h ∈ Submonoid.closure saSet) :
    ∀ j < m, ∃ j' < m, ((spanOf d0).map (T j : V12 →ₗ[ZMod 2] V12)).map (h : V12 →ₗ[ZMod 2] V12) =
      (spanOf d0).map (T j' : V12 →ₗ[ZMod 2] V12) := by
  induction hh using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨r, hr, hxr⟩ := hx
    intro j hj
    obtain ⟨j', hj', he⟩ := hsa r hr j hj
    refine ⟨j', hj', ?_⟩
    rw [← he]
    have e : (x : V12 →ₗ[ZMod 2] V12) = linOfRows r := LinearMap.ext hxr
    rw [e]
  | one =>
    intro j hj
    refine ⟨j, hj, ?_⟩
    have e : ((1 : V12 ≃ₗ[ZMod 2] V12) : V12 →ₗ[ZMod 2] V12) = LinearMap.id := rfl
    rw [e, Submodule.map_id]
  | mul x y _ _ hx hy =>
    intro j hj
    obtain ⟨j₁, hj₁, h₁⟩ := hy j hj
    obtain ⟨j₂, hj₂, h₂⟩ := hx j₁ hj₁
    refine ⟨j₂, hj₂, ?_⟩
    have e : ((x * y : V12 ≃ₗ[ZMod 2] V12) : V12 →ₗ[ZMod 2] V12) =
        (x : V12 →ₗ[ZMod 2] V12).comp (y : V12 →ₗ[ZMod 2] V12) := rfl
    rw [e, Submodule.map_comp, h₁, h₂]

theorem frame_at_a0 (h16963 : StepAOrbitFacts) (h16964 : StepATFacts)
    {m : ℕ} (T : ℕ → V12 ≃ₗ[ZMod 2] V12)
    (hT : ∀ j < m, T j ∈ gammaU ∧ T j (vecOf a0) = vecOf a0)
    (h0 : ∃ j < m, (spanOf d0).map (T j : V12 →ₗ[ZMod 2] V12) = spanOf d0)
    (hsa : ∀ r ∈ saGens, ∀ j < m, ∃ j' < m,
      ((spanOf d0).map (T j : V12 →ₗ[ZMod 2] V12)).map (linOfRows r) =
        (spanOf d0).map (T j' : V12 →ₗ[ZMod 2] V12))
    {D : Submodule (ZMod 2) V12} {L : Subgroup (V12 ≃ₗ[ZMod 2] V12)}
    (H : Hyp (vecOf a0) D L) :
    ∃ j < m, ∃ c < 32, D = (spanOf d0).map (T j : V12 →ₗ[ZMod 2] V12) ∧
      ∀ l, l ∈ L ↔ ∃ r ∈ compOf c, ∀ x, ((T j)⁻¹ * l * T j) x = linOfRows r x := by
  obtain ⟨rep, hrep, h₂, hh₂m, hD⟩ := h16963.exists_rep D H.sing H.finrank_eq H.mem
  by_cases hne : rep = d0
  · subst hne
    obtain ⟨j₀, hj₀, he₀⟩ := h0
    obtain ⟨j, hj, hsj⟩ := saMonoid_perm T hsa hh₂m j₀ hj₀
    have hDj : D = (spanOf d0).map (T j : V12 →ₗ[ZMod 2] V12) := by
      rw [hD, ← hsj, he₀]
    obtain ⟨hTj, ha⟩ := hT j hj
    have H₂ := H.conj (inv_mem hTj)
    have ha' : (T j)⁻¹ (vecOf a0) = vecOf a0 := by
      conv_lhs => rw [← ha]
      exact inv_apply_apply (T j) _
    have hD₂ : D.map (((T j)⁻¹ : V12 ≃ₗ[ZMod 2] V12) : V12 →ₗ[ZMod 2] V12) = spanOf d0 := by
      ext y
      rw [hDj, Submodule.mem_map]
      constructor
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hw
        change (T j)⁻¹ (T j z) ∈ spanOf d0
        rwa [inv_apply_apply]
      · intro hy
        exact ⟨T j y, Submodule.mem_map_of_mem hy, inv_apply_apply (T j) y⟩
    rw [ha', hD₂] at H₂
    obtain ⟨c, hc, hcL⟩ := comp_of_d0 h16964 H₂
    refine ⟨j, hj, c, hc, hDj, fun l => ?_⟩
    rw [← hcL, mem_map_conj_inv']
    constructor
    · intro hl
      convert hl using 1
      group
    · intro hl
      convert hl using 1
      group
  · exfalso
    obtain ⟨hh₂, ha₂⟩ := saMonoid_spec h16963 hh₂m
    have H₂ := H.conj (inv_mem hh₂)
    have hD₂ : D.map ((h₂⁻¹ : V12 ≃ₗ[ZMod 2] V12) : V12 →ₗ[ZMod 2] V12) = spanOf rep := by
      rw [hD, map_inv_map]
    have ha₂' : h₂⁻¹ (vecOf a0) = vecOf a0 := by
      conv_lhs => rw [← ha₂]
      exact inv_apply_apply h₂ _
    rw [ha₂', hD₂] at H₂
    exact false_of_bad h16964 hrep hne H₂

theorem frame_at (h16963 : StepAOrbitFacts) (h16964 : StepATFacts)
    {m : ℕ} (T : ℕ → V12 ≃ₗ[ZMod 2] V12)
    (hT : ∀ j < m, T j ∈ gammaU ∧ T j (vecOf a0) = vecOf a0)
    (h0 : ∃ j < m, (spanOf d0).map (T j : V12 →ₗ[ZMod 2] V12) = spanOf d0)
    (hsa : ∀ r ∈ saGens, ∀ j < m, ∃ j' < m,
      ((spanOf d0).map (T j : V12 →ₗ[ZMod 2] V12)).map (linOfRows r) =
        (spanOf d0).map (T j' : V12 →ₗ[ZMod 2] V12))
    {g : V12 ≃ₗ[ZMod 2] V12} (hg : g ∈ gammaU)
    {D : Submodule (ZMod 2) V12} {L : Subgroup (V12 ≃ₗ[ZMod 2] V12)}
    (H : Hyp (g (vecOf a0)) D L) :
    ∃ j < m, ∃ c < 32, D = (spanOf d0).map ((g * T j : V12 ≃ₗ[ZMod 2] V12) : V12 →ₗ[ZMod 2] V12) ∧
      ∀ l, l ∈ L ↔ ∃ r ∈ compOf c, ∀ x, ((g * T j)⁻¹ * l * (g * T j)) x = linOfRows r x := by
  have H₁ := H.conj (inv_mem hg)
  rw [inv_apply_apply] at H₁
  obtain ⟨j, hj, c, hc, hD, hL⟩ := frame_at_a0 h16963 h16964 T hT h0 hsa H₁
  refine ⟨j, hj, c, hc, ?_, fun l => ?_⟩
  · ext y
    constructor
    · intro hy
      have hy' : g⁻¹ y ∈ D.map ((g⁻¹ : V12 ≃ₗ[ZMod 2] V12) : V12 →ₗ[ZMod 2] V12) :=
        Submodule.mem_map_of_mem hy
      rw [hD] at hy'
      obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.1 hy'
      refine Submodule.mem_map.2 ⟨z, hz, ?_⟩
      change g (T j z) = y
      rw [show (T j : V12 →ₗ[ZMod 2] V12) z = T j z from rfl] at hzy
      rw [hzy, apply_inv_apply]
    · intro hy
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
      have hz' : T j z ∈ D.map ((g⁻¹ : V12 ≃ₗ[ZMod 2] V12) : V12 →ₗ[ZMod 2] V12) := by
        rw [hD]
        exact Submodule.mem_map_of_mem hz
      obtain ⟨w, hw, hwz⟩ := Submodule.mem_map.1 hz'
      change g (T j z) ∈ D
      rw [← hwz]
      change g (g⁻¹ w) ∈ D
      rwa [apply_inv_apply]
  · rw [show l ∈ L ↔ g⁻¹ * l * g ∈ L.map (MulAut.conj g⁻¹).toMonoidHom by
      rw [mem_map_conj_inv']
      constructor
      · intro hl
        convert hl using 1
        group
      · intro hl
        convert hl using 1
        group, hL]
    constructor
    · rintro ⟨r, hr, hx⟩
      refine ⟨r, hr, fun x => ?_⟩
      rw [← hx x]
      simp only [mul_inv_rev, mul_assoc]
    · rintro ⟨r, hr, hx⟩
      refine ⟨r, hr, fun x => ?_⟩
      rw [← hx x]
      simp only [mul_inv_rev, mul_assoc]

end CFSG.GF2Type.Smith1979.GammaU.StepA
