module

public import CFSG.GF2Type.Widths1112.Good

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial

namespace CFSG.GF2Type.Widths1112

variable {G : Type} [Group G] [Finite G]

theorem goodThroughSingular_of_native (S : Setting G) {n : ℕ} {Γ : Type}
    (e : S.Mbar ≃ Γ) (ψ : S.Qt ≃ₗ[ZMod 2] (Fin n → ZMod 2))
    (act : Γ → Module.End (ZMod 2) (Fin n → ZMod 2))
    (hψ : ∀ (m : S.Mbar) (v : S.Qt),
      ψ (((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = act (e m) (ψ v))
    (q₀ : (Fin n → ZMod 2) → ZMod 2) (hq : ∀ v, S.q v = q₀ (ψ v))
    (good : Set (Fin n → ZMod 2))
    (hgood : ∀ u ∈ good, u ≠ 0 ∧ q₀ u = 0 ∧
      ∀ Y : Submodule (ZMod 2) (Fin n → ZMod 2), u ∈ Y →
        (∀ y ∈ Y, QuadraticMap.polar q₀ y u = 0) →
        (∀ A : Γ, act A u = u → ∀ y ∈ Y, act A y ∈ Y) →
        Y = Submodule.span (ZMod 2) {u} ∨ ∀ y, QuadraticMap.polar q₀ y u = 0 → y ∈ Y)
    (hF3 : ∀ v : Fin n → ZMod 2, v ≠ 0 → q₀ v = 0 →
      ∀ U : Submodule (ZMod 2) (Fin n → ZMod 2), v ∈ U → 2 ≤ Module.finrank (ZMod 2) U →
        (∀ u ∈ U, q₀ u = 0) → (∀ A : Γ, act A v = v → ∀ u ∈ U, act A u ∈ U) →
        ∃ u ∈ U, u ≠ v ∧ u ∈ good)
    (hcard : ¬ 2 ^ (2 * S.width - 2) ∣ Nat.card Γ) :
    GoodThroughSingular S := by
  unfold GoodThroughSingular
  have hpol : ∀ a b : S.Qt,
      QuadraticMap.polar S.q a b = QuadraticMap.polar q₀ (ψ a) (ψ b) := by
    intro a b
    simp only [QuadraticMap.polar, map_add, hq]
  have hinj : Function.Injective (ψ : S.Qt →ₗ[ZMod 2] (Fin n → ZMod 2)) := ψ.injective
  have hcardM : Nat.card S.Mbar = Nat.card Γ := Nat.card_congr e
  intro v hv0 hqv U hvU hdim hsing hstab
  have hv'0 : ψ v ≠ 0 := fun h => hv0 (ψ.map_eq_zero_iff.mp h)
  have hqv' : q₀ (ψ v) = 0 := by
    rw [← hq v]
    exact hqv
  have hvU' : ψ v ∈ U.map (ψ : S.Qt →ₗ[ZMod 2] (Fin n → ZMod 2)) :=
    Submodule.mem_map.mpr ⟨v, hvU, rfl⟩
  have hdim' : 2 ≤ Module.finrank (ZMod 2) (U.map (ψ : S.Qt →ₗ[ZMod 2] (Fin n → ZMod 2))) := by
    rw [LinearEquiv.finrank_map_eq]
    exact hdim
  have hsing' : ∀ w ∈ U.map (ψ : S.Qt →ₗ[ZMod 2] (Fin n → ZMod 2)), q₀ w = 0 := by
    intro w hw
    obtain ⟨u, hu, hu'⟩ := Submodule.mem_map.mp hw
    have hu'' : ψ u = w := hu'
    subst hu''
    rw [← hq u]
    exact hsing u hu
  have hinvW : ∀ A : Γ, act A (ψ v) = ψ v →
      ∀ w ∈ U.map (ψ : S.Qt →ₗ[ZMod 2] (Fin n → ZMod 2)),
        act A w ∈ U.map (ψ : S.Qt →ₗ[ZMod 2] (Fin n → ZMod 2)) := by
    intro A hA w hw
    obtain ⟨u, hu, hu'⟩ := Submodule.mem_map.mp hw
    have hu'' : ψ u = w := hu'
    subst hu''
    obtain ⟨m, hm⟩ : ∃ m : S.Mbar, e m = A := ⟨e.symm A, e.apply_symm_apply A⟩
    have hmv : ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
      refine ψ.injective ?_
      rw [hψ m v, hm, hA]
    have hmU : U.map (((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) = U :=
      hstab (m : S.O) m.2 hmv
    have hmu : ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ U := by
      rw [← hmU]
      exact Submodule.mem_map.mpr ⟨u, hu, rfl⟩
    have hAu : act A (ψ u) = ψ (((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u) := by
      rw [hψ m u, hm]
    rw [hAu]
    exact Submodule.mem_map.mpr ⟨_, hmu, rfl⟩
  obtain ⟨u', hu'U, hu'v, hu'good⟩ :=
    hF3 (ψ v) hv'0 hqv' (U.map (ψ : S.Qt →ₗ[ZMod 2] (Fin n → ZMod 2))) hvU' hdim' hsing' hinvW
  obtain ⟨u₀, hu₀U, hu₀⟩ := Submodule.mem_map.mp hu'U
  have hu₀' : ψ u₀ = u' := hu₀
  subst hu₀'
  have hgu := hgood (ψ u₀) hu'good
  obtain ⟨H, hH⟩ : ∃ H : Subgroup S.O, ∀ h : S.O,
      h ∈ H ↔ (h ∈ S.Mbar ∧ ((h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u₀ = u₀) :=
    ⟨{ carrier := {h | h ∈ S.Mbar ∧ ((h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u₀ = u₀}
       mul_mem' := by
         rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
         refine ⟨S.Mbar.mul_mem ha hb, ?_⟩
         show ((a : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((b : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u₀) = u₀
         rw [hb', ha']
       one_mem' := ⟨S.Mbar.one_mem, rfl⟩
       inv_mem' := by
         rintro a ⟨ha, ha'⟩
         exact ⟨S.Mbar.inv_mem ha,
           ((a : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).symm_apply_eq.mpr ha'.symm⟩ }, fun h => Iff.rfl⟩
  have hHM : H ≤ S.Mbar := fun h hh => ((hH h).mp hh).1
  have hHfix : ∀ h ∈ H, ((h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u₀ = u₀ :=
    fun h hh => ((hH h).mp hh).2
  have hirr : ∀ X : Submodule (ZMod 2) S.Qt, u₀ ∈ X →
      X ≤ LinearMap.ker (QuadraticMap.polarBilin S.q u₀) →
      (∀ h ∈ H, X.map (((h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) = X) →
      X = Submodule.span (ZMod 2) {u₀} ∨ X = LinearMap.ker (QuadraticMap.polarBilin S.q u₀) := by
    intro X hXu hXk hXH
    have hYu : ψ u₀ ∈ X.map (ψ : S.Qt →ₗ[ZMod 2] (Fin n → ZMod 2)) :=
      Submodule.mem_map.mpr ⟨u₀, hXu, rfl⟩
    have hYpol : ∀ y ∈ X.map (ψ : S.Qt →ₗ[ZMod 2] (Fin n → ZMod 2)),
        QuadraticMap.polar q₀ y (ψ u₀) = 0 := by
      intro y hy
      obtain ⟨y₀, hy₀X, hy₀⟩ := Submodule.mem_map.mp hy
      have hy₀' : ψ y₀ = y := hy₀
      subst hy₀'
      have h1 : QuadraticMap.polar S.q u₀ y₀ = 0 := by
        have h := hXk hy₀X
        rwa [LinearMap.mem_ker, QuadraticMap.polarBilin_apply_apply] at h
      rw [← hpol, QuadraticMap.polar_comm]
      exact h1
    have hYinv : ∀ A : Γ, act A (ψ u₀) = ψ u₀ →
        ∀ y ∈ X.map (ψ : S.Qt →ₗ[ZMod 2] (Fin n → ZMod 2)),
          act A y ∈ X.map (ψ : S.Qt →ₗ[ZMod 2] (Fin n → ZMod 2)) := by
      intro A hA y hy
      obtain ⟨y₀, hy₀X, hy₀⟩ := Submodule.mem_map.mp hy
      have hy₀' : ψ y₀ = y := hy₀
      subst hy₀'
      obtain ⟨m, hm⟩ : ∃ m : S.Mbar, e m = A := ⟨e.symm A, e.apply_symm_apply A⟩
      have hmu : ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u₀ = u₀ := by
        refine ψ.injective ?_
        rw [hψ m u₀, hm, hA]
      have hmX : X.map (((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) = X :=
        hXH (m : S.O) ((hH (m : S.O)).mpr ⟨m.2, hmu⟩)
      have hmy : ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y₀ ∈ X := by
        rw [← hmX]
        exact Submodule.mem_map.mpr ⟨y₀, hy₀X, rfl⟩
      have hAy : act A (ψ y₀) = ψ (((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y₀) := by
        rw [hψ m y₀, hm]
      rw [hAy]
      exact Submodule.mem_map.mpr ⟨_, hmy, rfl⟩
    rcases hgu.2.2 (X.map (ψ : S.Qt →ₗ[ZMod 2] (Fin n → ZMod 2))) hYu hYpol hYinv with
      hYspan | hYall
    · left
      have hspan : (Submodule.span (ZMod 2) {u₀}).map (ψ : S.Qt →ₗ[ZMod 2] (Fin n → ZMod 2)) =
          X.map (ψ : S.Qt →ₗ[ZMod 2] (Fin n → ZMod 2)) := by
        rw [hYspan, Submodule.map_span, Set.image_singleton]
        rfl
      exact (Submodule.map_injective_of_injective hinj hspan).symm
    · right
      apply le_antisymm hXk
      intro y₀ hy₀
      have hy₀' : QuadraticMap.polar S.q u₀ y₀ = 0 := by
        rwa [LinearMap.mem_ker, QuadraticMap.polarBilin_apply_apply] at hy₀
      have hmem : ψ y₀ ∈ X.map (ψ : S.Qt →ₗ[ZMod 2] (Fin n → ZMod 2)) :=
        hYall (ψ y₀) (by rw [← hpol, QuadraticMap.polar_comm]; exact hy₀')
      obtain ⟨x, hxX, hx⟩ := Submodule.mem_map.mp hmem
      have hx' : ψ x = ψ y₀ := hx
      have hxy : x = y₀ := ψ.injective hx'
      rw [← hxy]
      exact hxX
  refine ⟨u₀, hu₀U, fun h => hu'v (by rw [h]), ?_⟩
  unfold IsGood
  refine ⟨fun h => hgu.1 (by rw [h, map_zero]), (hq u₀).trans hgu.2.1, ?_, H, hHM, hHfix, hirr⟩
  rw [hcardM]
  exact hcard

end CFSG.GF2Type.Widths1112
