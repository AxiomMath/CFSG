module

public import CFSG.LieType.ChevTwo.OppCl.Defs

public section

namespace CFSG.LieType.ChevTwo.OppCl

open CFSG.Open CFSG.LieType.BorelTits

namespace FormsCases

section SplitAPI

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
variable {Φ : ReflForm F V} {TS : Submodule F V → Prop} {W M W' : Submodule F V}

theorem split3_decomp (hS : Split3 Φ TS W M W') (v : V) :
    ∃ w ∈ W, ∃ m ∈ M, ∃ w' ∈ W', v = w + m + w' := by
  have hv : v ∈ W ⊔ M ⊔ W' := by
    rw [hS.sup_eq]
    exact Submodule.mem_top
  obtain ⟨a, ha, w', hw', rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨w, hw, m, hm, rfl⟩ := Submodule.mem_sup.mp ha
  exact ⟨w, hw, m, hm, w', hw', rfl⟩

theorem split3_kernel_W' (hS : Split3 Φ TS W M W') (hW' : Φ.IsTotallyIsotropic W') :
    ∀ u ∈ W', (∀ w ∈ W, Φ.β w u = 0) → u = 0 := by
  intro u hu hu0
  apply Φ.nondeg
  intro v
  obtain ⟨w, hw, m, hm, w', hw', rfl⟩ := split3_decomp hS v
  have h1 : Φ.β u w = 0 := Φ.refl _ _ (hu0 w hw)
  have h2 : Φ.β u m = 0 := Φ.refl _ _ (hS.perp_MW' m hm u hu)
  have h3 : Φ.β u w' = 0 := (Φ.mem_perp.mp (hW' hw')) u hu
  rw [Φ.add_right, Φ.add_right, h1, h2, h3, add_zero, add_zero]

theorem split3_kernel_W (hS : Split3 Φ TS W M W') (hW : Φ.IsTotallyIsotropic W) :
    ∀ u ∈ W, (∀ w' ∈ W', Φ.β w' u = 0) → u = 0 := by
  intro u hu hu0
  apply Φ.nondeg
  intro v
  obtain ⟨w, hw, m, hm, w', hw', rfl⟩ := split3_decomp hS v
  have h1 : Φ.β u w = 0 := (Φ.mem_perp.mp (hW hw)) u hu
  have h2 : Φ.β u m = 0 := hS.perp_WM u hu m hm
  have h3 : Φ.β u w' = 0 := Φ.refl _ _ (hu0 w' hw')
  rw [Φ.add_right, Φ.add_right, h1, h2, h3, add_zero, add_zero]

theorem split3_perp_W (hS : Split3 Φ TS W M W') (hW : Φ.IsTotallyIsotropic W)
    (hW' : Φ.IsTotallyIsotropic W') : Φ.perp W = W ⊔ M := by
  have hle : W ⊔ M ≤ Φ.perp W :=
    sup_le hW fun m hm w hw => hS.perp_WM w hw m hm
  refine le_antisymm (fun v hv => ?_) hle
  obtain ⟨w₀, hw₀, m, hm, w', hw', rfl⟩ := split3_decomp hS v
  have ha : w₀ + m ∈ Φ.perp W := hle (Submodule.add_mem_sup hw₀ hm)
  have hw'0 : w' = 0 := by
    refine split3_kernel_W' hS hW' w' hw' fun w hw => ?_
    have h1 := (Φ.mem_perp.mp hv) w hw
    rwa [Φ.add_right, (Φ.mem_perp.mp ha) w hw, zero_add] at h1
  rw [hw'0, add_zero]
  exact Submodule.add_mem_sup hw₀ hm

theorem toDual_surjective_aux [FiniteDimensional F V] (Φ : ReflForm F V) (φ : Module.Dual F V) :
    ∃ v₀, ∀ v, Φ.β v₀ v = φ v := by
  have htop : (⊤ : Submodule F V).map Φ.toDual = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Φ.finrank_map_toDual, finrank_top, Subspace.dual_finrank_eq]
  have hφ : φ ∈ (⊤ : Submodule F V).map Φ.toDual := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨v₀, -, hv₀⟩ := hφ
  exact ⟨v₀, fun v => by rw [← Φ.toDual_apply, hv₀]⟩

theorem split3_exists_dual_W' [FiniteDimensional F V] (hS : Split3 Φ TS W M W')
    (hW : Φ.IsTotallyIsotropic W) (hW' : Φ.IsTotallyIsotropic W') (φ : Module.Dual F V)
    (hφ : ∀ v ∈ M ⊔ W', φ v = 0) : ∃ w' ∈ W', ∀ v, Φ.β w' v = φ v := by
  obtain ⟨v₀, hv₀⟩ := toDual_surjective_aux Φ φ
  obtain ⟨w, hw, μ, hμ, w', hw', rfl⟩ := split3_decomp hS v₀
  have hw0 : w = 0 := by
    refine split3_kernel_W hS hW w hw fun w'' hw'' => ?_
    have h0 : φ w'' = 0 := hφ w'' (Submodule.mem_sup_right hw'')
    have h1 := hv₀ w''
    have h2 : Φ.β μ w'' = 0 := hS.perp_MW' μ hμ w'' hw''
    have h3 : Φ.β w' w'' = 0 := (Φ.mem_perp.mp (hW' hw'')) w' hw'
    rw [h0, Φ.add_left, Φ.add_left, h2, h3, add_zero, add_zero] at h1
    exact Φ.refl _ _ h1
  have hμM : ∀ z ∈ M, Φ.β μ z = 0 := by
    intro z hz
    have h0 : φ z = 0 := hφ z (Submodule.mem_sup_left hz)
    have h1 := hv₀ z
    have h2 : Φ.β w z = 0 := hS.perp_WM w hw z hz
    have h3 : Φ.β w' z = 0 := Φ.refl _ _ (hS.perp_MW' z hz w' hw')
    rw [h0, Φ.add_left, Φ.add_left, h2, h3, zero_add, add_zero] at h1
    exact h1
  have hμ0 : μ = 0 := by
    apply Φ.nondeg
    intro v
    obtain ⟨y, hy, z, hz, y', hy', rfl⟩ := split3_decomp hS v
    rw [Φ.add_right, Φ.add_right, Φ.refl _ _ (hS.perp_WM y hy μ hμ), hμM z hz,
      hS.perp_MW' μ hμ y' hy', add_zero, add_zero]
  refine ⟨w', hw', fun v => ?_⟩
  have h := hv₀ v
  rwa [hw0, hμ0, zero_add, zero_add] at h

end SplitAPI

end FormsCases

end CFSG.LieType.ChevTwo.OppCl
