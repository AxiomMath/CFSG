module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSwapBar

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable {X : Type*} [Group X]

theorem fixSub_comp_subtype (ρ : X →* (V ≃ₗ[k] V)) (A : Subgroup X) (B : Subgroup ↥A) :
    fixSub (ρ.comp A.subtype) B = fixSub ρ (B.map A.subtype) := by
  ext v
  simp only [mem_fixSub, Subgroup.mem_map]
  constructor
  · rintro h _ ⟨b, hb, rfl⟩
    exact h b hb
  · intro h b hb
    exact h _ ⟨b, hb, rfl⟩

theorem weight_comp_subtype (ρ : X →* (V ≃ₗ[k] V)) (A : Subgroup X) (B : Subgroup ↥A) :
    weight (ρ.comp A.subtype) B = weight ρ (B.map A.subtype) := by
  unfold weight
  rw [fixSub_comp_subtype, Subgroup.card_map_of_injective A.subtype_injective]

theorem map_subtype_top (A : Subgroup X) : (⊤ : Subgroup ↥A).map A.subtype = A := by
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem map_mul_eq {M : Type*} [AddCommGroup M] [Module k M] (τ : X →* (M ≃ₗ[k] M)) (x y : X)
    (S : Submodule k M) :
    S.map (τ (x * y) : M →ₗ[k] M) = (S.map (τ y : M →ₗ[k] M)).map (τ x : M →ₗ[k] M) := by
  ext z
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨τ y s, ⟨s, hs, rfl⟩, by simp [map_mul]⟩
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s, hs, by simp [map_mul]⟩

theorem map_inv_map {M : Type*} [AddCommGroup M] [Module k M] (τ : X →* (M ≃ₗ[k] M)) (x : X)
    (S : Submodule k M) : (S.map (τ x : M →ₗ[k] M)).map (τ x⁻¹ : M →ₗ[k] M) = S := by
  rw [← map_mul_eq, inv_mul_cancel]
  ext z
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨s, hs, rfl⟩
    simpa using hs
  · intro hz
    exact ⟨z, hz, by simp⟩

section Normal

variable (ρ : X →* (V ≃ₗ[k] V)) (H A : Subgroup X) [H.Normal]

theorem isSwap_bar (hAel : CFSG.IsElementaryAbelian 2 A) (hHA : ⁅H, A⁆ = H) {a : X} (ha : a ∈ A)
    (hq : ∀ b ∈ A, ∀ v, ρ b (ρ a v - v) = ρ a v - v) {I : Submodule k V}
    (hI : IsGoodModule ρ H I) (hmove : ¬ I.map (ρ a : V →ₗ[k] V) ≤ I) :
    IsSwap (barHom ρ H) H A a (I.map (bar ρ H)) := by
  have hI₂ : IsGoodModule ρ H (I.map (ρ a : V →ₗ[k] V)) := hI.map (mem_normalizer_of_normal H a)
  have := hAel
  refine ⟨fun x _ => mem_normalizer_of_normal H x, hHA, ha, ?_, ?_, hI.isSimpleSub_bar,
    hI.not_le_fixSub_bar, ?_, ?_⟩
  · have h2 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) a ha
    rwa [pow_two] at h2
  · intro b hb
    have h := hAel.toIsMulCommutative.is_comm.comm (⟨a, ha⟩ : ↥A) ⟨b, hb⟩
    exact congrArg Subtype.val h
  · have hne : I.map (bar ρ H) ≠ (I.map (ρ a : V →ₗ[k] V)).map (bar ρ H) := fun h =>
      hmove (hI.eq_of_map_bar_eq hI₂ h).symm.le
    have := hI.isSimpleSub_bar.inf_eq_bot_of_ne hI₂.isSimpleSub_bar hne
    rwa [map_map_bar] at this
  · intro b hb y hy
    obtain ⟨x, hx, rfl⟩ := hy
    show barHom ρ H b (barHom ρ H a (bar ρ H x) - bar ρ H x) =
      barHom ρ H a (bar ρ H x) - bar ρ H x
    rw [barHom_bar, ← map_sub, barHom_bar, hq b hb x]

variable [Finite V]

theorem swap_invariant (hAel : CFSG.IsElementaryAbelian 2 A) (hHA : ⁅H, A⁆ = H) {a : X}
    (ha : a ∈ A) (hq : ∀ b ∈ A, ∀ v, ρ b (ρ a v - v) = ρ a v - v) {I : Submodule k V}
    (hI : IsGoodModule ρ H I) (hmove : ¬ I.map (ρ a : V →ₗ[k] V) ≤ I) :
    Offender.IsInvariant ρ A (I ⊔ I.map (ρ a : V →ₗ[k] V)) ∧
      commSub ρ H (I ⊔ I.map (ρ a : V →ₗ[k] V)) = I ⊔ I.map (ρ a : V →ₗ[k] V) := by
  have hS := isSwap_bar ρ H A hAel hHA ha hq hI hmove
  have hI₂ : IsGoodModule ρ H (I.map (ρ a : V →ₗ[k] V)) := hI.map (mem_normalizer_of_normal H a)
  have hWH : Offender.IsInvariant ρ H (I ⊔ I.map (ρ a : V →ₗ[k] V)) :=
    isInvariant_sup' hI.inv hI₂.inv
  have hWc : commSub ρ H (I ⊔ I.map (ρ a : V →ₗ[k] V)) = I ⊔ I.map (ρ a : V →ₗ[k] V) := by
    refine le_antisymm (commSub_le_of_isInvariant hWH) ?_
    calc I ⊔ I.map (ρ a : V →ₗ[k] V) = commSub ρ H I ⊔ commSub ρ H (I.map (ρ a : V →ₗ[k] V)) := by
          rw [hI.comm, hI₂.comm]
      _ ≤ commSub ρ H (I ⊔ I.map (ρ a : V →ₗ[k] V)) :=
          sup_le (commSub_mono_right ρ le_sup_left) (commSub_mono_right ρ le_sup_right)
  refine ⟨?_, hWc⟩
  set D : Submodule k V := I.map ((ρ a : V →ₗ[k] V) - LinearMap.id) with hD
  set U : Submodule k V := spanOrbit ρ H D with hU
  have hDW : D ≤ I ⊔ I.map (ρ a : V →ₗ[k] V) := by
    rintro _ ⟨x, hx, rfl⟩
    show ρ a x - x ∈ I ⊔ I.map (ρ a : V →ₗ[k] V)
    exact Submodule.sub_mem _ (Submodule.mem_sup_right (show ρ a x ∈ I.map (ρ a : V →ₗ[k] V) from
      ⟨x, hx, rfl⟩)) (Submodule.mem_sup_left hx)
  have hUW : U ≤ I ⊔ I.map (ρ a : V →ₗ[k] V) := spanOrbit_le hWH hDW
  have hUH : Offender.IsInvariant ρ H U := isInvariant_spanOrbit ρ H D
  have hDfix : ∀ b ∈ A, ∀ d ∈ D, ρ b d = d := by
    rintro b hb _ ⟨x, hx, rfl⟩
    exact hq b hb x
  have hUA : Offender.IsInvariant ρ A U := by
    intro b hb u hu
    induction hu using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨h, hh, d, hd, rfl⟩ := hw
      refine Submodule.subset_span ⟨b * h * b⁻¹,
        conj_mem_of_mem_normalizer (mem_normalizer_of_normal H b) hh, d, hd, ?_⟩
      rw [ρ_mul_apply, ρ_mul_apply, hDfix b⁻¹ (A.inv_mem hb) d hd]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx
  have hbarD : swapD (barHom ρ H) a (I.map (bar ρ H)) = D.map (bar ρ H) := by
    ext d
    rw [mem_swapD]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨ρ a x - x, ⟨x, hx, rfl⟩, ?_⟩
      rw [map_sub, barHom_bar]
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨bar ρ H x, ⟨x, hx, rfl⟩, ?_⟩
      show barHom ρ H a (bar ρ H x) - bar ρ H x = bar ρ H (ρ a x - x)
      rw [map_sub, barHom_bar]
  have hbarW : (I ⊔ I.map (ρ a : V →ₗ[k] V)).map (bar ρ H) =
      I.map (bar ρ H) ⊔ (I.map (bar ρ H)).map (barHom ρ H a : (V ⧸ fixSub ρ H) →ₗ[k] (V ⧸ fixSub ρ H)) := by
    rw [Submodule.map_sup, map_map_bar]
  have key : (I ⊔ I.map (ρ a : V →ₗ[k] V)).map (bar ρ H) ≤ U.map (bar ρ H) := by
    rw [hbarW]
    refine hS.sup_le_of_invariant (isInvariant_map_bar ρ H hUH) ?_ ?_
    · rw [hbarD]; exact Submodule.map_mono (le_spanOrbit ρ H D)
    · rw [← hbarW]; exact Submodule.map_mono hUW
  have hWU : I ⊔ I.map (ρ a : V →ₗ[k] V) ≤ U ⊔ fixSub ρ H := by
    intro w hw
    obtain ⟨u, hu, hub⟩ := key ⟨w, hw, rfl⟩
    have h1 : u - w ∈ fixSub ρ H := (bar_eq_bar_iff ρ H).1 hub
    have : w = u + -(u - w) := by abel
    rw [this]
    exact Submodule.add_mem_sup hu ((fixSub ρ H).neg_mem h1)
  have hWU' : I ⊔ I.map (ρ a : V →ₗ[k] V) ≤ U := calc
    I ⊔ I.map (ρ a : V →ₗ[k] V) = commSub ρ H (I ⊔ I.map (ρ a : V →ₗ[k] V)) := hWc.symm
    _ ≤ commSub ρ H (U ⊔ fixSub ρ H) := commSub_mono_right ρ hWU
    _ = commSub ρ H U := commSub_sup_of_le_fixSub ρ H U _ le_rfl
    _ ≤ U := commSub_le_of_isInvariant hUH
  have hUeq : U = I ⊔ I.map (ρ a : V →ₗ[k] V) := le_antisymm hUW hWU'
  rw [← hUeq]
  exact hUA

end Normal

end CFSG.QuasithinUnique.Setup.Layer
