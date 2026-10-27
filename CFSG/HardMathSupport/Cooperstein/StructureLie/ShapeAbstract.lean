module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.ShapeSym

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open Module CFSG.ComponentClassification.OutcomeLocal
open scoped commutatorElement

section Transvection

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem isF2Transvection_conj {t : LinearMap.GeneralLinearGroup (ZMod 2) W}
    (ht : IsF2Transvection t) (g : LinearMap.GeneralLinearGroup (ZMod 2) W) :
    IsF2Transvection (g * t * g⁻¹) := by
  obtain ⟨φ, a, h, hφ, ha, rfl⟩ := (isF2Transvection_iff t).mp ht
  have hgg : ∀ v : W, ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W)
      ((g : W →ₗ[ZMod 2] W) v) = v := fun v => by
    change ((g⁻¹ * g : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) v = v
    rw [inv_mul_cancel]; rfl
  have h' : (φ ∘ₗ ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W))
      ((g : W →ₗ[ZMod 2] W) a) = 0 := by
    rw [LinearMap.comp_apply, hgg]; exact h
  rw [conj_tv g φ a h h']
  refine (isF2Transvection_iff _).mpr ⟨_, _, h', ?_, ?_, rfl⟩
  · intro h0
    apply hφ
    ext v
    have := LinearMap.congr_fun h0 ((g : W →ₗ[ZMod 2] W) v)
    rw [LinearMap.comp_apply, hgg] at this
    simpa using this
  · intro h0
    apply ha
    have := congrArg ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) h0
    rw [hgg] at this
    simpa using this

theorem isF2Transvection_mul_self {t : LinearMap.GeneralLinearGroup (ZMod 2) W}
    (ht : IsF2Transvection t) : t * t = 1 := by
  obtain ⟨φ, a, h, -, -, rfl⟩ := (isF2Transvection_iff t).mp ht
  exact tv_mul_self φ a h

end Transvection

section Rep

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {M : Type*} [Group M]

omit [FiniteDimensional (ZMod 2) W] in
theorem range_eq_closure_conj (ρ : M →* LinearMap.GeneralLinearGroup (ZMod 2) W) (s : M)
    (hgen : ∀ T : Subgroup M, T.Normal → ρ.ker ≤ T → s ∈ T → T = ⊤) :
    ρ.range = Subgroup.closure {x | ∃ g ∈ ρ.range, x = g * ρ s * g⁻¹} := by
  set S : Set (LinearMap.GeneralLinearGroup (ZMod 2) W) := {x | ∃ g ∈ ρ.range, x = g * ρ s * g⁻¹}
  have hSr : S ⊆ ρ.range := by
    rintro _ ⟨g, hg, rfl⟩
    exact ρ.range.mul_mem (ρ.range.mul_mem hg ⟨s, rfl⟩) (ρ.range.inv_mem hg)
  apply le_antisymm
  · have hconj : ∀ g ∈ ρ.range, ∀ y ∈ Subgroup.closure S, g * y * g⁻¹ ∈ Subgroup.closure S := by
      intro g hg y hy
      induction hy using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨g', hg', rfl⟩ := hx
        refine Subgroup.subset_closure ⟨g * g', ρ.range.mul_mem hg hg', ?_⟩
        group
      | one => simp
      | mul a b _ _ ha hb =>
        have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
        rw [this]; exact Subgroup.mul_mem _ ha hb
      | inv a _ ha =>
        have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
        rw [this]; exact Subgroup.inv_mem _ ha
    set T : Subgroup M := (Subgroup.closure S).comap ρ
    have hTn : T.Normal := ⟨fun x hx m => by
      show ρ (m * x * m⁻¹) ∈ Subgroup.closure S
      rw [map_mul, map_mul, map_inv]
      exact hconj _ ⟨m, rfl⟩ _ hx⟩
    have hT : T = ⊤ := hgen T hTn (fun k hk => by
        show ρ k ∈ Subgroup.closure S
        rw [MonoidHom.mem_ker.mp hk]; exact Subgroup.one_mem _)
      (Subgroup.subset_closure ⟨1, ρ.range.one_mem, by simp⟩)
    rintro _ ⟨m, rfl⟩
    have : m ∈ T := by rw [hT]; trivial
    exact this
  · exact (Subgroup.closure_le _).mpr hSr

omit [FiniteDimensional (ZMod 2) W] in
theorem relIndex_map_eq_two (ρ : M →* LinearMap.GeneralLinearGroup (ZMod 2) W) (L : Subgroup M)
    [L.Normal] (s : M) (htr : IsF2Transvection (ρ s))
    (hM : ⊤ ≤ L ⊔ Subgroup.zpowers s ⊔ ρ.ker) (hs : ρ s ∉ L.map ρ) :
    (L.map ρ).relIndex ρ.range = 2 := by
  have hsq := isF2Transvection_mul_self htr
  have hsqM : ρ (s * s) = 1 := by rw [map_mul]; exact hsq
  have hsl : ∀ z ∈ L, ρ s * ρ z * ρ s ∈ L.map ρ := by
    intro z hz
    refine ⟨s * z * s⁻¹, Subgroup.Normal.conj_mem ‹L.Normal› z hz s, ?_⟩
    have : ρ (s * z * s⁻¹) = ρ s * ρ z * ρ s⁻¹ := by simp
    rw [this]
    have h1 : (ρ s)⁻¹ = ρ s := inv_eq_of_mul_eq_one_right hsq
    rw [map_inv, h1]
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨ρ s, ⟨s, rfl⟩, ?_⟩
  rintro _ ⟨m, rfl⟩
  have hm : m ∈ (Subgroup.zpowers s ⊔ ρ.ker) ⊔ L := by
    have h := hM (Subgroup.mem_top m)
    have e : L ⊔ Subgroup.zpowers s ⊔ ρ.ker = (Subgroup.zpowers s ⊔ ρ.ker) ⊔ L := by
      rw [sup_comm (Subgroup.zpowers s ⊔ ρ.ker) L, ← sup_assoc]
    rwa [e] at h
  have hker : ρ.ker.Normal := MonoidHom.normal_ker ρ
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hm
  obtain ⟨a, ha, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have hk1 : ρ k = 1 := hk
  have hρ : ρ (s ^ n * k * z) = (ρ s) ^ n * ρ z := by
    rw [map_mul, map_mul, hk1, mul_one, map_zpow]
  obtain ⟨q, rfl | rfl⟩ := Int.even_or_odd' n
  · have h2 : (ρ s) ^ (2 * q) = 1 := by
      rw [zpow_mul, zpow_two, hsq, one_zpow]
    rw [hρ, h2, one_mul]
    have hl : ρ z ∈ L.map ρ := ⟨z, hz, rfl⟩
    refine Or.inr ⟨hl, fun h => hs ?_⟩
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hl) h
    rwa [inv_mul_cancel_left] at this
  · have h2 : (ρ s) ^ (2 * q + 1) = ρ s := by
      rw [zpow_add_one, zpow_mul, zpow_two, hsq, one_zpow, one_mul]
    rw [hρ, h2]
    have hl : ρ s * ρ z * ρ s ∈ L.map ρ := hsl z hz
    refine Or.inl ⟨hl, fun h => hs ?_⟩
    have hl' : ρ z ∈ L.map ρ := ⟨z, hz, rfl⟩
    have := Subgroup.mul_mem _ h (Subgroup.inv_mem _ hl')
    rwa [mul_inv_cancel_right] at this

theorem shapeOut_map_of_transvection_rep [Nontrivial W]
    (ρ : M →* LinearMap.GeneralLinearGroup (ZMod 2) W) (L : Subgroup M) [L.Normal] (s : M)
    (hirr : ∀ P : Submodule (ZMod 2) W,
      (∀ m : M, ∀ w ∈ P, (ρ m : W →ₗ[ZMod 2] W) w ∈ P) → P = ⊥ ∨ P = ⊤)
    (htr : IsF2Transvection (ρ s))
    (hgen : ∀ T : Subgroup M, T.Normal → ρ.ker ≤ T → s ∈ T → T = ⊤)
    (hM : ⊤ ≤ L ⊔ Subgroup.zpowers s ⊔ ρ.ker)
    (hperf : L ≤ ⁅L, L⁆ ⊔ ρ.ker) (hL1 : ¬ L ≤ ρ.ker) (hs : ρ s ∉ L.map ρ) :
    ShapeOut ↥(L.map ρ) := by
  refine shapeOut_of_perfect_index_two Module.finrank_pos ρ.range (L.map ρ)
    ⟨_, ?_, range_eq_closure_conj ρ s hgen⟩ ?_ (Subgroup.map_le_range ρ L)
    (relIndex_map_eq_two ρ L s htr hM hs) ?_ ?_
  · rintro _ ⟨g, -, rfl⟩
    exact isF2Transvection_conj htr g
  · intro P hP
    refine hirr P fun m w hw => hP (ρ m) ⟨m, rfl⟩ w hw
  · apply le_antisymm
    · exact Subgroup.commutator_le.mpr fun x hx y hy => by
        have : ⁅x, y⁆ = x * y * x⁻¹ * y⁻¹ := rfl
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
          (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
    · calc L.map ρ ≤ (⁅L, L⁆ ⊔ ρ.ker).map ρ := Subgroup.map_mono hperf
        _ = ⁅L.map ρ, L.map ρ⁆ := by
          rw [Subgroup.map_sup, Subgroup.map_commutator, (Subgroup.map_eq_bot_iff _).mpr le_rfl, sup_bot_eq]
  · intro h
    exact hL1 (Subgroup.map_eq_bot_iff _ |>.mp h)

end Rep

end CFSG.HardMathSupport.Cooperstein.StructureLie
