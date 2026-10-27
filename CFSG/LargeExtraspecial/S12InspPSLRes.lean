module

public import CFSG.LargeExtraspecial.S12InspPSLLin
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLCaseA

public section

namespace CFSG.LargeExtraspecial.S12InspPSL

open Module Submodule CFSG.ComponentClassification.OutcomeLocal

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {Γ : Type*} [Group Γ] (ρ : Γ →* (V ≃ₗ[ZMod 2] V)) (W : Submodule (ZMod 2) V)

@[expose] def IsInv : Prop := ∀ γ : Γ, ∀ w ∈ W, ρ γ w ∈ W

variable {ρ W}

theorem map_eq_of_isInv (hW : IsInv ρ W) (γ : Γ) :
    W.map ((ρ γ : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) = W := by
  refine le_antisymm (Submodule.map_le_iff_le_comap.mpr fun w hw => hW γ w hw) fun w hw => ?_
  refine ⟨ρ γ⁻¹ w, hW γ⁻¹ w hw, ?_⟩
  change ρ γ (ρ γ⁻¹ w) = w
  rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

variable (ρ W) in
@[expose] noncomputable def resGL (hW : IsInv ρ W) :
    Γ →* LinearMap.GeneralLinearGroup (ZMod 2) W where
  toFun γ := LinearMap.GeneralLinearGroup.ofLinearEquiv
    ((ρ γ).ofSubmodules W W (map_eq_of_isInv hW γ))
  map_one' := by
    ext w
    simp
  map_mul' γ δ := by
    ext w
    simp [LinearEquiv.mul_apply]

theorem resGL_apply (hW : IsInv ρ W) (γ : Γ) (w : W) :
    (((resGL ρ W hW γ : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) w : V) =
      ρ γ w :=
  rfl

theorem resGL_eq_one_iff (hW : IsInv ρ W) (γ : Γ) :
    resGL ρ W hW γ = 1 ↔ ∀ w ∈ W, ρ γ w = w := by
  constructor
  · intro h w hw
    have := resGL_apply hW γ ⟨w, hw⟩
    rw [h] at this
    exact this.symm
  · intro h
    refine tv_ext fun w => Subtype.ext ?_
    rw [resGL_apply]
    exact h w w.2

theorem isF2Transvection_resGL (hW : IsInv ρ W) {γ : Γ} {c : V} (hc : c ∈ W)
    (hcomm : ∀ w ∈ W, ρ γ w - w ∈ span (ZMod 2) {c}) (hne : ∃ w ∈ W, ρ γ w ≠ w) :
    IsF2Transvection (resGL ρ W hW γ) := by
  obtain ⟨w₀, hw₀, hne₀⟩ := hne
  have hc0 : c ≠ 0 := by
    intro h0
    have := hcomm w₀ hw₀
    rw [h0, span_singleton_eq_bot.mpr rfl, mem_bot, sub_eq_zero] at this
    exact hne₀ this
  refine ⟨fun h1 => hne₀ ((resGL_eq_one_iff hW γ).mp h1 w₀ hw₀), ?_⟩
  have hspan : commutatorSpace (resGL ρ W hW γ) = span (ZMod 2) {(⟨c, hc⟩ : W)} := by
    apply le_antisymm
    · rintro _ ⟨w, rfl⟩
      have h := hcomm w w.2
      rw [mem_span_singleton_iff] at h ⊢
      rcases h with h | h
      · left
        apply Subtype.ext
        change (w : V) + ρ γ w = 0
        rw [sub_eq_zero.mp h, zmod2_add_self]
      · right
        apply Subtype.ext
        change (w : V) + ρ γ w = c
        rw [← h, sub_eq_add_neg, zmod2_neg, add_comm]
    · rw [span_le, Set.singleton_subset_iff]
      have h := hcomm w₀ hw₀
      rw [mem_span_singleton_iff] at h
      rcases h with h | h
      · exact absurd (sub_eq_zero.mp h) hne₀
      · refine ⟨⟨w₀, hw₀⟩, Subtype.ext ?_⟩
        change w₀ + ρ γ w₀ = c
        rw [← h, sub_eq_add_neg, zmod2_neg, add_comm]
  rw [hspan, finrank_span_singleton]
  intro h
  exact hc0 (congrArg Subtype.val h)

theorem genByTransvections_range (hW : IsInv ρ W) {E : Set Γ} (hE : Subgroup.closure E = ⊤)
    (htv : ∀ e ∈ E, IsF2Transvection (resGL ρ W hW e)) :
    GenByTransvections (resGL ρ W hW).range := by
  refine ⟨resGL ρ W hW '' E, ?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    exact htv e he
  · rw [← MonoidHom.map_closure, hE, ← MonoidHom.range_eq_map]

theorem isIrreducibleOn_range (hW : IsInv ρ W)
    (hirr : ∀ U : Submodule (ZMod 2) V, U ≤ W → IsInv ρ U → U = ⊥ ∨ U = W) :
    IsIrreducibleOn (resGL ρ W hW).range := by
  intro U hU
  have hle : U.map W.subtype ≤ W := by
    rintro _ ⟨u, -, rfl⟩
    exact u.2
  have hinv : IsInv ρ (U.map W.subtype) := by
    rintro γ _ ⟨u, hu, rfl⟩
    refine ⟨(resGL ρ W hW γ : W →ₗ[ZMod 2] W) u, hU _ ⟨γ, rfl⟩ u hu, ?_⟩
    rfl
  rcases hirr _ hle hinv with h | h
  · left
    rw [eq_bot_iff]
    intro u hu
    have : (u : V) ∈ U.map W.subtype := ⟨u, hu, rfl⟩
    rw [h, mem_bot] at this
    rw [mem_bot]
    exact Subtype.ext this
  · right
    rw [eq_top_iff]
    intro u _
    have : (u : V) ∈ U.map W.subtype := by rw [h]; exact u.2
    obtain ⟨u', hu', hu'u⟩ := this
    rwa [← Subtype.ext hu'u]

theorem exists_tv_of_isF2Transvection (hW : IsInv ρ W) {γ : Γ}
    (h : IsF2Transvection (resGL ρ W hW γ)) :
    ∃ (φ : Dual (ZMod 2) W) (a : W) (ha : φ a = 0), φ ≠ 0 ∧ a ≠ 0 ∧
      resGL ρ W hW γ = tv φ a ha ∧ ∀ w (hw : w ∈ W), ρ γ w = w + φ ⟨w, hw⟩ • (a : V) := by
  obtain ⟨φ, a, ha, hφ, ha0, he⟩ := (isF2Transvection_iff _).mp h
  refine ⟨φ, a, ha, hφ, ha0, he, fun w hw => ?_⟩
  have h1 := resGL_apply hW γ ⟨w, hw⟩
  rw [he, tv_apply] at h1
  rw [← h1]
  rfl

theorem exists_lift_tv (hW : IsInv ρ W) (htop : (resGL ρ W hW).range = ⊤)
    (ψ : V →ₗ[ZMod 2] ZMod 2) {u : V} (hu : u ∈ W) (hψu : ψ u = 0) :
    ∃ γ : Γ, ∀ w ∈ W, ρ γ w = w + ψ w • u := by
  have hψu' : (ψ ∘ₗ W.subtype) ⟨u, hu⟩ = 0 := hψu
  have hmem : tv (ψ ∘ₗ W.subtype) ⟨u, hu⟩ hψu' ∈ (resGL ρ W hW).range := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨γ, hγ⟩ := hmem
  refine ⟨γ, fun w hw => ?_⟩
  have h1 := resGL_apply hW γ ⟨w, hw⟩
  rw [hγ, tv_apply] at h1
  exact h1.symm

theorem range_eq_top_of_dihedral [FiniteDimensional (ZMod 2) V] (hW : IsInv ρ W) {E : Set Γ}
    (hE : Subgroup.closure E = ⊤)
    (htv : ∀ e ∈ E, IsF2Transvection (resGL ρ W hW e))
    (hirr : ∀ U : Submodule (ZMod 2) V, U ≤ W → IsInv ρ U → U = ⊥ ∨ U = W)
    {γ δ : Γ} {φ ψ : Dual (ZMod 2) W} {a b : W} (ha : φ a = 0) (hb : ψ b = 0)
    (hφ : φ ≠ 0) (hψ : ψ ≠ 0) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hγ : resGL ρ W hW γ = tv φ a ha) (hδ : resGL ρ W hW δ = tv ψ b hb) (hd : φ b ≠ ψ a) :
    (resGL ρ W hW).range = ⊤ := by
  have hgen := genByTransvections_range hW hE htv
  have hirr' := isIrreducibleOn_range hW hirr
  have hφa : InG (resGL ρ W hW).range φ a := ⟨ha, hγ ▸ ⟨γ, rfl⟩⟩
  have hψb : InG (resGL ρ W hW).range ψ b := ⟨hb, hδ ▸ ⟨δ, rfl⟩⟩
  rcases zmod2_eq_zero_or_one (φ b) with h0 | h1
  · have h1 : ψ a = 1 := zmod2_eq_one_of_ne_zero (fun h => hd (h0.trans h.symm))
    exact eq_top_of_dihedral hgen hirr' hb0 hφ hψb hφa h1 h0
  · have h0 : ψ a = 0 := (zmod2_eq_zero_or_one _).resolve_right (fun h => hd (h1.trans h.symm))
    exact eq_top_of_dihedral hgen hirr' ha0 hψ hφa hψb h1 h0

end CFSG.LargeExtraspecial.S12InspPSL
