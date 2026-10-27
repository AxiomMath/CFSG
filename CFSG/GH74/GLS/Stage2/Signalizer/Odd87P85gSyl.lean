module

public import CFSG.GH74.GLS.IVK.Defs
public import CFSG.Adapters.LinearSmallCatalog

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85

open Subgroup
open scoped commutatorElement

structure SylCfg {Y : Type} [Group Y] (α : Y → Y) (P E F : Subgroup Y) : Prop where
  card_P : Nat.card P = 64
  exp_P : ∀ x ∈ P, x ^ 4 = 1
  alpha_P : ∀ x ∈ P, α x ∈ P
  E_le : E ≤ P
  F_le : F ≤ P
  E_le_F : E ≤ F
  card_E : Nat.card E = 4
  card_F : Nat.card F = 16
  E_sq : ∀ e ∈ E, e * e = 1
  E_cen : ∀ e ∈ E, ∀ x ∈ P, e * x = x * e
  E_center : ∀ x ∈ P, (∀ y ∈ P, x * y = y * x) → x ∈ E
  E_alpha : ∀ e ∈ E, α e = e
  E_comm : ∀ e ∈ E, ∃ a ∈ P, ∃ b ∈ P, a * b * a⁻¹ * b⁻¹ = e
  F_comm : ∀ f ∈ F, ∀ g ∈ F, f * g = g * f
  F_sq : ∀ f ∈ F, f * f = 1
  fusion : ∀ e ∈ E, e ≠ 1 → ∀ e' ∈ E, e' ≠ 1 →
    ∃ n ∈ normalizer (P : Set Y), n * e * n⁻¹ = e'

theorem SylCfg.map {Y Y' : Type} [Group Y] [Group Y'] (f : Y →* Y') (hf : Function.Injective f)
    {α : Y → Y} {α' : Y' → Y'} (hα : ∀ y, α' (f y) = f (α y)) {P E F : Subgroup Y}
    (h : SylCfg α P E F) : SylCfg α' (P.map f) (E.map f) (F.map f) where
  card_P := by rw [Subgroup.card_map_of_injective hf]; exact h.card_P
  exp_P := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, h.exp_P x hx, map_one]
  alpha_P := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨α x, h.alpha_P x hx, (hα x).symm⟩
  E_le := Subgroup.map_mono h.E_le
  F_le := Subgroup.map_mono h.F_le
  E_le_F := Subgroup.map_mono h.E_le_F
  card_E := by rw [Subgroup.card_map_of_injective hf]; exact h.card_E
  card_F := by rw [Subgroup.card_map_of_injective hf]; exact h.card_F
  E_sq := by
    rintro _ ⟨e, he, rfl⟩
    rw [← map_mul, h.E_sq e he, map_one]
  E_cen := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, h.E_cen e he x hx]
  E_center := by
    rintro _ ⟨x, hx, rfl⟩ hc
    refine ⟨x, h.E_center x hx (fun y hy => hf ?_), rfl⟩
    rw [map_mul, map_mul]
    exact hc (f y) ⟨y, hy, rfl⟩
  E_alpha := by
    rintro _ ⟨e, he, rfl⟩
    rw [hα, h.E_alpha e he]
  E_comm := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨a, ha, b, hb, hab⟩ := h.E_comm e he
    exact ⟨f a, ⟨a, ha, rfl⟩, f b, ⟨b, hb, rfl⟩, by rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hab]⟩
  F_comm := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, h.F_comm x hx y hy]
  F_sq := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, h.F_sq x hx, map_one]
  fusion := by
    rintro _ ⟨e, he, rfl⟩ hne _ ⟨e', he', rfl⟩ hne'
    have hne₀ : e ≠ 1 := fun h1 => hne (by rw [h1, map_one])
    have hne₀' : e' ≠ 1 := fun h1 => hne' (by rw [h1, map_one])
    obtain ⟨n, hn, hne'e⟩ := h.fusion e he hne₀ e' he' hne₀'
    refine ⟨f n, ?_, by rw [← map_inv, ← map_mul, ← map_mul, hne'e]⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hn1 := Subgroup.mem_normalizer_iff.mp hn
    have hn2 := Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn)
    constructor
    · rintro ⟨y₀, hy₀, rfl⟩
      exact ⟨n * y₀ * n⁻¹, (hn1 y₀).mp hy₀, by rw [map_mul, map_mul, map_inv]⟩
    · rintro ⟨w, hw, hwy⟩
      refine ⟨n⁻¹ * w * n, ?_, ?_⟩
      · have := (hn2 w).mp hw
        simpa using this
      · rw [map_mul, map_mul, map_inv, hwy]
        group

section Fix

variable {Y Y' : Type} [Group Y] [Group Y']

@[expose] def fixSub (α : MulAut Y) : Subgroup Y := MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id Y)

theorem mem_fixSub {α : MulAut Y} {y : Y} : y ∈ fixSub α ↔ α y = y := Iff.rfl

theorem card_fixSub_congr (ψ : Y ≃* Y') (α : MulAut Y) :
    Nat.card (fixSub (MulAut.congr ψ α)) = Nat.card (fixSub α) := by
  have h : (fixSub α).map ψ.toMonoidHom = fixSub (MulAut.congr ψ α) := by
    ext y
    rw [Subgroup.mem_map_equiv, mem_fixSub, mem_fixSub]
    constructor
    · intro h
      have : MulAut.congr ψ α y = ψ (α (ψ.symm y)) := rfl
      rw [this, h, MulEquiv.apply_symm_apply]
    · intro h
      have h1 : ψ (α (ψ.symm y)) = y := h
      have h2 := congrArg ψ.symm h1
      rwa [MulEquiv.symm_apply_apply] at h2
  rw [← h]
  exact Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective

theorem fixSub_one : fixSub (1 : MulAut Y) = ⊤ := by
  ext y
  simp [mem_fixSub]

end Fix

theorem card_isL2_four {X : Type} [Group X] (h : IVK.IsL2 X (fun q => q = 4)) : Nat.card X = 60 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_congr (IVK.L2.equivPSL F).toEquiv]
  exact CFSG.ClassicalModels.projectiveSpecialLinear_two_card_of_card_four F hF

theorem center_eq_bot_of_isL2_four {X : Type} [Group X] (h : IVK.IsL2 X (fun q => q = 4)) :
    Subgroup.center X = ⊥ := by
  have hc := card_isL2_four h
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  have hs : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hF])
  have hs' : IsSimpleGroup X := MulEquiv.isSimpleGroup (e.trans (IVK.L2.equivPSL F))
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h1 | h1
  · exact h1
  · exfalso
    let : CommGroup X := Group.commGroupOfCenterEqTop h1
    have hp := IsSimpleGroup.prime_card (α := X)
    rw [hc] at hp
    exact absurd hp (by norm_num)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85
