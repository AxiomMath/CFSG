module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8TableU43A
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13Syl
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8TableGlue

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup
open scoped Pointwise

theorem map_ne_one_of_injective {X Y : Type*} [Group X] [Group Y] {f : X →* Y}
    (hf : Function.Injective f) {a : X} (ha : a ≠ 1) : f a ≠ 1 :=
  fun h => ha (hf (h.trans (map_one f).symm))

theorem map_ne_of_injective {X Y : Type*} [Group X] [Group Y] {f : X →* Y}
    (hf : Function.Injective f) {a b : X} (hab : a ≠ b) : f a ≠ f b :=
  fun h => hab (hf h)

theorem exists_conj_of_table
    {X : Type} [Group X] [Finite X]
    (e : X ≃* ↥(U43Ext : Subgroup (Equiv.Perm (Fin 820))))
    {ζ α t g₁ g₂ h₁ h₂ : X} (hT : OuterTable ζ α t g₁ g₂ h₁ h₂) :
    ∃ k : X, k * ζ * k⁻¹ = α := by
  classical
  have hT' := hT
  obtain ⟨hζζ, -, -, hα1, ht1, hαt, -, hζα, hζt, hh1, hh2, hA, -, -, -, -, -, -, -, -, -⟩ := hT'
  have hT2 : IsPGroup 2 (closure ({ζ, α, t, g₁, g₂, h₁, h₂} : Set X)) :=
    isPGroup_closure_seven hζζ hA hζα hζt hh1 hh2
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hT2
  let Hs : Subgroup ↥(U43Ext : Subgroup (Equiv.Perm (Fin 820))) :=
    (TS8J.Jsub : Subgroup (Equiv.Perm (Fin 820))).subgroupOf U43Ext
  let Hx : Subgroup X := Hs.comap e.toMonoidHom
  have hHs : Nat.card Hs = 256 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe TS8J.Jsub_le).toEquiv).trans TS8J.card_Jsub
  have hmapHx : Hx.map e.toMonoidHom = Hs := by
    show (Hs.comap e.toMonoidHom).map e.toMonoidHom = Hs
    rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top.2 e.surjective, top_inf_eq]
  have hHx : Nat.card Hx = 256 := by
    rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hmapHx, hHs]
  have hXcard : Nat.card X = 6531840 := by
    rw [Nat.card_congr e.toEquiv, card_U43Ext]
  have hHxP : IsPGroup 2 Hx := IsPGroup.of_card (n := 8) (by rw [hHx]; norm_num)
  have hHxmax : ∀ R : Subgroup X, IsPGroup 2 R → R ≤ ⊤ → Hx ≤ R → R ≤ Hx :=
    fun R hR _ hle => max_of_card hXcard hHx hR hle
  have hQmax : ∀ R : Subgroup X, IsPGroup 2 R → R ≤ ⊤ → (Q : Subgroup X) ≤ R →
      R ≤ (Q : Subgroup X) :=
    fun R hR _ hle => (Q.is_maximal' hR hle).le
  obtain ⟨g, -, hg⟩ := sylow_conj le_top le_top hHxP Q.isPGroup' hHxmax hQmax
  have hφ : Function.Injective (MulAut.conj g⁻¹).toMonoidHom := (MulAut.conj g⁻¹).injective
  have hTc : OuterTable (g⁻¹ * ζ * g) (g⁻¹ * α * g) (g⁻¹ * t * g) (g⁻¹ * g₁ * g)
      (g⁻¹ * g₂ * g) (g⁻¹ * h₁ * g) (g⁻¹ * h₂ * g) := by
    have := outerTable_map (MulAut.conj g⁻¹).toMonoidHom hT
      (map_ne_one_of_injective hφ hα1) (map_ne_one_of_injective hφ ht1)
      (map_ne_of_injective hφ hαt)
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using this
  have hα1c : g⁻¹ * α * g ≠ 1 := by
    have := map_ne_one_of_injective hφ hα1
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using this
  have ht1c : g⁻¹ * t * g ≠ 1 := by
    have := map_ne_one_of_injective hφ ht1
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using this
  have hαtc : g⁻¹ * α * g ≠ g⁻¹ * t * g := by
    have := map_ne_of_injective hφ hαt
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using this
  have hmem : ∀ x ∈ ({ζ, α, t, g₁, g₂, h₁, h₂} : Set X), g⁻¹ * x * g ∈ Hx :=
    fun x hx => (hg x).1 (hQ (subset_closure hx))
  let ψ : X →* Equiv.Perm (Fin 820) :=
    (U43Ext : Subgroup (Equiv.Perm (Fin 820))).subtype.comp e.toMonoidHom
  have hψ : Function.Injective ψ := by
    intro a b h
    apply e.injective
    apply Subtype.ext
    exact h
  have hψapp : ∀ x : X, ψ x = ((e x : ↥U43Ext) : Equiv.Perm (Fin 820)) := fun x => rfl
  have hTψ := outerTable_map ψ hTc (map_ne_one_of_injective hψ hα1c)
    (map_ne_one_of_injective hψ ht1c) (map_ne_of_injective hψ hαtc)
  have key : ∀ x ∈ ({ζ, α, t, g₁, g₂, h₁, h₂} : Set X), ψ (g⁻¹ * x * g) ∈ TS8J.Jsub :=
    fun x hx => by
      have h1 : e (g⁻¹ * x * g) ∈ Hs := hmem x hx
      exact (Subgroup.mem_subgroupOf).1 h1
  obtain ⟨k, hkU, hk⟩ := TS8J.table_conj (key ζ (by simp)) (key α (by simp)) (key t (by simp))
    (key g₁ (by simp)) (key g₂ (by simp)) (key h₁ (by simp)) (key h₂ (by simp)) hTψ
  have hψW : ∃ W : X, ψ W = k := ⟨e.symm ⟨k, hkU⟩, by rw [hψapp, MulEquiv.apply_symm_apply]⟩
  obtain ⟨W, hWk⟩ := hψW
  obtain ⟨w, hw⟩ : ∃ w : X, w * (g⁻¹ * ζ * g) * w⁻¹ = g⁻¹ * α * g := by
    refine ⟨W, hψ ?_⟩
    rw [map_mul ψ (W * (g⁻¹ * ζ * g)) W⁻¹, map_mul ψ W (g⁻¹ * ζ * g), map_inv ψ W, hWk]
    exact hk
  refine ⟨g * w * g⁻¹, ?_⟩
  calc g * w * g⁻¹ * ζ * (g * w * g⁻¹)⁻¹ = g * (w * (g⁻¹ * ζ * g) * w⁻¹) * g⁻¹ := by group
    _ = g * (g⁻¹ * α * g) * g⁻¹ := by rw [hw]
    _ = α := by group

theorem outerTableU43 :
    OuterTableU43 := by
  unfold OuterTableU43
  intro X _ _ he ζ α t g₁ g₂ h₁ h₂ hT
  obtain ⟨e⟩ := he
  exact exists_conj_of_table e hT

end CFSG.EvenSporadicStandard.Fin76b
