module

public import CFSG.GH74.GLS.LU.Local.FiveBundles

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU
open scoped MatrixGroups

namespace CFSG.GH74.GLS.LU.Local.Five

@[expose] def Leaf66 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ) (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G) (t u : G),
    FiveCtx G p f z S K₁ K₂ t u → ∃ (H : Subgroup G) (w₁ : G), Five66 z t u K₁ K₂ H w₁

@[expose] def Leaf82 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ) (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G) (t u : G),
    FiveCtx G p f z S K₁ K₂ t u → ∀ (H : Subgroup G) (w₁ : G), Five66 z t u K₁ K₂ H w₁ →
      ∃ X₁ : Subgroup G, Five82 z t u K₁ K₂ H w₁ X₁

@[expose] def Leaf83 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ) (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G) (t u : G),
    FiveCtx G p f z S K₁ K₂ t u → ∀ (H : Subgroup G) (w₁ : G), Five66 z t u K₁ K₂ H w₁ →
      ∀ X₁ : Subgroup G, Five82 z t u K₁ K₂ H w₁ X₁ → ∃ Y : Subgroup G, Five83 z t u H X₁ Y

@[expose] def Leaf84 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ) (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G) (t u : G),
    FiveCtx G p f z S K₁ K₂ t u → ∀ (H : Subgroup G) (w₁ : G), Five66 z t u K₁ K₂ H w₁ →
      ∀ X₁ : Subgroup G, Five82 z t u K₁ K₂ H w₁ X₁ → ∀ Y : Subgroup G, Five83 z t u H X₁ Y →
        ∃ v : G, Five84 z t u H X₁ Y v

@[expose] def Leaf85 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ) (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G) (t u : G),
    FiveCtx G p f z S K₁ K₂ t u → ∀ (H : Subgroup G) (w₁ : G), Five66 z t u K₁ K₂ H w₁ →
      ∀ X₁ : Subgroup G, Five82 z t u K₁ K₂ H w₁ X₁ → ∀ Y : Subgroup G, Five83 z t u H X₁ Y →
        ∀ v : G, Five84 z t u H X₁ Y v → Five85 z t u K₁ K₂ H w₁ X₁ Y v

@[expose] def Leaf86 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ) (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G) (t u : G),
    FiveCtx G p f z S K₁ K₂ t u → ∀ (H : Subgroup G) (w₁ : G), Five66 z t u K₁ K₂ H w₁ →
      ∀ X₁ : Subgroup G, Five82 z t u K₁ K₂ H w₁ X₁ → ∀ Y : Subgroup G, Five83 z t u H X₁ Y →
        ∀ v : G, Five84 z t u H X₁ Y v → Five85 z t u K₁ K₂ H w₁ X₁ Y v → Five86 t w₁ X₁ v

@[expose] def Leaf87 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ) (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G) (t u : G),
    FiveCtx G p f z S K₁ K₂ t u → ∀ (H : Subgroup G) (w₁ : G), Five66 z t u K₁ K₂ H w₁ →
      ∀ X₁ : Subgroup G, Five82 z t u K₁ K₂ H w₁ X₁ → ∀ Y : Subgroup G, Five83 z t u H X₁ Y →
        ∀ v : G, Five84 z t u H X₁ Y v → Five85 z t u K₁ K₂ H w₁ X₁ Y v → Five86 t w₁ X₁ v →
          Five87 t H w₁ X₁ v

@[expose] def Leaf88 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ) (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G) (t u : G),
    FiveCtx G p f z S K₁ K₂ t u → ∀ (H : Subgroup G) (w₁ : G), Five66 z t u K₁ K₂ H w₁ →
      ∀ X₁ : Subgroup G, Five82 z t u K₁ K₂ H w₁ X₁ → ∀ Y : Subgroup G, Five83 z t u H X₁ Y →
        ∀ v : G, Five84 z t u H X₁ Y v → Five85 z t u K₁ K₂ H w₁ X₁ Y v → Five86 t w₁ X₁ v →
          Five87 t H w₁ X₁ v → ∃ L' : Subgroup G, Five88 z t u K₁ K₂ w₁ X₁ v L'

@[expose] def Leaf89 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ) (z : G) (S : Sylow 2 G) (K₁ K₂ : Subgroup G) (t u : G),
    FiveCtx G p f z S K₁ K₂ t u → ∀ (H : Subgroup G) (w₁ : G), Five66 z t u K₁ K₂ H w₁ →
      ∀ X₁ : Subgroup G, Five82 z t u K₁ K₂ H w₁ X₁ → ∀ Y : Subgroup G, Five83 z t u H X₁ Y →
        ∀ v : G, Five84 z t u H X₁ Y v → Five85 z t u K₁ K₂ H w₁ X₁ Y v → Five86 t w₁ X₁ v →
          Five87 t H w₁ X₁ v → ∀ L' : Subgroup G, Five88 z t u K₁ K₂ w₁ X₁ v L' →
            ∃ (h : G) (L : Subgroup G), h⁻¹ * z * h = u ∧ (L = cj K₁ h ∨ L = cj K₂ h) ∧
              L.map (MulAut.conj t).toMonoidHom = L ∧ Nonempty (SL(3, ZMod 5) ≃* ↥(K₁ ⊔ L))

theorem luA3Five'_of_leaves (h66 : Leaf66) (h82 : Leaf82) (h83 : Leaf83) (h84 : Leaf84)
    (h85 : Leaf85) (h86 : Leaf86) (h87 : Leaf87) (h88 : Leaf88) (h89 : Leaf89) : LUA3Five' := by
  intro G _ _ hG p f hp hp2 _ hpf z S K₁ K₂ t u hH he hF
  have ctx : FiveCtx G p f z S K₁ K₂ t u := ⟨hG, hp, hp2, hpf, hH, he, hF⟩
  obtain ⟨H, w₁, b66⟩ := h66 G p f z S K₁ K₂ t u ctx
  obtain ⟨X₁, b82⟩ := h82 G p f z S K₁ K₂ t u ctx H w₁ b66
  obtain ⟨Y, b83⟩ := h83 G p f z S K₁ K₂ t u ctx H w₁ b66 X₁ b82
  obtain ⟨v, b84⟩ := h84 G p f z S K₁ K₂ t u ctx H w₁ b66 X₁ b82 Y b83
  have b85 := h85 G p f z S K₁ K₂ t u ctx H w₁ b66 X₁ b82 Y b83 v b84
  have b86 := h86 G p f z S K₁ K₂ t u ctx H w₁ b66 X₁ b82 Y b83 v b84 b85
  have b87 := h87 G p f z S K₁ K₂ t u ctx H w₁ b66 X₁ b82 Y b83 v b84 b85 b86
  obtain ⟨L', b88⟩ := h88 G p f z S K₁ K₂ t u ctx H w₁ b66 X₁ b82 Y b83 v b84 b85 b86 b87
  obtain ⟨h, L, hh, hL, htL, ⟨e⟩⟩ :=
    h89 G p f z S K₁ K₂ t u ctx H w₁ b66 X₁ b82 Y b83 v b84 b85 b86 b87 L' b88
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcard : Nat.card (ZMod 5) = p ^ f := by rw [hpf, Nat.card_zmod]
  let α₁ : SL(3, ZMod 5) →* G := (K₁ ⊔ L).subtype.comp e.toMonoidHom
  have hα₁inj : Function.Injective α₁ := (K₁ ⊔ L).subtype_injective.comp e.injective
  have hα₁range : α₁.range = K₁ ⊔ L := by
    have h1 : e.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr e.surjective
    rw [MonoidHom.range_comp, h1, Subgroup.map_top, Subgroup.range_subtype]
  let α₂ : SL(3, ZMod 5) →* G := (MulAut.conj t).toMonoidHom.comp α₁
  have hα₂inj : Function.Injective α₂ := (MulAut.conj t).injective.comp hα₁inj
  have hswap : K₁.map (MulAut.conj t).toMonoidHom = K₂ := hH.2.1.t_swap
  have hα₂range : α₂.range = L ⊔ K₂ := by
    rw [MonoidHom.range_comp, hα₁range, Subgroup.map_sup, htL, hswap, sup_comm]
  unfold A3CoreLin
  refine ⟨ZMod 5, inferInstance, inferInstance, u, h, L, hcard, Or.inl rfl, hh, hL,
    ⟨α₁, ?_, hα₁range⟩, ⟨α₂, ?_, hα₂range⟩⟩
  · rw [(MonoidHom.ker_eq_bot_iff _).mpr hα₁inj]; exact bot_le
  · rw [(MonoidHom.ker_eq_bot_iff _).mpr hα₂inj]; exact bot_le

end CFSG.GH74.GLS.LU.Local.Five
