module

public import CFSG.ClassicalGroups.F2Fixed
public import CFSG.ClassicalGroups.Alternating.PointRadical

public section

namespace CFSG.ClassicalGroups.Alternating

open CFSG.ClassicalGroups.F2Fixed CFSG.LocalAnalysis.ComponentInitial
open LinearMap (BilinForm)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {B : BilinForm K V}

abbrev Gsp (B : BilinForm K V) : Type _ := ↥(bilinIsometryGroup B)

@[expose] def Gsp.app (g : Gsp B) (v : V) : V :=
  ((g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) v

theorem Gsp.app_mul (g h : Gsp B) (v : V) : (g * h).app v = g.app (h.app v) := rfl

theorem Gsp.app_one (v : V) : (1 : Gsp B).app v = v := rfl

theorem Gsp.app_inv_app (g : Gsp B) (v : V) : g⁻¹.app (g.app v) = v := by
  show ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)
    (((g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) v) = v
  rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Module.End.one_apply]

theorem Gsp.app_app_inv (g : Gsp B) (v : V) : g.app (g⁻¹.app v) = v := by
  have := Gsp.app_inv_app g⁻¹ v
  rwa [inv_inv] at this

theorem Gsp.map_add (g : Gsp B) (v w : V) : g.app (v + w) = g.app v + g.app w := by
  simp [Gsp.app]

theorem Gsp.map_smul (g : Gsp B) (c : K) (v : V) : g.app (c • v) = c • g.app v := by
  simp [Gsp.app]

theorem Gsp.form_app (g : Gsp B) (v w : V) : B (g.app v) (g.app w) = B v w := g.2 v w

@[expose] def Lsp (B : BilinForm K V) (hB : B.IsAlt) (v : V) : Subgroup (Gsp B) :=
  (pointRadical B hB v).subgroupOf (bilinIsometryGroup B)

theorem mem_Lsp {hB : B.IsAlt} {v : V} {g : Gsp B} :
    g ∈ Lsp B hB v ↔ (g : LinearMap.GeneralLinearGroup K V) ∈ pointRadical B hB v := Iff.rfl

theorem conj_mem_Lsp (hB : B.IsAlt) (g : Gsp B) {v : V} {x : Gsp B} (hx : x ∈ Lsp B hB v) :
    g * x * g⁻¹ ∈ Lsp B hB (g.app v) :=
  conj_mem_pointRadical hB g.2 hx

theorem image_conj_Lsp (hB : B.IsAlt) (g : Gsp B) (v : V) :
    (fun s => g * s * g⁻¹) '' (Lsp B hB v : Set (Gsp B)) = (Lsp B hB (g.app v) : Set (Gsp B)) := by
  ext y
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact conj_mem_Lsp hB g hs
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, by group⟩
    have := conj_mem_Lsp hB g⁻¹ hy
    rwa [Gsp.app_inv_app] at this

theorem card_fixedSub_Lsp (hB : B.IsAlt) {M : Type*} [AddCommGroup M] [DistribMulAction (Gsp B) M]
    (g : Gsp B) (v : V) :
    Nat.card (fixedSub M (Lsp B hB (g.app v) : Set (Gsp B))) =
      Nat.card (fixedSub M (Lsp B hB v : Set (Gsp B))) := by
  rw [← image_conj_Lsp hB g v]
  exact card_fixedSub_conj _ g

theorem Lsp_smul (hB : B.IsAlt) {v : V} {s : K} (hs : s ≠ 0) :
    Lsp B hB (s • v) = Lsp B hB v := by
  ext g
  rw [mem_Lsp, mem_Lsp, pointRadical_smul hB hs]

end CFSG.ClassicalGroups.Alternating
