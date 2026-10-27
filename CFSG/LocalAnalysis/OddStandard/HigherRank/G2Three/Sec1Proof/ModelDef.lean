module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.Codes
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Frame
public import CFSG.RankThree.PartTwo.Census.Carrier.G2ThreeData

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof

open CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.RankThree.PartTwo.Census.Carrier.G2Three
open Subgroup

@[expose] def gx0W : Wm := wdiag (dec14 x0c) (dec14 x1c)

@[expose] def gx1W : Wm := wdiag (dec14 x1c) (dec14 x0c)

@[expose] def gy0W : Wm := wdiag (dec14 y0c) (dec14 y1c)

@[expose] def gy1W : Wm := wdiag (dec14 y1c) (dec14 y0c)

@[expose] def gsW : Wm := wanti 1 1

structure G23Base (G : Type) [Group G] [Finite G] where
  L : Subgroup G
  normal : L.Normal
  card_L : Nat.card L = 4245696
  card_G : Nat.card G = 8491392
  invol_conj : ∀ u ∈ invols L, ∀ v ∈ invols L, ∃ l ∈ L, v = l * u * l⁻¹
  card_cent : ∀ u ∈ invols L, Nat.card (centEl L u) = 576
  cent_outer : ∀ τ : G, τ ∉ L → τ * τ = 1 →
    Nonempty (↥(centEl L τ) ≃*
      MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3)))

structure G23Model (G : Type) [Group G] [Finite G] extends G23Base G where
  ρ : G →* Wm
  inj : Function.Injective ρ
  gX0 : G
  gX1 : G
  gY0 : G
  gY1 : G
  gS : G
  gX0_mem : gX0 ∈ L
  gX1_mem : gX1 ∈ L
  gY0_mem : gY0 ∈ L
  gY1_mem : gY1 ∈ L
  gS_not_mem : gS ∉ L
  gS_sq : gS * gS = 1
  ρ_gX0 : ρ gX0 = gx0W
  ρ_gX1 : ρ gX1 = gx1W
  ρ_gY0 : ρ gY0 = gy0W
  ρ_gY1 : ρ gY1 = gy1W
  ρ_gS : ρ gS = gsW

variable {G : Type} [Group G] [Finite G]

@[expose] def mn0 (m : G23Model G) : G := m.gX0 * m.gY0 ^ 2 * m.gX0

@[expose] def mn1 (m : G23Model G) : G := m.gX1 * m.gY1 ^ 2 * m.gX1

@[expose] def frameOf (m : G23Model G) : Frame G :=
  ⟨⟨mn0 m * m.gX1 * (mn0 m)⁻¹, mn0 m * mn1 m * (mn0 m)⁻¹, mn1 m * m.gX0 * (mn1 m)⁻¹,
    mn1 m * mn0 m * (mn1 m)⁻¹, mn1 m ^ 2⟩, m.gS⟩

theorem conj_inv_conj (g x : G) : (MulAut.conj g⁻¹) (g * x * g⁻¹) = x := by
  rw [MulAut.conj_apply]
  group

@[expose] def twist (g : G) (m : G23Model G) : G23Model G where
  toG23Base := m.toG23Base
  ρ := m.ρ.comp (MulAut.conj g⁻¹).toMonoidHom
  inj := m.inj.comp (MulAut.conj g⁻¹).injective
  gX0 := g * m.gX0 * g⁻¹
  gX1 := g * m.gX1 * g⁻¹
  gY0 := g * m.gY0 * g⁻¹
  gY1 := g * m.gY1 * g⁻¹
  gS := g * m.gS * g⁻¹
  gX0_mem := m.normal.conj_mem _ m.gX0_mem g
  gX1_mem := m.normal.conj_mem _ m.gX1_mem g
  gY0_mem := m.normal.conj_mem _ m.gY0_mem g
  gY1_mem := m.normal.conj_mem _ m.gY1_mem g
  gS_not_mem := fun h => m.gS_not_mem (by
    have h1 := m.normal.conj_mem _ h g⁻¹
    rwa [show g⁻¹ * (g * m.gS * g⁻¹) * g⁻¹⁻¹ = m.gS by group] at h1)
  gS_sq := by
    calc g * m.gS * g⁻¹ * (g * m.gS * g⁻¹) = g * (m.gS * m.gS) * g⁻¹ := by group
      _ = 1 := by rw [m.gS_sq]; group
  ρ_gX0 := by
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, conj_inv_conj]
    exact m.ρ_gX0
  ρ_gX1 := by
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, conj_inv_conj]
    exact m.ρ_gX1
  ρ_gY0 := by
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, conj_inv_conj]
    exact m.ρ_gY0
  ρ_gY1 := by
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, conj_inv_conj]
    exact m.ρ_gY1
  ρ_gS := by
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, conj_inv_conj]
    exact m.ρ_gS

@[expose] def frameMap {G' : Type} [Group G'] (φ : G →* G') (fr : Frame G) : Frame G' :=
  ⟨⟨φ fr.u₁, φ fr.b₁, φ fr.u₂, φ fr.b₂, φ fr.h₀⟩, φ fr.σ⟩

theorem conj_sq (g y : G) : (g * y * g⁻¹) ^ 2 = g * y ^ 2 * g⁻¹ := by
  rw [sq, sq]
  group

theorem mn0_twist (g : G) (m : G23Model G) : mn0 (twist g m) = g * mn0 m * g⁻¹ := by
  simp only [mn0, twist]
  rw [conj_sq]
  group

theorem mn1_twist (g : G) (m : G23Model G) : mn1 (twist g m) = g * mn1 m * g⁻¹ := by
  simp only [mn1, twist]
  rw [conj_sq]
  group

theorem frameOf_twist (g : G) (m : G23Model G) :
    frameOf (twist g m) = frameMap (MulAut.conj g).toMonoidHom (frameOf m) := by
  simp only [frameOf, frameMap]
  rw [mn0_twist, mn1_twist]
  simp only [twist, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Frame.mk.injEq,
    SFrame.mk.injEq]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · group
  · group
  · group
  · group
  · rw [conj_sq]
  · trivial

theorem frameMap_Sσ {G' : Type} [Group G'] (φ : G →* G') (fr : Frame G) :
    (frameMap φ fr).Sσ = fr.Sσ.map φ := by
  have h1 : (frameMap φ fr).a₁ = φ fr.a₁ := by
    simp [frameMap, SFrame.a₁, map_mul, map_pow, map_inv]
  have h2 : (frameMap φ fr).a₂ = φ fr.a₂ := by
    simp [frameMap, SFrame.a₂, map_mul, map_pow, map_inv]
  unfold Frame.Sσ
  rw [MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton, h1, h2]
  rfl

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof
