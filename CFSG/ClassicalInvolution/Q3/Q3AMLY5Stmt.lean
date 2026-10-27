module

public import CFSG.ClassicalInvolution.Q3.Q3AMLYBase
public import CFSG.ClassicalInvolution.Q3.Q3T8B10

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL

section Defs


structure E4SettingY {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G) : Prop where
  bad : BadStd8 Ω K J S R T W z t
  hint : IsIntrinsicU (.sl2 3 1) K z
  noTri : NoTriangleAtEdge Ω K J
  thin : ThinY Ω K z
  mu : MuIsoE4 Ω W

@[expose] def LayerE4 {G : Type} [Group G] (Ω : Set (Subgroup G)) (K : Subgroup G) (z : G) :
    Prop :=
  LayerL3 Ω K z ∨ LayerM11 Ω K z

@[expose] def E4AxisLeafY : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), E4SettingY Ω K J S R T W z t →
      ∃ s : G, E4Axis Ω K J R z t s

@[expose] def SectionLeafY : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), E4SettingY Ω K J S R T W z t →
      LayerE4 Ω K z

@[expose] def VertexZLeafY : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), E4SettingY Ω K J S R T W z t →
      ∀ s : G, E4Axis Ω K J R z t s → Hyp51At (Subgroup.closure ({z, t, s} : Set G)) z

@[expose] def VertexTLeafY : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), E4SettingY Ω K J S R T W z t →
      LayerE4 Ω K z → ∀ s : G, E4Axis Ω K J R z t s →
        Hyp51At (Subgroup.closure ({z, t, s} : Set G)) t ∧
          Hyp51At (Subgroup.closure ({z, t, s} : Set G)) s ∧
            Hyp51At (Subgroup.closure ({z, t, s} : Set G)) (t * s)

@[expose] def VertexALeafY : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), E4SettingY Ω K J S R T W z t →
      LayerE4 Ω K z → ∀ s : G, E4Axis Ω K J R z t s →
        Hyp51At (Subgroup.closure ({z, t, s} : Set G)) (z * t) ∧
          Hyp51At (Subgroup.closure ({z, t, s} : Set G)) (z * s) ∧
            Hyp51At (Subgroup.closure ({z, t, s} : Set G)) (z * t * s)

@[expose] def LinkLeafY : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), E4SettingY Ω K J S R T W z t →
      LayerE4 Ω K z → ∀ s : G, E4Axis Ω K J R z t s →
        ∀ J' ∈ omegaNbr Ω K, ∀ t' : G, IsUniqueInvolution J' t' →
          ∃ y ∈ rankTwoSpan (Subgroup.closure ({z, t, s} : Set G)),
            y * z * y⁻¹ = z ∧ y * t * y⁻¹ = t'

structure CFBYLeaves : Prop where
  axis : E4AxisLeafY
  sect : SectionLeafY
  vertexZ : VertexZLeafY
  vertexT : VertexTLeafY
  vertexA : VertexALeafY
  link : LinkLeafY

end Defs

section Axis

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J R : Subgroup G} {z t s : G}

theorem E4Axis.ofNbr (hsq : s * s = 1) (hne : s ≠ 1) (hcz : z * s = s * z) (hct : t * s = s * t)
    (hind : s ∉ Subgroup.closure ({z, t} : Set G)) (hcR : ∀ r ∈ R, r * s = s * r)
    (hnJ : conjSub s J = J) (h₁ : ∃ J₁ ∈ omegaNbr Ω K, IsUniqueInvolution J₁ s)
    (h₂ : ∃ J₂ ∈ omegaNbr Ω K, IsUniqueInvolution J₂ (t * s)) : E4Axis Ω K J R z t s where
  sq := hsq
  ne_one := hne
  comm_z := hcz
  comm_t := hct
  indep := hind
  mem_X := by
    obtain ⟨J₁, hJ₁, hu⟩ := h₁
    exact le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) J₁ hJ₁ hu.mem
  cent_R := hcR
  norm_J := hnJ
  nbr₁ := h₁
  nbr₂ := h₂

end Axis

end CFSG.ClassicalInvolution.Q3.Q3AM
