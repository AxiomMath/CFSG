module

public import CFSG.ClassicalInvolution.Asc77.AscP1SevenDihedral
public import CFSG.ClassicalInvolution.Asc77.AscT7AEnd
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77.Thompson

section YNe

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C21_14_Y_ne_W : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W → u ∈ W →
      alphaOf (Subgroup.closure {u, z}) = ⊥ → dComp Ω K ≠ dstarComp Ω K →
        rLayer Ω u ≤ sigmaGen Ω K ∨ rLayer Ω u ≤ rLayer Ω (t * z)

end YNe

namespace T7N

section Frame

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' J W : Subgroup G} {z u t : G}

omit [Finite G] [IsSimpleGroup G] in
theorem not_rLayer_le_sigmaGen_of (hΩ : HypOmegaMod p f Ω) {K : Subgroup G} (hK : K ∈ Ω) {u' : G}
    {R : Subgroup G} (hR : R ∈ RSet Ω) (hRu : R ≤ Subgroup.centralizer ({u'} : Set G)) {r : G}
    (hrR : r ∈ R) (hr : r ∉ sigmaNorm Ω K) : ¬ rLayer Ω u' ≤ sigmaGen Ω K := by
  intro hle
  have h1 : R ≤ rLayer Ω u' := le_iSup₂_of_le R hR (le_iSup_of_le hRu le_rfl)
  exact hr (T7A.sigmaGen_le_sigmaNorm hΩ.conjInvariant hK (hle (h1 hrR)))

theorem Hyp21.of_involution (h : Hyp21 p f Ω K K' z u J t W) {u' : G} (hu : u' ∈ K ⊔ K')
    (hu2 : u' * u' = 1) (hu1 : u' ≠ 1) (huz : u' ≠ z) (htu : t * u' = u' * t) :
    Hyp21 p f Ω K K' z u' J t W :=
  ⟨h.std, hu, hu2, hu1, huz, h.hJ, h.ht, htu, h.hW, h.hzW, h.htW⟩

theorem Hyp21.alphaOf_zt_eq (h : Hyp21 p f Ω K K' z u J t W) (hC3 : C21_3 p f) :
    alphaOf (Subgroup.closure ({z, t} : Set G)) = alphaOf (Subgroup.closure ({u, z} : Set G)) := by
  have hst := h.std.stand
  have hp : p ≠ 2 := hst.odd
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hfr := h.twinFrameData
  have hzt : z * t = t * z := hfr.comm_zt hp hΩ
  have hz : IsUniqueInvolution K z := h.std.hz
  have htz : t ≠ z := hfr.t_ne_z
  have hA : IsElemAbelian2 (Subgroup.closure ({z, t} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair hz.sq h.ht.sq hz.ne_one h.ht.ne_one htz.symm hzt
  have hle : Subgroup.closure ({z, t} : Set G) ≤ Subgroup.closure ({z, u, t} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  exact (hC3 G Ω K K' z u J t W h).2 _ hle hA

theorem Hyp21.alphaOf_eq_bot_of_frame (h : Hyp21 p f Ω K K' z u J t W) (hC3 : C21_3 p f)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) {u' : G}
    (h' : Hyp21 p f Ω K K' z u' J t W) :
    alphaOf (Subgroup.closure ({u', z} : Set G)) = ⊥ := by
  rw [← Hyp21.alphaOf_zt_eq h' hC3, Hyp21.alphaOf_zt_eq h hC3, hα]

theorem Hyp21.rLayer_le_of_Y_ne (h : Hyp21 p f Ω K K' z u J t W) (hC3 : C21_3 p f)
    (hY : C21_14_Y_ne_W p f) (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥)
    (hne : dComp Ω K ≠ dstarComp Ω K) {u' : G} (h' : Hyp21 p f Ω K K' z u' J t W) (hu'W : u' ∈ W)
    (hY' : ¬ rLayer Ω u' ≤ sigmaGen Ω K) : rLayer Ω u' ≤ rLayer Ω (t * z) := by
  have hα' := Hyp21.alphaOf_eq_bot_of_frame h hC3 hα h'
  exact (hY G Ω K K' z u' J t W h' hu'W hα' hne).resolve_left hY'

end Frame

end T7N

end CFSG.ClassicalInvolution.Asc77
