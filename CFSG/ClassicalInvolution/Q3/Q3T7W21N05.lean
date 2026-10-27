module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q22Sect
public import CFSG.ClassicalInvolution.Q3.Q3T7W21A01

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson


@[expose] def C21_14_Y_ne_W : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Q3T8.Asc77.Hyp21 Ω K K' z u J t W →
      u ∈ W → alphaOf (Subgroup.closure {u, z}) = ⊥ → dComp Ω K ≠ dstarComp Ω K →
        ExactLayer.exactLayer Ω u ≤ sigmaGen Ω K ∨
          ExactLayer.exactLayer Ω u ≤ Subgroup.centralizer ({t * z} : Set G)

namespace T7N

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem not_exactLayer_le_sigmaGen_of (hΩ : Q3T7M.HM Ω) {K : Subgroup G} (hK : K ∈ Ω)
    {u' : G} (hu'2 : u' * u' = 1) {R : Subgroup G} (hR : R ∈ RSet Ω)
    (hRu : R ≤ Subgroup.centralizer ({u'} : Set G)) {r : G} (hrR : r ∈ R)
    (hr : r ∉ sigmaNorm Ω K) : ¬ ExactLayer.exactLayer Ω u' ≤ sigmaGen Ω K := by
  intro hle
  have hcA : IsPGroup 2 (Subgroup.zpowers u') := ExactLayer.isPGroup_zpowers_of_sq_eq_one hu'2
  obtain ⟨K₁, hK₁, hRK₁⟩ := exists_isSylow2In_of_mem_RSet hR
  have hK₁t : K₁ ∈ ExactLayer.tqMembers Ω u' :=
    (ExactLayer.mem_tqMembers_iff_exists_sylow hΩ hcA).mpr ⟨hK₁, R, hRK₁, hRu⟩
  have h1 : R ≤ ExactLayer.exactLayer Ω u' := by
    refine le_trans ?_ (ExactLayer.exactCore_le_exactLayer hK₁t)
    rw [ExactLayer.exactCore_def]
    exact le_inf hRK₁.1 hRu
  exact hr (T7A.sigmaGen_le_sigmaNorm hΩ.conjInvariant hK (hle (h1 hrR)))

variable [IsSimpleGroup G] {K K' J W : Subgroup G} {z u t : G}

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp21.of_involution
    (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W) {u' : G} (hu : u' ∈ K ⊔ K') (hu2 : u' * u' = 1)
    (hu1 : u' ≠ 1) (huz : u' ≠ z) (htu : t * u' = u' * t) :
    Q3T8.Asc77.Hyp21 Ω K K' z u' J t W :=
  ⟨h.std, hu, hu2, hu1, huz, h.hJ, h.ht, htu, h.hW, h.hzW, h.htW⟩

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp21.alphaOf_zt_eq
    (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W) (hC3 : Q3T8.Asc77.C21_3) :
    alphaOf (Subgroup.closure ({z, t} : Set G)) =
      alphaOf (Subgroup.closure ({u, z} : Set G)) := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hfr := h.twinFrameData
  have hzt : z * t = t * z := hfr.comm_zt hΩ
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

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp21.alphaOf_eq_bot_of_frame
    (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W) (hC3 : Q3T8.Asc77.C21_3)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) {u' : G}
    (h' : Q3T8.Asc77.Hyp21 Ω K K' z u' J t W) :
    alphaOf (Subgroup.closure ({u', z} : Set G)) = ⊥ := by
  rw [← Hyp21.alphaOf_zt_eq h' hC3, Hyp21.alphaOf_zt_eq h hC3, hα]

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp21.exactLayer_le_of_Y_ne
    (h : Q3T8.Asc77.Hyp21 Ω K K' z u J t W) (hC3 : Q3T8.Asc77.C21_3)
    (hY : Q3T8.Asc77.C21_14_Y_ne_W) (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥)
    (hne : dComp Ω K ≠ dstarComp Ω K) {u' : G}
    (h' : Q3T8.Asc77.Hyp21 Ω K K' z u' J t W) (hu'W : u' ∈ W)
    (hY' : ¬ ExactLayer.exactLayer Ω u' ≤ sigmaGen Ω K) :
    ExactLayer.exactLayer Ω u' ≤ Subgroup.centralizer ({t * z} : Set G) := by
  have hα' := Hyp21.alphaOf_eq_bot_of_frame h hC3 hα h'
  exact (hY G Ω K K' z u' J t W h' hu'W hα' hne).resolve_left hY'

end T7N

end Asc77
end

end CFSG.ClassicalInvolution.Q3.Q3T8
