module

public import CFSG.CGT.Stroth76.NoInv
public import CFSG.CGT.Stroth77.Arch76FrameLemma2
public import CFSG.CGT.Stroth76.TFacts

public section

namespace CFSG.CGT.Stroth76

open CFSG.CGT.Stroth77 CFSG.CGT.Stroth77.Arch76

@[expose] def centACheck (p : Tc) : Bool :=
  !(tmul p ((1, 0, 0), 0) == tmul ((1, 0, 0), 0) p &&
      tmul p ((0, 1, 0), 0) == tmul ((0, 1, 0), 0) p &&
      tmul p ((0, 0, 1), 0) == tmul ((0, 0, 1), 0) p) || p.2 == 0

theorem centACheck_all : ∀ p : Tc, centACheck p = true := by decide +kernel

section Config

variable {X : Type*} [Group X] (K : Config X)

theorem mem_A_of_mem_Tsub_of_mem_centralizer {g : X} (hg : g ∈ Tsub K)
    (hgA : g ∈ Subgroup.centralizer (K.A : Set X)) : g ∈ K.A := by
  obtain ⟨p, rfl⟩ := exists_tElt K hg
  rw [tElt_mem_A_iff]
  have hcomm : ∀ {q : Tc}, tElt K q ∈ K.A → tmul p q = tmul q p := by
    intro q hq
    apply tElt_injective K
    rw [tElt_mul, tElt_mul]
    exact (Subgroup.mem_centralizer_iff.mp hgA _ hq).symm
  have hw := hcomm (q := ((1, 0, 0), 0)) (by rw [tElt_w]; exact K.w_mem)
  have hx := hcomm (q := ((0, 1, 0), 0)) (by rw [tElt_x]; exact K.x_mem)
  have hy := hcomm (q := ((0, 0, 1), 0)) (by rw [tElt_y]; exact K.y_mem)
  have hc := centACheck_all p
  simp only [centACheck, hw, hx, hy, beq_self_eq_true, Bool.and_self, Bool.not_true,
    Bool.false_or, beq_iff_eq] at hc
  exact hc

end Config

variable {G : Type} [Group G] [Finite G] (F : StrothFrame G)

theorem frame_closureE_eq :
    Subgroup.closure {F.dA.toConfig.x ^ 2, F.dA.toConfig.y ^ 2, F.dA.toConfig.uv,
      F.dA.toConfig.t} = F.E := by
  rw [F.E_eq, StrothWeakTypeData.toConfig_x, StrothWeakTypeData.toConfig_y,
    StrothWeakTypeData.toConfig_uv, StrothWeakTypeData.toConfig_t, F.a_inv_sq, F.b_inv_sq]

theorem frame_mem_A_of_mem_normalizer_E {z : G} (hzS : z ∈ (F.S : Subgroup G))
    (hzE : z ∈ Subgroup.normalizer (F.E : Set G))
    (hzA : z ∈ Subgroup.centralizer (F.A : Set G)) : z ∈ F.A :=
  mem_A_of_mem_Tsub_of_mem_centralizer F.dA.toConfig (F.mem_T_of_normalizer_E hzS hzE) hzA

theorem frame_noInvolutionsCentralizing_of_conj {B C : Subgroup G} (hAB : F.A ≤ B)
    (hB2 : ∀ b ∈ B, b * b = 1 → b ∈ F.A) (hCS : C ≤ (F.S : Subgroup G))
    (hCB : C ≤ Subgroup.centralizer (B : Set G))
    (huv : ∀ z ∈ C, z⁻¹ * (F.dA.uv⁻¹ * z * F.dA.uv) ∈ B)
    (ht : ∀ z ∈ C, z⁻¹ * (F.dA.t⁻¹ * z * F.dA.t) ∈ B) :
    NoInvolutionsCentralizing C B :=
  noInvolutionsCentralizing_of_conj_mem F.dA.toConfig hAB hB2
    (fun z hz hzE => frame_mem_A_of_mem_normalizer_E F (hCS hz)
      (by rw [← frame_closureE_eq F]; exact hzE) (Subgroup.centralizer_le hAB (hCB hz)))
    huv ht

end CFSG.CGT.Stroth76
