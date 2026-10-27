module

public import CFSG.ClassicalInvolution.Asc77.AscS24B
public import CFSG.ClassicalInvolution.Asc77.AscT7K4

public section

namespace CFSG.ClassicalInvolution.Asc77.S24

open CFSG CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
open CFSG.Open (IsElemAbelian classicalInvolutionOddCore IsSubnormal)

set_option linter.unusedSectionVars false


section Vertex

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem hyp51At_of_twin_vertex_z' {K₀ : Subgroup G} (hst : AscStand p f Ω K₀)
    {K K' : Subgroup G} {z x y e₁ e₂ : G} (hKΩ : K ∈ Ω) (hK'Ω : K' ∈ Ω)
    (hzK : IsUniqueInvolution K z) (hzK' : IsUniqueInvolution K' z)
    {B : Subgroup G} (hB : IsElemAbelian 2 B) (hzB : z ∈ B)
    (hxK : x ∈ K) (hyK' : y ∈ K') (hxyB : x * y ∈ B) (hxy1 : x * y ≠ 1) (hxyz : x * y ≠ z)
    (he₁B : e₁ ∈ B) (he₁1 : e₁ ≠ 1) (he₁z : e₁ ≠ z) (he₁K : e₁ ∈ trivialOnQuot K)
    (he₂B : e₂ ∈ B) (he₂1 : e₂ ≠ 1) (he₂z : e₂ ≠ z) (he₂K' : e₂ ∈ trivialOnQuot K') :
    Hyp51At B z := by
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hc₁ : IsClassicalMember p f K z := isClassicalMember_of_twin hΩ hKΩ hzK
  have hc₂ : IsClassicalMember p f K' z := isClassicalMember_of_twin hΩ hK'Ω hzK'
  have hz1 : z ≠ 1 := hzK.ne_one
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) := T7S22.le_centralizer_of_classical hc₁
  have hK'z : K' ≤ Subgroup.centralizer ({z} : Set G) := T7S22.le_centralizer_of_classical hc₂
  have hxC : x * y ∈ Subgroup.centralizer ({z} : Set G) :=
    (Subgroup.centralizer ({z} : Set G)).mul_mem (hKz hxK) (hK'z hyK')
  have key : ∀ (e : G), e ∈ B → e ≠ 1 → e ≠ z → ∀ M : Subgroup G,
      IsSubnormal M (Subgroup.centralizer ({z} : Set G)) →
      e ∈ trivialOnQuot M → ¬ MovedByAll B z (modOdd z M) := by
    intro e heB he1 hez M hMs hmt hmov
    have heC : e ∈ Subgroup.centralizer ({z} : Set G) :=
      Lemma52Proof.le_centralizer_of_mem hB hzB heB
    have hxm : oddQuotMk z ⟨e, heC⟩ ∈ modOdd z B := oddQuotMk_mem_modOdd heB heC
    have hnot := Lemma52Proof.oddQuotMk_not_mem_zpowers hB hzB hz1 heB he1 hez heC
    obtain ⟨w, hw, hwne⟩ := hmov _ hxm hnot
    exact hwne (T7K.oddQuotMk_comm_of_trivialOnQuot heC hmt hMs hw)
  have hno : ∀ L : Subgroup (OddQuot z), CFSG.IsComponent L → MovedByAll B z L → False := by
    intro L hL hmov
    rcases T7S22.eq_or_eq_of_movedByAll hq hc₁ hc₂ hB hzB hz1 hxK hyK' hxyB hxy1 hxyz hxC hL
      hmov with rfl | rfl
    · exact key e₁ he₁B he₁1 he₁z K hc₁.subnormal he₁K hmov
    · exact key e₂ he₂B he₂1 he₂z K' hc₂.subnormal he₂K' hmov
  exact ⟨fun L₁ L₂ h1 _ m1 _ => (hno L₁ h1 m1).elim, fun L hL hm => (hno L hL hm).elim⟩

end Vertex

namespace Ctx

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u g : G}
  (C : Ctx p f Ω K K' W S R R' z u g)

include C

theorem e0u_ne_one : C.e0 * u ≠ 1 := fun h =>
  C.e0_not_mem (by
    have : C.e0 = u⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))

theorem e0u_ne_z : C.e0 * u ≠ z := fun h =>
  C.e0_not_mem (by
    have : C.e0 = z * u⁻¹ := eq_mul_inv_of_mul_eq h
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))))

theorem e0_ne_z : C.e0 ≠ z := fun h =>
  C.e0_not_mem (by rw [h]; exact Subgroup.subset_closure (by simp))

theorem e0u_sq (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥) :
    C.e0 * u * (C.e0 * u) = 1 := by
  calc C.e0 * u * (C.e0 * u) = C.e0 * (u * C.e0) * u := by group
    _ = C.e0 * (C.e0 * u) * u := by rw [C.comm_ue]
    _ = (C.e0 * C.e0) * (u * u) := by group
    _ = 1 := by rw [C.e0_sq hZ, C.u_sq]; group

theorem e0u_mem_B : C.e0 * u ∈ C.B := C.B.mul_mem C.e0_mem_B C.u_mem_B

theorem K_mem_tq_e0 (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥) :
    K ∈ tqMembers Ω C.e0 := by
  have h := C.D.K_mem_tq C.hc hZ
  rwa [C.hK] at h

theorem K'_mem_tq_e0u (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥) :
    K' ∈ tqMembers Ω (C.e0 * u) := by
  have hst := C.hs.stand
  have hR'syl : IsSylow2In R' K' := by
    have h := C.D.F.ρ'.hRK
    rwa [C.hR', C.hK'] at h
  exact (mem_tqMembers_iff_exists_sylow hst.odd hst.five hst.hyp
    (isPGroup_zpowers_of_sq_eq_one (C.e0u_sq hZ))).mpr ⟨C.hs.hK'.1, R', hR'syl, C.e0u_cent_R'⟩

theorem hyp51At_z (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥) :
    Hyp51At C.B z := by
  have hst := C.hs.stand
  have hKΩ : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := C.hs.hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet C.hs.hz C.hs.hK'
  have hbK : C.D.x₁ ^ C.D.m ∈ K := by
    have h := C.D.F.ρ.hRK.1 (bEl_mem C.D)
    rwa [C.hK] at h
  have hb'K' : C.D.x₂ ^ C.D.m ∈ K' := by
    have h := C.D.F.ρ'.hRK.1 (bEl'_mem C.D)
    rwa [C.hK'] at h
  have he0K : C.e0 ∈ trivialOnQuot K := (C.K_mem_tq_e0 hZ).2
  have he0uK' : C.e0 * u ∈ trivialOnQuot K' := (C.K'_mem_tq_e0u hZ).2
  have hu := C.u_cases
  obtain ⟨x, hxK, hxy⟩ : ∃ x ∈ K, x * C.D.x₂ ^ C.D.m = u := by
    rcases hu with h | h
    · exact ⟨C.D.x₁ ^ C.D.m, hbK, h.symm⟩
    · exact ⟨z * C.D.x₁ ^ C.D.m, K.mul_mem C.hs.hz.mem hbK, by rw [mul_assoc]; exact h.symm⟩
  refine hyp51At_of_twin_vertex_z' hst hKΩ hK'Ω C.hs.hz hzK' (C.B_isElemAbelian hZ) C.z_mem_B
    hxK hb'K' (by rw [hxy]; exact C.u_mem_B) (by rw [hxy]; exact C.u_ne_one)
    (by rw [hxy]; exact C.u_ne_z) C.e0_mem_B C.e0_ne_one
    C.e0_ne_z he0K C.e0u_mem_B C.e0u_ne_one C.e0u_ne_z he0uK'

end Ctx

end CFSG.ClassicalInvolution.Asc77.S24
