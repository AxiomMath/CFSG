module

public import CFSG.GH74.GLS.Stage2.Local.P34S5W
public import CFSG.GH74.GLS.Stage2.Local.P34NS12Stmt

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
open CFSG.ComponentClassification.LBalance (SchreierSections)

theorem step5H_of_w
    {Ctx : ∀ (G : Type) [Group G] [Finite G], G → Kind → Subgroup G → Prop}
    (hto : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G),
      Stage2Ctx G z k S → Ctx G z k S)
    (h27 : Leaf_Prop27W Ctx) (hSch : GHSchreier) (hNS : NSm12H) :
    ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
      ∀ H : Subgroup G, H ≠ ⊤ → Cen z ≤ H → pCore 2 (HBar H) = ⊥ →
        IsSimpleGroup ↥(generalizedFitting (HBar H)) →
        (∃ a b : ↥(generalizedFitting (HBar H)), a * b ≠ b * a) → PerfInJ H →
        HasTwoInvolutionClasses (HBar H) → FUS H → False := by
  intro G _ _ z k S hctx H hne hCH hV hs hnab hPerf h2 hFUS
  have hz2 := hctx.orderOf_z
  have hzH : z ∈ H := z_mem_of_cen_le hCH
  obtain ⟨a, b, ha, hb, hab⟩ := exists_two_involutions_not_conj hFUS h2
  rcases kind_cases hctx with hone | ⟨hk, x₀, hx₀2, hx₀z, hcls⟩
  · exact hab (hone a b ha hb)
  obtain ⟨x₁, hx₁S, hx₁nc⟩ := exists_nonCentral_in_S hctx hx₀2 hx₀z
  have hx₁C : x₁ ∈ Cen z := hctx.S_le_Cen hx₁S
  have hW : Prop27W z k := h27 G z k S (hto G z k S hctx)
  obtain ⟨x, hxC, hxnc, hJ, hm⟩ : ∃ x ∈ Cen z, IsNonCentralInvolution x ∧
      (IsClassicalKind k → Ixz z x ≠ ⊥ ∧ Prop27WJ z x) ∧ (k = Kind.m12 → Prop27WM12 z x) := by
    rcases hk with hcl | hmk
    · obtain ⟨x, hxC, hxnc, hI, hJ⟩ := hW.1 hcl ⟨x₁, hx₁C, hx₁nc⟩
      refine ⟨x, hxC, hxnc, fun _ => ⟨hI, hJ⟩, fun h => ?_⟩
      subst h
      rcases hcl with h | ⟨ε, h⟩ <;> cases h
    · subst hmk
      exact ⟨x₁, hx₁C, hx₁nc, (fun hc => by rcases hc with h | ⟨ε, h⟩ <;> cases h),
        fun _ => hW.2 rfl x₁ hx₁C hx₁nc⟩
  have hx2 : orderOf x = 2 := hxnc.1
  have hJ' : IsClassicalKind k → Prop27WJ z x := fun h => (hJ h).2
  have hDih := dihJ_of_prop27W hk hJ' hm
  have hzN : z ∈ centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.1 hxC).symm
  have hns : ¬ Group.IsSolvable ↥(Jx x ⊓ H) := by
    have hk' := hk
    rcases hk' with hcl | hmk
    · have hsch : SchreierSections ↥(centralizer ({x} : Set G)) :=
        schreierSections_of_ghGroup hSch
          (Uniqueness.SU.SU0.GHGroup.of_kgh hctx.std.kgh (centralizer_ne_top_of_nonCentral hxnc))
      exact not_isSolvable_J0 hCH (Ixz_le_Jx_of_sections hsch hzN hz2) (hJ hcl).1
    · subst hmk
      exact hNS G z S hctx H hne hCH hV hs hnab hPerf h2 x hxC hxnc
  have hNH : centralizer ({x} : Set G) ≤ H := step5_core_w hz2 hCH hFUS hxC hx2 hk hJ' hm hDih hns
  have hxx₀ : IsConj x₀ x := by
    rcases hcls x hx2 with hc | hc
    · exact absurd (isCentralInvolution_of_isConj_P34 hctx.central hc) hxnc.2
    · exact hc
  have hclosed : ∀ t ∈ H, orderOf t = 2 → centralizer ({t} : Set G) ≤ H := by
    intro t htH ht2
    rcases hcls t ht2 with hzt | hxt
    · exact centralizer_le_of_fus hFUS hCH hz2 htH ht2 hzt
    · exact centralizer_le_of_fus hFUS hNH hx2 htH ht2 (hxx₀.symm.trans hxt)
  obtain ⟨M, hM⟩ := exists_stronglyEmbedded_of_closed hctx.std.kps.1 hne hz2 hzH hclosed
  exact not_exists_stronglyEmbedded hctx.std ⟨M, hM⟩

end CFSG.GH74.GLS.Stage2.Local.P34
