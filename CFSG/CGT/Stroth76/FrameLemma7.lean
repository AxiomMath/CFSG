module

public import CFSG.CGT.Stroth76.FrameFusion
public import CFSG.CGT.Stroth76.Lemma56
public import CFSG.CGT.Stroth76.Lemma7OneMain
public import CFSG.CGT.Stroth77.Arch76FrameChar

public section

namespace CFSG.CGT.Stroth76

open CFSG.CGT.Stroth77 CFSG.CGT.Stroth77.Arch76

variable {G : Type} [Group G] [Finite G] (F : StrothFrame G)

theorem closure_insert_four_eq {X : Type*} [Group X] (a b c d : X) :
    Subgroup.closure ({a, b, c, d} : Set X) =
      Subgroup.closure ({a, b, c} : Set X) ⊔ Subgroup.closure {d} := by
  rw [← Subgroup.closure_union]
  congr 1
  ext g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
  tauto

theorem frame_centralizer_inf_ne_A
    (hAnn1 : ¬ IsConj F.dA.toConfig.w ((F.dA.toConfig.x * F.dA.toConfig.y) ^ 2)) :
    Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) ≠ F.A := by
  intro hCA
  haveI := F.simple
  obtain ⟨hfusE, huw, hwu, -, -, -⟩ := frame_fusion F
  set K := F.dA.toConfig with hK
  have hx : K.x = (F.dA.a : G)⁻¹ := rfl
  have hy : K.y = (F.dA.b : G)⁻¹ := rfl
  rcases F.arch76Lemma2 hCA with hS | ⟨s, -, hS, hs2, hsw, hsa, hsb, hcase⟩
  · exact frame_arch76Lemma4 F hAnn1 F.S hS.symm.le hS.symm
  · have hS' : (F.S : Subgroup G) = Tsub K ⊔ Subgroup.closure {s} := by
      rw [hS, closure_insert_four_eq, ← sup_assoc]
      rfl
    have hsx : s⁻¹ * K.x * s = K.x⁻¹ := by
      rw [hx, inv_inv, show s⁻¹ * (F.dA.a : G)⁻¹ * s = (s⁻¹ * (F.dA.a : G) * s)⁻¹ by group, hsa,
        inv_inv]
    have hsy : s⁻¹ * K.y * s = K.y⁻¹ := by
      rw [hy, inv_inv, show s⁻¹ * (F.dA.b : G)⁻¹ * s = (s⁻¹ * (F.dA.b : G) * s)⁻¹ by group, hsb,
        inv_inv]
    rcases hcase with ⟨huv, ht, hu⟩ | ⟨huv, ht, hu⟩
    · refine arch76Lemma7_self_centralizing (K := K) (frame_nonab F) hfusE huw hwu hAnn1 F.S hS'
        (by rw [pow_two]; exact hs2) hsw hsx hsy ?_ ?_ hu
      · show s⁻¹ * F.dA.uv * s = (F.dA.a : G)⁻¹ * (F.dA.b : G)⁻¹ * F.dA.uv
        exact huv
      · show s⁻¹ * F.dA.t * s = ((F.dA.a : G)⁻¹)⁻¹ * F.dA.t
        rw [inv_inv]; exact ht
    · refine false_of_lemma2_iii K hfusE huw hwu hAnn1 (s := s) ?_ hu
      show s⁻¹ * F.dA.uv * s = ((F.dA.a : G)⁻¹)⁻¹ * (F.dA.b : G)⁻¹ * F.dA.uv
      rw [inv_inv]; exact huv

theorem frame_arch76Lemma7_index_two
    (hAnn1 : ¬ IsConj F.dA.toConfig.w ((F.dA.toConfig.x * F.dA.toConfig.y) ^ 2)) {c : G}
    (hS : (F.S : Subgroup G) = Tsub F.dA.toConfig ⊔ Subgroup.closure {c})
    (hcx : c⁻¹ * F.dA.toConfig.x * c = F.dA.toConfig.x)
    (hcy : c⁻¹ * F.dA.toConfig.y * c = F.dA.toConfig.y) (hc2 : c ^ 2 = F.dA.toConfig.w)
    (hcase : (F.dA.toConfig.uv⁻¹ * c * F.dA.toConfig.uv =
          c * F.dA.toConfig.x⁻¹ * F.dA.toConfig.y⁻¹ ∧
        F.dA.toConfig.t⁻¹ * c * F.dA.toConfig.t = c * F.dA.toConfig.x ∧
        F.dA.toConfig.u⁻¹ * c * F.dA.toConfig.u = c) ∨
      (F.dA.toConfig.uv⁻¹ * c * F.dA.toConfig.uv = c * F.dA.toConfig.x * F.dA.toConfig.y⁻¹ ∧
        F.dA.toConfig.t⁻¹ * c * F.dA.toConfig.t =
          c * F.dA.toConfig.x * F.dA.toConfig.y ^ 2 ∧
        F.dA.toConfig.u⁻¹ * c * F.dA.toConfig.u = c⁻¹)) :
    False := by
  haveI := F.simple
  obtain ⟨hfusE, huw, hwu, -, -, -⟩ := frame_fusion F
  exact arch76Lemma7_index_two F.dA.toConfig (frame_nonab F) hfusE huw hwu hAnn1 F.S hS hcx hcy
    hc2 hcase

end CFSG.CGT.Stroth76
