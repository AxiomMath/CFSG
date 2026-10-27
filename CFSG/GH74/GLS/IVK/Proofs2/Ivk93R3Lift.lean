module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93W
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Sylow
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Lift

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P34 CFSG.ComponentClassification CFSG.Blueprint

section Lift

variable {G : Type} [Group G] [Finite G] {z : G} {r₁ : ℕ} {L₁ : Subgroup (CentralizerBar z)}

theorem pcomp_eq_of_comp_unique {H : Subgroup G} (hCH : Cen z ≤ H)
    (huniq : ∀ K : Subgroup (CentralizerBar z), IsComponent K → K = L₁)
    {A A' : Subgroup ↥(barIn H (Cen z))} (hA : IsPComponent 2 A) (hA' : IsPComponent 2 A') :
    A = A' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hρ := cenToBar_surjective H hCH
  have hodd : ∀ y ∈ (cenToBar H hCH).ker, Odd (orderOf y) := fun y hy =>
    odd_orderOf_of_cenToBar_eq_one H hCH y hy
  have hY : pPrimeCore 2 (CentralizerBar z) = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2
  let e := quotEquivOfHom (cenToBar H hCH) hρ hodd hY
  have hπ : ∀ B : Subgroup ↥(barIn H (Cen z)), B.map (cenToBar H hCH) =
      (B.map (QuotientGroup.mk' (pPrimeCore 2 ↥(barIn H (Cen z))))).map e.toMonoidHom := by
    intro B
    rw [Subgroup.map_map]
    rfl
  have himg : ∀ B : Subgroup ↥(barIn H (Cen z)), IsPComponent 2 B →
      B.map (cenToBar H hCH) = L₁ := by
    intro B hB
    obtain ⟨K, hK, -, hBK, -⟩ := hB
    rw [hπ B, hBK]
    exact huniq _ (CFSG.LocalCores.isComponent_map_mulEquiv e hK)
  have h1 : (A.map (QuotientGroup.mk' (pPrimeCore 2 ↥(barIn H (Cen z))))).map e.toMonoidHom =
      (A'.map (QuotientGroup.mk' (pPrimeCore 2 ↥(barIn H (Cen z))))).map e.toMonoidHom := by
    rw [← hπ A, ← hπ A', himg A hA, himg A' hA']
  exact CFSG.ComponentClassification.UnbalancedLayer.pComponent_eq_of_map_eq hA hA'
    (Subgroup.map_injective e.injective h1)

theorem exists_cfgW {k : Kind} {S : Subgroup G} (hctx : Stage2Ctx G z k S) {H : Subgroup G}
    (hCH : Cen z ≤ H) (hPerf : PerfInJ H) (hc₁ : IsComponent L₁)
    (huniq : ∀ K : Subgroup (CentralizerBar z), IsComponent K → K = L₁)
    (hzL : toBar z ⟨z, mem_Cen_self z⟩ ∈ L₁) (hodd₁ : Odd r₁) (h5 : 5 ≤ r₁)
    (hsl : HasSL2Model ↥L₁ (fun r => r = r₁)) :
    ∃ (hzJ : mkH H ⟨z, hCH (mem_Cen_self z)⟩ ∈ generalizedFitting (HBar H))
      (B : Subgroup (HBar H)), B ≤ generalizedFitting (HBar H) ∧ B ≤ barIn H (Cen z) ∧
      (B.subgroupOf (barIn H (Cen z))).map (cenToBar H hCH) = L₁ ∧
      Ivk93W (⟨mkH H ⟨z, hCH (mem_Cen_self z)⟩, hzJ⟩ : ↥(generalizedFitting (HBar H))) r₁
        (B.subgroupOf (generalizedFitting (HBar H))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : orderOf z = 2 := hctx.orderOf_z
  have hzmem : z ∈ H := hCH (mem_Cen_self z)
  set x : HBar H := mkH H ⟨z, hzmem⟩ with hx
  set C' : Subgroup (HBar H) := barIn H (Cen z) with hC'
  obtain ⟨B, hBJ, hBC, hxB, hBcomp, hBmap⟩ := lift_comp hz2 hCH hPerf hc₁ hzL
  have hxJ : x ∈ generalizedFitting (HBar H) := hBJ hxB
  have hcent : centralizer ({x} : Set (HBar H)) = C' := centralizer_mk_eq H hz2 hzmem
  have hcJ := centralizer_singleton_subgroupOf (J := generalizedFitting (HBar H)) hxJ
  rw [hcent] at hcJ
  have hodd : ∀ y ∈ (cenToBar H hCH).ker, Odd (orderOf y) := fun y hy =>
    odd_orderOf_of_cenToBar_eq_one H hCH y hy
  have : (generalizedFitting (HBar H)).Normal := LocalCores.generalized_fitting_characteristic.2
  refine ⟨hxJ, B, hBJ, hBC, hBmap, isCentralInvolution_zbar hctx hCH hxJ, hodd₁, h5, ?_,
    Subgroup.mem_subgroupOf.2 hxB, ?_, ?_⟩
  ·
    rw [hcJ]
    exact ⟨fun y hy => hBC hy,
      ComponentClassification.Sp4Rec.isPComponent_subgroupOf_restrict hBC hBJ hBcomp⟩
  ·
    exact hasSL2Model_quot_of_equiv
      ((Subgroup.subgroupOfEquivOfLe hBC).trans (Subgroup.subgroupOfEquivOfLe hBJ).symm)
      (hasSL2Model_quot_of_hom (cenToBar H hCH) hodd hBmap hodd₁ h5 hsl)
  ·
    intro M hM
    rw [hcJ] at hM
    obtain ⟨hMle, hMc⟩ := hM
    set L : Subgroup (HBar H) := M.map (generalizedFitting (HBar H)).subtype with hL
    have hLJ : L ≤ generalizedFitting (HBar H) := by
      rintro _ ⟨m, -, rfl⟩
      exact m.2
    have hLC : L ≤ C' := by
      rintro _ ⟨m, hm, rfl⟩
      exact Subgroup.mem_subgroupOf.1 (hMle hm)
    have hLM : L.subgroupOf (generalizedFitting (HBar H)) = M :=
      Subgroup.comap_map_eq_self_of_injective (generalizedFitting (HBar H)).subtype_injective M
    have hLcomp : IsPComponent 2 (L.subgroupOf C') := by
      refine ComponentClassification.Sp4Rec.isPComponent_subgroupOf_extend hLC hLJ ?_
      rw [hLM]
      exact hMc
    have heq := pcomp_eq_of_comp_unique hCH huniq hLcomp hBcomp
    have hLB : L = B := by
      have h1 := Subgroup.subgroupOf_inj.mp heq
      rwa [inf_of_le_left hLC, inf_of_le_left hBC] at h1
    rw [← hLM, hLB]

end Lift

end CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt
