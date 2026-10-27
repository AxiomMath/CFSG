module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4Basic
public import CFSG.RankThree.Chevalley.SteinbergBID4TrialityDescent

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthD4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.FieldGraphFieldPointwise
open CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent
open CFSG.LocalAnalysis.ComponentInitial

set_option linter.unusedSectionVars false


section Regular

variable {K : Type} [Field K]

abbrev orbitIdx : List (Fin Tag.D4.rank) := [0, 1, 3, 2]

theorem orbitIdx_sum (j : Fin Tag.D4.rank) (f : Fin Tag.D4.rank → K) :
    (orbitIdx.map fun i => if i = j then f i else 0).sum = f j := by
  fin_cases j <;>
    simp (config := { decide := true }) only [orbitIdx, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil] <;> simp <;> rfl

def regularElt (K : Type) [Field K] : adjointGroup Tag.D4 K :=
  (orbitIdx.map fun i => adjX Tag.D4 K i 1).prod

theorem coe_regularElt :
    (regularElt K : ModGL Tag.D4 K) = (orbitIdx.map fun i => xUnit Tag.D4 K i 1).prod := by
  rw [regularElt, Subgroup.val_list_prod, List.map_map]
  rfl

theorem regularElt_mem_posUnipotent :
    (regularElt K : ModGL Tag.D4 K) ∈ posUnipotent Tag.D4 K := by
  rw [coe_regularElt]
  refine list_prod_mem fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact xUnit_mem_posUnipotent i 1

theorem rootCoord_regularElt [Finite K] (j : Fin Tag.D4.rank) :
    rootCoord (single_pos j) (regularElt K : ModGL Tag.D4 K) = 1 := by
  rw [coe_regularElt, rootCoord_single_list_prod, orbitIdx_sum]

theorem regularElt_mem_fixedFieldImage (σ : K ≃+* K) :
    (regularElt K : ModGL Tag.D4 K) ∈ fixedFieldImage Tag.D4 σ := by
  rw [coe_regularElt]
  refine list_prod_mem fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact xUnit_mem_fixedFieldImage i (map_one σ)

theorem regularElt_mem_graphFixedRootGroup (σ : K →+* K) :
    (regularElt K : ModGL Tag.D4 K) ∈ graphFixedRootGroup TwistTag.D4 K σ := by
  have h : (regularElt K : ModGL Tag.D4 K) =
      (orbitX TwistTag.D4 K σ ⟨0, by decide⟩ 1 : ModGL TwistTag.D4.tag K) *
        (orbitX TwistTag.D4 K σ ⟨1, by decide⟩ 1 : ModGL TwistTag.D4.tag K) := by
    rw [coe_regularElt, CFSG.RankThree.Chevalley.coe_orbitX_D4_outer,
      CFSG.RankThree.Chevalley.coe_orbitX_D4_middle]
    simp [orbitIdx, mul_assoc]
    rfl
  rw [h]
  have hm := fun a => graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
    (orbitX_mem_graphFixedPosUnipotent TwistTag.D4 σ a 1)
  exact mul_mem (hm _) (hm _)

variable [Finite K]

theorem mem_unipotentPairAut_of_fix_regular
    {w₀ : WeylGroup Tag.D4}
    (hw₀ : ∀ w, (coxeterSystem Tag.D4).length w ≤ (coxeterSystem Tag.D4).length w₀)
    {n₀ u : adjointGroup Tag.D4 K}
    (hn₀ : (n₀ : ModGL Tag.D4 K) = canonicalRep (coxeterSystem Tag.D4) K w₀)
    (hu : (u : ModGL Tag.D4 K) ∈ posUnipotent Tag.D4 K)
    (hreg : ∀ i, rootCoord (single_pos i) (u : ModGL Tag.D4 K) ≠ 0)
    {β : MulAut (adjointGroup Tag.D4 K)} (hβu : β u = u)
    (hβv : β (n₀ * u * n₀⁻¹) = n₀ * u * n₀⁻¹) :
    β ∈ unipotentPairAut Tag.D4 K := by
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  obtain ⟨c, β', hU, hV, rfl⟩ :=
    (exceptional_ordinary_Sylow_opposition Tag.D4 K (ringChar K) w₀ hw₀).2.2.2.2.2 β
  have hN : β' ∈ unipotentPairAut Tag.D4 K := ⟨hU, hV⟩
  have hNx : ∀ x : adjointGroup Tag.D4 K, (MulAut.conj c * β') x = x → β' x = c⁻¹ * x * c := by
    intro x hx
    have h : c * β' x * c⁻¹ = x := hx
    calc β' x = c⁻¹ * (c * β' x * c⁻¹) * c := by group
      _ = c⁻¹ * x * c := by rw [h]
  have hNu := congrArg Subtype.val (hNx u hβu)
  have hNv := congrArg Subtype.val (hNx _ hβv)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hNu hNv
  have hcB : (c : ModGL Tag.D4 K)⁻¹ ∈ borelGroup Tag.D4 K := by
    refine mem_borelGroup_of_conj_regular (inv_mem c.2) hu hreg ?_
    rw [inv_inv, ← hNu]
    exact Subgroup.mem_subgroupOf.1 (apply_mem_of_mem_pairAut hN (Subgroup.mem_subgroupOf.2 hu))
  have hU' := map_conj_canonicalRep_longest (K := K) hw₀
  have hvV : ((n₀ * u * n₀⁻¹ : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) ∈
      negUnipotent Tag.D4 K := by
    rw [← hU']
    refine ⟨u, hu, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hn₀]
    rfl
  have hNvV := Subgroup.mem_subgroupOf.1
    (apply_mem_of_mem_pairAut_right hN (Subgroup.mem_subgroupOf.2 hvV))
  rw [hNv, ← hU'] at hNvV
  obtain ⟨z, hz, hzv⟩ := hNvV
  have hzv' : (n₀ : ModGL Tag.D4 K) * z * (n₀ : ModGL Tag.D4 K)⁻¹ =
      (c : ModGL Tag.D4 K)⁻¹ * ((n₀ : ModGL Tag.D4 K) * u * (n₀ : ModGL Tag.D4 K)⁻¹) * c :=
    (congrArg (fun x => x * z * x⁻¹) hn₀).trans hzv
  have hgB : (n₀ : ModGL Tag.D4 K)⁻¹ * (c : ModGL Tag.D4 K)⁻¹ * n₀ ∈ borelGroup Tag.D4 K := by
    refine mem_borelGroup_of_conj_regular
      (mul_mem (mul_mem (inv_mem n₀.2) (inv_mem c.2)) n₀.2) hu hreg ?_
    have e : (n₀ : ModGL Tag.D4 K)⁻¹ * (c : ModGL Tag.D4 K)⁻¹ * n₀ * u *
        ((n₀ : ModGL Tag.D4 K)⁻¹ * (c : ModGL Tag.D4 K)⁻¹ * n₀)⁻¹ = z :=
      calc _ = (n₀ : ModGL Tag.D4 K)⁻¹ *
            ((c : ModGL Tag.D4 K)⁻¹ * ((n₀ : ModGL Tag.D4 K) * u * (n₀ : ModGL Tag.D4 K)⁻¹) *
              c) * n₀ := by group
        _ = (n₀ : ModGL Tag.D4 K)⁻¹ * ((n₀ : ModGL Tag.D4 K) * z * (n₀ : ModGL Tag.D4 K)⁻¹) *
              n₀ := by rw [hzv']
        _ = z := by group
    rw [e]
    exact hz
  obtain ⟨-, hBmap, hBH, -⟩ := opposite_Borel_intersection Tag.D4 K w₀ hw₀
  have hcH : (c : ModGL Tag.D4 K)⁻¹ ∈ torusGroup Tag.D4 K := by
    rw [← hBH]
    refine Subgroup.mem_inf.2 ⟨hcB, ?_⟩
    rw [← hBmap]
    refine ⟨_, hgB, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hn₀]
    group
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (inv_mem_iff.1 hcH)
  have hc : MulAut.conj c = exactNormalAut Tag.D4 K b 1 0 := by
    refine MulEquiv.ext fun g => Subtype.ext ?_
    rw [coe_exactNormalAut, exactQ_D4, inv_one, mul_one, mul_one, ← hb]
    change (c : ModGL Tag.D4 K) * g * (c : ModGL Tag.D4 K)⁻¹ = _
    congr 2
    exact (Units.ext (entrywise_id _)).symm
  rw [hc]
  exact mul_mem (exactNormalAut_mem b 1 0) hN

theorem eq_one_of_exactNormalAut_zero_fix {a : Fin Tag.D4.rank → Kˣ} {φ : K ≃+* K}
    (h : exactNormalAut Tag.D4 K a φ 0 (regularElt K) = regularElt K) : a = 1 := by
  have himg : (exactNormalAut Tag.D4 K a φ 0 (regularElt K) : ModGL Tag.D4 K) =
      (orbitIdx.map fun i => xUnit Tag.D4 K i ((a i : K) * φ 1)).prod := by
    rw [regularElt, map_list_prod, List.map_map, Subgroup.val_list_prod, List.map_map]
    refine congrArg List.prod (List.map_congr_left fun i _ => ?_)
    simp only [Function.comp_apply, exactNormalAut_adjX, exactPerm_D4, Equiv.Perm.one_apply]
    rfl
  funext j
  have h1 : rootCoord (single_pos j)
      (exactNormalAut Tag.D4 K a φ 0 (regularElt K) : ModGL Tag.D4 K) =
        rootCoord (single_pos j) (regularElt K : ModGL Tag.D4 K) := by
    rw [h]
  rw [himg, rootCoord_regularElt, rootCoord_single_list_prod, orbitIdx_sum, map_one,
    mul_one] at h1
  exact Units.ext h1

theorem eq_of_mem_simplePosSubgroup_xUnit_one {i j : Fin Tag.D4.rank}
    (h : adjX Tag.D4 K i 1 ∈ simplePosSubgroup Tag.D4 K j) : j = i := by
  obtain ⟨c, hc⟩ := h
  have h1 : adjX Tag.D4 K i 1 = adjX Tag.D4 K j c := Subtype.ext hc
  have h2 := rootCoord_ite_eq_of_adjX_eq h1 i
  by_contra hji
  simp only [if_true, if_neg hji] at h2
  exact one_ne_zero h2

end Regular

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthD4
