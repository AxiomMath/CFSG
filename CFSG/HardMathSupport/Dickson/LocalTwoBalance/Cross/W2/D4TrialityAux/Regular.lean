module

public import CFSG.LieType.Chevalley.E6FieldGraphFieldPointwiseCentralizer

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Chevalley CFSG.LieType.Chevalley.FieldGraphFieldPointwise
open scoped Pointwise

section Regular

variable {τ : Tag} {K : Type} [Field K] [Finite K]


theorem mem_unipotentPairAut_of_fix_regular
    {w₀ : WeylGroup τ} (hw₀ : ∀ w, (coxeterSystem τ).length w ≤ (coxeterSystem τ).length w₀)
    {n₀ u : adjointGroup τ K} (hn₀ : (n₀ : ModGL τ K) = canonicalRep (coxeterSystem τ) K w₀)
    (hu : (u : ModGL τ K) ∈ posUnipotent τ K)
    (hreg : ∀ i, rootCoord (single_pos i) (u : ModGL τ K) ≠ 0)
    {β : MulAut (adjointGroup τ K)} (hβu : β u = u)
    (hβv : β (n₀ * u * n₀⁻¹) = n₀ * u * n₀⁻¹) : β ∈ unipotentPairAut τ K := by
  classical
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  obtain ⟨c, N, hNU, hNV, rfl⟩ :=
    (exceptional_ordinary_Sylow_opposition τ K (ringChar K) w₀ hw₀).2.2.2.2.2 β
  have hN : N ∈ unipotentPairAut τ K := ⟨hNU, hNV⟩
  have hNx : ∀ x : adjointGroup τ K, (MulAut.conj c * N) x = x → N x = c⁻¹ * x * c := by
    intro x hx
    have h : c * N x * c⁻¹ = x := hx
    calc N x = c⁻¹ * (c * N x * c⁻¹) * c := by group
      _ = c⁻¹ * x * c := by rw [h]
  have hNu := congrArg Subtype.val (hNx u hβu)
  have hNv := congrArg Subtype.val (hNx _ hβv)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hNu hNv
  have hcB : (c : ModGL τ K)⁻¹ ∈ borelGroup τ K := by
    refine mem_borelGroup_of_conj_regular (inv_mem c.2) hu hreg ?_
    rw [inv_inv, ← hNu]
    exact Subgroup.mem_subgroupOf.1 (apply_mem_of_mem_pairAut hN (Subgroup.mem_subgroupOf.2 hu))
  have hU := map_conj_canonicalRep_longest (K := K) hw₀
  have hvV : ((n₀ * u * n₀⁻¹ : adjointGroup τ K) : ModGL τ K) ∈ negUnipotent τ K := by
    rw [← hU]
    refine ⟨u, hu, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hn₀]
    rfl
  have hNvV := Subgroup.mem_subgroupOf.1
    (apply_mem_of_mem_pairAut_right hN (Subgroup.mem_subgroupOf.2 hvV))
  rw [hNv, ← hU] at hNvV
  obtain ⟨z, hz, hzv⟩ := hNvV
  have hzv' : (n₀ : ModGL τ K) * z * (n₀ : ModGL τ K)⁻¹ =
      (c : ModGL τ K)⁻¹ * ((n₀ : ModGL τ K) * u * (n₀ : ModGL τ K)⁻¹) * c :=
    (congrArg (fun x => x * z * x⁻¹) hn₀).trans hzv
  have hgB : (n₀ : ModGL τ K)⁻¹ * (c : ModGL τ K)⁻¹ * n₀ ∈ borelGroup τ K := by
    refine mem_borelGroup_of_conj_regular
      (mul_mem (mul_mem (inv_mem n₀.2) (inv_mem c.2)) n₀.2) hu hreg ?_
    have e : (n₀ : ModGL τ K)⁻¹ * (c : ModGL τ K)⁻¹ * n₀ * u *
        ((n₀ : ModGL τ K)⁻¹ * (c : ModGL τ K)⁻¹ * n₀)⁻¹ = z :=
      calc _ = (n₀ : ModGL τ K)⁻¹ *
            ((c : ModGL τ K)⁻¹ * ((n₀ : ModGL τ K) * u * (n₀ : ModGL τ K)⁻¹) * c) * n₀ := by
            group
        _ = (n₀ : ModGL τ K)⁻¹ * ((n₀ : ModGL τ K) * z * (n₀ : ModGL τ K)⁻¹) * n₀ := by
            rw [hzv']
        _ = z := by group
    rw [e]
    exact hz
  obtain ⟨-, hBmap, hBH, -⟩ := opposite_Borel_intersection τ K w₀ hw₀
  have hcH : (c : ModGL τ K)⁻¹ ∈ torusGroup τ K := by
    rw [← hBH]
    refine Subgroup.mem_inf.2 ⟨hcB, ?_⟩
    rw [← hBmap]
    refine ⟨_, hgB, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hn₀]
    group
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (inv_mem_iff.1 hcH)
  have hc : MulAut.conj c = exactNormalAut τ K b 1 0 := by
    refine MulEquiv.ext fun g => Subtype.ext ?_
    rw [coe_exactNormalAut, exactQ_zero, inv_one, mul_one, mul_one, ← hb]
    change (c : ModGL τ K) * g * (c : ModGL τ K)⁻¹ = _
    congr 2
    exact (Units.ext (entrywise_id _)).symm
  exact mul_mem (hc ▸ exactNormalAut_mem b 1 0) hN

end Regular

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
