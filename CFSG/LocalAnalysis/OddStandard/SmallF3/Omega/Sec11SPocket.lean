module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Steps
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ZSub
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ZNorm

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private theorem isSubnormal_subgroupOf_of_eq' {X : Type*} [Group X] {K A B : Subgroup X}
    (hAB : A = B) (h : (K.subgroupOf A).IsSubnormal) : (K.subgroupOf B).IsSubnormal := by
  subst hAB
  exact h

theorem asc82StepPocketOfNormal_of (hb : Asc82Basic10) (hP5 : Asc82FactPockets5) :
    Asc82StepPocketOfNormal := by
  intro G _ _ t L S z K1 K2 hctx hnorm
  obtain ⟨hpsp, -, -, -, -, -⟩ := hb G t L S z hctx.toSec10Z
  let H : Subgroup G := centralizer ({z} : Set G)
  have hK1H : K1 ≤ H := hctx.pocket1.2.1.trans inf_le_right
  have hK2H : K2 ≤ H := hctx.pocket2.2.1.trans inf_le_right
  have hcomm12 : ∀ a ∈ K1, ∀ b ∈ K2, a * b = b * a :=
    fun a ha b hb => sec10Z_comm hP5 hpsp hctx a ha b hb
  have hN : oddCoreIn H ≤ H := CFSG.ClassicalInvolution.Balance.oddCoreIn_le H
  have hNn : ∀ h ∈ H, ∀ n ∈ oddCoreIn H, h * n * h⁻¹ ∈ oddCoreIn H :=
    fun h hh n hn => CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn (X := H) hh hn
  have hBle : K1 ⊔ K2 ⊔ oddCoreIn H ≤ H := sup_le (sup_le hK1H hK2H) hN
  have hAle : K1 ⊔ oddCoreIn H ≤ K1 ⊔ K2 ⊔ oddCoreIn H :=
    sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hBnormal : ((K1 ⊔ K2 ⊔ oddCoreIn H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBle).mpr hnorm
  have hK2nK1 : K2 ≤ Subgroup.normalizer (K1 : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb a ha
    have hba : b * a = a * b := (hcomm12 a ha b hb).symm
    rw [hba, mul_assoc, mul_inv_cancel, mul_one]
    exact ha
  have hK2nN : K2 ≤ Subgroup.normalizer (oddCoreIn H : Set G) :=
    Subgroup.le_normalizer_iff.mpr (fun b hb n hn => hNn b (hK2H hb) n hn)
  have hK2nA : K2 ≤ Subgroup.normalizer (K1 ⊔ oddCoreIn H : Subgroup G) :=
    (le_inf hK2nK1 hK2nN).trans (Subgroup.inf_normalizer_le_normalizer_sup K1 (oddCoreIn H))
  have hBnA : K1 ⊔ K2 ⊔ oddCoreIn H ≤ Subgroup.normalizer (K1 ⊔ oddCoreIn H : Subgroup G) :=
    sup_le (sup_le (le_sup_left.trans (Subgroup.le_normalizer (H := K1 ⊔ oddCoreIn H))) hK2nA)
      (le_sup_right.trans (Subgroup.le_normalizer (H := K1 ⊔ oddCoreIn H)))
  have hAnormal : (((K1 ⊔ oddCoreIn H).subgroupOf H).subgroupOf
      ((K1 ⊔ K2 ⊔ oddCoreIn H).subgroupOf H)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.subgroupOf_mono H hAle)]
    rw [Subgroup.le_normalizer_iff]
    intro x hx a ha
    exact Subgroup.mem_subgroupOf.mpr
      (Subgroup.le_normalizer_iff.mp hBnA (x : G) (Subgroup.mem_subgroupOf.mp hx)
        (a : G) (Subgroup.mem_subgroupOf.mp ha))
  have hsub : ((K1 ⊔ oddCoreIn H).subgroupOf H).IsSubnormal :=
    Subgroup.IsSubnormal.step ((K1 ⊔ oddCoreIn H).subgroupOf H)
      ((K1 ⊔ K2 ⊔ oddCoreIn H).subgroupOf H) (Subgroup.subgroupOf_mono H hAle)
      hBnormal.isSubnormal hAnormal
  have hSL : IsSL23Mod ↥(K1 ⊔ oddCoreIn H) :=
    isSL23Mod_sup_odd (K1 := K1) (N := oddCoreIn H) hctx.pocket1.2.2.2
      (fun k hk n hn =>
        CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn (X := H) (hK1H hk) hn)
      (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn H)
  refine ⟨hctx.toSec10Z.pocket.1, K1 ⊔ oddCoreIn H, Subgroup.mem_sup_left hctx.pocket1.1,
    ?_, ?_, hSL⟩
  · exact le_inf le_top (sup_le hK1H hN)
  · exact isSubnormal_subgroupOf_of_eq' (K := K1 ⊔ oddCoreIn H) (A := H)
      (B := ⊤ ⊓ centralizer ({z} : Set G)) (top_inf_eq H).symm hsub

end CFSG.OddStandard.SmallF3.Omega
