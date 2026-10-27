module

public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.WeakClosure81.SevenOne
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem pPrimeCore_map_subtype_le_normalizer_of_isTI {V H : Subgroup G} (hVH : V ≤ H)
    (hVel : IsElemAbelian 2 V) (hVcard : 4 ≤ Nat.card V)
    (hTI : CFSG.CGT.Timmesfeld75.IsTI V) :
    (CFSG.pPrimeCore 2 ↥H).map H.subtype ≤ normalizer (V : Set G) := by
  have hVp : IsPGroup 2 V := CFSG.Open.IsElemAbelian.isPGroup hVel
  have hOle : (CFSG.pPrimeCore 2 ↥H).map H.subtype ≤ H := Subgroup.map_subtype_le _
  have hEq : ((CFSG.pPrimeCore 2 ↥H).map H.subtype).subgroupOf H = CFSG.pPrimeCore 2 ↥H := by
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  have hOnormal : (((CFSG.pPrimeCore 2 ↥H).map H.subtype).subgroupOf H).Normal := by
    rw [hEq]
    infer_instance
  have hHnormO : H ≤ normalizer ((CFSG.pPrimeCore 2 ↥H).map H.subtype : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOle).mp hOnormal
  have hOcard : Nat.card ((CFSG.pPrimeCore 2 ↥H).map H.subtype) =
      Nat.card (CFSG.pPrimeCore 2 ↥H) :=
    Subgroup.card_map_of_injective (K := CFSG.pPrimeCore 2 ↥H) (f := H.subtype)
      H.subtype_injective
  have hOcop : Nat.Coprime 2 (Nat.card ((CFSG.pPrimeCore 2 ↥H).map H.subtype)) := by
    rw [hOcard]
    exact CFSG.pPrimeCore_coprime_card
  let act : MulDistribMulAction ↥V ↥((CFSG.pPrimeCore 2 ↥H).map H.subtype) :=
    { smul := fun v m =>
        ⟨(v : G) * (m : G) * (v : G)⁻¹, by
          exact (Subgroup.mem_normalizer_iff.mp (hHnormO (hVH v.2)) (m : G)).1 m.2⟩
      one_smul := fun m => Subtype.ext (by
        change (1 : G) * (m : G) * (1 : G)⁻¹ = (m : G)
        simp)
      mul_smul := fun v w m => Subtype.ext (by
        change ((v : G) * (w : G)) * (m : G) * ((v : G) * (w : G))⁻¹ =
          (v : G) * ((w : G) * (m : G) * (w : G)⁻¹) * (v : G)⁻¹
        group)
      smul_one := fun v => Subtype.ext (by
        change (v : G) * (1 : G) * (v : G)⁻¹ = (1 : G)
        simp)
      smul_mul := fun v m n => Subtype.ext (by
        change (v : G) * ((m : G) * (n : G)) * (v : G)⁻¹ =
          ((v : G) * (m : G) * (v : G)⁻¹) * ((v : G) * (n : G) * (v : G)⁻¹)
        group) }
  haveI : IsElementaryAbelian 2 ↥V :=
    CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hVel
  have hnot2 : ¬ 2 ∣ Nat.card ↥((CFSG.pPrimeCore 2 ↥H).map H.subtype) :=
    Nat.Prime.coprime_iff_not_dvd Nat.prime_two |>.mp hOcop
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := 2)
    (A := ↥V) (H := ↥((CFSG.pPrimeCore 2 ↥H).map H.subtype)) hVcard hnot2
  have hle : (⊤ : Subgroup ↥((CFSG.pPrimeCore 2 ↥H).map H.subtype)) ≤
      (Subgroup.normalizer (V : Set G)).comap ((CFSG.pPrimeCore 2 ↥H).map H.subtype).subtype := by
    rw [← hgen]
    refine iSup₂_le fun a ha => ?_
    intro m hm
    rw [CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff] at hm
    have hsmul : (a : G) * (m : G) * (a : G)⁻¹ = (m : G) := congrArg Subtype.val hm
    have hcent : (m : G) ∈ centralizer ({(a : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      calc (a : G) * (m : G) = ((a : G) * (m : G) * (a : G)⁻¹) * (a : G) := by group
        _ = (m : G) * (a : G) := by rw [hsmul]
    have ha1 : (a : G) ≠ 1 := by
      intro ha1
      exact ha (Subtype.ext ha1)
    exact (CFSG.LocalAnalysis.WeakClosure81.centralizer_le_normalizer_of_isTI hTI a.2 ha1) hcent
  intro m hm
  have hmN := hle (Subgroup.mem_top (⟨m, hm⟩ : ↥((CFSG.pPrimeCore 2 ↥H).map H.subtype)))
  rw [Subgroup.mem_comap] at hmN
  exact hmN

end CFSG.GroupTheory
