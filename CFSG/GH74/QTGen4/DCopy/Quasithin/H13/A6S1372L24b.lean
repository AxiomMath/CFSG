module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S13721b

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section NonAb

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

omit hab in

theorem not_mem_QH_of_L1_F4 {c : G} (hcL : c ∈ S.L1)
    (hcO : c ∉ pCoreOf 2 S.L1) : c ∉ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL1H := S.L1_le_of_mem_Hz_F4 hNS h13315 h1356two hH
  have hHQ : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hL1Q : S.L1 ⊓ pCoreOf 2 H ≤ pCoreOf 2 S.L1 := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      ((pCoreOf_isPGroup 2 H).to_le inf_le_right)
    exact fun l hl => mem_normalizer_inf_of (Subgroup.le_normalizer hl) (hHQ (hL1H hl))
  exact fun h => hcO (hL1Q ⟨hcL, h⟩)

theorem four_pow_five_le_nu_F4
    {K : Subgroup G} (hL1K : S.L1 ≤ K)
    (hKU0 : K ≤ Subgroup.centralizer ((conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G))
    {c : G} (hcL : c ∈ S.L1) (hc3 : c ^ 3 = 1)
    (hO : ∃ o ∈ pCoreOf 2 S.L1, c * o * c⁻¹ * o⁻¹ ∉ pCoreOf 2 H)
    (hU : 4 ^ 2 ≤ nu c (conjClosure S.V3 H)) :
    4 ^ 5 ≤ nu c (pCoreOf 2 S.L1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  have hL1H := S.L1_le_of_mem_Hz_F4 hNS h13315 h1356two hH
  have hcH : c ∈ H := hL1H hcL
  have hHQ : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hHU : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
    le_normalizer_conjClosure S.V3 H
  have hQH : pCoreOf 2 H ≤ H := pCoreOf_le 2 H
  have hQL1 := S.QH_le_normalizer_L1_F4 hNS h13315 h1356two hH
  have hQO : pCoreOf 2 H ≤ Subgroup.normalizer (pCoreOf 2 S.L1 : Set G) :=
    hQL1.trans (normalizer_le_normalizer_pCoreOf 2 S.L1)
  have hcO' : c ∈ Subgroup.normalizer (pCoreOf 2 S.L1 : Set G) := le_normalizer_pCoreOf 2 S.L1 hcL
  have hOH : pCoreOf 2 S.L1 ≤ H := (pCoreOf_le 2 S.L1).trans hL1H

  have hL1Q : S.L1 ⊓ pCoreOf 2 H ≤ pCoreOf 2 S.L1 := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      ((pCoreOf_isPGroup 2 H).to_le inf_le_right)
    exact fun l hl => mem_normalizer_inf_of (Subgroup.le_normalizer hl) (hHQ (hL1H hl))

  have hA : 4 * nu c (pCoreOf 2 S.L1 ⊓ pCoreOf 2 H) ≤ nu c (pCoreOf 2 S.L1) := by
    obtain ⟨o, ho, hno⟩ := hO
    refine four_mul_nu_le hc3 (pCoreOf_isPGroup 2 S.L1) inf_le_left hcO'
      (mem_normalizer_inf_of hcO' (hHQ hcH)) ?_ ⟨o, ho, fun h => hno h.2⟩
    exact fun x hx => mem_normalizer_inf_of (Subgroup.le_normalizer (mem_cfix.1 hx).1)
      (hHQ (hOH (mem_cfix.1 hx).1))

  have hB : nu c (pCoreOf 2 S.L1 ⊓ pCoreOf 2 H) = nu c (pCoreOf 2 H) := by
    have hY3 : ¬ 3 ∣ Nat.card ↥(pCoreOf 2 S.L1 ⊓ pCoreOf 2 H) := by
      obtain ⟨e, he⟩ := IsPGroup.iff_card.mp ((pCoreOf_isPGroup 2 H).to_le
        (inf_le_right : pCoreOf 2 S.L1 ⊓ pCoreOf 2 H ≤ pCoreOf 2 H))
      rw [he]
      intro h
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      omega
    have hcY : ∀ y ∈ pCoreOf 2 S.L1 ⊓ pCoreOf 2 H, c * y * c⁻¹ ∈ pCoreOf 2 S.L1 ⊓ pCoreOf 2 H :=
      fun y hy => (Subgroup.mem_normalizer_iff.mp (mem_normalizer_inf_of hcO' (hHQ hcH)) y).mp hy
    have hcX : ∀ q ∈ pCoreOf 2 H, q⁻¹ * (c * q * c⁻¹) ∈ pCoreOf 2 S.L1 ⊓ pCoreOf 2 H := by
      intro q hq
      have h1 : q⁻¹ * c * q⁻¹⁻¹ ∈ S.L1 :=
        (Subgroup.mem_normalizer_iff.mp (hQL1 ((pCoreOf 2 H).inv_mem hq)) _).mp hcL
      have hmem : q⁻¹ * (c * q * c⁻¹) ∈ S.L1 ⊓ pCoreOf 2 H := by
        refine ⟨?_, (pCoreOf 2 H).mul_mem ((pCoreOf 2 H).inv_mem hq)
          ((Subgroup.mem_normalizer_iff.mp (hHQ hcH) q).mp hq)⟩
        have e : q⁻¹ * (c * q * c⁻¹) = (q⁻¹ * c * q⁻¹⁻¹) * c⁻¹ := by group
        rw [e]
        exact S.L1.mul_mem h1 (S.L1.inv_mem hcL)
      exact ⟨hL1Q hmem, hmem.2⟩
    have hN : cfix c (pCoreOf 2 H) ≤
        Subgroup.normalizer ((pCoreOf 2 S.L1 ⊓ pCoreOf 2 H : Subgroup G) : Set G) :=
      fun x hx => mem_normalizer_inf_of (hQO (mem_cfix.1 hx).1)
        (Subgroup.le_normalizer (mem_cfix.1 hx).1)
    rw [nu_mul c (inf_le_right : pCoreOf 2 S.L1 ⊓ pCoreOf 2 H ≤ pCoreOf 2 H) hN,
      relIndex_cfix_sup_eq_one hc3 inf_le_right hY3 hcY hcX, one_mul]

  have hHCQ : pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G) ≤ pCoreOf 2 H :=
    inf_le_left
  have hNHC : cfix c (pCoreOf 2 H) ≤ Subgroup.normalizer ((pCoreOf 2 H ⊓
      Subgroup.centralizer (conjClosure S.V3 H : Set G) : Subgroup G) : Set G) := by
    intro x hx
    have hxH := hQH (mem_cfix.1 hx).1
    exact mem_normalizer_inf_of (hHQ hxH) (normalizes_of_conj_mem (X := H) (fun l hl y hy =>
      conj_centralizer_mem (hHU hl) hy) hxH)
  have hU0U : conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤
      conjClosure S.V3 H := inf_le_left
  have hNU0 : cfix c (conjClosure S.V3 H) ≤ Subgroup.normalizer ((conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) := by
    intro x hx
    have hxH := hQH (hF.conjClosure_Vp_le_pCoreOf (mem_cfix.1 hx).1)
    exact mem_normalizer_inf_of (hHU hxH) (normalizes_of_conj_mem (X := H) (fun l hl y hy =>
      conj_centralizer_mem (hHQ hl) hy) hxH)
  have hnuU0 : nu c (conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)) = 1 := by
    rw [nu, Subgroup.relIndex_eq_one]
    intro u hu
    refine mem_cfix.2 ⟨hu, ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp (hKU0 (hL1K hcL)) u hu).symm
  have hdual := nu_dual_F97 hF hab hcH hc3
  have hC : nu c (pCoreOf 2 H) = nu c (conjClosure S.V3 H) *
      nu c (pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G)) := by
    rw [nu_mul c hHCQ hNHC, hdual, nu_mul c hU0U hNU0, hnuU0, mul_one]

  have hVQ := S.VH_le_QH_F4 hNS h13315 h1356two hH hab
  have hUHC : conjClosure S.V3 H ≤
      pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G) :=
    le_inf (S.UH_le_VH.trans hVQ)
      (S.UH_le_VH.trans (S.VH_le_centralizer_UH_F4 hNS h13315 h1356two hH hab))
  have hD : nu c (conjClosure S.V3 H) ≤
      nu c (pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G)) :=
    nu_le_nu hUHC fun x hx => hHU (hQH (mem_cfix.1 hx).1.1)
  calc 4 ^ 5 = 4 * (4 ^ 2 * 4 ^ 2) := by norm_num
    _ ≤ 4 * (nu c (conjClosure S.V3 H) * nu c (conjClosure S.V3 H)) := by gcongr
    _ ≤ 4 * (nu c (conjClosure S.V3 H) * nu c (pCoreOf 2 H ⊓
        Subgroup.centralizer (conjClosure S.V3 H : Set G))) := by gcongr
    _ = 4 * nu c (pCoreOf 2 S.L1 ⊓ pCoreOf 2 H) := by rw [hB, hC]
    _ ≤ nu c (pCoreOf 2 S.L1) := hA

end NonAb

end Setting4

end CFSG.Quasithin.H13.A6
