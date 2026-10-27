module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GroupTheory.SteinbergBSNormalPlane
import CFSG.GroupTheory.SteinbergBKOddMetacyclicTorsion
import CFSG.GroupTheory.SteinbergBKOddNoncyclicRankTwo
import CFSG.Goldschmidt.Steps.Sec82PGroup

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L618Om

open Subgroup

theorem exists_plane_of_omega {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {R : Type*} [Group R]
    [Finite R] (hR : IsPGroup p R) {A : Subgroup R} (hAe : CFSG.IsElementaryAbelian p A)
    (hAc : Nat.card A = p ^ 3) {Q E : Subgroup R} (hEQ : E ≤ Q)
    (hEe : CFSG.IsElementaryAbelian p E) (hEc : Nat.card E = p ^ 2) {q : R} (hqQ : q ∈ Q)
    (hq1 : q ^ p = 1) (hqE : q ∉ E) :
    ∃ U : Subgroup R, U ≤ Q ∧ CFSG.IsElementaryAbelian p U ∧ Nat.card U = p ^ 2 ∧
      ∀ u ∈ U, u ≠ 1 → ∃ W : Subgroup R, W ≤ centralizer ({u} : Set R) ∧
        CFSG.IsElementaryAbelian p W ∧ p ^ 3 ≤ Nat.card W := by
  classical
  have : CFSG.IsElementaryAbelian p A := hAe
  have : CFSG.IsElementaryAbelian p E := hEe
  have hnc : ¬ IsCyclic (⊤ : Subgroup R) := by
    intro hc
    have : IsCyclic R :=
      isCyclic_of_surjective (Subgroup.topEquiv (G := R)).toMonoidHom
        (Subgroup.topEquiv (G := R)).surjective
    have : IsCyclic A := inferInstance
    have h1 : Monoid.exponent A = Nat.card A := IsCyclic.exponent_eq_card
    have h2 : Monoid.exponent A ∣ p := CFSG.IsElementaryAbelian.exponent_dvd_p p A
    rw [h1, hAc] at h2
    have h3 := Nat.le_of_dvd hp.out.pos h2
    have h4 : p < p ^ 3 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 3 := Nat.pow_lt_pow_right hp.out.one_lt (by norm_num)
    omega
  obtain ⟨V, -, hVn, hVc, hVp, hVcomm⟩ :=
    CFSG.Goldschmidt.Sec82.exists_normal_plane_le hp2 hR (⊤ : Subgroup R) hnc
  have : V.Normal := hVn
  have hVe : CFSG.IsElementaryAbelian p V := CFSG.IsElementaryAbelian.of_forall hVcomm hVp
  obtain ⟨hCn, -, hidx, -, -, hVW, hWe, hW3, -⟩ :=
    CFSG.GroupTheory.SteinbergBS.normal_plane_centralizer_rank_three hR V A hVc hAc
  set C : Subgroup R := centralizer (V : Set R) with hC
  have : C.Normal := hCn
  have hQp : IsPGroup p Q := hR.to_subgroup Q
  have hDnc : ¬ IsCyclic (C ⊓ Q : Subgroup R) := by
    intro hcyc
    have hidxp : C.index ∣ p := by
      obtain ⟨k, hk⟩ := hR.index C
      have hk1 : k ≤ 1 := by
        refine (Nat.pow_le_pow_iff_right hp.out.one_lt).mp ?_
        rw [pow_one, ← hk]
        exact hidx
      rw [hk]
      calc p ^ k ∣ p ^ 1 := pow_dvd_pow p hk1
        _ = p := pow_one p
    have hmeta : CFSG.IsMetacyclic Q := by
      refine ⟨C.subgroupOf Q, Subgroup.Normal.subgroupOf hCn Q, ?_, ?_⟩
      · rw [← Subgroup.subgroupOf_map_subtype] at hcyc
        exact ((C.subgroupOf Q).equivMapOfInjective Q.subtype
          Q.subtype_injective).isCyclic.mpr hcyc
      · refine isCyclic_of_card_dvd_prime (p := p) ?_
        exact (Subgroup.relIndex_dvd_index_of_normal C Q).trans hidxp
    have hle := CFSG.GroupTheory.SteinbergBK.card_omega₁_le hp2 hQp hmeta
    have hEQ' : E.subgroupOf Q ≤ CFSG.omega₁ (G := ↥Q) (p := p) := by
      have : CFSG.IsElementaryAbelian p (E.subgroupOf Q) :=
        CFSG.IsElementaryAbelian.subgroupOf hEQ
      exact CFSG.elementaryAbelian_le_omega₁
    have hqmem : (⟨q, hqQ⟩ : ↥Q) ∈ CFSG.omega₁ (G := ↥Q) (p := p) := by
      refine Subgroup.subset_closure ?_
      show (⟨q, hqQ⟩ : ↥Q) ^ p ^ 1 = 1
      rw [pow_one]
      exact Subtype.ext hq1
    have hlt : E.subgroupOf Q < CFSG.omega₁ (G := ↥Q) (p := p) := by
      refine lt_of_le_of_ne hEQ' fun h => hqE ?_
      have : (⟨q, hqQ⟩ : ↥Q) ∈ E.subgroupOf Q := by
        rw [h]
        exact hqmem
      exact this
    have hcard := Subgroup.card_lt_of_lt hlt
    have hEcard : Nat.card (E.subgroupOf Q) = p ^ 2 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEQ).toEquiv).trans hEc
    rw [hEcard] at hcard
    exact absurd hle (not_le.mpr hcard)
  have hDp : IsPGroup p (C ⊓ Q : Subgroup R) := hR.to_subgroup _
  obtain ⟨B₀, hB₀e, hB₀c⟩ := CFSG.GroupTheory.SteinbergBK.odd_noncyclic_pgroup_rank_two
    (hp.out.odd_of_ne_two hp2) hDp hDnc
  have : CFSG.IsElementaryAbelian p B₀ := hB₀e
  set U : Subgroup R := B₀.map (C ⊓ Q).subtype with hU
  have hUD : U ≤ C ⊓ Q := Subgroup.map_subtype_le B₀
  have hUe : CFSG.IsElementaryAbelian p U := CFSG.IsElementaryAbelian.map_subtype
  have hUc : Nat.card U = p ^ 2 := by
    rw [hU, Subgroup.card_map_of_injective (C ⊓ Q).subtype_injective, hB₀c]
  have hUV : U ≤ centralizer (V : Set R) := hUD.trans inf_le_left
  have hVU : CFSG.IsElementaryAbelian p ↥(V ⊔ U) :=
    CFSG.IsElementaryAbelian.sup_of_le_centralizer hUV
  have hcomm : ∀ (W : Subgroup R) [CFSG.IsElementaryAbelian p W], ∀ a ∈ W, ∀ b ∈ W,
      a * b = b * a := by
    intro W _ a ha b hb
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : W) ⟨b, hb⟩)
  refine ⟨U, hUD.trans inf_le_right, hUe, hUc, fun u huU hu1 => ?_⟩
  by_cases h3 : p ^ 3 ≤ Nat.card ↥(V ⊔ U)
  · refine ⟨V ⊔ U, fun w hw => ?_, hVU, h3⟩
    rw [mem_centralizer_singleton_iff]
    exact hcomm (V ⊔ U) w hw u (mem_sup_right huU)
  ·
    have hpg : IsPGroup p ↥(V ⊔ U) := CFSG.IsElementaryAbelian.isPGroup p _
    obtain ⟨k, hk⟩ := hpg.exists_card_eq
    have hk3 : k < 3 := by
      rw [hk] at h3
      exact (Nat.pow_lt_pow_iff_right hp.out.one_lt).mp (not_le.mp h3)
    have hVsup : V = V ⊔ U := by
      refine Subgroup.eq_of_le_of_card_ge le_sup_left ?_
      rw [hk, hVc]
      exact Nat.pow_le_pow_right hp.out.pos (by omega)
    have huV : u ∈ V := by
      rw [hVsup]
      exact mem_sup_right huU
    refine ⟨(A ⊓ C) ⊔ V, fun w hw => ?_, hWe, hW3⟩
    rw [mem_centralizer_singleton_iff]
    exact hcomm ((A ⊓ C) ⊔ V) w hw u (hVW huV)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L618Om
