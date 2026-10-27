module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBElem
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBLevel1

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF

open CFSG.AGLEmbedding.Norton.MON5_7 CFSG.Monster.Generated CFSG.Monster.B.Pinned

section Orders


theorem finite_Gmat : Finite Gmat :=
  Nat.finite_of_card_ne_zero (by
    rw [CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder]; norm_num [CFSG.Open.monsterOrder])

theorem factorization_tbL (h : SylFact) : (Nat.card tbL).factorization 3 = 20 := by
  have : Finite Gmat := finite_Gmat
  have hpos : Nat.card tbL ≠ 0 := Nat.card_pos.ne'
  have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hpos).1
    (three_pow_twenty_dvd h)
  have hlt : ¬ 21 ≤ (Nat.card tbL).factorization 3 := fun h21 =>
    not_three_pow_21_dvd
      (((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hpos).2 h21).trans card_tbL_dvd)
  omega

theorem factorization_ker (h : SylFact) :
    (Nat.card rhoL.ker).factorization 3 = 13 := by
  have : Finite Gmat := finite_Gmat
  have h1 := factorization_tbL h
  have h2 := factorization_range h
  rw [card_tbL_eq, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
    Finsupp.add_apply] at h1
  omega

theorem normal_QQ : (QQ.subgroupOf tbL).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have := tbL_conj (g⁻¹ : tbL) (g⁻¹ : tbL).2 n hn
  simpa using this

theorem le_QQ_of_le_ker (h : SylFact) {P : Subgroup tbL} (hP : IsPGroup 3 P)
    (hPK : P ≤ rhoL.ker) : P ≤ QQ.subgroupOf tbL := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite Gmat := finite_Gmat
  have hQK : QQ.subgroupOf tbL ≤ rhoL.ker := QQ_le_ker
  let S : Sylow 3 rhoL.ker := Sylow.ofCard ((QQ.subgroupOf tbL).subgroupOf rhoL.ker) (by
    rw [factorization_ker h, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQK).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe QQ_le_tbL).toEquiv, card_QQ])
  have hSn : (S : Subgroup rhoL.ker).Normal := normal_QQ.subgroupOf rhoL.ker
  have hPK' : IsPGroup 3 (P.subgroupOf rhoL.ker) :=
    hP.comap_of_injective rhoL.ker.subtype Subtype.val_injective
  obtain ⟨S', hS'⟩ := hPK'.exists_le_sylow
  have hSS : S = S' := by
    have := Sylow.unique_of_normal S hSn
    exact Subsingleton.elim S S'
  intro x hx
  have hxS : (⟨x, hPK hx⟩ : rhoL.ker) ∈ (S : Subgroup rhoL.ker) := by
    rw [hSS]; exact hS' (Subgroup.mem_subgroupOf.2 hx)
  exact Subgroup.mem_subgroupOf.1 hxS

theorem le_zpowers_of_le_CQ (h : SylFact) :
    ∀ P : Subgroup Gmat, P ≤ CQ → IsPGroup 3 P → P ≤ Subgroup.zpowers tbw := by
  intro P hPC hP x hx
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite Gmat := finite_Gmat
  have hxC := hPC hx
  have hPL : IsPGroup 3 (P.subgroupOf tbL) :=
    hP.comap_of_injective tbL.subtype Subtype.val_injective
  have hPK : P.subgroupOf tbL ≤ rhoL.ker := by
    intro y hy
    rw [MonoidHom.mem_ker]
    apply Units.ext
    rw [coe_rhoL, Units.val_one]
    exact actMat_eq_one_of_mem_centralizer (hPC (Subgroup.mem_subgroupOf.1 hy)).1
  have hxQ : x ∈ QQ := Subgroup.mem_subgroupOf.1
    (le_QQ_of_le_ker h hPL hPK (show (⟨x, hxC.2⟩ : tbL) ∈ P.subgroupOf tbL from hx))
  have hcen : (⟨x, hxQ⟩ : QQ) ∈ Subgroup.center QQ := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxC.1 g g.2)
  rw [tbCommData.center_eq] at hcen
  exact Subgroup.mem_subgroupOf.1 hcen

end Orders

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF
