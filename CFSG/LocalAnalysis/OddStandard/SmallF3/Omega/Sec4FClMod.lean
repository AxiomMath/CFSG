module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FClWt

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem sec4FCl_model (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 7)
    (hσ : quadSign Q = 1) {t : OGroup Q} (htt : t * t = 1) (ht6 : invType t = (6, 1)) :
    ∃ w : OGroup Q, IsComponentIn (sec4FClXt hQ htt) (Sec4FDDt hQ t) ∧
      oddCore ↥(sec4FClXt hQ htt) = ⊥ ∧ LieModel ↥(sec4FClXt hQ htt) .PSL 4 3 1 ∧
      w ∈ Sec4FDDt hQ t ∧ w * w = 1 ∧ invType w = (4, 1) ∧
      Sec4FDDt hQ t ≤ sec4FClXt hQ htt ⊔ Subgroup.zpowers w := by
  obtain ⟨w, hwD, hw2, hwt, hwX⟩ := sec4FCl_exists_wt hQ hdim hσ htt ht6
  refine ⟨w, sec4FClXt_isComponentIn hQ htt ht6, sec4FClXt_oddCore hQ htt ht6,
    sec4FClXt_lieModel hQ htt ht6, hwD, hw2, hwt, ?_⟩
  haveI : Finite (OGroup Q) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  set D : Subgroup (OGroup Q) := Sec4FDDt hQ t with hD
  haveI : Finite D := inferInstance
  have hXD : sec4FClXt hQ htt ≤ D := by rw [hD]; exact sec4FClXt_le_dt hQ htt ht6
  set N : Subgroup D := (sec4FClXt hQ htt).subgroupOf D with hN
  set w' : D := ⟨w, hwD⟩ with hw'
  have hw'N : w' ∉ N := by
    rw [hw', hN]
    intro h
    exact hwX (by simpa using (Subgroup.mem_subgroupOf.mp h))
  have hcardN : Nat.card N = 6065280 := by
    have h1 : Nat.card N = Nat.card (sec4FClXt hQ htt) := by
      rw [hN]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXD).toEquiv
    rw [h1, natCard_sec4FClXt hQ htt ht6]
  have hcardD : Nat.card D ≤ 12130560 := by
    rw [hD]; exact sec4FClDt_card_le hQ hdim hσ htt ht6
  have hmul : Nat.card N * N.index ≤ Nat.card N * 2 := by
    rw [Subgroup.card_mul_index]
    calc Nat.card D ≤ 12130560 := hcardD
      _ = Nat.card N * 2 := by norm_num [hcardN]
  have hposN : 0 < Nat.card N := by norm_num [hcardN]
  have hNidx_le : N.index ≤ 2 := Nat.le_of_mul_le_mul_left hmul hposN
  have hNne : N ≠ ⊤ := by
    intro h
    exact hw'N (h.symm ▸ Subgroup.mem_top w')
  have hNidx : N.index = 2 := by
    have hlt := Subgroup.one_lt_index_of_ne_top hNne
    omega
  set P : Subgroup D := N ⊔ Subgroup.zpowers w' with hP
  have hNleP : N ≤ P := by rw [hP]; exact le_sup_left
  have hNneP : N ≠ P := by
    intro h
    refine hw'N ?_
    rw [h, hP]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers w')
  have hNltP : N < P := lt_of_le_of_ne hNleP hNneP
  have hPidx_dvd : P.index ∣ N.index := Subgroup.index_dvd_of_le hNleP
  have hPidx : P.index = 1 := by
    have hdvd : P.index ∣ 2 := by simpa [hNidx] using hPidx_dvd
    have hlt : P.index < 2 := by
      have := Subgroup.index_strictAnti hNltP
      simpa [hNidx] using this
    have hpos : P.index ≠ 0 := by
      intro h0
      rw [h0] at hdvd
      norm_num at hdvd
    have hle : P.index ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hPtop : P = ⊤ := Subgroup.index_eq_one.mp hPidx
  have hmapN : N.map D.subtype = sec4FClXt hQ htt := by
    rw [hN]
    exact Subgroup.map_subgroupOf_eq_of_le hXD
  have hmapw : (Subgroup.zpowers w').map D.subtype = Subgroup.zpowers w := by
    rw [MonoidHom.map_zpowers, hw']
    rfl
  have hmap : P.map D.subtype = sec4FClXt hQ htt ⊔ Subgroup.zpowers w := by
    rw [hP, Subgroup.map_sup, hmapN, hmapw]
  have hDeq : D = sec4FClXt hQ htt ⊔ Subgroup.zpowers w := by
    rw [← hmap, hPtop, Subgroup.map_top, Subgroup.range_subtype]
  exact le_of_eq hDeq

end CFSG.OddStandard.SmallF3.Omega
