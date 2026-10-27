module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08HBasic
public import Certificates.Certificate26883
public import Certificates.Certificate26884

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.M22Std.HS08Check

theorem outInvProp : OutInvProp :=
  of_decide_eq_true Certificates.certificate26883

theorem genInvProp : GenInvProp :=
  of_decide_eq_true Certificates.certificate26884

end CFSG.EvenSporadicStandard.M22Std.HS08Check

namespace CFSG.EvenSporadicStandard.M22Std.HS08H

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.OutCheck
  CFSG.EvenSporadicStandard.M22Std.E32Check CFSG.EvenSporadicStandard.M22Std.HS08Check
  CFSG.Blueprint.NativeSporadic


@[expose] noncomputable def s0Sylow : Sylow 2 (MulAut (Carrier .M22)) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  isPGroup_s0.toSylow index_s0_odd

theorem outer_involution_jSub (w : MulAut (Carrier .M22)) (hw : w * w = 1)
    (hwi : w ∉ innerImage (Carrier .M22) ⊤) : ∃ a : MulAut (Carrier .M22), a * w * a⁻¹ ∈ jSub := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : IsPGroup 2 (Subgroup.zpowers w) := by
    have hord : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hw])
    rcases (Nat.dvd_prime Nat.prime_two).1 hord with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; norm_num)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; norm_num)
  obtain ⟨Q, hQle⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (MulAut (Carrier .M22)) Q s0Sylow
  have hwQ : w ∈ (Q : Subgroup (MulAut (Carrier .M22))) := hQle (Subgroup.mem_zpowers w)
  have hv : g * w * g⁻¹ ∈ s0 := by
    have hmem : g * w * g⁻¹ ∈ ((g • Q : Sylow 2 (MulAut (Carrier .M22))) :
        Subgroup (MulAut (Carrier .M22))) := by
      rw [Sylow.coe_subgroup_smul]
      exact Set.mem_smul_set.mpr ⟨w, hwQ, rfl⟩
    rw [hg] at hmem
    exact hmem
  have hv2 : (g * w * g⁻¹) * (g * w * g⁻¹) = 1 := by
    calc (g * w * g⁻¹) * (g * w * g⁻¹) = g * (w * w) * g⁻¹ := by group
      _ = 1 := by rw [hw]; group
  have hvi : g * w * g⁻¹ ∉ innerImage (Carrier .M22) ⊤ := fun h =>
    hwi ((conj_mem_innerImage_iff g w).1 h)
  have hvo : autTab (g * w * g⁻¹) ∈ s0Outer := (outer_iff_of_mem_s0 hv).1 hvi
  have hvt : tmul (autTab (g * w * g⁻¹)) (autTab (g * w * g⁻¹)) = idTab := by
    rw [← autTab_mul, hv2, autTab_one]
  obtain ⟨w', -, j, hj, hcj⟩ := outInvProp (autTab (g * w * g⁻¹)) hvo hvt
  obtain ⟨j', hj', rfl⟩ := exists_mem_jSub hj
  refine ⟨wordElt autLetters w' * g, ?_⟩
  have h1 : wordElt autLetters w' * (g * w * g⁻¹) * (wordElt autLetters w')⁻¹ = j' :=
    conj_eq_of_tmul (by rw [autTab_wordElt_letters]; exact hcj)
  have h2 : wordElt autLetters w' * g * w * (wordElt autLetters w' * g)⁻¹ =
      wordElt autLetters w' * (g * w * g⁻¹) * (wordElt autLetters w')⁻¹ := by group
  rw [h2, h1]
  exact hj'

theorem exists_mem_s0_of_mem_s0Invs {t : Tab} (ht : t ∈ s0Invs) :
    ∃ u ∈ s0, u * u = 1 ∧ autTab u = t := by
  obtain ⟨hts, htt⟩ := List.mem_filter.1 ht
  obtain ⟨u, hu, hut⟩ := isTabsOf_s0.exists_mem t hts
  have hut' : autTab u = t := hut
  refine ⟨u, hu, autTab_injective ?_, hut'⟩
  rw [autTab_mul, autTab_one, hut']
  exact of_decide_eq_true htt

theorem gen_involutions_s0 :
    Subgroup.closure {x : MulAut (Carrier .M22) | x ∈ s0 ∧ x * x = 1} = s0 := by
  refine le_antisymm ((Subgroup.closure_le _).2 fun x hx => hx.1) ?_
  set K := Subgroup.closure {x : MulAut (Carrier .M22) | x ∈ s0 ∧ x * x = 1} with hK
  have hword : ∀ w : List Nat, ∃ x ∈ K, autTab x = wordTab s0Invs w := by
    intro w
    induction w with
    | nil => exact ⟨1, K.one_mem, autTab_one⟩
    | cons i w ih =>
      obtain ⟨x, hx, hxt⟩ := ih
      have hu : ∃ u ∈ K, autTab u = s0Invs.getD i idTab := by
        rcases lt_or_ge i s0Invs.length with h | h
        · rw [List.getD_eq_getElem _ _ h]
          obtain ⟨u, hu, hu2, hut⟩ := exists_mem_s0_of_mem_s0Invs (List.getElem_mem h)
          exact ⟨u, Subgroup.subset_closure ⟨hu, hu2⟩, hut⟩
        · rw [List.getD_eq_default _ _ h]
          exact ⟨1, K.one_mem, autTab_one⟩
      obtain ⟨u, hu, hut⟩ := hu
      exact ⟨u * x, K.mul_mem hu hx, by rw [autTab_mul, hut, hxt]; rfl⟩
  refine (Subgroup.closure_le _).2 fun g hg => ?_
  have hgt : autTab g ∈ genInvWords.map (wordTab s0Invs) := by
    rw [genInvProp, ← map_autTab_s0Gens']
    exact List.mem_map_of_mem hg
  obtain ⟨w, -, hw⟩ := List.mem_map.1 hgt
  obtain ⟨x, hx, hxt⟩ := hword w
  have : g = x := autTab_injective (by rw [hxt, hw])
  rw [this]
  exact hx

end CFSG.EvenSporadicStandard.M22Std.HS08H
