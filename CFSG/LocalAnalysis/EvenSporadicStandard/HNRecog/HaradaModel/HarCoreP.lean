module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.SylowSpec2
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.SylowSpec

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel

open Subgroup CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.SmallOddCore
open scoped commutatorElement

section Cert


theorem sylowP_card : Nat.card ↥(wordSubgroupP sWords) = 2 ^ 11 := by
  rw [card_wordSubgroupP sWords, sylow_card]

theorem sylowP_isPGroup : IsPGroup 2 ↥(wordSubgroupP sWords) :=
  IsPGroup.of_card (n := 11) sylowP_card

private theorem closure_subgroupOf_eq {X : Set (Equiv.Perm (Fin 1408))} (hX : X ⊆ P1408) :
    (Subgroup.closure X).subgroupOf P1408 = Subgroup.closure (P1408.subtype ⁻¹' X) := by
  apply Subgroup.map_injective (f := P1408.subtype) P1408.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le ((Subgroup.closure_le P1408).2 hX), MonoidHom.map_closure,
    Set.image_preimage_eq_of_subset (fun x hx => ⟨⟨x, hX hx⟩, rfl⟩)]

theorem harCoreP (hB1 : TwoHSFacts ↥P1408 pA pZ pB pZ₁) {Ep : Subgroup ↥P1408}
    (hEp : ∀ x : ↥P1408, x ∈ Ep ↔ (x : Equiv.Perm (Fin 1408)) ∈ blocks1408) (hEn : Ep.Normal) :
    HarCoreData pA pZ (wordSubgroupP sWords) Ep (wordSubgroupP sWords ⊓ Ep)
      (wordSubgroupP tpWords) (wordSubgroupP (tpWords ++ w0Extra)) := by
  have hP : Nat.card ↥P1408 = 177408000 := by
    have := hB1.card_eq
    norm_num at this
    exact this
  have hbasic := twoHSBasic_spec
  have hcommA : ∀ g ∈ P1408, elemA * g = g * elemA := hbasic.2.2.2.2.1
  have hAblocks : elemA ∈ blocks1408 := hbasic.2.2.2.2.2.1
  have hZblocks : elemZ ∈ blocks1408 := hbasic.2.2.2.2.2.2.1
  refine
    { t_sq := ?_, t_ne_one := ?_, z1_ne_one := ?_, z1_ne_t := ?_, t_mem := ?_, z1_mem := ?_,
      S_comm_t := ?_, T0_eq := rfl, Eg_norm := ?_, z1_comm := ?_, cent_le := ?_, centre := ?_,
      derived := ?_, W0_eq := ?_, card_T0_t := ?_, card_T0_z2 := ?_, card_T0'_t := ?_,
      card_T0'_z1 := ?_, card_T0'_z2 := ?_, card_W0_t := ?_, card_W0_z2 := ?_ }
  · rw [← hB1.orderOf_a]
    exact pow_orderOf_eq_one pA
  · intro h
    have h1 : orderOf pA = 1 := by rw [h, orderOf_one]
    have h2 := hB1.orderOf_a
    omega
  · intro h
    have h1 : orderOf pZ = 1 := by rw [h, orderOf_one]
    have h2 := hB1.orderOf_z
    omega
  · have hna := hB1.not_isConj 0 1 (by decide)
    change ¬ IsConj pA pZ at hna
    intro h
    exact hna (h.symm ▸ IsConj.refl pA)
  · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [mem_wordSubgroupP, coe_pA]
      exact elemA_mem_sylow
    · exact (hEp pA).2 (by rw [coe_pA]; exact hAblocks)
  · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [mem_wordSubgroupP, coe_pZ]
      exact elemZ_mem_sylow
    · exact (hEp pZ).2 (by rw [coe_pZ]; exact hZblocks)
  · intro s hs
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_pA]
    exact (hcommA (s : Equiv.Perm (Fin 1408))
      (wordSubgroup_le sWords (mem_wordSubgroupP.mp hs))).symm
  · intro s hs e he
    exact hEn.conj_mem e he s
  · intro y hy
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_pZ]
    exact elemZ_comm_T (mem_wordSubgroupP.mp hy.1) ((hEp y).1 hy.2)
  · intro x _ hcomm
    refine (hEp x).2 (centralizer_T_le hP x.2 ?_)
    · intro y hyS hyE
      have hyP : y ∈ P1408 := wordSubgroup_le sWords hyS
      have h := hcomm ⟨y, hyP⟩
        (Subgroup.mem_inf.mpr ⟨mem_wordSubgroupP.mpr hyS, (hEp ⟨y, hyP⟩).2 hyE⟩)
      have := congrArg Subtype.val h
      simpa [Subgroup.coe_mul] using this
  · intro x hx hc
    have hxS : (x : Equiv.Perm (Fin 1408)) ∈ wordSubgroup sWords := mem_wordSubgroupP.mp hx.1
    have hxE : (x : Equiv.Perm (Fin 1408)) ∈ blocks1408 := (hEp x).1 hx.2
    have hc' : ∀ y ∈ wordSubgroup sWords, y ∈ blocks1408 →
        (x : Equiv.Perm (Fin 1408)) * y = y * (x : Equiv.Perm (Fin 1408)) := by
      intro y hyS hyE
      have hyP : y ∈ P1408 := wordSubgroup_le sWords hyS
      have h := hc ⟨y, hyP⟩
        (Subgroup.mem_inf.mpr ⟨mem_wordSubgroupP.mpr hyS, (hEp ⟨y, hyP⟩).2 hyE⟩)
      have := congrArg Subtype.val h
      simpa [Subgroup.coe_mul] using this
    rcases centre_T hxS hxE hc' with h | h | h | h
    · left; apply Subtype.ext; simpa using h
    · right; left; apply Subtype.ext; rw [coe_pA]; exact h
    · right; right; left; apply Subtype.ext; rw [coe_pZ]; exact h
    · right; right; right; apply Subtype.ext
      rw [Subgroup.coe_mul, coe_pA, coe_pZ]; exact h
  · change ⁅(wordSubgroup sWords).subgroupOf P1408, (wordSubgroup sWords).subgroupOf P1408⁆ =
      (wordSubgroup tpWords).subgroupOf P1408
    rw [commutator_subgroupOf_P (wordSubgroup_le sWords), derived_eq]
  · have hpow : ∀ y : ↥P1408,
        (y ^ 2 = 1) ↔ ((P1408.subtype y : Equiv.Perm (Fin 1408)) ^ 2 = 1) := by
      intro y
      constructor
      · intro h
        rw [← map_pow, h, map_one]
      · intro h
        apply P1408.subtype_injective
        rw [map_pow, map_one]
        exact h
    have hY : P1408.subtype ⁻¹'
        ((wordSubgroup tpWords : Set (Equiv.Perm (Fin 1408))) ∪
          {y : Equiv.Perm (Fin 1408) |
            y ∈ wordSubgroup sWords ⊓ blocks1408 ∧ y ^ 2 = 1}) =
        ((wordSubgroupP tpWords : Set ↥P1408) ∪
          {y | y ∈ wordSubgroupP sWords ⊓ Ep ∧ y ^ 2 = 1}) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_union, Set.mem_setOf_eq, Subgroup.mem_inf,
        mem_wordSubgroupP, hEp y]
      constructor
      · intro h
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨⟨h.1.1, h.1.2⟩, (hpow y).mpr h.2⟩
      · intro h
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨⟨h.1.1, h.1.2⟩, (hpow y).mp h.2⟩
    calc wordSubgroupP (tpWords ++ w0Extra)
        = (wordSubgroup (tpWords ++ w0Extra)).subgroupOf P1408 := rfl
      _ = (Subgroup.closure ((wordSubgroup tpWords : Set (Equiv.Perm (Fin 1408))) ∪
            {y : Equiv.Perm (Fin 1408) |
              y ∈ wordSubgroup sWords ⊓ blocks1408 ∧ y ^ 2 = 1})).subgroupOf P1408 := by
            rw [w0_eq]
      _ = Subgroup.closure (P1408.subtype ⁻¹'
            ((wordSubgroup tpWords : Set (Equiv.Perm (Fin 1408))) ∪
              {y : Equiv.Perm (Fin 1408) |
                y ∈ wordSubgroup sWords ⊓ blocks1408 ∧ y ^ 2 = 1})) :=
            closure_subgroupOf_eq (by
              intro y hy
              rcases hy with hy | ⟨hy, -⟩
              · exact wordSubgroup_le tpWords hy
              · exact wordSubgroup_le sWords hy.1)
      _ = Subgroup.closure ((wordSubgroupP tpWords : Set ↥P1408) ∪
            {y | y ∈ wordSubgroupP sWords ⊓ Ep ∧ y ^ 2 = 1}) := by rw [hY]
  · rw [wordSubgroupP_inf_eq hEp sWords,
      harSqCard_subgroupOf_P (inf_le_of_left_le (wordSubgroup_le sWords)) pA, coe_pA]
    exact card_T_a
  · rw [wordSubgroupP_inf_eq hEp sWords,
      harSqCard_subgroupOf_P (inf_le_of_left_le (wordSubgroup_le sWords)) (pA * pZ),
      Subgroup.coe_mul, coe_pA, coe_pZ]
    exact card_T_az
  · change harSqCard ((wordSubgroup tpWords).subgroupOf P1408) pA = 16
    rw [harSqCard_subgroupOf_P (wordSubgroup_le tpWords) pA, coe_pA]
    exact card_T'_a
  · change harSqCard ((wordSubgroup tpWords).subgroupOf P1408) pZ = 32
    rw [harSqCard_subgroupOf_P (wordSubgroup_le tpWords) pZ, coe_pZ]
    exact card_T'_z
  · change harSqCard ((wordSubgroup tpWords).subgroupOf P1408) (pA * pZ) = 16
    rw [harSqCard_subgroupOf_P (wordSubgroup_le tpWords) (pA * pZ),
      Subgroup.coe_mul, coe_pA, coe_pZ]
    exact card_T'_az
  · change harSqCard ((wordSubgroup (tpWords ++ w0Extra)).subgroupOf P1408) pA = 48
    rw [harSqCard_subgroupOf_P (wordSubgroup_le (tpWords ++ w0Extra)) pA, coe_pA]
    exact card_W0_a
  · change harSqCard ((wordSubgroup (tpWords ++ w0Extra)).subgroupOf P1408) (pA * pZ) = 16
    rw [harSqCard_subgroupOf_P (wordSubgroup_le (tpWords ++ w0Extra)) (pA * pZ),
      Subgroup.coe_mul, coe_pA, coe_pZ]
    exact card_W0_az

end Cert

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel
