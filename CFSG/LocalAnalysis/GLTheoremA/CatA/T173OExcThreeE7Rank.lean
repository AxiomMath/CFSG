module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UpperE7Levi
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerExcOne
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCentralizerTUBasic
public import CFSG.LocalAnalysis.SeitzReduction.EPilotCentralizerHigh
public import CFSG.LieType.Chevalley.ParabolicRootsMono
public import CFSG.LieType.Chevalley.GraphFixedOrbitParametrization

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.SeitzReduction.EPilot CFSG.SeitzReduction.F4Pilot

section Small


variable {F : Type} [Field F] [Finite F]

private theorem torusGroup_E7_eq_bot_of_card_two (hF : Nat.card F = 2) :
    torusGroup .E7 F = ⊥ := by
  refine torusGroup_eq_bot_of_forall_units_eq_one (τ := .E7) (K := F) fun u => ?_
  have hcard : Nat.card Fˣ = 1 := by rw [Nat.card_units, hF]
  haveI : Subsingleton Fˣ := (Nat.card_eq_one_iff_unique.1 hcard).1
  exact Subsingleton.elim u 1

theorem parabolicLevi_eq_subsystemGroup_E7_two (hF : Nat.card F = 2)
    (J : Set (Fin Tag.E7.rank)) :
    parabolicLevi .E7 F J = subsystemGroup .E7 F J := by
  rw [parabolicLevi, torusGroup_E7_eq_bot_of_card_two hF, bot_sup_eq]
  rfl

theorem parabolicLevi_le_rootSpan_perpRoots_E7_two (hF : Nat.card F = 2)
    {J : Set (Fin Tag.E7.rank)} (hJ : J ⊆ perpNodes .E7) :
    parabolicLevi .E7 F J ≤ rootSpan .E7 F (perpRoots .E7) := by
  calc parabolicLevi .E7 F J
      ≤ torusGroup .E7 F ⊔ rootSpan .E7 F (parabolicRoots .E7 J) :=
        parabolicLevi_le_torusGroup_sup J
    _ = rootSpan .E7 F (parabolicRoots .E7 J) := by
        rw [torusGroup_E7_eq_bot_of_card_two hF, bot_sup_eq]
    _ ≤ rootSpan .E7 F (parabolicRoots .E7 (perpNodes .E7)) :=
        rootSpan_mono (parabolicRoots_mono hJ)
    _ = rootSpan .E7 F (perpRoots .E7) := by rw [parabolicRoots_perpNodes]

end Small

section Big


variable {F : Type} [Field F] [Finite F]

private theorem card_le_pow_five_of_le_subsystemGroup_e7a6 (hF : Nat.card F = 2)
    {J : Set (Fin Tag.E7.rank)} (hi : (1 : Fin Tag.E7.rank) ∉ J)
    {E : Subgroup (ModGL .E7 F)} (hE : E ≤ subsystemGroup .E7 F J)
    (hEel : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 5 := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  have hpq : ¬ 3 ∣ Nat.card F - 1 := by rw [hF]; norm_num
  have hJ : J ⊆ CFSG.RankThree.PartOne.KE.e7a6support := by
    intro j hj
    rw [CFSG.RankThree.PartOne.KE.mem_e7a6support]
    fin_cases j
    · exact Or.inl rfl
    · exact absurd hj hi
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  refine (CFSG.LocalAnalysis.GLTheoremA.card_le_pow_three_subsystemGroup_e7a6
    Nat.prime_three (by norm_num) hpq
    (hE.trans (CFSG.StandardType.F4Rest.subsystemGroup_mono hJ)) hEel).trans ?_
  exact Nat.pow_le_pow_right (by norm_num) (by norm_num : 3 ≤ 5)

private theorem card_le_pow_five_of_le_subsystemGroup_e7A1A5 (hF : Nat.card F = 2)
    {J : Set (Fin Tag.E7.rank)} (hi : (2 : Fin Tag.E7.rank) ∉ J)
    {E : Subgroup (ModGL .E7 F)} (hE : E ≤ subsystemGroup .E7 F J)
    (hEel : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 5 := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  have hpq : ¬ 3 ∣ Nat.card F - 1 := by rw [hF]; norm_num
  have hJ : J ⊆ {j : Fin Tag.E7.rank | j.val ≠ 2} := by
    intro j hj hval
    have hji : j = (2 : Fin Tag.E7.rank) := Fin.ext hval
    exact hi (hji ▸ hj)
  refine (CFSG.LocalAnalysis.GLTheoremA.card_le_pow_four_subsystemGroup_e7A1A5
    Nat.prime_three (by norm_num) hpq
    (hE.trans (CFSG.StandardType.F4Rest.subsystemGroup_mono hJ)) hEel).trans ?_
  exact Nat.pow_le_pow_right (by norm_num) (by norm_num : 4 ≤ 5)

private theorem card_le_pow_five_of_le_subsystemGroup_e7A1A2A3 (hF : Nat.card F = 2)
    {J : Set (Fin Tag.E7.rank)} (hi : (3 : Fin Tag.E7.rank) ∉ J)
    {E : Subgroup (ModGL .E7 F)} (hE : E ≤ subsystemGroup .E7 F J)
    (hEel : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 5 := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  have hpq : ¬ 3 ∣ Nat.card F - 1 := by rw [hF]; norm_num
  have hJ : J ⊆ {j : Fin Tag.E7.rank | j.val ≠ 3} := by
    intro j hj hval
    have hji : j = (3 : Fin Tag.E7.rank) := Fin.ext hval
    exact hi (hji ▸ hj)
  exact CFSG.LocalAnalysis.GLTheoremA.card_le_pow_five_subsystemGroup_e7A1A2A3
    Nat.prime_three (by norm_num) hpq
    (hE.trans (CFSG.StandardType.F4Rest.subsystemGroup_mono hJ)) hEel

private theorem card_le_pow_five_of_le_subsystemGroup_e7A2A4 (hF : Nat.card F = 2)
    {J : Set (Fin Tag.E7.rank)} (hi : (4 : Fin Tag.E7.rank) ∉ J)
    {E : Subgroup (ModGL .E7 F)} (hE : E ≤ subsystemGroup .E7 F J)
    (hEel : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 5 := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  have hpq : ¬ 3 ∣ Nat.card F - 1 := by rw [hF]; norm_num
  have hKn : Nat.card F = 2 ^ 1 := by rw [hF]; norm_num
  have hd : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have hJ : J ⊆ {j : Fin Tag.E7.rank | j.val ≠ 4} := by
    intro j hj hval
    have hji : j = (4 : Fin Tag.E7.rank) := Fin.ext hval
    exact hi (hji ▸ hj)
  exact CFSG.LocalAnalysis.GLTheoremA.card_le_pow_five_subsystemGroup_e7A2A4
    hKn Nat.prime_three (by norm_num) hd hpq
    (hE.trans (CFSG.StandardType.F4Rest.subsystemGroup_mono hJ)) hEel

private theorem card_le_pow_five_of_le_subsystemGroup_e7A1D5 (hF : Nat.card F = 2)
    {J : Set (Fin Tag.E7.rank)} (hi : (5 : Fin Tag.E7.rank) ∉ J)
    {E : Subgroup (ModGL .E7 F)} (hE : E ≤ subsystemGroup .E7 F J)
    (hEel : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 5 := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  have hpq : ¬ 3 ∣ Nat.card F - 1 := by rw [hF]; norm_num
  have hKn : Nat.card F = 2 ^ 1 := by rw [hF]; norm_num
  have hd : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have hJ : J ⊆ {j : Fin Tag.E7.rank | j.val ≠ 5} := by
    intro j hj hval
    have hji : j = (5 : Fin Tag.E7.rank) := Fin.ext hval
    exact hi (hji ▸ hj)
  exact CFSG.LocalAnalysis.GLTheoremA.card_le_pow_five_subsystemGroup_e7A1D5
    hKn Nat.prime_three (by norm_num) hd hpq
    (hE.trans (CFSG.StandardType.F4Rest.subsystemGroup_mono hJ)) hEel

private theorem card_le_pow_five_of_le_subsystemGroup_e7E6 (hF : Nat.card F = 2)
    {J : Set (Fin Tag.E7.rank)} (hi : (6 : Fin Tag.E7.rank) ∉ J)
    {E : Subgroup (ModGL .E7 F)} (hE : E ≤ subsystemGroup .E7 F J)
    (hEel : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 5 := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  have hKn : Nat.card F = 2 ^ 1 := by rw [hF]; norm_num
  have hd : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have hJ : J ⊆ {j : Fin Tag.E7.rank | j ≠ (6 : Fin 7)} := by
    intro j hj hval
    have hji : j = (6 : Fin Tag.E7.rank) := by rw [hval]; rfl
    exact hi (hji ▸ hj)
  refine (CFSG.LocalAnalysis.GLTheoremA.card_le_pow_four_subsystemGroup_e7E6
    hKn Nat.prime_three (by norm_num) hd
    (hE.trans (CFSG.StandardType.F4Rest.subsystemGroup_mono hJ)) hEel).trans ?_
  exact Nat.pow_le_pow_right (by norm_num) (by norm_num : 4 ≤ 5)

private theorem card_le_pow_five_of_notMem {J : Set (Fin Tag.E7.rank)}
    (hF : Nat.card F = 2) {i : Fin Tag.E7.rank} (hi0 : i ≠ 0) (hi : i ∉ J)
    {E : Subgroup (ModGL .E7 F)} (hE : E ≤ subsystemGroup .E7 F J)
    (hEel : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 5 := by
  have hi_cases : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by
    fin_cases i
    · exact absurd rfl hi0
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  rcases hi_cases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact card_le_pow_five_of_le_subsystemGroup_e7a6 hF hi hE hEel
  · exact card_le_pow_five_of_le_subsystemGroup_e7A1A5 hF hi hE hEel
  · exact card_le_pow_five_of_le_subsystemGroup_e7A1A2A3 hF hi hE hEel
  · exact card_le_pow_five_of_le_subsystemGroup_e7A2A4 hF hi hE hEel
  · exact card_le_pow_five_of_le_subsystemGroup_e7A1D5 hF hi hE hEel
  · exact card_le_pow_five_of_le_subsystemGroup_e7E6 hF hi hE hEel

theorem subset_perpNodes_of_three_pow_six_le (hF : Nat.card F = 2)
    {J : Set (Fin Tag.E7.rank)} (hJ : J ≠ Set.univ)
    {E : Subgroup (ModGL .E7 F)} (hE : E ≤ parabolicLevi .E7 F J)
    (hEel : IsElemAbelian 3 E) (h6 : 3 ^ 6 ≤ Nat.card E) : J ⊆ perpNodes .E7 := by
  by_contra hsub
  obtain ⟨j, hj, hjperp⟩ := Set.not_subset.1 hsub
  have hhigh : CFSG.SeitzReduction.highNode .E7 = (0 : Fin Tag.E7.rank) := rfl
  have hjhigh : j = CFSG.SeitzReduction.highNode .E7 := by simpa [perpNodes] using hjperp
  have h0 : (0 : Fin Tag.E7.rank) ∈ J := by rw [← hhigh, ← hjhigh]; exact hj
  obtain ⟨i, hi⟩ := (Set.ne_univ_iff_exists_notMem J).1 hJ
  have hi0 : i ≠ 0 := fun h => hi (h ▸ h0)
  have hEsub : E ≤ subsystemGroup .E7 F J :=
    hE.trans (le_of_eq (parabolicLevi_eq_subsystemGroup_E7_two hF J))
  have hle : 3 ^ 6 ≤ 3 ^ 5 := h6.trans (card_le_pow_five_of_notMem hF hi0 hi hEsub hEel)
  exact absurd hle (by norm_num)

theorem parabolicLevi_le_rootSpan_perpRoots_of_card (hF : Nat.card F = 2)
    {J : Set (Fin Tag.E7.rank)} (hJ : J ≠ Set.univ) {E : Subgroup (ModGL .E7 F)}
    (hE : E ≤ parabolicLevi .E7 F J) (hEel : IsElemAbelian 3 E) (h6 : 3 ^ 6 ≤ Nat.card E) :
    parabolicLevi .E7 F J ≤ rootSpan .E7 F (perpRoots .E7) :=
  parabolicLevi_le_rootSpan_perpRoots_E7_two hF
    (subset_perpNodes_of_three_pow_six_le hF hJ hE hEel h6)

theorem six_le_glaTwoLocalRank_E7_two [Finite ↥(adjointGroup .E7 F)] (hF : Nat.card F = 2) :
    6 ≤ GLATwoLocalRank 3 ↥(adjointGroup .E7 F) :=
  six_le_twoLocalPrimeRank_adjointGroup_E7 F hF

end Big

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
