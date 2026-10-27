module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UpperE8Levi
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerExcOne
public import CFSG.LieType.Chevalley.ParabolicRootsMono

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.SeitzReduction.EPilot CFSG.SeitzReduction.F4Pilot
open CFSG.StandardType.F4Rest

section Small


variable {F : Type} [Field F] [Finite F]

private theorem torusGroup_E8_eq_bot_of_card_two (hF : Nat.card F = 2) :
    torusGroup .E8 F = ⊥ := by
  refine torusGroup_eq_bot_of_forall_units_eq_one (τ := .E8) (K := F) fun u => ?_
  have hcard : Nat.card Fˣ = 1 := by rw [Nat.card_units, hF]
  haveI : Subsingleton Fˣ := (Nat.card_eq_one_iff_unique.1 hcard).1
  exact Subsingleton.elim u 1

theorem parabolicLevi_eq_subsystemGroup_E8_two (hF : Nat.card F = 2)
    (J : Set (Fin Tag.E8.rank)) :
    parabolicLevi .E8 F J = subsystemGroup .E8 F J := by
  rw [parabolicLevi, torusGroup_E8_eq_bot_of_card_two hF, bot_sup_eq]
  rfl

theorem parabolicLevi_le_rootSpan_perpRoots_E8_two (hF : Nat.card F = 2)
    {J : Set (Fin Tag.E8.rank)} (h7 : (7 : Fin Tag.E8.rank) ∉ J) :
    parabolicLevi .E8 F J ≤ rootSpan .E8 F (perpRoots .E8) := by
  have hJ : J ⊆ perpNodes .E8 := by
    intro j hj hjperp
    have hjhigh : j = CFSG.SeitzReduction.highNode .E8 := by
      simpa [perpNodes] using hjperp
    have h7' : CFSG.SeitzReduction.highNode .E8 ∉ J := h7
    exact h7' (hjhigh ▸ hj)
  calc parabolicLevi .E8 F J
      ≤ torusGroup .E8 F ⊔ rootSpan .E8 F (parabolicRoots .E8 J) :=
        parabolicLevi_le_torusGroup_sup J
    _ = rootSpan .E8 F (parabolicRoots .E8 J) := by
        rw [torusGroup_E8_eq_bot_of_card_two hF, bot_sup_eq]
    _ ≤ rootSpan .E8 F (parabolicRoots .E8 (perpNodes .E8)) :=
        rootSpan_mono (parabolicRoots_mono hJ)
    _ = rootSpan .E8 F (perpRoots .E8) := by rw [parabolicRoots_perpNodes]

end Small

section Big


private theorem card_le_pow_six_subsystemGroup_e8delete2 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ Nat.card K + 1)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K {j : Fin Tag.E8.rank | j ≠ 2})
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 6 := by
  have hpq : ¬ p ∣ Nat.card K - 1 :=
    CFSG.RankThree.PartOne.S15K.not_dvd_sub_one_of_dvd_add_one Nat.card_pos
      (by have := hp.two_le; omega) hd
  have hsub : ({j : Fin Tag.E8.rank | j ≠ 2} : Set _) ⊆
      ({0} : Set (Fin Tag.E8.rank)) ∪ Set.range e8A6Node := by
    intro j hj
    fin_cases j <;> first | exact absurd rfl hj | decide
  have hE' : E ≤ subsystemGroup Tag.E8 K (({0} : Set (Fin Tag.E8.rank)) ∪ Set.range e8A6Node) :=
    hE.trans (subsystemGroup_mono hsub)
  rw [subsystemGroup_union] at hE'
  have hcomm := commute_subsystemGroup_of_cartan_zero (K := K)
    (A := ({0} : Set (Fin Tag.E8.rank))) (B := Set.range e8A6Node) (by
      intro a ha b hb
      have ha0 : a = 0 := by simpa using ha
      subst ha0
      have hb' : b = 1 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 := by
        have h1 := (mem_range_e8A6Node b).1 hb
        fin_cases b <;> first | exact absurd rfl h1.1 | exact absurd rfl h1.2 | decide
      rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hboundA : ∀ F : Subgroup (subsystemGroup Tag.E8 K ({0} : Set (Fin Tag.E8.rank))),
      IsElemAbelian p F → Nat.card F ≤ p ^ 1 :=
    bound_subgroup_of_ambient (fun F hF hFel =>
      card_le_pow_one_subsystemGroup_e8node hp hp2 hpq 0 hF hFel)
  have hboundB : ∀ F : Subgroup (subsystemGroup Tag.E8 K (Set.range e8A6Node)),
      IsElemAbelian p F → Nat.card F ≤ p ^ 3 :=
    bound_subgroup_of_ambient (fun F hF hFel =>
      card_le_pow_three_subsystemGroup_e8A6 hp hp2 hpq hF hFel)
  have h := card_le_pow_add_of_le_sup_of_not_dvd_inf (p := p) hp hcomm
    (not_dvd_card_inf_subsystemGroup_e8 hp hpq hcomm) hboundA hboundB hE' hEel
  exact h.trans (Nat.pow_le_pow_right hp.pos (by norm_num))

private theorem card_le_pow_six_subsystemGroup_e8delete3 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ Nat.card K + 1)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K {j : Fin Tag.E8.rank | j ≠ 3})
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 6 := by
  have hpq : ¬ p ∣ Nat.card K - 1 :=
    CFSG.RankThree.PartOne.S15K.not_dvd_sub_one_of_dvd_add_one Nat.card_pos
      (by have := hp.two_le; omega) hd
  have hsub : ({j : Fin Tag.E8.rank | j ≠ 3} : Set _) ⊆
      ({1} : Set (Fin Tag.E8.rank)) ∪ (({0, 2} : Set (Fin Tag.E8.rank)) ∪ Set.range e8A4Node) := by
    intro j hj
    fin_cases j <;> first | exact absurd rfl hj | decide
  have hE' : E ≤ subsystemGroup Tag.E8 K
      (({1} : Set (Fin Tag.E8.rank)) ∪ (({0, 2} : Set (Fin Tag.E8.rank)) ∪ Set.range e8A4Node)) :=
    hE.trans (subsystemGroup_mono hsub)
  rw [subsystemGroup_union] at hE'
  have hcomm₁ := commute_subsystemGroup_of_cartan_zero (K := K)
    (A := ({1} : Set (Fin Tag.E8.rank)))
    (B := (({0, 2} : Set (Fin Tag.E8.rank)) ∪ Set.range e8A4Node)) (by
      intro a ha b hb
      have ha1 : a = 1 := by simpa using ha
      subst ha1
      rcases hb with hb | hb
      · rcases (by simpa using hb : b = 0 ∨ b = 2) with rfl | rfl <;> decide
      · have hb' := (mem_range_e8A4Node b).1 hb
        rcases hb' with rfl | rfl | rfl | rfl <;> decide)
  have hcomm₂ := commute_subsystemGroup_of_cartan_zero (K := K)
    (A := ({0, 2} : Set (Fin Tag.E8.rank))) (B := Set.range e8A4Node) (by
      intro a ha b hb
      have ha' : a = 0 ∨ a = 2 := by simpa using ha
      have hb' := (mem_range_e8A4Node b).1 hb
      rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl <;> decide)
  have hboundA : ∀ F : Subgroup (subsystemGroup Tag.E8 K ({1} : Set (Fin Tag.E8.rank))),
      IsElemAbelian p F → Nat.card F ≤ p ^ 1 :=
    bound_subgroup_of_ambient (fun F hF hFel =>
      card_le_pow_one_subsystemGroup_e8node hp hp2 hpq 1 hF hFel)
  have hboundB : ∀ F : Subgroup (subsystemGroup Tag.E8 K
      (({0, 2} : Set (Fin Tag.E8.rank)) ∪ Set.range e8A4Node)),
      IsElemAbelian p F → Nat.card F ≤ p ^ (1 + 2) :=
    bound_subgroup_of_ambient (fun E hE hEel => by
      have hE' : E ≤ subsystemGroup Tag.E8 K ({0, 2} : Set (Fin Tag.E8.rank)) ⊔
          subsystemGroup Tag.E8 K (Set.range e8A4Node) := by
        rw [← subsystemGroup_union]
        exact hE
      exact card_le_pow_add_of_le_sup_of_not_dvd_inf (p := p) hp hcomm₂
        (not_dvd_card_inf_subsystemGroup_e8 hp hpq hcomm₂)
        (bound_subgroup_of_ambient (fun G hG hGel =>
          card_le_pow_one_subsystemGroup_e8A2 (i := 0) (j := 2) hp hp2 hpq
            (by decide) (by decide) (by decide) ⟨3, by decide⟩ hG hGel))
        (bound_subgroup_of_ambient (fun G hG hGel =>
          card_le_pow_two_subsystemGroup_e8A4 hp hp2 hpq hG hGel)) hE' hEel)
  have h := card_le_pow_add_of_le_sup_of_not_dvd_inf (p := p) hp hcomm₁
    (not_dvd_card_inf_subsystemGroup_e8 hp hpq hcomm₁) hboundA hboundB hE' hEel
  exact h.trans (Nat.pow_le_pow_right hp.pos (by norm_num))

private theorem card_le_pow_six_subsystemGroup_e8delete4 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ Nat.card K + 1)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K {j : Fin Tag.E8.rank | j ≠ 4})
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 6 := by
  have hpq : ¬ p ∣ Nat.card K - 1 :=
    CFSG.RankThree.PartOne.S15K.not_dvd_sub_one_of_dvd_add_one Nat.card_pos
      (by have := hp.two_le; omega) hd
  have hsub : ({j : Fin Tag.E8.rank | j ≠ 4} : Set _) ⊆
      Set.range e8A4Node' ∪ Set.range e8A3Node := by
    intro j hj
    fin_cases j <;> first | exact absurd rfl hj | decide
  have hE' : E ≤ subsystemGroup Tag.E8 K (Set.range e8A4Node' ∪ Set.range e8A3Node) :=
    hE.trans (subsystemGroup_mono hsub)
  rw [subsystemGroup_union] at hE'
  have hcomm := commute_subsystemGroup_of_cartan_zero (K := K)
    (A := Set.range e8A4Node') (B := Set.range e8A3Node) (by
      intro a ha b hb
      have ha' := (mem_range_e8A4Node' a).1 ha
      have hb' := (mem_range_e8A3Node b).1 hb
      rcases ha' with rfl | rfl | rfl | rfl <;>
        rcases hb' with rfl | rfl | rfl <;> decide)
  have hboundA : ∀ F : Subgroup (subsystemGroup Tag.E8 K (Set.range e8A4Node')),
      IsElemAbelian p F → Nat.card F ≤ p ^ 2 :=
    bound_subgroup_of_ambient (fun F hF hFel =>
      card_le_pow_two_subsystemGroup_e8A4' hp hp2 hpq hF hFel)
  have hboundB : ∀ F : Subgroup (subsystemGroup Tag.E8 K (Set.range e8A3Node)),
      IsElemAbelian p F → Nat.card F ≤ p ^ 2 :=
    bound_subgroup_of_ambient (fun F hF hFel =>
      card_le_pow_two_subsystemGroup_e8A3 hp hp2 hpq hF hFel)
  have h := card_le_pow_add_of_le_sup_of_not_dvd_inf (p := p) hp hcomm
    (not_dvd_card_inf_subsystemGroup_e8 hp hpq hcomm) hboundA hboundB hE' hEel
  exact h.trans (Nat.pow_le_pow_right hp.pos (by norm_num))

private theorem card_le_pow_six_subsystemGroup_e8delete5 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ Nat.card K + 1)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K {j : Fin Tag.E8.rank | j ≠ 5})
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 6 := by
  have hpq : ¬ p ∣ Nat.card K - 1 :=
    CFSG.RankThree.PartOne.S15K.not_dvd_sub_one_of_dvd_add_one Nat.card_pos
      (by have := hp.two_le; omega) hd
  have hsub : ({j : Fin Tag.E8.rank | j ≠ 5} : Set _) ⊆
      Set.range e8D5Node ∪ Set.range e8A2Node := by
    intro j hj
    fin_cases j <;> first | exact absurd rfl hj | decide
  have hE' : E ≤ subsystemGroup Tag.E8 K (Set.range e8D5Node ∪ Set.range e8A2Node) :=
    hE.trans (subsystemGroup_mono hsub)
  rw [subsystemGroup_union] at hE'
  have hcomm := commute_subsystemGroup_of_cartan_zero (K := K)
    (A := Set.range e8D5Node) (B := Set.range e8A2Node) (by
      intro a ha b hb
      have ha' := (mem_range_e8D5Node a).1 ha
      have hb' := (mem_range_e8A2Node b).1 hb
      rcases ha' with rfl | rfl | rfl | rfl | rfl <;>
        rcases hb' with rfl | rfl <;> decide)
  have hboundA : ∀ F : Subgroup (subsystemGroup Tag.E8 K (Set.range e8D5Node)),
      IsElemAbelian p F → Nat.card F ≤ p ^ 4 :=
    bound_subgroup_of_ambient (fun F hF hFel =>
      card_le_pow_four_subsystemGroup_e8D5 hp hp2 hd hF hFel)
  have hboundB : ∀ F : Subgroup (subsystemGroup Tag.E8 K (Set.range e8A2Node)),
      IsElemAbelian p F → Nat.card F ≤ p ^ 1 :=
    bound_subgroup_of_ambient (fun E hE hEel => by
      have hE' : E ≤ subsystemGroup Tag.E8 K ({6, 7} : Set (Fin Tag.E8.rank)) := by
        rw [← e8A2Node_range]
        exact hE
      exact card_le_pow_one_subsystemGroup_e8A2 (i := 6) (j := 7) hp hp2 hpq
        (by decide) (by decide) (by decide) ⟨5, by decide⟩ hE' hEel)
  have h := card_le_pow_add_of_le_sup_of_not_dvd_inf (p := p) hp hcomm
    (not_dvd_card_inf_subsystemGroup_e8 hp hpq hcomm) hboundA hboundB hE' hEel
  exact h.trans (Nat.pow_le_pow_right hp.pos (by norm_num))

private theorem card_le_pow_six_subsystemGroup_e8delete6 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ Nat.card K + 1)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K {j : Fin Tag.E8.rank | j ≠ 6})
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 6 := by
  have hpq : ¬ p ∣ Nat.card K - 1 :=
    CFSG.RankThree.PartOne.S15K.not_dvd_sub_one_of_dvd_add_one Nat.card_pos
      (by have := hp.two_le; omega) hd
  have hsub : ({j : Fin Tag.E8.rank | j ≠ 6} : Set _) ⊆
      Set.range e8E6Node ∪ ({7} : Set (Fin Tag.E8.rank)) := by
    intro j hj
    fin_cases j <;> first | exact absurd rfl hj | decide
  have hE' : E ≤ subsystemGroup Tag.E8 K (Set.range e8E6Node ∪ ({7} : Set (Fin Tag.E8.rank))) :=
    hE.trans (subsystemGroup_mono hsub)
  rw [subsystemGroup_union] at hE'
  have hcomm := commute_subsystemGroup_of_cartan_zero (K := K)
    (A := Set.range e8E6Node) (B := ({7} : Set (Fin Tag.E8.rank))) (by
      intro a ha b hb
      have ha' := (mem_range_e8E6Node a).1 ha
      have hb7 : b = 7 := by simpa using hb
      subst hb7
      rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hboundA : ∀ F : Subgroup (subsystemGroup Tag.E8 K (Set.range e8E6Node)),
      IsElemAbelian p F → Nat.card F ≤ p ^ 4 :=
    bound_subgroup_of_ambient (fun F hF hFel =>
      card_le_pow_four_subsystemGroup_e8E6 hp hp2 hd hF hFel)
  have hboundB : ∀ F : Subgroup (subsystemGroup Tag.E8 K ({7} : Set (Fin Tag.E8.rank))),
      IsElemAbelian p F → Nat.card F ≤ p ^ 1 :=
    bound_subgroup_of_ambient (fun F hF hFel =>
      card_le_pow_one_subsystemGroup_e8node hp hp2 hpq 7 hF hFel)
  have h := card_le_pow_add_of_le_sup_of_not_dvd_inf (p := p) hp hcomm
    (not_dvd_card_inf_subsystemGroup_e8 hp hpq hcomm) hboundA hboundB hE' hEel
  exact h.trans (Nat.pow_le_pow_right hp.pos (by norm_num))


variable {F : Type} [Field F] [Finite F]

private theorem card_le_pow_six_of_notMem_E8 (hF : Nat.card F = 2)
    {J : Set (Fin Tag.E8.rank)} {i : Fin Tag.E8.rank} (hi7 : i ≠ 7) (hi : i ∉ J)
    {E : Subgroup (ModGL .E8 F)} (hE : E ≤ subsystemGroup .E8 F J)
    (hEel : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 6 := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  have hd : 3 ∣ Nat.card F + 1 := by rw [hF]
  have hi_cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    · exact absurd rfl hi7
  rcases hi_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hJ : J ⊆ Set.range e8D7Node := fun j hj =>
      (mem_range_e8D7Node j).2 (by rintro rfl; exact hi hj)
    exact card_le_pow_six_subsystemGroup_e8D7 Nat.prime_three (by norm_num) hd
      (hE.trans (CFSG.StandardType.F4Rest.subsystemGroup_mono hJ)) hEel
  · have hpq : ¬ 3 ∣ Nat.card F - 1 := by rw [hF]; norm_num
    have hJ : J ⊆ Set.range e8A7Node := fun j hj =>
      (mem_range_e8A7Node j).2 (by rintro rfl; exact hi hj)
    exact (card_le_pow_four_subsystemGroup_e8A7 Nat.prime_three (by norm_num) hpq
      (hE.trans (CFSG.StandardType.F4Rest.subsystemGroup_mono hJ)) hEel).trans
      (Nat.pow_le_pow_right (by norm_num) (by norm_num : 4 ≤ 6))
  · have hJ : J ⊆ {j : Fin Tag.E8.rank | j ≠ 2} := fun j hj hji => hi (hji ▸ hj)
    exact card_le_pow_six_subsystemGroup_e8delete2 Nat.prime_three (by norm_num) hd
      (hE.trans (CFSG.StandardType.F4Rest.subsystemGroup_mono hJ)) hEel
  · have hJ : J ⊆ {j : Fin Tag.E8.rank | j ≠ 3} := fun j hj hji => hi (hji ▸ hj)
    exact card_le_pow_six_subsystemGroup_e8delete3 Nat.prime_three (by norm_num) hd
      (hE.trans (CFSG.StandardType.F4Rest.subsystemGroup_mono hJ)) hEel
  · have hJ : J ⊆ {j : Fin Tag.E8.rank | j ≠ 4} := fun j hj hji => hi (hji ▸ hj)
    exact card_le_pow_six_subsystemGroup_e8delete4 Nat.prime_three (by norm_num) hd
      (hE.trans (CFSG.StandardType.F4Rest.subsystemGroup_mono hJ)) hEel
  · have hJ : J ⊆ {j : Fin Tag.E8.rank | j ≠ 5} := fun j hj hji => hi (hji ▸ hj)
    exact card_le_pow_six_subsystemGroup_e8delete5 Nat.prime_three (by norm_num) hd
      (hE.trans (CFSG.StandardType.F4Rest.subsystemGroup_mono hJ)) hEel
  · have hJ : J ⊆ {j : Fin Tag.E8.rank | j ≠ 6} := fun j hj hji => hi (hji ▸ hj)
    exact card_le_pow_six_subsystemGroup_e8delete6 Nat.prime_three (by norm_num) hd
      (hE.trans (CFSG.StandardType.F4Rest.subsystemGroup_mono hJ)) hEel

theorem card_le_pow_six_of_mem_parabolicLevi_E8 (hF : Nat.card F = 2)
    {J : Set (Fin Tag.E8.rank)} (hJ : J ≠ Set.univ) (h7 : (7 : Fin Tag.E8.rank) ∈ J)
    {E : Subgroup (ModGL .E8 F)} (hE : E ≤ parabolicLevi .E8 F J) (hEel : IsElemAbelian 3 E) :
    Nat.card E ≤ 3 ^ 6 := by
  obtain ⟨i, hi⟩ := (Set.ne_univ_iff_exists_notMem J).1 hJ
  exact card_le_pow_six_of_notMem_E8 hF (by rintro rfl; exact hi h7) hi
    (hE.trans (le_of_eq (parabolicLevi_eq_subsystemGroup_E8_two hF J))) hEel

theorem parabolicLevi_le_rootSpan_perpRoots_of_card_E8 (hF : Nat.card F = 2)
    {J : Set (Fin Tag.E8.rank)} (hJ : J ≠ Set.univ) {E : Subgroup (ModGL .E8 F)}
    (hE : E ≤ parabolicLevi .E8 F J) (hEel : IsElemAbelian 3 E) (h7 : 3 ^ 7 ≤ Nat.card E) :
    parabolicLevi .E8 F J ≤ rootSpan .E8 F (perpRoots .E8) := by
  by_cases hJ7 : (7 : Fin Tag.E8.rank) ∈ J
  · have hle := card_le_pow_six_of_mem_parabolicLevi_E8 hF hJ hJ7 hE hEel
    omega
  · exact parabolicLevi_le_rootSpan_perpRoots_E8_two hF hJ7

theorem seven_le_glaTwoLocalRank_E8_two [Finite ↥(adjointGroup .E8 F)]
    (hF : Nat.card F = 2) :
    7 ≤ GLATwoLocalRank 3 ↥(adjointGroup .E8 F) :=
  seven_le_twoLocalPrimeRank_adjointGroup_E8 F hF

end Big

end CFSG.LocalAnalysis.GLTheoremA.T173O

end