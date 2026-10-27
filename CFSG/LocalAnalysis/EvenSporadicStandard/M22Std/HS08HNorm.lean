module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08HBasic
public import Certificates.Certificate26880
public import Certificates.Certificate26881

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.M22Std.HS08Check

theorem dProp : DProp :=
  of_decide_eq_true Certificates.certificate26880

theorem conjProp : ConjProp :=
  of_decide_eq_true Certificates.certificate26881

end CFSG.EvenSporadicStandard.M22Std.HS08Check

namespace CFSG.EvenSporadicStandard.M22Std.HS08H

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.OutCheck
  CFSG.EvenSporadicStandard.M22Std.E32Check CFSG.EvenSporadicStandard.M22Std.HS08Check
  CFSG.Blueprint.NativeSporadic CFSG.Monster.B.TwoA.Fischer


@[expose] noncomputable def dGensA : List (MulAut (Carrier .M22)) :=
  s0Gens' ++ [wordElt autLetters xWord]

@[expose] noncomputable def dSub : Subgroup (MulAut (Carrier .M22)) :=
  Subgroup.closure {g | g ∈ dGensA}

theorem map_autTab_dGensA : dGensA.map autTab = dGens := by
  simp only [dGensA, List.map_append, map_autTab_s0Gens', List.map_cons, List.map_nil,
    autTab_wordElt_letters, dGens, xTab]

theorem mem_dSub_of_mem_dGensA {g : MulAut (Carrier .M22)} (hg : g ∈ dGensA) : g ∈ dSub :=
  Subgroup.subset_closure hg

theorem s0_le_dSub : s0 ≤ dSub :=
  (Subgroup.closure_le _).2 fun _ hg => mem_dSub_of_mem_dGensA (List.mem_append_left _ hg)

theorem isTabsOf_dSub : autTabMap.IsTabsOf dSub dTabs := by
  have hD := dProp
  have hmap : dGensA.map autTabMap.tb = dGens := map_autTab_dGensA
  refine autTabMap.isTabsOf_closure_of_mem dGensA dTabs hD.2.2.1 ?_ ?_
  · intro l hl g hg
    refine hD.2.2.2.1 l hl _ ?_
    rw [← hmap]
    exact List.mem_map_of_mem hg
  · intro l hl
    obtain ⟨r, hr, hlr⟩ := List.mem_flatMap.1 hl
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hlr
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hr
    obtain ⟨s', hs', hss'⟩ := isTabsOf_s0.exists_mem s hs
    have hw : wordElt dGensA w ∈ dSub := wordElt_mem_of_forall dSub (fun _ hg =>
      mem_dSub_of_mem_dGensA hg) w
    refine ⟨s' * wordElt dGensA w, dSub.mul_mem (s0_le_dSub hs') hw, ?_⟩
    rw [autTabMap.mul, hss', show autTabMap.tb (wordElt dGensA w) = wordTab dGens w by
      rw [← hmap]; exact autTab_wordElt dGensA w]

theorem card_dSub : Nat.card dSub = 3840 := by
  rw [isTabsOf_dSub.card dProp.2.1, dProp.1]

theorem dSub_le_normalizer : dSub ≤ Subgroup.normalizer (jSub : Set (MulAut (Carrier .M22))) := by
  refine (Subgroup.closure_le _).2 fun g hg => ?_
  refine mem_normalizer_of_conj_mem jSub g fun x hx => ?_
  have hgt : autTab g ∈ dGens := by
    rw [← map_autTab_dGensA]
    exact List.mem_map_of_mem hg
  obtain ⟨j', hj', hxj⟩ := dProp.2.2.2.2 _ hgt _ (mem_jSub.1 hx)
  obtain ⟨y, hy, hyj⟩ := exists_mem_jSub hj'
  have hgx : g * x = y * g :=
    autTab_injective (by rw [autTab_mul, autTab_mul, hyj]; exact hxj)
  have : g * x * g⁻¹ = y := by rw [hgx]; group
  rw [this]
  exact hy

@[expose] noncomputable def cElt (w : List Nat) : MulAut (Carrier .M22) := wordElt autLetters w

theorem cElt_invWord {w : List Nat}
    (h : tmul (wordTab letterTabs4 w) (wordTab letterTabs4 (invWordL w)) = idTab) :
    cElt (invWordL w) = (cElt w)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  refine autTab_injective ?_
  rw [autTab_mul, autTab_one, cElt, cElt, autTab_wordElt_letters, autTab_wordElt_letters]
  exact h

theorem inv_mul_not_mem_normalizer {i j : Nat} (hi : i < cWords.length) (hj : j < cWords.length)
    (hij : i < j) :
    (cElt cWords[i])⁻¹ * cElt cWords[j] ∉
      Subgroup.normalizer (jSub : Set (MulAut (Carrier .M22))) := by
  obtain ⟨hlen, hinv, hpw⟩ := conjProp
  have hlen' : cPairs.length = cWords.length := List.length_map _
  have hR := List.pairwise_iff_getElem.1 hpw i j (hlen' ▸ hi) (hlen' ▸ hj) hij
  obtain ⟨x, hx, hxn⟩ := hR
  have hpi : cPairs[i]'(hlen' ▸ hi) =
      (wordTab letterTabs4 cWords[i], wordTab letterTabs4 (invWordL cWords[i])) := by
    simp [cPairs]
  have hpj : cPairs[j]'(hlen' ▸ hj) =
      (wordTab letterTabs4 cWords[j], wordTab letterTabs4 (invWordL cWords[j])) := by
    simp [cPairs]
  rw [hpi, hpj] at hxn
  have hii := hinv _ (List.getElem_mem (hlen' ▸ hi))
  have hjj := hinv _ (List.getElem_mem (hlen' ▸ hj))
  rw [hpi] at hii
  rw [hpj] at hjj
  have e1 := cElt_invWord hii
  have e2 := cElt_invWord hjj
  intro hN
  obtain ⟨x', hx', rfl⟩ := exists_mem_jSub hx
  have h1 := (Subgroup.mem_normalizer_iff.1 hN x').1 hx'
  apply hxn
  have h2 : autTab ((cElt cWords[i])⁻¹ * cElt cWords[j] * x' *
      ((cElt cWords[i])⁻¹ * cElt cWords[j])⁻¹) ∈ jTabs := mem_jSub.1 h1
  have h3 : ((cElt cWords[i])⁻¹ * cElt cWords[j] * x' *
      ((cElt cWords[i])⁻¹ * cElt cWords[j])⁻¹) =
      cElt (invWordL cWords[i]) * cElt cWords[j] * x' *
        (cElt (invWordL cWords[j]) * cElt cWords[i]) := by
    rw [e1, e2, mul_inv_rev, inv_inv]
  rw [h3] at h2
  simpa only [autTab_mul, cElt, autTab_wordElt_letters] using h2

theorem le_index_normalizer :
    231 ≤ (Subgroup.normalizer (jSub : Set (MulAut (Carrier .M22)))).index := by
  set N := Subgroup.normalizer (jSub : Set (MulAut (Carrier .M22))) with hN
  have hlen : cWords.length = 231 := by
    have := conjProp.1
    rwa [cPairs, List.length_map] at this
  let f : Fin cWords.length → MulAut (Carrier .M22) ⧸ N := fun i => ((cElt cWords[i] : _) : _)
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hq : (cElt cWords[i])⁻¹ * cElt cWords[j] ∈ N := QuotientGroup.eq.1 hij
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hlt
    · exact inv_mul_not_mem_normalizer i.2 j.2 hlt hq
    · refine inv_mul_not_mem_normalizer j.2 i.2 hlt ?_
      have := N.inv_mem hq
      rwa [mul_inv_rev, inv_inv] at this
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_eq_fintype_card, Fintype.card_fin, hlen, ← Subgroup.index_eq_card] at this

theorem card_normalizer_jSub_le :
    Nat.card (Subgroup.normalizer (jSub : Set (MulAut (Carrier .M22)))) ≤ 3840 := by
  have h1 := Subgroup.card_mul_index (Subgroup.normalizer (jSub : Set (MulAut (Carrier .M22))))
  have h0 : Nat.card (MulAut (Carrier .M22)) = 887040 := catalog_M22_full_automorphism_order.1
  rw [h0] at h1
  have h2 := le_index_normalizer
  by_contra hlt
  have hlt' := not_le.1 hlt
  nlinarith

theorem normalizer_jSub_eq :
    Subgroup.normalizer (jSub : Set (MulAut (Carrier .M22))) = dSub :=
  (Subgroup.eq_of_le_of_card_ge dSub_le_normalizer
    (by rw [card_dSub]; exact card_normalizer_jSub_le)).symm

theorem card_normalizer_jSub :
    Nat.card (Subgroup.normalizer (jSub : Set (MulAut (Carrier .M22)))) = 3840 := by
  rw [normalizer_jSub_eq, card_dSub]

theorem mem_normalizer_jSub_iff (α : MulAut (Carrier .M22)) :
    α ∈ Subgroup.normalizer (jSub : Set (MulAut (Carrier .M22))) ↔ autTab α ∈ dTabs := by
  rw [normalizer_jSub_eq]
  exact isTabsOf_dSub.mem_iff α

end CFSG.EvenSporadicStandard.M22Std.HS08H
