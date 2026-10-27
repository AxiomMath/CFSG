module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieIdx
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuter

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms

theorem kd264CaseY1_inner {d : TauCeti.ValidLieTypeIndex}
    [Finite (TauCeti.CFSGIndex.lie d).Group]
    {A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group)}
    (hI : KD264LieInputs) (h : KD264CoreHyp 3 d A 3 1)
    (hA : A ≤ innAutDerived (TauCeti.CFSGIndex.lie d).Group) :
    ∃ F ≤ A, Nat.card F = 9 ∧ IsGood 3 F := by
  have hnotK3 : ¬ k3Lie d.1 := fun hk3 => h.notK3 ⟨rfl, hk3⟩
  have hnotMult : ¬ multIdx 3 d.1 := by
    intro hm
    rcases k3Lie_or_k2Lie_three_of_lpEpsIdx d (lpEpsIdx_of_multIdx_three hm h.low) with h3 | h2
    · exact hnotK3 h3
    · exact h.notK2 h2
  exact hI.y1Row d h.notChev h.notK2 hnotK3 (h.noMult hnotMult).1 A hA h.elem
    (by rw [h.card]; norm_num)

theorem kd264CaseY1_overEight {d : TauCeti.ValidLieTypeIndex}
    [Finite (TauCeti.CFSGIndex.lie d).Group]
    {A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group)}
    (hI : KD264LieInputs) (h : KD264CoreHyp 3 d A 3 1)
    {b : MulAut (TauCeti.CFSGIndex.lie d).Group} (hbA : b ∈ A)
    (hbout : b ∉ innAutDerived (TauCeti.CFSGIndex.lie d).Group) (hover : overEight d.1)
    (hnotTri : ¬ ∃ q : TauCeti.PrimePower, d.1 = .trialityD4 q) :
    ∃ F ≤ A, Nat.card F = 9 ∧ IsGood 3 F := by
  have hnotK3 : ¬ k3Lie d.1 := fun hk3 => h.notK3 ⟨rfl, hk3⟩
  have hf : ∀ k, i5FieldBound d.1 k → k + 1 ≤ 4 := by
    intro k hk
    have := h.field rfl b hbA hbout k hk
    omega
  obtain ⟨hU, hE⟩ := not_multIdx_field_of_overEight d hover h.notK2 hf
  have hnotMult : ¬ multIdx 3 d.1 := not_multIdx_three_of_overEight hover hU hE
  have hno := h.noMult hnotMult
  have hrank : CFSG.Open.pRank 3 A = 3 :=
    CFSG.HardMathSupport.Solomon.LocalBalance.pRank_eq_of_card h.prime h.elem h.card
  refine hI.f8Row d h.notChev h.notK2 hnotK3 hover hnotTri hU hE A h.elem ?_ ?_ ?_ ?_ ?_
  · rw [hrank]
  · rw [hrank]
    norm_num
  · simpa [hrank] using hno.1
  · intro a ha haout E hE1 hE2
    have := hno.2 a ha haout E hE1 hE2
    omega
  · intro hAle
    exact hbout (hAle hbA)

theorem kd264CaseY1_outer {d : TauCeti.ValidLieTypeIndex}
    [Finite (TauCeti.CFSGIndex.lie d).Group]
    {A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group)}
    (hI : KD264LieInputs) (hBS : KD264BS 3) (hAmb : KD264Amb 3)
    (h : KD264CoreHyp 3 d A 3 1)
    (hNo : ∀ F ≤ A, Nat.card F = 3 ^ 2 → ¬ IsGood 3 F)
    (hTri : (∃ q : TauCeti.PrimePower, d.1 = .trialityD4 q) →
      A ≤ innAutDerived (TauCeti.CFSGIndex.lie d).Group)
    (hb : ∃ b ∈ A, b ∉ innAutDerived (TauCeti.CFSGIndex.lie d).Group) :
    ∃ F ≤ A, Nat.card F = 9 ∧ IsGood 3 F := by
  classical
  obtain ⟨b, hbA, hbout⟩ := hb
  have hd3 : d.1.characteristic ≠ 3 :=
    characteristic_ne_of_not_isChevSimple d.2 ⟨MulEquiv.refl _⟩ h.notChev
  have hbp : b ^ 3 = 1 := h.elem.2 b hbA
  have hbne : b ≠ 1 := by
    rintro rfl
    exact hbout (Subgroup.one_mem _)
  have hnotK3 : ¬ k3Lie d.1 := fun hk3 => h.notK3 ⟨rfl, hk3⟩
  have hcardA : Nat.card A = 3 ^ 3 := h.card
  have hexc : ¬ (3 = 3 ∧ ((∃ q : TauCeti.PrimePower,
        (d.1 = .A 1 q ∨ d.1 = .twistedA 2 q) ∧ q.card = 8) ∨
      ∃ q : TauCeti.PrimePower, d.1 = .trialityD4 q)) := by
    rintro ⟨-, h8 | htri⟩
    · obtain ⟨q, hq, hq8⟩ := h8
      rcases hq with hq | hq
      · exact h.notK2 (k2Lie_three_of_card_eight (Or.inl hq) hq8)
      · exact h.notK2 (k2Lie_three_of_card_eight (Or.inr hq) hq8)
    · obtain ⟨q, hq⟩ := htri
      exact hbout (hTri ⟨q, hq⟩ hbA)
  have hnot5 : ¬ (3 = 5 ∧ d.1 = .suzuki 2) := by
    rintro ⟨h5, -⟩
    omega
  obtain ⟨J, hJcomp, hJdvd, i, ⟨eJ⟩, hsub⟩ :=
    hI.outerIdx d 3 h.prime h.odd hd3.symm h.dvd hexc hnot5 b hbp hbout
  obtain ⟨-, ⟨D, hDelem, hDcard⟩, hBS4⟩ :=
    hBS (TauCeti.CFSGIndex.lie d).Group A h.elem (by rw [hcardA]) hNo b hbA hbne
      J hJcomp hJdvd i ⟨eJ⟩
  have hD9 : Nat.card D = 9 := by
    have := hDcard
    rw [hcardA] at this
    norm_num at this
    omega
  have hover : overEight d.1 := by
    cases i with
    | lie e =>
      have hsub' : subRel 3 d.1 e.1 := hsub
      rcases characteristic_ne_of_subRel h.prime h.odd hsub' hd3.symm with hchar | h7 | h3
      · rcases hBS4 e rfl hchar with h1 | h2 | h3' | h4
        · exact overEight_of_subRel e hsub' h1.2 hd3
        · exact absurd (k2Lie_three_of_subRel_of_eight d hsub' hd3 h2.2.1) h.notK2
        · exact absurd h3'.1 (by norm_num)
        · rcases k3Lie_or_k2Lie_three_of_lpEpsIdx d
            (lpEpsIdx_of_subRel h.prime h.odd hsub' h4.1) with hk3 | hk2
          · exact absurd hk3 hnotK3
          · exact absurd hk2 h.notK2
      · exact absurd h7.1 (by norm_num)
      · exact h3.2.2
    | alternating n hn =>
      have hsub' : subRelC 3 d.1 (.alternating n hn) := hsub
      rcases subRelC_alternating_three hsub' hd3 with hn5 | hover8
      · exfalso
        have hle := hAmb.1 n hn (Or.inl hn5)
          (by rintro ⟨-, h68 | h68⟩ <;> omega) D hDelem
        omega
      · exact hover8
    | cyclic r hr =>
      exfalso
      simpa [subRelC] using hsub
    | sporadic s =>
      exfalso
      simpa [subRelC] using hsub
  exact kd264CaseY1_overEight hI h hbA hbout hover fun ⟨q, hq⟩ => hbout (hTri ⟨q, hq⟩ hbA)

theorem kd264CaseY1_holds (hI : KD264LieInputs) (hBS : KD264BS 3) (hAmb : KD264Amb 3) :
    KD264CaseY1 := by
  intro d _ A h hov2 hTri
  by_contra hgoal
  have hNo : ∀ F ≤ A, Nat.card F = 3 ^ 2 → ¬ IsGood 3 F := by
    intro F hFA hF hgood
    exact hgoal ⟨F, hFA, by rw [hF]; norm_num, hgood⟩
  by_cases hA : A ≤ innAutDerived (TauCeti.CFSGIndex.lie d).Group
  · exact hgoal (kd264CaseY1_inner hI h hA)
  · have hb : ∃ b ∈ A, b ∉ innAutDerived (TauCeti.CFSGIndex.lie d).Group := by
      by_contra hcon
      exact hA fun x hx => by
        by_contra hxout
        exact hcon ⟨x, hx, hxout⟩
    exact hgoal (kd264CaseY1_outer hI hBS hAmb h hNo hTri hb)

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
