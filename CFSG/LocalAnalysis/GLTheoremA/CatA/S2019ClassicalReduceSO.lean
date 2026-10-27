module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ClassicalPartsSO
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ClassicalReduce

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Open

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem s2019Omega_of_conj_of_not_conj {p : ℕ} (hp : p.Prime) {S B D J : Subgroup Ω}
    [S.Normal] (hSq : CFSG.Open.IsQuasisimple ↥S) (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hBel : IsElemAbelian p B)
    (hI : ∀ a : ↥S ⧸ Subgroup.center ↥S, a ^ p = 1 → S2019FixCentralizes p (MulAut.conj a))
    (hO : ∀ β : MulAut (↥S ⧸ Subgroup.center ↥S), β ^ p = 1 → (∀ a, β ≠ MulAut.conj a) →
      S2019FixCentralizes p β) :
    S2019Omega p S B D J := by
  refine s2019Omega_of_fixCentralizes (S := S) (B := B) (D := D) (J := J) hp hSp
    (MulEquiv.refl _) fun b _ hbB _ => ?_
  have hβp : transAut (MulEquiv.refl (↥S ⧸ Subgroup.center ↥S)) b ^ p = 1 :=
    transAut_pow_eq_one _ (hBel.2 b hbB)
  by_cases hinn : ∃ a, transAut (MulEquiv.refl (↥S ⧸ Subgroup.center ↥S)) b = MulAut.conj a
  · obtain ⟨a, ha⟩ := hinn
    rw [ha] at hβp ⊢
    haveI : Group.IsPerfect ↥S := ⟨hSq.1⟩
    refine hI a ?_
    have h1 : MulAut.conj (a ^ p) = 1 := by rw [map_pow, hβp]
    have hmem : a ^ p ∈ Subgroup.center (↥S ⧸ Subgroup.center ↥S) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h2 := congrArg (fun φ : MulAut (↥S ⧸ Subgroup.center ↥S) => φ g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      calc g * a ^ p = a ^ p * g * (a ^ p)⁻¹ * a ^ p := by rw [h2]
        _ = a ^ p * g := by group
    rw [Group.IsPerfect.center_quotient_center_eq_bot ↥S] at hmem
    exact Subgroup.mem_bot.1 hmem
  · push Not at hinn
    exact hO _ hβp hinn

theorem s2019FactClassicalOn_symplectic (hI5 : S2019SympInner (5 ≤ ·))
    (hI3 : S2019SympInner (· = 3)) (hO5 : S2019SympOuter (5 ≤ ·))
    (hO3 : S2019SympOuter (· = 3)) : S2019FactClassicalOn .symplectic := by
  intro p q hp hp2 hq hq2 hqp Ω _ _ S B D J hSn hSq hSp hcat hBel hSB hrank
  obtain ⟨i, hi, ⟨e₀⟩⟩ := hcat
  rcases i with _ | _ | ⟨⟨d, hv⟩⟩ | _
  · exact absurd hi id
  · exact absurd hi id
  swap
  · exact absurd hi id
  obtain ⟨hchar, hfam, -⟩ := hi
  obtain ⟨m, Q, rfl⟩ : ∃ m Q, d = .C m Q := by
    cases d <;> first | exact ⟨_, _, rfl⟩ | simp [s2019Family] at hfam
  have hQq : Q.p = q := by simpa using hchar
  subst hQq
  haveI := hSn
  have hG := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC m Q hv
    ((pSimpleEquivQuotCenter hSp).symm.trans e₀)
  refine s2019Omega_of_conj_of_not_conj hp hSq hSp hBel (fun a ha => ?_) (fun β hβ hn => ?_)
  · rcases eq_three_or_five_le hq hq2 with h3 | h5
    · exact hI3 p Q.p hp hp2 hq hq2 hqp h3 _ m Q.exponent hG a ha
    · exact hI5 p Q.p hp hp2 hq hq2 hqp h5 _ m Q.exponent hG a ha
  · rcases eq_three_or_five_le hq hq2 with h3 | h5
    · exact hO3 p Q.p hp hp2 hq hq2 hqp h3 _ m Q.exponent hG β hβ hn
    · exact hO5 p Q.p hp hp2 hq hq2 hqp h5 _ m Q.exponent hG β hβ hn

theorem s2019FactClassicalOn_orthogonal (hI5 : S2019OrthInner (5 ≤ ·))
    (hI3 : S2019OrthInner (· = 3)) (hO5 : S2019OrthOuter (5 ≤ ·))
    (hO3 : S2019OrthOuter (· = 3)) (hD4 : S2019OrthD4Outer) (hSI5 : S2019SympInner (5 ≤ ·))
    (hSI3 : S2019SympInner (· = 3)) (hSO5 : S2019SympOuter (5 ≤ ·))
    (hSO3 : S2019SympOuter (· = 3)) : S2019FactClassicalOn .orthogonal := by
  intro p q hp hp2 hq hq2 hqp Ω _ _ S B D J hSn hSq hSp hcat hBel hSB hrank
  obtain ⟨i, hi, ⟨e₀⟩⟩ := hcat
  rcases i with _ | _ | ⟨⟨d, hv⟩⟩ | _
  · exact absurd hi id
  · exact absurd hi id
  swap
  · exact absurd hi id
  obtain ⟨hchar, hfam, -⟩ := hi
  haveI := hSn
  have hinner : ∀ (t : StatedLieTag), (t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) →
      ∀ n f, StatedClassicalModel (↥S ⧸ Subgroup.center ↥S) t n q f →
      ∀ a : ↥S ⧸ Subgroup.center ↥S, a ^ p = 1 → S2019FixCentralizes p (MulAut.conj a) := by
    intro t ht n f hG a ha
    rcases eq_three_or_five_le hq hq2 with h3 | h5
    · exact hI3 p q hp hp2 hq hq2 hqp h3 t ht _ n f hG a ha
    · exact hI5 p q hp hp2 hq hq2 hqp h5 t ht _ n f hG a ha
  have horth : ∀ (t : StatedLieTag), (t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) →
      ∀ n f, StatedClassicalModel (↥S ⧸ Subgroup.center ↥S) t n q f →
      (t = .POmegaPlus → n = 4 → p ≠ 3) → S2019Omega p S B D J := by
    intro t ht n f hG hn
    refine s2019Omega_of_conj_of_not_conj hp hSq hSp hBel (hinner t ht n f hG)
      (fun β hβ hnot => ?_)
    rcases eq_three_or_five_le hq hq2 with h3 | h5
    · exact hO3 p q hp hp2 hq hq2 hqp h3 t ht _ n f hG hn β hβ hnot
    · exact hO5 p q hp hp2 hq hq2 hqp h5 t ht _ n f hG hn β hβ hnot
  have hd4 : ∀ f, StatedClassicalModel (↥S ⧸ Subgroup.center ↥S) .POmegaPlus 4 q f → p = 3 →
      S2019Omega p S B D J := by
    intro f hG hp3
    refine s2019Omega_of_conj_of_not_conj hp hSq hSp hBel
      (hinner .POmegaPlus (Or.inr (Or.inl rfl)) 4 f hG) (fun β hβ hnot => ?_)
    subst hp3
    exact hD4 q hq hq2 hqp _ f hG β hβ hnot
  have hsymp : ∀ n f, StatedClassicalModel (↥S ⧸ Subgroup.center ↥S) .PSp n q f →
      S2019Omega p S B D J := by
    intro n f hG
    refine s2019Omega_of_conj_of_not_conj hp hSq hSp hBel (fun a ha => ?_)
      (fun β hβ hnot => ?_)
    · rcases eq_three_or_five_le hq hq2 with h3 | h5
      · exact hSI3 p q hp hp2 hq hq2 hqp h3 _ n f hG a ha
      · exact hSI5 p q hp hp2 hq hq2 hqp h5 _ n f hG a ha
    · rcases eq_three_or_five_le hq hq2 with h3 | h5
      · exact hSO3 p q hp hp2 hq hq2 hqp h3 _ n f hG β hβ hnot
      · exact hSO5 p q hp hp2 hq hq2 hqp h5 _ n f hG β hβ hnot
  obtain ⟨m, Q, rfl⟩ | ⟨m, Q, rfl⟩ | ⟨m, Q, rfl⟩ :
      (∃ m Q, d = .B m Q) ∨ (∃ m Q, d = .D m Q) ∨ (∃ m Q, d = .twistedD m Q) := by
    cases d <;> first
      | exact Or.inl ⟨_, _, rfl⟩
      | exact Or.inr (Or.inl ⟨_, _, rfl⟩)
      | exact Or.inr (Or.inr ⟨_, _, rfl⟩)
      | simp [s2019Family] at hfam
  ·
    have hQq : Q.p = q := by simpa using hchar
    subst hQq
    have hm : 2 ≤ m := by
      have hv' := (TauCeti.LieTypeIndex.valid_iff _).1 hv
      rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hv'
      exact hv'.1.1
    rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
    · exact hsymp 2 Q.exponent (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 Q hv
        ((pSimpleEquivQuotCenter hSp).symm.trans e₀))
    · exact horth .POmegaOdd (Or.inl rfl) m Q.exponent
        (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd m Q hv hq2 hm3
          ((pSimpleEquivQuotCenter hSp).symm.trans e₀)) (fun h => nomatch h)
  ·
    have hQq : Q.p = q := by simpa using hchar
    subst hQq
    have hG := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD m Q hv
      ((pSimpleEquivQuotCenter hSp).symm.trans e₀)
    by_cases h43 : m = 4 ∧ p = 3
    · obtain ⟨rfl, hp3⟩ := h43
      exact hd4 Q.exponent hG hp3
    · exact horth .POmegaPlus (Or.inr (Or.inl rfl)) m Q.exponent hG
        (fun _ hm4 hp3 => h43 ⟨hm4, hp3⟩)
  ·
    have hQq : Q.p = q := by simpa using hchar
    subst hQq
    exact horth .POmegaMinus (Or.inr (Or.inr rfl)) m Q.exponent
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD m Q hv
        ((pSimpleEquivQuotCenter hSp).symm.trans e₀)) (fun h => nomatch h)

end CFSG.LocalAnalysis.GLTheoremA.S2019
