module

public import CFSG.CharacterTheory.Wreathed.ProjectiveTwoParameterUniqueness
public import CFSG.LieType.Simplicity.Suzuki
public import CFSG.Sporadic.J1
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdNineBasic
public import CFSG.Quasithin.Vol2.Ch1Rank

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint

theorem finite_of_is121List
    {X : Type} [Group X] (h : Is121List X) : Finite X := by
  obtain ⟨-, -, -, hcases⟩ := h
  rcases hcases with ⟨n, -, hn⟩ | ⟨n, -, -, hn⟩ | ⟨p, -, -, hp⟩ | he
  · exact CFSG.Wreathed.ProjectiveTwoParameterUniqueness.finite_stated_psl_two X 2 n hn
  · exact CFSG.LieType.Simplicity.fam_suzuki_finiteness X 2 n hn
  · exact CFSG.Wreathed.ProjectiveTwoParameterUniqueness.finite_stated_psl_two X p 1 hp
  · obtain ⟨e⟩ := he
    have h1 : Finite (NativeSporadic.Carrier .J1) := CFSG.Sporadic.J1.fam_j1_simplicity.1
    exact Finite.of_equiv _ e.symm.toEquiv

theorem a38Types_of_is121List {X : Type} [Group X] (h : Is121List X) : A38Types X := by
  obtain ⟨-, -, -, hcases⟩ := h
  rcases hcases with ⟨n, -, hn⟩ | ⟨n, -, -, hn⟩ | ⟨p, hp, h5, hpsl⟩ | he
  · exact Or.inl ⟨n, hn⟩
  · exact Or.inr (Or.inl ⟨n, hn⟩)
  · exact Or.inr (Or.inr (Or.inr ⟨p, hp, by omega, hpsl⟩))
  · exact Or.inr (Or.inr (Or.inl he))

theorem threeRank_list_of_rank (hrank : Lemma122Rank) :
    ∀ (X : Type) [Group X], Is121List X → ∀ A : Subgroup X, IsElemAbelian 3 A →
      Nat.card A ≤ 3 := by
  intro X _ hX A hA
  have := finite_of_is121List hX
  have h1 := hrank X (a38Types_of_is121List hX) 3 Nat.prime_three (by norm_num)
  have hp : IsPGroup 3 A := fun x => ⟨1, by
    have := hA.2 x x.2
    simpa using Subtype.ext this⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hp
  have hmle : m ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_top hA (by rw [hm])
  have : m ≤ 1 := hmle.trans h1
  rw [hm]
  calc 3 ^ m ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    _ = 3 := by norm_num

theorem tabThreeRank_of
    (hrank : Lemma122Rank) (hnine : TabThreeRankNine) : TabThreeRank :=
  ⟨threeRank_list_of_rank hrank, hnine⟩

end CFSG.QuasithinUnique.Id2519
