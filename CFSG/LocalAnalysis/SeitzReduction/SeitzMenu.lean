module

public import CFSG.Blueprint.EvenStandardExact
public import CFSG.Blueprint.EvenBNRankTwoExact

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def SeitzRankOne (X : Type) [Group X] : Prop :=
  (∃ f : ℕ, 3 ≤ f ∧ LieModel X .PSL 2 2 f) ∨ (∃ f : ℕ, 2 ≤ f ∧ LieModel X .PSU 3 2 f) ∨
    ∃ f : ℕ, LieModel X .twistedB2 0 2 f

@[expose] def SeitzSmallFour (X : Type) [Group X] : Prop :=
  LieModel X .PSp 3 2 1 ∨ LieModel X .PSU 6 2 1 ∨ LieModel X .POmegaMinus 4 2 1 ∨
    LieModel X .POmegaPlus 4 2 1

@[expose] def SeitzHighRank (X : Type) [Group X] : Prop :=
  ∃ (t : StatedLieTag) (n f : ℕ), LieModel X t n 2 f ∧
    ((t = .PSL ∧ 4 ≤ n ∧ (n, f) ≠ (4, 1)) ∨ (t = .PSU ∧ 6 ≤ n ∧ (n, f) ≠ (6, 1)) ∨
      (t = .PSp ∧ 3 ≤ n ∧ (n, f) ≠ (3, 1)) ∨
      ((t = .POmegaPlus ∨ t = .POmegaMinus) ∧ 4 ≤ n ∧ (n, f) ≠ (4, 1)) ∨
      (n = 0 ∧ (t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6)))

theorem seitz_menu_case_cover (X : Type) [Group X] (hX : EvenLieType X)
    (hexc : ¬ Recognition.Exact.EvenStandardException X) :
    SeitzRankOne X ∨ Recognition.Exact.EvenBNRankTwoType X ∨ SeitzSmallFour X ∨
      SeitzHighRank X := by
  obtain ⟨t, n, f, ⟨-, hf, hadm⟩, hm⟩ := hX
  have two : ∀ (t' : StatedLieTag) (n' : ℕ), (t', n') ∈ ({(.PSL, 3), (.PSU, 4), (.PSU, 5),
      (.PSp, 2), (.G2, 0), (.trialityD4, 0), (.twistedF4, 0), (.Tits, 0)} :
        Set (StatedLieTag × ℕ)) → LieModel X t' n' 2 f →
      SeitzRankOne X ∨ Recognition.Exact.EvenBNRankTwoType X ∨ SeitzSmallFour X ∨
        SeitzHighRank X :=
    fun t' n' htn hm' => Or.inr (Or.inl ⟨t', n', f, hf, htn, hm'⟩)
  cases t with
  | PSL =>
    obtain ⟨hn, h22, -⟩ := hadm
    rcases (show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | hn4
    ·
      rcases (show f = 1 ∨ f = 2 ∨ 3 ≤ f by omega) with rfl | rfl | hf3
      · exact absurd rfl h22
      · exact absurd (Or.inl hm) hexc
      · exact Or.inl (Or.inl ⟨f, hf3, hm⟩)
    · exact two _ _ (by simp) hm
    · by_cases hnf : (n, f) = (4, 1)
      ·
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hnf
        exact absurd (Or.inr (Or.inr (Or.inl hm))) hexc
      · exact Or.inr (Or.inr (Or.inr ⟨.PSL, n, f, hm, Or.inl ⟨rfl, hn4, hnf⟩⟩))
  | PSU =>
    obtain ⟨hn, h32⟩ := hadm
    rcases (show n = 3 ∨ n = 4 ∨ n = 5 ∨ 6 ≤ n by omega) with rfl | rfl | rfl | hn6
    ·
      rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | hf2
      · exact absurd rfl h32
      · exact Or.inl (Or.inr (Or.inl ⟨f, hf2, hm⟩))
    · exact two _ _ (by simp) hm
    · exact two _ _ (by simp) hm
    · by_cases hnf : (n, f) = (6, 1)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hnf
        exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl hm))))
      · exact Or.inr (Or.inr (Or.inr ⟨.PSU, n, f, hm, Or.inr (Or.inl ⟨rfl, hn6, hnf⟩)⟩))
  | PSp =>
    obtain ⟨hn, -⟩ := hadm
    rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
    · exact two _ _ (by simp) hm
    · by_cases hnf : (n, f) = (3, 1)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hnf
        exact Or.inr (Or.inr (Or.inl (Or.inl hm)))
      · exact Or.inr (Or.inr (Or.inr ⟨.PSp, n, f, hm, Or.inr (Or.inr (Or.inl ⟨rfl, hn3, hnf⟩))⟩))
  | POmegaOdd => exact absurd rfl hadm.2
  | POmegaPlus =>
    by_cases hnf : (n, f) = (4, 1)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hnf
      exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr hm)))))
    · exact Or.inr (Or.inr (Or.inr ⟨.POmegaPlus, n, f, hm,
        Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, hadm, hnf⟩)))⟩))
  | POmegaMinus =>
    by_cases hnf : (n, f) = (4, 1)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hnf
      exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl hm)))))
    · exact Or.inr (Or.inr (Or.inr ⟨.POmegaMinus, n, f, hm,
        Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr rfl, hadm, hnf⟩)))⟩))
  | G2 =>
    obtain ⟨rfl, -⟩ := hadm
    exact two _ _ (by simp) hm
  | F4 =>
    obtain rfl : n = 0 := hadm
    exact Or.inr (Or.inr (Or.inr ⟨.F4, 0, f, hm, Or.inr (Or.inr (Or.inr (Or.inr
      ⟨rfl, Or.inl rfl⟩)))⟩))
  | E6 =>
    obtain rfl : n = 0 := hadm
    exact Or.inr (Or.inr (Or.inr ⟨.E6, 0, f, hm, Or.inr (Or.inr (Or.inr (Or.inr
      ⟨rfl, Or.inr (Or.inl rfl)⟩)))⟩))
  | E7 =>
    obtain rfl : n = 0 := hadm
    exact Or.inr (Or.inr (Or.inr ⟨.E7, 0, f, hm, Or.inr (Or.inr (Or.inr (Or.inr
      ⟨rfl, Or.inr (Or.inr (Or.inl rfl))⟩)))⟩))
  | E8 =>
    obtain rfl : n = 0 := hadm
    exact Or.inr (Or.inr (Or.inr ⟨.E8, 0, f, hm, Or.inr (Or.inr (Or.inr (Or.inr
      ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩)))⟩))
  | twistedE6 =>
    obtain rfl : n = 0 := hadm
    exact Or.inr (Or.inr (Or.inr ⟨.twistedE6, 0, f, hm, Or.inr (Or.inr (Or.inr (Or.inr
      ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩)))⟩))
  | trialityD4 =>
    obtain rfl : n = 0 := hadm
    exact two _ _ (by simp) hm
  | twistedB2 =>
    obtain ⟨rfl, -⟩ := hadm
    exact Or.inl (Or.inr (Or.inr ⟨f, hm⟩))
  | twistedG2 => exact absurd hadm.2.1 (by decide)
  | twistedF4 =>
    obtain ⟨rfl, -⟩ := hadm
    exact two _ _ (by simp) hm
  | Tits =>
    obtain ⟨rfl, -⟩ := hadm
    exact two _ _ (by simp) hm

end CFSG.SeitzReduction
