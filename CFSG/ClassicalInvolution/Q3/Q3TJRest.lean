module

public import CFSG.ClassicalInvolution.Q3.Q3TJCl
public import CFSG.ClassicalInvolution.Q3.Q3TJTw

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open CFSG.Blueprint.Chevalley

@[expose] def SteinbergOddAut3Rest : Prop :=
  ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ),
    (t = .PSU ∨ t = .POmegaOdd ∨ (t = .POmegaPlus ∧ n ≠ 4) ∨ t = .POmegaMinus) →
    CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n 3 1 →
      ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X → Subgroup.center X = ⊥ →
        ∀ f : (Generic.modelUniv t n 3 1 Nat.prime_three).K →* X, Function.Surjective f →
          f.ker ≤ Subgroup.center (Generic.modelUniv t n 3 1 Nat.prime_three).K →
            ∀ α : MulAut X, Odd (orderOf α) → ∃ g : X, α = MulAut.conj g

theorem steinbergOddAut3_of_rest (h : SteinbergOddAut3Rest) : SteinbergOddAut3 := by
  intro t n ht hadm X _ _ hX hZ f hf hker α hodd
  cases t with
  | PSL => exact Or.inl (exists_eq_conj_PSL hadm hZ f hf hker α hodd)
  | PSU => exact Or.inl (h .PSU n (Or.inl rfl) hadm X hX hZ f hf hker α hodd)
  | PSp => exact Or.inl (exists_eq_conj_PSp hadm hZ f hf hker α hodd)
  | POmegaOdd =>
    exact Or.inl (h .POmegaOdd n (Or.inr (Or.inl rfl)) hadm X hX hZ f hf hker α hodd)
  | POmegaPlus =>
    by_cases hn : n = 4
    · exact Or.inr (Or.inl ⟨rfl, hn⟩)
    · exact Or.inl (h .POmegaPlus n (Or.inr (Or.inr (Or.inl ⟨rfl, hn⟩))) hadm X hX hZ f hf hker
        α hodd)
  | POmegaMinus =>
    exact Or.inl (h .POmegaMinus n (Or.inr (Or.inr (Or.inr rfl))) hadm X hX hZ f hf hker α hodd)
  | G2 =>
    obtain rfl : n = 0 := hadm.2.2.1
    exact Or.inl (exists_eq_conj_G2 hZ f hf hker α hodd)
  | F4 =>
    obtain rfl : n = 0 := hadm.2.2
    exact Or.inl (exists_eq_conj_F4 hZ f hf hker α hodd)
  | E6 =>
    obtain rfl : n = 0 := hadm.2.2
    exact Or.inl (exists_eq_conj_E6 hZ f hf hker α hodd)
  | E7 =>
    obtain rfl : n = 0 := hadm.2.2
    exact Or.inl (exists_eq_conj_E7 hZ f hf hker α hodd)
  | E8 =>
    obtain rfl : n = 0 := hadm.2.2
    exact Or.inl (exists_eq_conj_E8 hZ f hf hker α hodd)
  | twistedE6 =>
    obtain rfl : n = 0 := hadm.2.2
    exact Or.inl (exists_eq_conj_twistedE6 hZ f hf hker α hodd)
  | trialityD4 => exact Or.inr (Or.inr rfl)
  | twistedB2 => exact (ht : False).elim
  | twistedG2 => exact (ht : False).elim
  | twistedF4 => exact (ht : False).elim
  | Tits => exact (ht : False).elim

theorem modelOddAutRigid_of_rest (hSt : SteinbergOddAut3Rest) (hD4 : D4OddAutInner3)
    (h3D4 : TrialityD4OddAutInner3) : ModelOddAutRigid :=
  modelOddAutRigid_of (steinbergOddAut3_of_rest hSt) hD4 h3D4

end CFSG.ClassicalInvolution.Q3.Q3T
