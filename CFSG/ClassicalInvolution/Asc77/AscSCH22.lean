module

public import CFSG.ClassicalInvolution.Asc77.AscSCH15
public import CFSG.ClassicalInvolution.Asc77.AscSCH20
public import CFSG.ClassicalInvolution.Asc77.AscSCH21
import CFSG.Adapters.StatedSLPerfect

public section

namespace CFSG.ClassicalInvolution.Asc77.SCH

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.CentralLift

@[expose] def DefSL : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (f : ℕ), Nat.card K = 3 ^ f → 5 ≤ 3 ^ f →
    ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* StatedSL 4 K),
      Function.Surjective π → π.ker ≤ Subgroup.center E → IsPGroup 3 π.ker → π.ker = ⊥

@[expose] def DefSU : Prop :=
  ∀ (K : Type) [Field K] (f : ℕ), UnitaryFieldData 3 f K → 5 ≤ 3 ^ f →
    ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* StatedSU 4 (3 ^ f) K),
      Function.Surjective π → π.ker ≤ Subgroup.center E → IsPGroup 3 π.ker → π.ker = ⊥

theorem isPerfect_statedSL_four (K : Type) [Field K] : Group.IsPerfect (StatedSL 4 K) :=
  CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le (by norm_num) K

theorem isPerfect_statedSU_four {K : Type} [Field K] {ℓ f : ℕ} (h : UnitaryFieldData ℓ f K) :
    Group.IsPerfect (StatedSU 4 (ℓ ^ f) K) := by
  have := h.finite
  obtain ⟨e⟩ := nonempty_statedSU_mulEquiv_sesq h 4
  have hsymm := gramForm_isSymm h (G := (1 : Matrix (Fin 4) (Fin 4) K))
    (by rw [Matrix.map_one _ (map_zero h.bar) (map_one h.bar), Matrix.transpose_one])
  have hsep := gramForm_separatingLeft h (G := (1 : Matrix (Fin 4) (Fin 4) K))
    (by rw [Matrix.det_one]; exact one_ne_zero)
  have : Group.IsPerfect (sesqSpecialUnitaryGroup (gramForm h (1 : Matrix (Fin 4) (Fin 4) K))) :=
    unitary_perfect h hsymm hsep (by rw [Module.finrank_fin_fun]; norm_num) (by
      intro h32
      have := congrArg Prod.fst h32
      simp only [Module.finrank_fin_fun] at this
      omega)
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem mod_three_cases {ℓ f : ℕ} (hℓ : ℓ.Prime) (h3 : ℓ ≠ 3) :
    ℓ ^ f % 3 = 1 ∨ ℓ ^ f % 3 = 2 := by
  have hn : ¬ 3 ∣ ℓ ^ f := fun h => h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
    (Nat.prime_three.dvd_of_dvd_pow h)).symm
  omega

theorem split3SL_of_def (hdef : DefSL) : Split3SL := by
  intro K _ _ ℓ f hℓ hℓ2 hq hK E _ _ π hπ hC hCp
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Group.IsPerfect (StatedSL 4 K) := isPerfect_statedSL_four K
  refine split_of_perfect_ker_eq_bot (r := 3) (fun E' _ _ _ π' hπ' hC' hCp' => ?_) E π hπ hC hCp
  by_cases h3 : ℓ = 3
  · subst h3
    exact hdef K f hK hq E' π' hπ' hC' hCp'
  · rcases mod_three_cases (f := f) hℓ h3 with h1 | h2
    · exact statedSL_four_perfect_ker_eq_bot_one (by rw [hK]; omega) π' hπ' hC' hCp'
    · exact statedSL_four_perfect_ker_eq_bot_two hℓ2 hK (by rw [hK]; exact h2) π' hπ' hC' hCp'

theorem split3SU_of_def (hdef : DefSU) : Split3SU := by
  intro K _ _ ℓ f hℓ hℓ2 hq hK E _ _ π hπ hC hCp
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have h : UnitaryFieldData ℓ f K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have : Group.IsPerfect (StatedSU 4 (ℓ ^ f) K) := isPerfect_statedSU_four h
  refine split_of_perfect_ker_eq_bot (r := 3) (fun E' _ _ _ π' hπ' hC' hCp' => ?_) E π hπ hC hCp
  by_cases h3 : ℓ = 3
  · subst h3
    exact hdef K f h hq E' π' hπ' hC' hCp'
  · rcases mod_three_cases (f := f) hℓ h3 with h1 | h2
    · exact statedSU_four_perfect_ker_eq_bot_one h (by omega) π' hπ' hC' hCp'
    · exact statedSU_four_perfect_ker_eq_bot_two hℓ2 h (by omega) π' hπ' hC' hCp'

theorem oddCenterClassical_of_def (hSL : DefSL) (hSU : DefSU) : T7Z.OddCenterClassical :=
  oddCenterClassical_of_split_three (split3SL_of_def hSL) (split3SU_of_def hSU) split3Sp

end CFSG.ClassicalInvolution.Asc77.SCH
