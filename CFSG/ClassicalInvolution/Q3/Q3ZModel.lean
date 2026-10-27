module

public import CFSG.ClassicalInvolution.Q3.Q3WACore

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Z

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.Generic
  (Commutes FundamentalSingleClass fundamentalSubgroups modelUniv)
open CFSG.ClassicalInvolution.Models.SymplecticPairs
  (isHyperbolicPlane_stdPlane longBlock planeGroup_stdPlane stdPlane)

theorem orderOf_not_dvd_three_of_center_sp {K : Type} [Field K] {n : ℕ} (hn : 1 ≤ n)
    {g : StatedSp n K} (hg : g ∈ Subgroup.center (StatedSp n K)) : ¬ 3 ∣ orderOf g := by
  have h2 : g * g = 1 := Models.SymplecticPairs.mul_self_eq_one_of_mem_center hn hg
  have hord : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
  intro h3
  have := Nat.le_of_dvd (by norm_num) (h3.trans hord)
  omega

theorem statedLieAdmissible_psp2 : StatedLieAdmissible .PSp 2 3 1 :=
  ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩

theorem statedLieAdmissible_psp3 : StatedLieAdmissible .PSp 3 3 1 :=
  ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩


theorem finite_psp2 : Finite (modelUniv .PSp 2 3 1 Nat.prime_three).K :=
  inferInstanceAs (Finite (StatedSp 2 (GaloisField 3 1)))

theorem fundamentalSingleClass_psp3 :
    FundamentalSingleClass .PSp (modelUniv .PSp 3 3 1 Nat.prime_three).D :=
  ModelFacts.fundamentalSingleClass .PSp 3 3 1 Nat.prime_three trivial statedLieAdmissible_psp3
    (by decide) (by decide)

theorem fundamentalSingleClass_psp2 :
    FundamentalSingleClass .PSp (modelUniv .PSp 2 3 1 Nat.prime_three).D :=
  ModelFacts.fundamentalSingleClass .PSp 2 3 1 Nat.prime_three trivial statedLieAdmissible_psp2
    (by decide) (by decide)

theorem nonempty_extModel3_psp : Nonempty (Q3W.ExtModel3 .PSp 3 .PSp 2 1) := by
  set F := GaloisField 3 1 with hF
  let L3 : Subgroup (StatedSp 3 F) := (longBlock F 3 (Fin.last 2)).range
  let L2 : Subgroup (StatedSp 2 F) := (longBlock F 2 (Fin.last 1)).range
  have hplane3 : ∀ R : Subgroup (StatedSp 3 F),
      (∃ P, Models.SymplecticPairs.IsHyperbolicPlane P ∧ R = Models.SymplecticPairs.planeGroup P) →
      R ∈ fundamentalSubgroups .PSp (modelUniv .PSp 3 3 1 Nat.prime_three).D := fun R h =>
    (Models.SymplecticPairs.mem_fundamentalSubgroups_PSp_iff statedLieAdmissible_psp3 R).2 h
  have hplane2 : ∀ R : Subgroup (StatedSp 2 F),
      (∃ P, Models.SymplecticPairs.IsHyperbolicPlane P ∧ R = Models.SymplecticPairs.planeGroup P) →
      R ∈ fundamentalSubgroups .PSp (modelUniv .PSp 2 3 1 Nat.prime_three).D := fun R h =>
    (Models.SymplecticPairs.mem_fundamentalSubgroups_PSp_iff statedLieAdmissible_psp2 R).2 h
  have hL3 : L3 ∈ fundamentalSubgroups .PSp (modelUniv .PSp 3 3 1 Nat.prime_three).D :=
    hplane3 _ ⟨stdPlane F 3 (Fin.last 2), isHyperbolicPlane_stdPlane _,
      (planeGroup_stdPlane _).symm⟩
  have hL2pl : ∃ P, Models.SymplecticPairs.IsHyperbolicPlane P ∧
      L2 = Models.SymplecticPairs.planeGroup P :=
    ⟨stdPlane F 2 (Fin.last 1), isHyperbolicPlane_stdPlane _, (planeGroup_stdPlane _).symm⟩
  have hL2 : L2 ∈ fundamentalSubgroups .PSp (modelUniv .PSp 2 3 1 Nat.prime_three).D :=
    hplane2 _ hL2pl
  have hΘinj : Function.Injective (spEmbedLast F 2) :=
    Models.SymplecticPairs.spEmbed_injective (Fin.castSucc_injective 2)
  have hΘker : (spEmbedLast F 2).ker ≤ Subgroup.center (StatedSp 2 F) := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 hΘinj]
    exact bot_le
  have hΘ₀ : L2.map (spEmbedLast F 2) ∈
      fundamentalSubgroups .PSp (modelUniv .PSp 3 3 1 Nat.prime_three).D := by
    obtain ⟨P, hP, hPeq⟩ := exists_planeGroup_map_spEmbedLast (by norm_num : 1 ≤ 2) hL2pl
    exact hplane3 _ ⟨P, hP, hPeq⟩
  have hcomm : Commutes (spEmbedLast F 2).range L3 := by
    rintro _ ⟨x, rfl⟩ _ ⟨A, rfl⟩
    exact (commute_spEmbedLast_longBlock_last 2 x A).eq
  exact Q3W.nonempty_extModel3U_one fundamentalSingleClass_psp3 fundamentalSingleClass_psp2
    hL3 (Q3W.pow3_range_sl2 Q3W.card_gf3 _) hL2 (Q3W.pow3_range_sl2 Q3W.card_gf3 _) hL3
    (spEmbedLast F 2) hΘker hΘ₀ hcomm
    (fun _ hz => orderOf_not_dvd_three_of_center_sp (by norm_num) hz)
    (fun _ hz => orderOf_not_dvd_three_of_center_sp (by norm_num) hz)

end CFSG.ClassicalInvolution.Q3.Q3Z
