module

public import CFSG.ClassicalInvolution.Q3.Q3ZModel

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.Generic
  (Commutes FundamentalSingleClass fundamentalSubgroups modelUniv)
open CFSG.ClassicalInvolution.Models.SymplecticPairs
  (isHyperbolicPlane_stdPlane longBlock planeGroup_stdPlane stdPlane)

theorem statedLieAdmissible_psp_rank {n : ℕ} (hn : 2 ≤ n) : StatedLieAdmissible .PSp n 3 1 :=
  ⟨Nat.prime_three, le_rfl, hn, fun h => by simpa using congrArg Prod.snd h⟩


theorem finite_psp_rank (n : ℕ) : Finite (modelUniv .PSp n 3 1 Nat.prime_three).K :=
  inferInstanceAs (Finite (StatedSp n (GaloisField 3 1)))

theorem fundamentalSingleClass_psp_rank (n : ℕ) (hn : 2 ≤ n) :
    FundamentalSingleClass .PSp (modelUniv .PSp n 3 1 Nat.prime_three).D :=
  ModelFacts.fundamentalSingleClass .PSp n 3 1 Nat.prime_three trivial
    (statedLieAdmissible_psp_rank hn) (by decide) (by decide)

theorem nonempty_extModel3_psp_rank (m : ℕ) (hm : 2 ≤ m) :
    Nonempty (Q3W.ExtModel3 .PSp (m + 1) .PSp m 1) := by
  set F := GaloisField 3 1 with hF
  have hadmT : StatedLieAdmissible .PSp (m + 1) 3 1 := statedLieAdmissible_psp_rank (by omega)
  have hadmY : StatedLieAdmissible .PSp m 3 1 := statedLieAdmissible_psp_rank hm
  let L₃ : Subgroup (StatedSp (m + 1) F) := (longBlock F (m + 1) (Fin.last m)).range
  let i₀ : Fin m := ⟨0, by omega⟩
  let L₂ : Subgroup (StatedSp m F) := (longBlock F m i₀).range
  have hplaneT : ∀ R : Subgroup (StatedSp (m + 1) F),
      (∃ P, Models.SymplecticPairs.IsHyperbolicPlane P ∧ R = Models.SymplecticPairs.planeGroup P) →
      R ∈ fundamentalSubgroups .PSp (modelUniv .PSp (m + 1) 3 1 Nat.prime_three).D := fun R h =>
    (Models.SymplecticPairs.mem_fundamentalSubgroups_PSp_iff hadmT R).2 h
  have hplaneY : ∀ R : Subgroup (StatedSp m F),
      (∃ P, Models.SymplecticPairs.IsHyperbolicPlane P ∧ R = Models.SymplecticPairs.planeGroup P) →
      R ∈ fundamentalSubgroups .PSp (modelUniv .PSp m 3 1 Nat.prime_three).D := fun R h =>
    (Models.SymplecticPairs.mem_fundamentalSubgroups_PSp_iff hadmY R).2 h
  have hL₃ : L₃ ∈ fundamentalSubgroups .PSp (modelUniv .PSp (m + 1) 3 1 Nat.prime_three).D :=
    hplaneT _ ⟨stdPlane F (m + 1) (Fin.last m), isHyperbolicPlane_stdPlane _,
      (planeGroup_stdPlane _).symm⟩
  have hL₂pl : ∃ P, Models.SymplecticPairs.IsHyperbolicPlane P ∧
      L₂ = Models.SymplecticPairs.planeGroup P :=
    ⟨stdPlane F m i₀, isHyperbolicPlane_stdPlane _, (planeGroup_stdPlane _).symm⟩
  have hL₂ : L₂ ∈ fundamentalSubgroups .PSp (modelUniv .PSp m 3 1 Nat.prime_three).D :=
    hplaneY _ hL₂pl
  have hΘinj : Function.Injective (spEmbedLast F m) :=
    Models.SymplecticPairs.spEmbed_injective (Fin.castSucc_injective m)
  have hΘker : (spEmbedLast F m).ker ≤ Subgroup.center (StatedSp m F) := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 hΘinj]
    exact bot_le
  have hΘ₀ : L₂.map (spEmbedLast F m) ∈
      fundamentalSubgroups .PSp (modelUniv .PSp (m + 1) 3 1 Nat.prime_three).D := by
    obtain ⟨P, hP, hPeq⟩ := exists_planeGroup_map_spEmbedLast (by omega : 1 ≤ m) hL₂pl
    exact hplaneT _ ⟨P, hP, hPeq⟩
  have hcomm : Commutes (spEmbedLast F m).range L₃ := by
    rintro _ ⟨x, rfl⟩ _ ⟨A, rfl⟩
    exact (commute_spEmbedLast_longBlock_last m x A).eq
  exact Q3W.nonempty_extModel3U_one (fundamentalSingleClass_psp_rank (m + 1) (by omega))
    (fundamentalSingleClass_psp_rank m hm)
    hL₃ (Q3W.pow3_range_sl2 Q3W.card_gf3 _) hL₂ (Q3W.pow3_range_sl2 Q3W.card_gf3 _) hL₃
    (spEmbedLast F m) hΘker hΘ₀ hcomm
    (fun _ hz => Q3Z.orderOf_not_dvd_three_of_center_sp (by omega) hz)
    (fun _ hz => Q3Z.orderOf_not_dvd_three_of_center_sp (by omega) hz)

end CFSG.ClassicalInvolution.Q3.Q3V
