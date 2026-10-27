module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotSwapBLiftLift
public import CFSG.LieType.Steinberg.CentralExt.Families
public import CFSG.LocalAnalysis.SectionRank.EvenCover.SLTwo

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Assembly.LowTwoRank

theorem injective_of_section_of_perfect {P K : Type*} [Group P] [Group K] [Group.IsPerfect P]
    (η : P →* K) (hcen : η.ker ≤ center P) (σ : K →* P) (hσ : ∀ x, η (σ x) = x) :
    Function.Injective η := by
  have hP : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = ⊤ := by
    rw [← commutator_def]
    exact Group.IsPerfect.commutator_eq_top
  have htop : (⊤ : Subgroup P) ≤ σ.range := by
    refine perfect_le_of_forall_exists_commute hP le_top fun a _ => ?_
    refine ⟨σ (η a), ⟨η a, rfl⟩, (σ (η a))⁻¹ * a, by group, fun b _ => ?_⟩
    have hz : (σ (η a))⁻¹ * a ∈ η.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, inv_mul_cancel]
    exact (mem_center_iff.1 (hcen hz) b).symm
  intro a b hab
  obtain ⟨x, rfl⟩ := htop (mem_top a)
  obtain ⟨y, rfl⟩ := htop (mem_top b)
  rw [hσ, hσ] at hab
  rw [hab]


theorem oddSchurTrivial_statedSp (r : ℕ) (k : Type) [Field k] [Finite k] [CharP k 2] :
    OddSchurTrivial (StatedSp r k) := by
  intro P _ _ hP η hη hcen hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC : ¬ 2 ∣ Nat.card η.ker := fun h2 =>
    (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
  have hlift : ∀ ρ : Matrix.SpecialLinearGroup (Fin 2) k →* StatedSp r k,
      ∃ ρ' : Matrix.SpecialLinearGroup (Fin 2) k →* P, ∀ g, η (ρ' g) = ρ g := by
    intro ρ
    obtain ⟨ρ', hρ', -⟩ := CFSG.SectionRank.EvenCover.sl2_existsUnique_lift (k := k) hη hcen hC ρ
    exact ⟨ρ', fun g => congrArg (· g) hρ'⟩
  obtain ⟨σ, hσ, -⟩ :=
    CFSG.LieType.Steinberg.sp_existsUnique_section_of_sl2_lift r (p := 2) hη hcen hC hlift
  exact injective_of_section_of_perfect η hcen σ hσ

end CFSG.SeitzReduction.F4Pilot
