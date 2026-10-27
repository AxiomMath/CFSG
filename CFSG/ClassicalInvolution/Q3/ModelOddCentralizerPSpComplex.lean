module

public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerSpGauss
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerCentralKernel

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.ModelFacts CFSG.ComponentClassification CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)

section Complex

variable {F : Type} [Field F] [Finite F] [hF3 : Fact (Nat.card F = 3)] {m : ℕ}

theorem oddCoreIn_centralizer_gComplex_eq_bot (hm : 2 ≤ m) :
    oddCoreIn (Subgroup.centralizer
      ({(QuotientGroup.mk (gComplex m) : StatedSp m F ⧸ Subgroup.center (StatedSp m F))} :
        Set (StatedSp m F ⧸ Subgroup.center (StatedSp m F)))) = ⊥ := by
  have hk : Nat.card F = 2 ^ 1 + 1 := by rw [hF3.out]; norm_num
  have hZ : IsPGroup 2 (Subgroup.center (StatedSp m F)) :=
    (centerExp_statedSp m 1 F hk).isPGroup
  set π := QuotientGroup.mk' (Subgroup.center (StatedSp m F)) with hπ
  refine oddCoreIn_centralizer_eq_bot_of_blocks hZ (gComplex m) (ι := Unit)
    (fun _ => (suToSp (F := F) m).range) ?_ ?_ ?_ ?_
  · rintro - x ⟨X, rfl⟩
    exact suToSp_mem_centralizer X
  · intro _ b hb x hx
    exact conj_mem_range_suToSp hb hx
  · intro _
    show oddCoreIn ((suToSp (F := F) m).range.map π) = ⊥
    rw [← MonoidHom.range_comp]
    refine oddCoreIn_range_eq_bot_of_central_kernel (π.comp (suToSp m))
      (componentOddCore_su_eq_bot m) ?_ ?_
    · intro X hX
      have h1 : suToSp m X ∈ Subgroup.center (StatedSp m F) :=
        (QuotientGroup.eq_one_iff _).mp hX
      rw [Subgroup.mem_center_iff]
      intro Y
      apply suToSp_injective
      rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.mp h1 (suToSp m Y)
    · intro X
      obtain ⟨k, hk⟩ := hZ ⟨suToSp m X.1, (QuotientGroup.eq_one_iff _).mp X.2⟩
      refine ⟨k, Subtype.ext (suToSp_injective ?_)⟩
      simpa using congrArg Subtype.val hk
  · intro ν hν hL
    exact ⟨2, by simpa using
      exists_pow_four_of_commute_range_suToSp hm hν fun y hy => hL () y hy⟩

end Complex

end CFSG.ClassicalInvolution.Q3
