module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.PSLType

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeRankOne
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Universal.SpecialLinear
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabHub
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open Matrix CFSG.AGLEmbedding
open scoped commutatorElement

section Reindex

variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] {R : Type}
  [CommRing R]

@[expose] noncomputable def slReindexEquiv (e : m ≃ n) :
    SpecialLinearGroup m R ≃* SpecialLinearGroup n R where
  toFun A := ⟨reindex e e (A : Matrix m m R), by rw [det_reindex_self]; exact A.2⟩
  invFun A := ⟨reindex e.symm e.symm (A : Matrix n n R), by rw [det_reindex_self]; exact A.2⟩
  left_inv A := Subtype.ext (by simp)
  right_inv A := Subtype.ext (by simp)
  map_mul' A B := Subtype.ext (by
    change reindex e e ((A : Matrix m m R) * (B : Matrix m m R)) =
      reindex e e (A : Matrix m m R) * reindex e e (B : Matrix m m R)
    rw [reindex_apply, reindex_apply, reindex_apply, submatrix_mul_equiv])

end Reindex

theorem isQuasisimple_of_simple {S : Type} [Group S] (hs : IsSimpleGroup S)
    (hnc : ∃ a b : S, a * b ≠ b * a) : CFSG.IsQuasisimple S := by
  have hcomm : commutator S = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      apply hab
      have : ⁅a, b⁆ ∈ commutator S := Subgroup.commutator_mem_commutator (Subgroup.mem_top a)
        (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot] at this
      exact commutatorElement_eq_one_iff_mul_comm.mp this
    · exact h
  have hcenter : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      apply hab
      have : a ∈ Subgroup.center S := by rw [h]; exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp this b).symm
  have e : S ⧸ Subgroup.center S ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  refine ⟨Group.isPerfect_def.mpr hcomm, (MulEquiv.isSimpleGroup_congr e).mpr hs, ?_⟩
  obtain ⟨a, b, hab⟩ := hnc
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

theorem isChevComponent_sl {k : ℕ} {F : Type} [Field F] [Finite F]
    [CharP F 2] (hk : 3 ≤ k ∨ (k = 2 ∧ 4 ≤ Nat.card F)) :
    CFSG.IsQuasisimple (SpecialLinearGroup (Fin k) F) ∧
      IsClassicalTwoOrG2 (SpecialLinearGroup (Fin k) F ⧸ Subgroup.center (SpecialLinearGroup (Fin k) F)) := by
  obtain ⟨f, hf1, hfcard⟩ := CFSG.AGLEmbedding.ParabHub.exists_card_eq_two_pow F
  have hk2 : 2 ≤ k := by omega
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hquasi : CFSG.IsQuasisimple (SpecialLinearGroup (Fin (m + 1)) F) := by
    rcases hk with hk3 | ⟨hk2', hF4⟩
    · exact CFSG.LieType.Universal.SpecialLinear.isQuasisimple m F (by omega)
    · have hm : m = 1 := by omega
      subst hm
      refine isQuasisimple_of_simple (CFSG.AGLEmbedding.ParabPrime.sl2_isSimpleGroup (k := F) hF4) ?_
      exact ⟨_, _, CFSG.AGLEmbedding.ParabHub.sl2_upper_lower_not_commute (F := F)⟩
  refine ⟨hquasi, ?_⟩
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL (m + 1) 2 f := by
    refine ⟨Nat.prime_two, hf1, hk2, ?_, ?_⟩
    · intro h
      have h1 : m + 1 = 2 := (Prod.mk.inj h).1
      have h2 : 2 ^ f = 2 := (Prod.mk.inj h).2
      rcases hk with hk3 | ⟨-, hF4⟩
      · omega
      · rw [hfcard] at hF4; omega
    · intro h
      have h2 : 2 ^ f = 3 := (Prod.mk.inj h).2
      have : 2 ^ f % 2 = 0 := by
        rw [Nat.pow_mod]; simp [Nat.zero_pow (by omega : 0 < f)]
      omega
  exact isClassicalTwoOrG2_of_statedPSL
    (CFSG.LieType.Universal.SpecialLinear.statedClassicalModel_center_quotient m F hadm hfcard)

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
