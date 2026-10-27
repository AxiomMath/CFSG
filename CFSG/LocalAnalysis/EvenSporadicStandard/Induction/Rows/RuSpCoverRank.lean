module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuCoverRankSection
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuOrders
public import CFSG.RankThree.Classical.SiegelRadical
public import CFSG.LieType.Steinberg.CentralExt.SpCentrallyClosed

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.RankThree.Classical

section Symplectic

variable {K : Type} [Field K] [Finite K]

theorem eq_one_of_mem_siegelRadicalSp_of_scalar {g : StatedSp 2 K} (hg : g ∈ siegelRadicalSp 2 K)
    (h : (g : GL (Fin 2 ⊕ Fin 2) K) ∈ StatedScalars (Fin 2 ⊕ Fin 2) K) : g = 1 := by
  obtain ⟨B, -, hB⟩ := mem_siegelRadicalSp.1 hg
  obtain ⟨c, hc⟩ := h
  have h1 := congrArg (fun g : GL (Fin 2 ⊕ Fin 2) K =>
    (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hc
  have hS : B = 0 := by
    ext i j
    have := congrFun (congrFun h1 (Sum.inl i)) (Sum.inr j)
    change (Matrix.scalar (Fin 2 ⊕ Fin 2) (c : K)) (Sum.inl i) (Sum.inr j) =
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (Sum.inl i)
        (Sum.inr j) at this
    rw [hB] at this
    simpa [Matrix.scalar_apply, Matrix.diagonal_apply] using this.symm
  apply Subtype.ext
  apply Units.ext
  rw [hB, hS]
  simp

theorem three_le_pRank_of_psp_cover {m : ℕ} (hm : 3 ≤ m) (hK : Nat.card K = 2 ^ m) {X : Type}
    [Group X] [Finite X] {φ : X →* StatedProj (StatedSp 2 K)} (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center X) : 3 ≤ CFSG.pRank 2 X := by
  let ρ : StatedSp 2 K →* StatedProj (StatedSp 2 K) :=
    QuotientGroup.mk' ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K))
  have h8 : 8 ≤ Nat.card K := by
    rw [hK]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  obtain ⟨⟨hcomm, hexp⟩, hcard⟩ := siegel_radical_sp Nat.prime_two hK 2
  refine three_le_pRank_of_section (ρ := ρ) (E := siegelRadicalSp 2 K) hφ hker
    (fun E _ _ π hπ hcen =>
      CFSG.LieType.Steinberg.CentralExt.SpClosed.sp_exists_section_of_central
        (n := 2) (by norm_num) (by omega) hπ hcen) ?_ ?_ ?_ ?_
  · intro x hx
    rw [← pow_two]
    exact hexp x hx
  · intro x hx y hy
    exact congrArg Subtype.val (hcomm.is_comm.comm (⟨x, hx⟩ : siegelRadicalSp 2 K) ⟨y, hy⟩)
  · rw [hcard]
    calc 8 ≤ 2 ^ 3 := by norm_num
      _ ≤ (2 ^ m) ^ (2 * (2 + 1) / 2) := by
        calc 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
          _ = (2 ^ m) ^ 1 := (pow_one _).symm
          _ ≤ (2 ^ m) ^ (2 * (2 + 1) / 2) := Nat.pow_le_pow_right (by positivity) (by norm_num)
  · intro x hx hx1
    have h1 : ((x : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) ∈ StatedScalars (Fin 2 ⊕ Fin 2) K :=
      (Subgroup.mem_subgroupOf).1 ((QuotientGroup.eq_one_iff _).1 hx1)
    exact eq_one_of_mem_siegelRadicalSp_of_scalar hx h1

end Symplectic

theorem three_le_pRank_of_psp_model_cover {m : ℕ} (hm : 3 ≤ m) {X : Type} [Group X] [Finite X]
    (h : LieModel (X ⧸ center X) .PSp 2 2 m) : 3 ≤ CFSG.pRank 2 X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := statedClassicalModel_of_lieModel_ne_zero (by norm_num) h
  let φ : X →* StatedProj (StatedSp 2 K) := e.toMonoidHom.comp (QuotientGroup.mk' (center X))
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker ≤ center X := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    exact hx
  exact three_le_pRank_of_psp_cover hm hK hφ hker

end CFSG.EvenSporadicStandard.Induction
