module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.PinnedPair
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.ONLocalQ
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Stage3Parts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverBasic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78
  CFSG.Blueprint.NativeSporadic CFSG.ONSchreier Cover


theorem on_card_centralizer {Y : Type} [Group Y] (h : IsSporadic Y .ONan) {a : Y}
    (ha : orderOf a = 2) : Nat.card ↥(centralizer ({a} : Set Y)) = 161280 := by
  obtain ⟨e⟩ := on_equiv_Pv h
  rw [card_centralizer_of_mulEquiv e a,
    pv_card_centralizer _ (by rw [MulEquiv.orderOf_eq]; exact ha)]

theorem on_pinned_pair : ∃ (ut : Pv) (Kt : Subgroup Pv), ut * ut = 1 ∧ ut ≠ 1 ∧
    (∀ k ∈ Kt, k * ut = ut * k) ∧ ⁅Kt, Kt⁆ = Kt ∧ Nat.card Kt = 80640 := by
  have hLP : onL ≤ Pv := onL_le_M.trans onM_le
  refine ⟨zP, onL.subgroupOf Pv, Subtype.ext onz_sq, fun h => onz_ne_one (congrArg Subtype.val h),
    ?_, isPerfect_iff.mp (isPerfect_subgroupOf_of_le hLP onL_isPerfect), ?_⟩
  · intro k hk
    have h1 : (k : Equiv.Perm (Fin N)) ∈ onM := onL_le_M (Subgroup.mem_subgroupOf.1 hk)
    rw [onM_eq_centralizer_z] at h1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 h1.2)
  · rw [card_subgroupOf, inf_of_le_right hLP, card_onL]

theorem on_rowExists (H : Type) [Group H] (L : Subgroup H) (hcov : OddCover .ONan L) :
    ∃ (K : Subgroup H) (u : H), ONQ H L K u := by
  obtain ⟨e⟩ := on_equiv_Pv hcov.2.2
  obtain ⟨ut, Kt, hut, hut1, hKtu, hKt, hcard⟩ := on_pinned_pair
  obtain ⟨K, u, hu, hu2, hKL, hKu, hKperf, hmap⟩ :=
    exists_pair_of_pinned_pair hcov.2.1 e hut hut1 hKtu hKt
  refine ⟨K, u, hu, hu2, hKL, hKu, hKperf, ?_⟩
  rw [hmap, Subgroup.card_map_of_injective e.symm.injective, hcard]

theorem on_rowFit (H : Type) [Group H] (L K : Subgroup H) (hcov : OddCover .ONan L) (hKL : K ≤ L)
    (hKq : CFSG.IsQuasisimple ↥K) (hK : IsOddCentralExt ↥onL (↥K ⧸ CFSG.oddCore ↥K))
    (hstd : SolStd (K.subgroupOf L)) : ∃ u : H, ONQ H L K u := by
  have : Finite ↥L := hcov.finite (by decide : TauCeti.SporadicName.ONan ≠ .M)
  have : Finite ↥K := Finite.of_injective _ (Subgroup.inclusion_injective hKL)
  obtain ⟨t, ht2, hcomp⟩ := hstd.exists_involution
  have hKt : ∀ k ∈ K, k * (t : H) = (t : H) * k := fun k hk => by
    have h1 : (⟨k, hKL hk⟩ : ↥L) ∈ centralizer ({t} : Set ↥L) := hcomp.1 (mem_subgroupOf.2 hk)
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.1 h1)
  have ht2' : orderOf (t : H) = 2 := by rw [Subgroup.orderOf_coe]; exact ht2
  have hqt : orderOf (q ↥L ⟨(t : H), t.2⟩) = 2 := hcov.orderOf_q_involution t.2 ht2'
  have hle : (K.subgroupOf L).map (q ↥L) ≤ centralizer ({q ↥L ⟨(t : H), t.2⟩} : Set _) := by
    rintro _ ⟨k, hk, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hKt k (Subgroup.mem_subgroupOf.1 hk))
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [on_card_centralizer hcov.2.2 hqt] at hdvd
  obtain ⟨hKq', π, hπs, hπc, hπo⟩ := hK
  have hqcard : Nat.card (↥K ⧸ CFSG.oddCore ↥K) = 80640 * Nat.card π.ker := by
    rw [← card_onL, ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπs).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
  have hcard : Nat.card ↥((K.subgroupOf L).map (q ↥L)) = 80640 :=
    card_map_q_eq hKL hcov.2.1 (a := 1) (by norm_num) hπo hqcard (by simpa using hdvd)
  exact ⟨(t : H), t.2, ht2', hKL, hKt, hKq.1, hcard⟩

end CFSG.EvenSporadicStandard.Induction
