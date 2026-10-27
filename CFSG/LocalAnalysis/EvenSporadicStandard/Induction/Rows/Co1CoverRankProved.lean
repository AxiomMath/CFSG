module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1Hyp31C
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.MultSporadic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CentralLift
public import CFSG.LieType.Steinberg.CentralExt.G2FourMultiplier
public import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels
public import CFSG.LieType.SteinbergBRTwoRankBound

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.EvenSporadicStandard.Induction.Hyp

theorem three_le_pRank_of_central_quotient {X : Type} [Group X] [Finite X] {Q : Type} [Group Q]
    (π : X →* Q) (hπ : Function.Surjective π) (hker : π.ker ≤ center X)
    (hZ : Nat.card π.ker ≤ 2) (V : Subgroup Q) [IsElementaryAbelian 2 V] {n : ℕ} (hn : 5 ≤ n)
    (hV : 2 ^ n ≤ Nat.card V) : 3 ≤ CFSG.pRank 2 X := by
  have hr : ∀ A : Subgroup X, A ≤ π.ker → (∀ a ∈ A, a * a = 1) → Nat.card A ≤ 2 ^ 1 :=
    fun A hA _ => (Subgroup.card_le_of_le hA).trans hZ
  obtain ⟨A, hA, k, hk3, hAk⟩ := exists_elementaryAbelian_of_quotient π hπ hker hr V hV
    (t := 3) (by intro k hk; omega)
  exact hk3.trans (CFSG.LieType.SteinbergBR.le_pRank_of_card (by norm_num) A hA hAk)

theorem three_le_pRank_of_quotient_co1
    (hSM : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers) {X : Type} [Group X] [Finite X]
    (hq : CFSG.IsQuasisimple X) (hS : IsSporadic (X ⧸ center X) .Co1) : 3 ≤ CFSG.pRank 2 X := by
  have h := card_center_dvd_of_sporadicMultipliers (s := .Co1) hSM
    CFSG.Sporadic.Bridge.Co1.nonempty_mulEquiv hq hS
  have hZ : Nat.card (center X) ∣ 2 := by
    have e : CFSG.RankThree.PartTwo.Sec4.Census.sporadicMultiplierOrder .Co1 = 2 := by decide
    rwa [e] at h
  obtain ⟨E, hE, hcard⟩ :=
    (CFSG.RankThree.PartOne.N143.co1_two_rank_at_least_five (X ⧸ center X) hS).1
  have := hE
  refine three_le_pRank_of_central_quotient (QuotientGroup.mk' (center X))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']) ?_ E (n := 5) le_rfl
    (by rw [hcard])
  rw [QuotientGroup.ker_mk']
  exact Nat.le_of_dvd (by norm_num) hZ

theorem three_le_pRank_of_quotient_g2
    {n : ℕ} (hn : 2 ≤ n) {X : Type} [Group X] [Finite X] (hq : CFSG.IsQuasisimple X)
    (hm : LieModel (X ⧸ center X) .G2 0 2 n) : 3 ≤ CFSG.pRank 2 X := by
  obtain ⟨-, hM⟩ := CFSG.LieType.Steinberg.CentralExt.GriessNative.chevalley_of_lieModel hm
    (by decide)
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hM
  have : CharP K 2 :=
    CFSG.LieType.Steinberg.CentralExt.GriessNative.charP_two_of_card (by omega) hK rfl
  let eC : AdjointQuotient .G2 K ≃* ↥(adjointGroup .G2 K) :=
    (QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot
  let f : X ⧸ center X ≃* ↥(adjointGroup .G2 K) := e.trans eC
  have hperf : Group.IsPerfect X := hq.1
  have hZ : Nat.card (center X) ≤ 2 := by
    rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
    · have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
      let η : X →* ↥(adjointGroup .G2 K) := f.toMonoidHom.comp (QuotientGroup.mk' (center X))
      have hη : Function.Surjective η := f.surjective.comp (QuotientGroup.mk'_surjective _)
      have hηk : η.ker = center X := by
        ext x
        rw [MonoidHom.mem_ker]
        change f (QuotientGroup.mk' (center X) x) = 1 ↔ _
        rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      have := CFSG.LieType.Steinberg.CentralExt.G2Four.g2_four_card_ker_le_two hK4 η hη hηk.le
      rwa [hηk] at this
    · have h5 : 5 ≤ Nat.card K := by
        rw [hK]
        calc 5 ≤ 2 ^ 3 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
      obtain ⟨-, hsub⟩ := CFSG.LieType.Steinberg.CentralExt.AdjointClosed.g2_hopfMultiplier h5
      have hdvd := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq e
      have h1 : Nat.card
          (CFSG.RankThree.PerfectCover.hopfMultiplier (AdjointQuotient .G2 K)) = 1 := by
        rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv]
        exact Nat.card_of_subsingleton 1
      rw [h1] at hdvd
      exact (Nat.le_of_dvd one_pos hdvd).trans (by norm_num)
  let Φ : Multiplicative K × Multiplicative K × Multiplicative K →* X ⧸ center X :=
    f.symm.toMonoidHom.comp g2RootProd
  have hΦ : Function.Injective Φ := f.symm.injective.comp g2RootProd_injective
  have hsq : ∀ z : Multiplicative K, z * z = 1 := fun z => by
    rw [← pow_two]
    change Multiplicative.ofAdd (2 • Multiplicative.toAdd z) = 1
    rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
    rfl
  let V : Subgroup (X ⧸ center X) := Φ.range
  have hVE : IsElementaryAbelian 2 V := isElementaryAbelian_of_sq_eq_one V
    (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul, mul_comm a b])
    (by
      rintro _ ⟨a, rfl⟩
      rw [← map_mul]
      have : a * a = 1 := Prod.ext (hsq _) (Prod.ext (hsq _) (hsq _))
      rw [this, map_one])
  have hVcard : Nat.card V = 2 ^ (3 * n) := by
    show Nat.card Φ.range = _
    rw [Nat.card_congr (MonoidHom.ofInjective hΦ).toEquiv.symm, Nat.card_prod, Nat.card_prod,
      show Nat.card (Multiplicative K) = Nat.card K from Nat.card_congr Multiplicative.toAdd, hK]
    ring
  exact three_le_pRank_of_central_quotient (QuotientGroup.mk' (center X))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk'])
    (by rw [QuotientGroup.ker_mk']; exact hZ) V (n := 3 * n) (by omega) hVcard.ge

theorem co1CoverRank_proved
    (hSM : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers) : Co1CoverRank :=
  ⟨fun _ _ _ hq hS _ => three_le_pRank_of_quotient_co1 hSM hq hS,
    fun _ hn _ _ _ hq hm => three_le_pRank_of_quotient_g2 hn hq hm⟩

end CFSG.EvenSporadicStandard.Induction
