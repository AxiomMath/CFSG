module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912Core
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieSp6
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.D4Dichotomy
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.SpTwoAux.Centralizer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD1912

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.GLTheoremA.LevelLieSp6
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open scoped commutatorElement

theorem oddCoreFact_three_statedProj_three_two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    OddCoreFact 3 (StatedProj (StatedSp 3 K)) := by
  classical
  have hρinj : Function.Injective (proj 3 K) := proj_injective_of_card_two hK
  have hρsurj : Function.Surjective (proj 3 K) := QuotientGroup.mk'_surjective _
  let ρ := proj 3 K
  let eProj : StatedSp 3 K ≃* StatedProj (StatedSp 3 K) :=
    MulEquiv.ofBijective ρ ⟨hρinj, hρsurj⟩
  have hZ : Subgroup.center (StatedProj (StatedSp 3 K)) = ⊥ := by
    have h1 : Subgroup.map (eProj : StatedSp 3 K →* StatedProj (StatedSp 3 K))
        (Subgroup.center (StatedSp 3 K)) = Subgroup.center (StatedProj (StatedSp 3 K)) :=
      Subgroup.map_center_eq eProj
    rw [← h1, W2.center_statedSp_eq_bot hK 3, Subgroup.map_bot]
  have hinj := mulAutConj_injective_of_center_eq_bot hZ
  constructor
  ·
    have hinnerAut : innerAut (StatedProj (StatedSp 3 K)) = ⊤ := by
      rw [eq_top_iff]
      intro α _
      obtain ⟨t, rfl⟩ := inner_of_card_two hK α
      exact ⟨t, rfl⟩
    have hinner : CFSG.ComponentClassification.OuterAutomorphisms.inner
        (StatedProj (StatedSp 3 K)) = ⊤ := by
      rw [← innerAut_eq_inner]
      exact hinnerAut
    refine ⟨⊤, inferInstance, le_top, ?_, fun α => ⟨0, Subgroup.mem_top α⟩⟩
    rw [hinner]
    simp
  ·
    intro x hx
    obtain ⟨t, ht⟩ := inner_of_card_two hK x
    subst ht
    have htord : orderOf t = 3 := by
      rw [← orderOf_injective (MulAut.conj :
        StatedProj (StatedSp 3 K) →* MulAut (StatedProj (StatedSp 3 K))) hinj t]
      exact hx
    have ht3 : t ^ 3 = 1 := by simpa only [htord] using pow_orderOf_eq_one t
    have ht1 : t ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at htord
      omega
    rw [innerAut_inf_centralizer_conj hZ t,
      card_gLAPPrimeCoreOf_map_of_injective 3 _ hinj
        (Subgroup.centralizer ({t} : Set (StatedProj (StatedSp 3 K))))]
    obtain ⟨u, hu⟩ := hρsurj t
    have hu3 : u ^ 3 = 1 := by
      apply hρinj
      rw [map_pow, hu, ht3, map_one]
    have hu1 : u ≠ 1 := by
      rintro rfl
      exact ht1 (by rw [← hu, map_one])
    have hC : Subgroup.centralizer ({t} : Set (StatedProj (StatedSp 3 K))) =
        (Subgroup.centralizer ({u} : Set (StatedSp 3 K))).map ρ := by
      rw [← hu]
      exact (CFSG.centralizer_singleton_map eProj u).symm
    have hNN : NoNormalPPrime 3 (Subgroup.centralizer ({u} : Set (StatedSp 3 K))) :=
      W2.noNormalPPrime_three_centralizer_statedSp hK (by norm_num) hu3 hu1
    have hO : GLAPPrimeCoreOf 3
        (Subgroup.centralizer ({t} : Set (StatedProj (StatedSp 3 K)))) = ⊥ := by
      rw [hC]
      exact W2.core_eq_bot_of_noNormalPPrime Nat.prime_three
        ((W2.noNormalPPrime_map_iff ρ hρinj _).2 hNN)
    rw [hO, Subgroup.card_bot]
    exact odd_one

theorem oddCoreFact_three_of_B3_two {S : Type} [Group S] [Finite S]
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.B 3 q).Valid) (hq : q.card = 2)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B 3 q, hv⟩).Group) :
    OddCoreFact 3 S := by
  classical
  obtain ⟨hA, hB⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq (q := q) (s := 1)
    Nat.prime_two (by norm_num) (by rw [hq]; norm_num)
  let K := TauCeti.ValidLieTypeIndex.fixedField ⟨TauCeti.LieTypeIndex.B 3 q, hv⟩
  have hKc : Nat.card K = 2 := by
    rw [show Nat.card K = q.p ^ q.exponent from
      CFSG.Models.card_fixedField_of (TauCeti.LieTypeIndex.characteristic_B 3 q)
        (TauCeti.LieTypeIndex.fieldExponent_B 3 q)]
    rw [hA, hB]
    norm_num
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hKc]; norm_num)
  have eT : S ≃* StatedProj (StatedSp 3 K) :=
    e.trans (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj 3 q hv hA
      (le_refl 3))
  exact (oddCoreFact_congr (p := 3) eT).mpr (oddCoreFact_three_statedProj_three_two hKc)

end CFSG.LocalAnalysis.GLTheoremA.KD1912
