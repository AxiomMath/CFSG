module

public import CFSG.HardMathSupport.Solomon.Proving.HopfLiftPrime
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6B67
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3317A
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.CoverOdd
import CFSG.Adapters.StatedSLPerfect
public import CFSG.Quasithin.Background.S1567ASymm

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.RankThree.PerfectCover

theorem pCore_three_le_center_of_quasisimple {Y : Type} [Group Y] [Finite Y]
    (hq : CFSG.Open.IsQuasisimple Y) : CFSG.pCore 3 Y ≤ Subgroup.center Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq
      (CFSG.pCore 3 Y) with h | h
  · exact h
  · exfalso
    have hY : IsPGroup 3 Y := fun g => by
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 3) (G := Y))
        ⟨g, by rw [h]; exact Subgroup.mem_top g⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have : Group.IsNilpotent Y := hY.isNilpotent
    have : Nontrivial (Y ⧸ Subgroup.center Y) := hq.2.toNontrivial
    have : Nontrivial Y := (QuotientGroup.mk'_surjective (Subgroup.center Y)).nontrivial
    have : Group.IsPerfect Y := ⟨hq.1⟩
    exact (Group.IsPerfect.not_isSolvable (G := Y)) inferInstance

theorem card_center_statedSL_three_four {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    Nat.card (Subgroup.center (StatedSL 3 K)) = 3 :=
  CFSG.Quasithin.Vol2.Ch11.SecA.C10KG.card_center_statedSL_three (by simp [hK])

theorem isPerfect_statedSL_three (K : Type) [Field K] : Group.IsPerfect (StatedSL 3 K) :=
  CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le (by norm_num) K

theorem card_hopfMultiplier_statedProj_three_four {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) :
    Nat.card (hopfMultiplier (StatedProj (StatedSL 3 K))) = 48 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e := CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K 3 2 2 (by norm_num)
    (hK.trans (by norm_num))
  have h1 : Nat.card (hopfMultiplier (StatedProj (StatedSL 3 K))) =
      Nat.card (hopfMultiplier (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField 2 2))) :=
    CFSG.Quasithin.H13.L3317.card_hopfMultiplier_congr e
  rw [h1, ← Nat.card_congr
    (hopfMultiplierEquivGriess (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField 2 2))).toEquiv]
  obtain ⟨g⟩ := (CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_three_four_hopfMultiplier).2
  rw [Nat.card_congr g.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_prod,
    Nat.card_prod, Nat.card_zmod, Nat.card_zmod]

theorem inputL34Cover_holds :
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.InputL34Cover := by
  unfold CFSG.HardMathSupport.Solomon.UniquenessMaximal.InputL34Cover
  intro Y _ _ hq hL
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, hKf, hKfin, hK, ⟨e⟩⟩ := hL
  let N₀ : Subgroup (StatedSL 3 K) := (StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K)
  have hN₀ : N₀ = Subgroup.center (StatedSL 3 K) :=
    (CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.center_statedSL_eq_scalars K).symm
  let p₀ : StatedSL 3 K →* StatedProj (StatedSL 3 K) := QuotientGroup.mk' N₀
  have hp₀ : Function.Surjective p₀ := QuotientGroup.mk'_surjective _
  have hp₀ker : p₀.ker = N₀ := QuotientGroup.ker_mk' N₀
  have hk₀ : p₀.ker ≤ Subgroup.center (StatedSL 3 K) := by rw [hp₀ker, hN₀]
  have hp₀card : Nat.card p₀.ker = 3 := by
    rw [hp₀ker, hN₀]
    exact card_center_statedSL_three_four hK
  let q : Y →* StatedProj (StatedSL 3 K) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 3 Y))
  have hqs : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqker : q.ker ≤ CFSG.pCore 3 Y := by
    intro x hx
    have h1 : e (x : Y ⧸ CFSG.pCore 3 Y) = 1 := (MonoidHom.mem_ker).1 hx
    exact (QuotientGroup.eq_one_iff x).1 (e.map_eq_one_iff.1 h1)
  have hk : q.ker ≤ Subgroup.center Y := hqker.trans (pCore_three_le_center_of_quasisimple hq)
  have hpgrp : IsPGroup 3 q.ker := fun g => by
    obtain ⟨k, hk'⟩ := (CFSG.pCore_isPGroup (p := 3) (G := Y)) ⟨g.1, hqker g.2⟩
    exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk')⟩
  have hS₀ : Group.IsPerfect (StatedSL 3 K) := isPerfect_statedSL_three K
  have hE : Group.IsPerfect Y := ⟨hq.1⟩
  have hcard : Nat.card (hopfMultiplier (StatedProj (StatedSL 3 K))) = Nat.card p₀.ker * 16 := by
    have h48 := card_hopfMultiplier_statedProj_three_four hK
    rw [hp₀card]
    omega
  obtain ⟨α, hαs, hαq⟩ := exists_lift_of_coprime_index (p := 3) hS₀ hE p₀ hp₀ hk₀ q hqs hk hpgrp
    16 (by norm_num) hcard
  have hkerle : α.ker ≤ p₀.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have h := congrArg (fun f => f x) hαq
    simp only [MonoidHom.comp_apply] at h
    rw [hx, map_one] at h
    exact h.symm
  have hdvd : Nat.card α.ker ∣ 3 := by
    have h := Subgroup.card_dvd_of_le hkerle
    rwa [hp₀card] at h
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
  ·
    have hbot : α.ker = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    have hinj : Function.Injective α := (MonoidHom.ker_eq_bot_iff α).1 hbot
    let φ : StatedSL 3 K ≃* Y := MulEquiv.ofBijective α ⟨hinj, hαs⟩
    refine Or.inr ?_
    unfold IsSLThreeFour
    exact ⟨K, hKf, hKfin, hK, ⟨φ.symm⟩⟩
  ·
    have hEq : α.ker = p₀.ker :=
      Subgroup.eq_of_le_of_card_ge hkerle (by rw [h3, hp₀card])
    let φ : Y ≃* StatedProj (StatedSL 3 K) :=
      ((QuotientGroup.quotientKerEquivOfSurjective α hαs).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hEq)).trans
        (QuotientGroup.quotientKerEquivOfSurjective p₀ hp₀)
    refine Or.inl ?_
    unfold IsLThreeFour
    exact ⟨K, hKf, hKfin, hK, ⟨φ⟩⟩

end CFSG.HardMathSupport.Solomon.Proving

end
