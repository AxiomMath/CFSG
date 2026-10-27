module

public import CFSG.LieType.SemisimpleCentralizers.HeldLangCoverLift
public import CFSG.LieType.SemisimpleCentralizers.HeldLangI5LinCover

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldLang

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.PerfectAutomorphisms

theorem card_center_SL_eq {K : Type} [Field K] [Finite K] {N : ℕ} [NeZero N] :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin N) K)) = Nat.gcd N (Nat.card K - 1) := by
  refine le_antisymm card_center_SL_le ?_
  have e := Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (n := Fin N) (R := K)
    ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩
  rw [Nat.card_congr e.toEquiv, Fintype.card_fin]
  haveI : NeZero (Nat.gcd N (Nat.card K - 1)) :=
    ⟨(Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne N))).ne'⟩
  have hcard := CFSG.LinearGroups.card_rootsOfUnity_of_dvd (K := K)
    (d := Nat.gcd N (Nat.card K - 1)) (Nat.gcd_dvd_right _ _)
  have hle : rootsOfUnity (Nat.gcd N (Nat.card K - 1)) K ≤ rootsOfUnity N K :=
    rootsOfUnity_le_of_dvd (Nat.gcd_dvd_left _ _)
  calc Nat.gcd N (Nat.card K - 1) = Nat.card (rootsOfUnity (Nat.gcd N (Nat.card K - 1)) K) := hcard.symm
    _ ≤ Nat.card (rootsOfUnity N K) :=
        Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)

theorem isCyclic_center_SL {K : Type} [Field K] [Finite K] {N : ℕ} [NeZero N] :
    IsCyclic (Subgroup.center (Matrix.SpecialLinearGroup (Fin N) K)) := by
  have e := Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (n := Fin N) (R := K)
    ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

theorem isI5UniversalCover_SL (n : ℕ) (q : TauCeti.PrimePower) (hd : (TauCeti.LieTypeIndex.A n q).Valid)
    (hN : 3 ≤ n + 1) [Fact q.p.Prime]
    (hsimple : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin (n + 1)) (GaloisField q.p q.exponent) ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (n + 1)) (GaloisField q.p q.exponent)))) :
    IsI5UniversalCover ⟨.A n q, hd⟩ (Matrix.SpecialLinearGroup (Fin (n + 1)) (GaloisField q.p q.exponent)) := by
  have hcardF : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  refine ⟨⟨(CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hN).commutator_eq_top, hsimple⟩,
    ⟨(CFSG.ClassicalModels.linearCatalogCandidateEquivPSL n q hd).symm⟩, isCyclic_center_SL, ?_⟩
  rw [card_center_SL_eq, hcardF]
  rfl

theorem false_of_outer_three_A_small' (n : ℕ) (q : TauCeti.PrimePower)
    (hd : (TauCeti.LieTypeIndex.A n q).Valid) (h3n : 3 ∣ n + 1) (hq8 : q.card < 8) {Q : Type} [Group Q]
    (e0 : Q ≃* (TauCeti.CFSGIndex.lie ⟨.A n q, hd⟩).Group) (γ : MulAut Q) (hγ3 : γ ^ 3 = 1)
    (hout : γ ∉ innAutDerived Q) : False := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  let e' : Q ≃* projectiveSL (n + 1) (GaloisField q.p q.exponent) :=
    (e0.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL n q hd)).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (n + 1) _)
  have hN : 3 ≤ n + 1 := Nat.le_of_dvd (by omega) h3n
  have hβ'3 : MulAut.congr e' γ ^ 3 = 1 := by
    rw [← map_pow, hγ3, map_one]
  have hout' : MulAut.congr e' γ ∉ innAutDerived (projectiveSL (n + 1) (GaloisField q.p q.exponent)) :=
    fun h => hout ((mem_innAutDerived_congr e').1 h)
  obtain ⟨A, σ, -, hσ, -⟩ := exists_sigma_of_outer_three hN _ hβ'3 hout'
  have hdvd := orderOf_dvd_of_card q.prime_p q.exponent_pos
    (GaloisField.card q.p q.exponent q.exponent_pos.ne') σ
  rw [hσ] at hdvd
  have h3e : 3 ≤ q.exponent := Nat.le_of_dvd q.exponent_pos hdvd
  have h8 : 2 ^ 3 ≤ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact (Nat.pow_le_pow_left q.prime_p.two_le 3).trans (Nat.pow_le_pow_right q.prime_p.pos h3e)
  omega

theorem kd264I5CoverLift_linear (n : ℕ) (q : TauCeti.PrimePower) (hd : (TauCeti.LieTypeIndex.A n q).Valid)
    (h3n : 3 ∣ n + 1) (h3q : 3 ∣ q.card - 1)
    (K : Type) [Group K] [Finite K] (hK : CFSG.Open.IsQuasisimple K)
    (eK : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie ⟨.A n q, hd⟩).Group)
    (β : MulAut K) (hβ3 : β ^ 3 = 1)
    (hout : onCenterQuotient β ∉ innAutDerived (K ⧸ Subgroup.center K)) :
    ∃ (L : Type) (_ : Group L) (_ : Finite L) (π : L →* K) (βL : MulAut L),
      Function.Surjective π ∧ (∀ x : L, π x = 1 → x ∈ Subgroup.center L) ∧
        IsI5UniversalCover ⟨.A n q, hd⟩ L ∧ βL ^ 3 = 1 ∧ ∀ x : L, π (βL x) = β (π x) := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  by_cases hq8 : q.card < 8
  · exfalso
    have hγ3 : onCenterQuotient β ^ 3 = 1 := by
      have := congrArg (centerQuotientHom K) hβ3
      rwa [map_pow, map_one] at this
    exact false_of_outer_three_A_small' n q hd h3n hq8 eK (onCenterQuotient β) hγ3 hout
  · have hN : 3 ≤ n + 1 := Nat.le_of_dvd (by omega) h3n
    have hn2 : 2 ≤ n := by omega
    have hcardF : Nat.card (GaloisField q.p q.exponent) = q.card := by
      rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', TauCeti.PrimePower.card_def]
    let eP : Matrix.SpecialLinearGroup (Fin (n + 1)) (GaloisField q.p q.exponent) ⧸
        Subgroup.center (Matrix.SpecialLinearGroup (Fin (n + 1)) (GaloisField q.p q.exponent)) ≃*
        (TauCeti.CFSGIndex.lie ⟨.A n q, hd⟩).Group :=
      (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL n q hd).symm
    let ι : Matrix.SpecialLinearGroup (Fin (n + 1)) (GaloisField q.p q.exponent) ⧸
        Subgroup.center (Matrix.SpecialLinearGroup (Fin (n + 1)) (GaloisField q.p q.exponent)) ≃*
        K ⧸ Subgroup.center K := eP.trans eK.symm
    have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin (n + 1)) (GaloisField q.p q.exponent)) :=
      CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hN
    have hsec : ∀ (E : Type) [Group E] [Finite E]
        (π : E →* Matrix.SpecialLinearGroup (Fin (n + 1)) (GaloisField q.p q.exponent)),
        Function.Surjective π → π.ker ≤ Subgroup.center E →
        ∃ s : Matrix.SpecialLinearGroup (Fin (n + 1)) (GaloisField q.p q.exponent) →* E, ∀ g, π (s g) = g :=
      fun E _ _ π hπ hc => CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_central hn2
        (by rw [hcardF]; omega) hπ hc
    obtain ⟨π, βL, hπ, hπc, hβL3, hβL⟩ := exists_cover_lift_of_equiv hK hperf ι hsec β hβ3
    haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2
    refine ⟨_, inferInstance, inferInstance, π, βL, hπ, hπc, ?_, hβL3, hβL⟩
    exact isI5UniversalCover_SL n q hd hN ι.isSimpleGroup

end CFSG.LieType.SemisimpleCentralizers.HeldLang
