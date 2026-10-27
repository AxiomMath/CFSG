module

public import CFSG.LieType.SemisimpleCentralizers.HeldLangCoverLift
public import CFSG.LieType.SemisimpleCentralizers.HeldLangI5UniCover
public import CFSG.LieType.Steinberg.CentralExt.UnitaryPerfect

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldLang

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.ComponentClassification.PerfectAutomorphisms
  CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary

theorem center_statedSU_eq {K : Type} [Field K] {p f N : ℕ} (hdat : UnitaryFieldData p f K) (hN : 3 ≤ N) :
    Subgroup.center ↥(StatedSU N (p ^ f) K) =
      (StatedScalars (Fin N) K).subgroupOf (StatedSU N (p ^ f) K) := by
  haveI : Finite K := hdat.finite
  haveI : Fact p.Prime := ⟨hdat.prime⟩
  haveI : CharP K p := hdat.charP
  have hK : Nat.card K = (p ^ f) ^ 2 := by rw [hdat.card, ← pow_mul, Nat.mul_comm]
  have hbar : IsUnitaryInvolution (unitaryInvolution K p f) := isUnitaryInvolution_unitaryInvolution hK
  have hS : StatedSU N (p ^ f) K = SUid (unitaryInvolution K p f) N := (SUid_eq_statedSU hK N).symm
  rw [hS]
  exact CFSG.ClassicalInvolution.Phan.center_SUid_eq hbar hN

theorem isI5UniversalCover_SU (n : ℕ) (q : TauCeti.PrimePower) (hd : (TauCeti.LieTypeIndex.twistedA n q).Valid)
    (hN : 3 ≤ n + 1) {F : Type} [Field F] (hdat : UnitaryFieldData q.p q.exponent F)
    (eM : (TauCeti.CFSGIndex.lie ⟨.twistedA n q, hd⟩).Group ≃*
      StatedProj (StatedSU (n + 1) (q.p ^ q.exponent) F))
    (hsimple : IsSimpleGroup (↥(StatedSU (n + 1) (q.p ^ q.exponent) F) ⧸
      Subgroup.center ↥(StatedSU (n + 1) (q.p ^ q.exponent) F))) :
    IsI5UniversalCover ⟨.twistedA n q, hd⟩ ↥(StatedSU (n + 1) (q.p ^ q.exponent) F) := by
  haveI : Finite F := hdat.finite
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  haveI : CharP F q.p := hdat.charP
  have hK : Nat.card F = (q.p ^ q.exponent) ^ 2 := by rw [hdat.card, ← pow_mul, Nat.mul_comm]
  have hNq := not_three_two_of_valid n q hd hN
  have hperf : Group.IsPerfect ↥(StatedSU (n + 1) (q.p ^ q.exponent) F) :=
    isPerfect_statedSU hK hN (fun h => hNq ⟨(Prod.mk.inj h).1, (Prod.mk.inj h).2⟩)
  have hc := center_statedSU_eq hdat hN
  have hcard := (CFSG.LinearGroups.unitary_scalar_kernel q.prime_p hK (n := n + 1) (by omega)).2.2
  have hcardq : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  refine ⟨⟨hperf.commutator_eq_top, hsimple⟩, ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans eM.symm⟩, ?_, ?_⟩
  · obtain ⟨hcyc, -⟩ := CFSG.LieType.Steinberg.isCyclic_scalars_statedSU hK (n := n + 1) (by omega)
    exact isCyclic_of_surjective (MulEquiv.subgroupCongr hc).symm.toMonoidHom
      (MulEquiv.subgroupCongr hc).symm.surjective
  · rw [Nat.card_congr (MulEquiv.subgroupCongr hc).toEquiv, hcard]
    show _ = Nat.gcd (n + 1) (q.card + 1)
    rw [hcardq]

theorem false_of_outer_three_twistedA_small' (n : ℕ) (q : TauCeti.PrimePower)
    (hd : (TauCeti.LieTypeIndex.twistedA n q).Valid) (hN : 3 ≤ n + 1) (hq8 : q.card < 8) {Q : Type} [Group Q]
    (e0 : Q ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA n q, hd⟩).Group) (γ : MulAut Q) (hγ3 : γ ^ 3 = 1)
    (hout : γ ∉ innAutDerived Q) : False := by
  obtain ⟨-, F, hF, hfin, hK, ⟨eM⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA n q hd (MulEquiv.refl _)
  have hdat : UnitaryFieldData q.p q.exponent F :=
    ⟨q.prime_p, q.exponent_pos, by rw [hK, ← pow_mul, mul_comm]⟩
  have hNq := not_three_two_of_valid n q hd hN
  let e' : Q ≃* StatedProj (StatedSU (n + 1) (q.p ^ q.exponent) F) := e0.trans eM
  have hβ'3 : MulAut.congr e' γ ^ 3 = 1 := by
    rw [← map_pow, hγ3, map_one]
  have hout' : MulAut.congr e' γ ∉ innAutDerived (StatedProj (StatedSU (n + 1) (q.p ^ q.exponent) F)) :=
    fun h => hout ((mem_innAutDerived_congr e').1 h)
  obtain ⟨A, φ, -, hφ⟩ := exists_phi_of_outer_three hdat hN hNq _ hβ'3 hout'
  have hdvd := orderOf_dvd_of_card (p := q.p) (e := 2 * q.exponent) q.prime_p
    (by have := q.exponent_pos; omega) hdat.card φ
  rw [hφ] at hdvd
  have h3e : 3 ≤ q.exponent := by
    have h3 : 3 ∣ q.exponent := by omega
    exact Nat.le_of_dvd q.exponent_pos h3
  have h8 : 2 ^ 3 ≤ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact (Nat.pow_le_pow_left q.prime_p.two_le 3).trans (Nat.pow_le_pow_right q.prime_p.pos h3e)
  omega

theorem kd264I5CoverLift_unitary (hSU : I5SUClosed) (n : ℕ) (q : TauCeti.PrimePower)
    (hd : (TauCeti.LieTypeIndex.twistedA n q).Valid) (h3n : 3 ∣ n + 1) (h3q : 3 ∣ q.card + 1)
    (K : Type) [Group K] [Finite K] (hK : CFSG.Open.IsQuasisimple K)
    (eK : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA n q, hd⟩).Group)
    (β : MulAut K) (hβ3 : β ^ 3 = 1)
    (hout : onCenterQuotient β ∉ innAutDerived (K ⧸ Subgroup.center K)) :
    ∃ (L : Type) (_ : Group L) (_ : Finite L) (π : L →* K) (βL : MulAut L),
      Function.Surjective π ∧ (∀ x : L, π x = 1 → x ∈ Subgroup.center L) ∧
        IsI5UniversalCover ⟨.twistedA n q, hd⟩ L ∧ βL ^ 3 = 1 ∧ ∀ x : L, π (βL x) = β (π x) := by
  have hN : 3 ≤ n + 1 := Nat.le_of_dvd (by omega) h3n
  by_cases hq8 : q.card < 8
  · exfalso
    have hγ3 : onCenterQuotient β ^ 3 = 1 := by
      have := congrArg (centerQuotientHom K) hβ3
      rwa [map_pow, map_one] at this
    exact false_of_outer_three_twistedA_small' n q hd hN hq8 eK (onCenterQuotient β) hγ3 hout
  · obtain ⟨-, F, hF, hfin, hFcard, ⟨eM⟩⟩ :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA n q hd (MulEquiv.refl _)
    have hdat : UnitaryFieldData q.p q.exponent F :=
      ⟨q.prime_p, q.exponent_pos, by rw [hFcard, ← pow_mul, mul_comm]⟩
    have hNq := not_three_two_of_valid n q hd hN
    have hK' : Nat.card F = (q.p ^ q.exponent) ^ 2 := by rw [hdat.card, ← pow_mul, Nat.mul_comm]
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    haveI : CharP F q.p := hdat.charP
    have hc := center_statedSU_eq hdat hN
    let ι : ↥(StatedSU (n + 1) (q.p ^ q.exponent) F) ⧸ Subgroup.center ↥(StatedSU (n + 1) (q.p ^ q.exponent) F) ≃*
        K ⧸ Subgroup.center K :=
      ((QuotientGroup.quotientMulEquivOfEq hc).trans eM.symm).trans eK.symm
    have hperf : Group.IsPerfect ↥(StatedSU (n + 1) (q.p ^ q.exponent) F) :=
      isPerfect_statedSU hK' hN (fun h => hNq ⟨(Prod.mk.inj h).1, (Prod.mk.inj h).2⟩)
    have hq8' : 8 ≤ q.p ^ q.exponent := by
      rw [← TauCeti.PrimePower.card_def]
      omega
    have hsec : ∀ (E : Type) [Group E] [Finite E] (π : E →* ↥(StatedSU (n + 1) (q.p ^ q.exponent) F)),
        Function.Surjective π → π.ker ≤ Subgroup.center E →
        ∃ s : ↥(StatedSU (n + 1) (q.p ^ q.exponent) F) →* E, ∀ g, π (s g) = g :=
      fun E _ _ π hπ hc' => hSU F q.p q.exponent (n + 1) hdat hN hq8' E π hπ hc'
    obtain ⟨π, βL, hπ, hπc, hβL3, hβL⟩ := exists_cover_lift_of_equiv hK hperf ι hsec β hβ3
    haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2
    refine ⟨_, inferInstance, inferInstance, π, βL, hπ, hπc, ?_, hβL3, hβL⟩
    exact isI5UniversalCover_SU n q hd hN hdat eM ι.isSimpleGroup

end CFSG.LieType.SemisimpleCentralizers.HeldLang
