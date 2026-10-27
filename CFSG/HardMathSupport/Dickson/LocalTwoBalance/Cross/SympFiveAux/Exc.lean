module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.Basic
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SymplecticPlaneQ
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldFixed
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldOuter
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldSemilinear
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldCentralizer
public import CFSG.RankThree.PartOne.KC.SymplecticNoninnerPlaneDescent
public import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldRadical
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (subfieldSpHom)
open CFSG.RankThree.PartOne.KCSpComm (spFixedGroup mem_spFixedGroup)
open CFSG.Open

section Centralizer

variable {r : ℕ} {K : Type} [Field K] [Finite K]

theorem centralizer_spFixedGroup_eq_zpowers {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hr : 2 ≤ r) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2) {σ : K ≃+* K}
    (hσ : orderOf σ = p) :
    Subgroup.centralizer (((spFixedGroup (fieldAut r K σ)).map
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))) :
        Subgroup (MulAut (StatedProj (StatedSp r K)))) :
          Set (MulAut (StatedProj (StatedSp r K)))) = Subgroup.zpowers (fieldAut r K σ) := by
  have : NeZero r := ⟨by omega⟩
  obtain ⟨hpf, -⟩ := CFSG.RankThree.PartOne.KCSpComm.card_descentField hℓ hf hK hσ
  have hq4 : 4 ≤ Nat.card K := by
    rw [hK]
    have hfp : p ≤ f := Nat.le_of_dvd (by omega) hpf
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp.two_le
      _ ≤ ℓ ^ p := Nat.pow_le_pow_left hℓ.two_le p
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hfp
  have hinj := CFSG.RankThree.PartOne.KCSymplectic.conj_injective_statedProj_statedSp (r := r)
    (K := K) hr hq4
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hσp : σ ^ p = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  apply le_antisymm
  · intro β hβ
    have hfix : ∀ x ∈ spFixedGroup (fieldAut r K σ), β x = x := by
      intro x hx
      have h1 := Subgroup.mem_centralizer_iff.mp hβ (MulAut.conj x) ⟨x, hx, rfl⟩
      have h2 : β * MulAut.conj x * β⁻¹ = MulAut.conj (β x) :=
        CFSG.RankThree.PartOne.KCSpComm.mulAut_conj_apply_conj β x
      have h3 : MulAut.conj (β x) = (MulAut.conj x : MulAut (StatedProj (StatedSp r K))) := by
        rw [← h2, ← h1]
        group
      exact hinj h3
    have hβg : ∀ g : StatedSp r (descentField σ),
        β (proj r K (subfieldSpHom r (descentField σ) g)) =
          proj r K (subfieldSpHom r (descentField σ) g) := fun g => by
      refine hfix _ ?_
      rw [CFSG.RankThree.PartOne.KCSpComm.spFixedGroup_fieldAut_eq_range hodd hσp]
      exact ⟨g, rfl⟩
    have hβE : β ∈ spSemilinearAutGroup r K :=
      CFSG.RankThree.PartOne.KCSpComm.mem_spSemilinearAutGroup_of_fixes_subfield hℓ hf hr hK
        (descentField σ) hβg
    obtain ⟨τ, hτk, rfl⟩ :=
      CFSG.RankThree.PartOne.KCSpComm.exists_fieldAut_of_fixes_subfield (descentField σ) hβE hβg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp
      (CFSG.RankThree.PartOne.KCSpComm.mem_zpowers_of_forall_fixed_prime hℓ hf hp hK hσ hτk)
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, by rw [map_zpow]⟩
  · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    have h1 := CFSG.RankThree.PartOne.KCSpComm.mulAut_conj_apply_conj (fieldAut r K σ) x
    rw [(hx : fieldAut r K σ x = x)] at h1
    show MulAut.conj x * fieldAut r K σ = fieldAut r K σ * MulAut.conj x
    calc MulAut.conj x * fieldAut r K σ
        = (fieldAut r K σ * MulAut.conj x * (fieldAut r K σ)⁻¹) * fieldAut r K σ := by rw [h1]
      _ = fieldAut r K σ * MulAut.conj x := by group

end Centralizer

theorem card_eq_one_of_normal_perm_six {M : Subgroup (Equiv.Perm (Fin 6))} [M.Normal] {p : ℕ}
    (hp : p = 3 ∨ p = 5) (hc : Nat.Coprime p (Nat.card M)) : Nat.card M = 1 := by
  by_contra hne
  have h1 : 1 < Nat.card M := by
    have := Nat.card_pos (α := M)
    omega
  have hnt : Nontrivial M := Finite.one_lt_card_iff_nontrivial.mp h1
  have hle : alternatingGroup (Fin 6) ≤ M :=
    Equiv.Perm.alternatingGroup_le_of_normal
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num) hnt
  have hdvd : Nat.card (alternatingGroup (Fin 6)) ∣ Nat.card M := Subgroup.card_dvd_of_le hle
  have hA : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num [Nat.factorial]
  rw [hA] at hdvd
  have hpM : p ∣ Nat.card M := by
    rcases hp with rfl | rfl
    · exact (by norm_num : 3 ∣ 360).trans hdvd
    · exact (by norm_num : 5 ∣ 360).trans hdvd
  have hp1 : p = 1 := Nat.Coprime.eq_one_of_dvd hc hpM
  rcases hp with rfl | rfl <;> norm_num at hp1

section Core

variable {K : Type} [Field K] [Finite K]

theorem coreFreeAt_fieldAut_two {p : ℕ} (hp : p = 3 ∨ p = 5) {σ : K ≃+* K}
    (hσ : orderOf σ = p) (hK : Nat.card K = 2 ^ p) :
    CoreFreeAt p (fieldAut 2 K σ) := by
  classical
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hodd2 : p ≠ 2 := by rcases hp with rfl | rfl <;> norm_num
  have hf : 1 ≤ p := hpp.one_le
  have hNZ : NeZero (2 : ℕ) := ⟨two_ne_zero⟩
  obtain ⟨-, hk⟩ := CFSG.RankThree.PartOne.KCSpComm.card_descentField Nat.prime_two hf hK hσ
  rw [Nat.div_self hpp.pos, pow_one] at hk
  have hσp : σ ^ p = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hodd : Odd p := hpp.odd_of_ne_two hodd2
  have hfinj : Function.Injective (fieldAut 2 K) :=
    (CFSG.RankThree.PartOne.KCSpComm.spOuter Nat.prime_two hf (le_refl 2) hK).fieldAut_injective
  have hord : orderOf (fieldAut 2 K σ) = p := by
    rw [orderOf_injective (fieldAut 2 K) hfinj σ, hσ]
  have hap : fieldAut 2 K σ ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  have hfixeq : spFixedGroup (fieldAut 2 K σ) =
      (CFSG.RankThree.PartOne.KCSpComm.subfieldInj (r := 2) σ).range := by
    rw [CFSG.RankThree.PartOne.KCSpComm.spFixedGroup_fieldAut_eq_range hodd hσp,
      CFSG.RankThree.PartOne.KCSpComm.range_subfieldInj]
  haveI : Fintype (descentField σ) := Fintype.ofFinite _
  have hk2 : Fintype.card (descentField σ) = 2 := by rw [← Nat.card_eq_fintype_card, hk]
  haveI : CharP (descentField σ) 2 := charP_of_card_eq_prime hk2
  obtain ⟨e6⟩ := CFSG.RankThree.CASymplecticSubfield.nonempty_statedSp_two_mulEquiv_perm hk2
  let e2 : StatedProj (StatedSp 2 (descentField σ)) ≃*
      (CFSG.RankThree.PartOne.KCSpComm.subfieldInj (r := 2) σ).range :=
    MonoidHom.ofInjective (CFSG.RankThree.PartOne.KCSpComm.subfieldInj_injective (r := 2) σ)
  let e3 : StatedProj (StatedSp 2 (descentField σ)) ≃* Equiv.Perm (Fin 6) :=
    (MulEquiv.ofBijective (proj 2 (descentField σ))
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo).symm.trans e6
  let eH : spFixedGroup (fieldAut 2 K σ) ≃* Equiv.Perm (Fin 6) :=
    (MulEquiv.subgroupCongr hfixeq).trans (e2.symm.trans e3)
  have hA : ∀ N : Subgroup (StatedProj (StatedSp 2 K)), N ≤ fixSub (fieldAut 2 K σ) →
      (∀ f ∈ fixSub (fieldAut 2 K σ), ∀ n ∈ N, f * n * f⁻¹ ∈ N) →
        Nat.Coprime p (Nat.card N) → N = ⊥ := by
    intro N hN hNn hcop
    have hN' : N ≤ spFixedGroup (fieldAut 2 K σ) := fun x hx => mem_spFixedGroup.2 (mem_fixSub.1 (hN hx))
    have hNn' : ∀ f ∈ spFixedGroup (fieldAut 2 K σ), ∀ n ∈ N, f * n * f⁻¹ ∈ N :=
      fun f hf' n hn => hNn f (mem_fixSub.2 (mem_spFixedGroup.1 hf')) n hn
    let M : Subgroup (spFixedGroup (fieldAut 2 K σ)) := N.subgroupOf (spFixedGroup (fieldAut 2 K σ))
    haveI hM : M.Normal := ⟨fun m hm g => by
      rw [Subgroup.mem_subgroupOf] at hm ⊢
      exact hNn' g.1 g.2 m.1 hm⟩
    have hcardM : Nat.card (M.map eH.toMonoidHom) = Nat.card N := by
      rw [Subgroup.card_map_of_injective eH.injective]
      exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN').toEquiv)
    haveI : (M.map eH.toMonoidHom).Normal := hM.map _ eH.surjective
    have hcop' : Nat.Coprime p (Nat.card (M.map eH.toMonoidHom)) := by rwa [hcardM]
    have h1 := card_eq_one_of_normal_perm_six hp hcop'
    rw [hcardM] at h1
    exact Subgroup.card_eq_one.mp h1
  have hB : ∀ g : MulAut (StatedProj (StatedSp 2 K)), Nat.Coprime p (orderOf g) →
      g * fieldAut 2 K σ = fieldAut 2 K σ * g → (∀ t ∈ fixSub (fieldAut 2 K σ), g t = t) →
        g = 1 := by
    intro g hg _ hfix
    have hcent : g ∈ Subgroup.centralizer
        (((spFixedGroup (fieldAut 2 K σ)).map
          (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))) :
            Subgroup (MulAut (StatedProj (StatedSp 2 K)))) :
              Set (MulAut (StatedProj (StatedSp 2 K)))) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨t, ht, rfl⟩
      have ht' : g t = t := hfix t (mem_fixSub.2 (mem_spFixedGroup.1 ht))
      ext y
      simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, ht']
    rw [centralizer_spFixedGroup_eq_zpowers Nat.prime_two hf (le_refl 2) hK hpp hodd2 hσ] at hcent
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hcent
    subst hn
    have hgp : (fieldAut 2 K σ ^ n) ^ p = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hap, one_zpow]
    have hdvd : orderOf (fieldAut 2 K σ ^ n) ∣ p := orderOf_dvd_of_pow_eq_one hgp
    have h1 : orderOf (fieldAut 2 K σ ^ n) = 1 := Nat.Coprime.eq_one_of_dvd hg.symm hdvd
    exact orderOf_eq_one_iff.mp h1
  exact ⟨hA, hB⟩

end Core

section Balance

variable {K : Type} [Field K] [Finite K]

theorem isLocallyBalancedAbs_two_sp_two_exc {p : ℕ} (hp : p = 3 ∨ p = 5)
    (hK : Nat.card K = 2 ^ p) : IsLocallyBalancedAbs p 2 (StatedProj (StatedSp 2 K)) := by
  classical
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hp2 : p ≠ 2 := by rcases hp with rfl | rfl <;> norm_num
  have hf : 1 ≤ p := hpp.one_le
  have hq4 : 4 ≤ 2 ^ p := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (hpp.two_le)
  have hrq : ¬ (2 = 2 ∧ 2 ^ p = 2) := by
    rintro ⟨-, h⟩
    rcases hp with rfl | rfl <;> norm_num at h
  have hinj := CFSG.RankThree.PartOne.KCSpFull.spConj_injective (K := K) Nat.prime_two hf hK
    (le_refl 2) hrq
  have O := CFSG.RankThree.PartOne.KCSpComm.spOuter (K := K) Nat.prime_two hf (le_refl 2) hK
  have hNZ : NeZero (2 : ℕ) := ⟨two_ne_zero⟩
  refine isLocallyBalancedAbs_two_of_kinds hpp hinj (innerAut _) ?_ ?_
  · intro E hEin hE hEc H hH
    exact localDeltaIn_eq_bot_psp_q Nat.prime_two hf hK hq4 hpp hp2 hp2 (le_refl 2) E hEin hE hEc hH
  · intro D hD _ hDin
    haveI hEel : CFSG.IsElementaryAbelian p D :=
      { toIsMulCommutative := hD.1
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
          Subtype.ext (hD.2 x x.2) }
    obtain ⟨x, hxD, hxin⟩ := IsConcreteLE.not_le_iff_exists.1 hDin
    obtain ⟨-, σ, hσ, h, -, hxh⟩ :=
      CFSG.RankThree.PartOne.KCSpComm.noninner_element_data O hpp hp2 (A := D) hxD hxin
    refine ⟨x, hxD, hxin, Or.inr ?_⟩
    rw [hxh]
    exact (coreFreeAt_fieldAut_two hp hσ hK).conj h

end Balance

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
