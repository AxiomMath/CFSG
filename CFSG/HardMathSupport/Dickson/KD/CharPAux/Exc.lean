module

public import CFSG.HardMathSupport.Dickson.KD.CharPAux.RadCent
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreE
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreF4G2
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreTwistedE6
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreReeD4
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieCore
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentral
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec2Statements
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.Proving.LBLayerConj
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour

public section

namespace CFSG.HardMathSupport.Dickson.KD

open CFSG.Open CFSG.LieType.BorelTits CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.GH74.GLS.Stage2.OddAut CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open CFSG.LieType.Ree (ReeTag)

theorem kdCharPAt_of_bridge_E {τ : Tag}
    (hact : ∀ (K : Type) [Field K] [Finite K] {J : Set (Fin τ.rank)}, J ≠ Set.univ →
      ∀ α : MulAut (adjointGroup τ K),
      (∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ parabolicRadical τ K J → α x = x) →
        α ∈ diagonalFieldActors τ K)
    {c : TauCeti.PrimePower → TauCeti.LieTypeIndex} (hbr : CFSG.TauCetiBridge.UntwistedBridge τ c)
    (q : TauCeti.PrimePower) (hv : (c q).Valid) {p : ℕ} (hp2 : p ≠ 2) (hpq : p = q.p) :
    KDCharPAt p (TauCeti.CFSGIndex.lie ⟨c q, hv⟩).Group := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hKq : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  have hq2 : q.p ≠ 2 := hpq ▸ hp2
  obtain ⟨eB⟩ := hbr q hv hq2 (GaloisField q.p q.exponent)
    (by rw [hKq]; simp [TauCeti.PrimePower.card_def])
  let e : TauCeti.ValidLieTypeIndex.Group ⟨c q, hv⟩ ≃*
      adjointGroup τ (GaloisField q.p q.exponent) :=
    eB.symm.trans adjointEquivQuotient.symm
  have hKchar : CharP (GaloisField q.p q.exponent) q.p := inferInstance
  subst hpq
  exact kdCharPAt_of_model e (holds_adjointGroup_tag τ _ q.p) center_adjointGroup_eq_bot
    (pCharData_adjoint_top τ _ q.p (hact _))

theorem kdCharPAt_E6 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E6 q).Valid) {p : ℕ}
    (hp2 : p ≠ 2) (hpq : p = q.p) : KDCharPAt p (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group :=
  kdCharPAt_of_bridge_E (τ := .E6)
    (fun K _ _ J hJ α hα => mem_diagonalFieldActors_E6_of_fixes_radical hJ hα)
    CFSG.TauCetiBridge.chevalleyBridges.e6 q hv hp2 hpq

theorem kdCharPAt_E7 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E7 q).Valid) {p : ℕ}
    (hp2 : p ≠ 2) (hpq : p = q.p) : KDCharPAt p (TauCeti.CFSGIndex.lie ⟨.E7 q, hv⟩).Group :=
  kdCharPAt_of_bridge_E (τ := .E7)
    (fun K _ _ J hJ α hα => mem_diagonalFieldActors_of_E7_E8 (Or.inl rfl) α)
    CFSG.TauCetiBridge.chevalleyBridges.e7 q hv hp2 hpq

theorem kdCharPAt_E8 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E8 q).Valid) {p : ℕ}
    (hp2 : p ≠ 2) (hpq : p = q.p) : KDCharPAt p (TauCeti.CFSGIndex.lie ⟨.E8 q, hv⟩).Group :=
  kdCharPAt_of_bridge_E (τ := .E8)
    (fun K _ _ J hJ α hα => mem_diagonalFieldActors_of_E7_E8 (Or.inr rfl) α)
    CFSG.TauCetiBridge.chevalleyBridges.e8 q hv hp2 hpq

theorem kdCharPAt_F4 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.F4 q).Valid) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p = q.p) :
    KDCharPAt p (TauCeti.CFSGIndex.lie ⟨.F4 q, hv⟩).Group := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set K := GaloisField q.p q.exponent
  have hK : Nat.card K = q.p ^ q.exponent := GaloisField.card _ _ q.exponent_pos.ne'
  have hK' : Nat.card K = q.card := by rw [hK, TauCeti.PrimePower.card_def]
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).f4 q hv K hK'
  let e : TauCeti.ValidLieTypeIndex.Group ⟨.F4 q, hv⟩ ≃* adjointGroup .F4 K :=
    b.symm.trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot)
  subst hpq
  have htop := diagonalFieldActors_eq_top_F4_G2 hp hp2 q.exponent_pos K hK .F4 (Or.inl rfl)
  have hd : PCharData (adjointGroup .F4 K) q.p ⊤ := by
    have := pCharData_adjoint .F4 K q.p
    rwa [htop] at this
  exact kdCharPAt_of_model e (holds_adjointGroup_tag .F4 K q.p) center_adjointGroup_eq_bot hd

theorem kdCharPAt_adjointG2_three {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 3]
    (hK : Nat.card K = 3 ^ f) {S : Type} [Group S] (e : S ≃* adjointGroup .G2 K) :
    KDCharPAt 3 S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : CharP K ReeTag.G2.prime := inferInstanceAs (CharP K 3)
  have hd := pCharData_adjoint_top_of_outer ReeTag.G2.tag K 3 (g2_three_sq_mem hf hK)
    (fun J hJ α hfix hsq => g2_three_hOut hf hK hJ α hfix hsq)
  exact kdCharPAt_of_model e (holds_adjointGroup_tag .G2 K 3) center_adjointGroup_eq_bot hd

theorem kdCharPAt_G2 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p = q.p) :
    KDCharPAt p (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set K := GaloisField q.p q.exponent
  have hK : Nat.card K = q.p ^ q.exponent := GaloisField.card _ _ q.exponent_pos.ne'
  have hK' : Nat.card K = q.card := by rw [hK, TauCeti.PrimePower.card_def]
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).g2 q hv K hK'
  let e : TauCeti.ValidLieTypeIndex.Group ⟨.G2 q, hv⟩ ≃* adjointGroup .G2 K :=
    b.symm.trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot)
  subst hpq
  by_cases h3 : q.p = 3
  · haveI : CharP K 3 := CharP.congr q.p h3
    have hK3 : Nat.card K = 3 ^ q.exponent := by rw [hK, h3]
    rw [h3]
    exact kdCharPAt_adjointG2_three q.exponent_pos K hK3 e
  · have htop := diagonalFieldActors_eq_top_F4_G2 hp hp2 q.exponent_pos K hK .G2
      (Or.inr ⟨rfl, h3⟩)
    have hd : PCharData (adjointGroup .G2 K) q.p ⊤ := by
      have := pCharData_adjoint .G2 K q.p
      rwa [htop] at this
    exact kdCharPAt_of_model e (holds_adjointGroup_tag .G2 K q.p) center_adjointGroup_eq_bot hd

theorem kdCharPAt_twistedE6 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) {p : ℕ} (hpq : p = q.p) :
    KDCharPAt p (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let K := GaloisField q.p (2 * q.exponent)
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hKc : Nat.card K = (q.p ^ q.exponent) ^ TwistTag.E6.order := by
    change Nat.card (GaloisField q.p (2 * q.exponent)) = _
    rw [GaloisField.card _ _ (by have := q.exponent_pos; omega)]
    change _ = (q.p ^ q.exponent) ^ 2
    rw [← pow_mul, mul_comm]
  obtain ⟨σ, hσ, -⟩ := finite_graph_field_parameter_fields TwistTag.E6 q.prime_p hf K hKc
  have hK2 : Nat.card K = (q.p ^ q.exponent) ^ 2 := hKc
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hcen, ⟨eC⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form q.prime_p hf K hK2 σ hσ
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 q hv K
    (by rw [hqc]; exact hK2) σ.toRingHom (fun x => by rw [hqc]; exact hσ x)
  have e : TauCeti.ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩ ≃*
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom := eB.symm.trans eC
  have hσ2 : σ ^ TwistTag.E6.order = 1 := by
    have h2 : TwistTag.E6.order = 2 := rfl
    rw [h2]
    ext c
    have : Fintype K := Fintype.ofFinite K
    have hcard : Fintype.card K = (q.p ^ q.exponent) ^ 2 := by
      rw [← Nat.card_eq_fintype_card, hK2]
    change σ (σ c) = c
    rw [hσ, hσ, ← pow_mul, ← sq, ← hcard, FiniteField.pow_card]
  have hBT : Holds (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) q.p :=
    holds_of_twistedChevalleyModel (t := TwistTag.E6) hf
      ⟨K, inferInstance, inferInstance, hK2, σ.toRingHom, hσ, ⟨eC.symm⟩⟩
  have hAtop := fixedDiagonalFieldActors_E6_eq_top_all q.prime_p hf hK2 σ hσ
  have hd := pCharData_fixed TwistTag.E6 K σ hσ2 q.p
  rw [hAtop] at hd
  subst hpq
  exact kdCharPAt_of_model e hBT hcen hd

theorem kdCharPAt_trialityD4 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) {p : ℕ} (hp2 : p ≠ 2) (hpq : p = q.p) :
    KDCharPAt p (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let K := GaloisField q.p (3 * q.exponent)
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hKc : Nat.card K = (q.p ^ q.exponent) ^ TwistTag.D4.order := by
    change Nat.card (GaloisField q.p (3 * q.exponent)) = _
    rw [GaloisField.card _ _ (by have := q.exponent_pos; omega)]
    change _ = (q.p ^ q.exponent) ^ 3
    rw [← pow_mul, mul_comm]
  obtain ⟨σ, hσ, -⟩ := finite_graph_field_parameter_fields TwistTag.D4 q.prime_p hf K hKc
  have hK3 : Nat.card K = (q.p ^ q.exponent) ^ 3 := hKc
  have hp2' : q.p ≠ 2 := hpq ▸ hp2
  obtain ⟨-, -, -, -, -, -, hcen, ⟨eC⟩⟩ :=
    odd_triality_exact_automorphism_normal_form q.prime_p hp2' hf K hK3 σ hσ
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.trialityD4 q hv K
    (by rw [hqc]; exact hK3) σ.toRingHom (fun x => by rw [hqc]; exact hσ x)
  have e : TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩ ≃*
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := eB.symm.trans eC
  have hσ3 : σ ^ TwistTag.D4.order = 1 :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.d4_sigma_pow_order K hK3 σ hσ
  have hBT : Holds (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) q.p :=
    holds_of_twistedChevalleyModel (t := TwistTag.D4) hf
      ⟨K, inferInstance, inferInstance, hK3, σ.toRingHom, hσ, ⟨eC.symm⟩⟩
  have hAtop := CFSG.GH74.GLS.Stage2.Bender.Thm1.par_fixedDiagonalFieldActors_D4_eq_top_odd
    q.prime_p hp2' hf K hK3 σ hσ
  have hd := CFSG.GH74.GLS.Stage2.Bender.Thm1.pCharData_fixed TwistTag.D4 K σ hσ3 q.p
  rw [hAtop] at hd
  subst hpq
  exact kdCharPAt_of_model e hBT hcen hd

theorem kdCharPAt_reeG2 (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeG2 m).Valid) {p : ℕ}
    (hp3 : p = 3) : KDCharPAt p (TauCeti.CFSGIndex.lie ⟨.reeG2 m, hv⟩).Group := by
  subst hp3
  have hm1 : 1 ≤ m :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card (GaloisField 3 (2 * m + 1)) = 3 ^ (2 * m + 1) :=
    GaloisField.card 3 (2 * m + 1) (by omega)
  have : CharP (GaloisField 3 (2 * m + 1)) ReeTag.G2.prime :=
    (inferInstance : CharP (GaloisField 3 (2 * m + 1)) 3)
  obtain ⟨b⟩ := CFSG.TauCetiBridge.reeG2Bridge m hv (GaloisField 3 (2 * m + 1)) hK
  have e1 : DerivedCentralQuotient (reeFixedGroup .G2 (GaloisField 3 (2 * m + 1)) reeG2Perm
      fun i => if i ∈ reeG2Long then 3 ^ m else 3 ^ (m + 1)) ≃*
        DerivedCentralQuotient (ReeTag.G2.reeGamma (GaloisField 3 (2 * m + 1)) m) := by
    rw [ReeTag.reeGamma_eq_reeFixedGroup]
    exact MulEquiv.refl _
  obtain ⟨E⟩ := ReeTag.nonempty_derivedCentralQuotient_mulEquiv_reeGamma_G2
    (K := GaloisField 3 (2 * m + 1)) hm1 hK
  let e : TauCeti.ValidLieTypeIndex.Group ⟨.reeG2 m, hv⟩ ≃*
      ReeTag.G2.reeGamma (GaloisField 3 (2 * m + 1)) m :=
    (b.symm.trans e1).trans E
  have : Finite (ReeTag.G2.reeGamma (GaloisField 3 (2 * m + 1)) m) :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.finite_reeGamma
  have hcen : Subgroup.center (ReeTag.G2.reeGamma (GaloisField 3 (2 * m + 1)) m) = ⊥ :=
    ReeTag.center_reeGamma_G2_eq_bot hK
  exact kdCharPAt_of_model e CFSG.GH74.GLS.Stage2.Bender.Thm1.ree_holds hcen
    (CFSG.GH74.GLS.Stage2.Bender.Thm1.ree_pCharData hm1 hK)

end CFSG.HardMathSupport.Dickson.KD
