module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ReeDim
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.OrthOrder
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SpArith
public import CFSG.Adapters.TauCetiExceptional.ReeBridge
public import CFSG.LieType.Steinberg.CentralExt.SmallReeMultiplier
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalSmallReeMain
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeOuter
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFReduction
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Quasithin TauCeti CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.LieType.Ree CFSG.Blueprint.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem card_aut_ree_lt {a : ℕ} (ha : 1 ≤ a) :
    (2 * a + 1) * ((3 ^ (2 * a + 1)) ^ 3 * ((3 ^ (2 * a + 1)) ^ 3 + 1) * (3 ^ (2 * a + 1) - 1)) <
      2 ^ ((3 ^ (2 * a + 1) - 1) * 3 ^ (2 * a + 1)) := by
  set q := 3 ^ (2 * a + 1) with hq
  have hq27 : 27 ≤ q := by
    rw [hq]
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h1 : 2 * a + 1 ≤ q := (Nat.lt_pow_self (by norm_num : 1 < 3)).le
  have h2 : q ^ 3 + 1 ≤ 2 * q ^ 3 := by have := Nat.one_le_pow 3 q (by omega); omega
  have h3 : q - 1 ≤ q := Nat.sub_le q 1
  have hle : (2 * a + 1) * (q ^ 3 * (q ^ 3 + 1) * (q - 1)) ≤ 2 * q ^ 8 := by
    calc (2 * a + 1) * (q ^ 3 * (q ^ 3 + 1) * (q - 1)) ≤ q * (q ^ 3 * (2 * q ^ 3) * q) :=
          Nat.mul_le_mul h1 (Nat.mul_le_mul (Nat.mul_le_mul_left _ h2) h3)
      _ = 2 * q ^ 8 := by ring
  have hlt : 2 * q ^ 8 < 2 ^ ((q - 1) * q) := by
    have h4 : q ^ 8 < (2 ^ q) ^ 8 := Nat.pow_lt_pow_left (Nat.lt_two_pow_self) (by norm_num)
    have h5 : 2 * (2 ^ q) ^ 8 = 2 ^ (8 * q + 1) := by rw [← pow_mul, pow_succ]; ring
    have h6 : 8 * q + 1 ≤ (q - 1) * q := by
      have : 26 * q ≤ (q - 1) * q := Nat.mul_le_mul_right q (by omega)
      omega
    calc 2 * q ^ 8 < 2 * (2 ^ q) ^ 8 := by omega
      _ = 2 ^ (8 * q + 1) := h5
      _ ≤ 2 ^ ((q - 1) * q) := Nat.pow_le_pow_right (by norm_num) h6
  exact hle.trans_lt hlt


theorem nonempty_reeGamma_equiv {a : ℕ} (hv : (LieTypeIndex.reeG2 a).Valid) {K : Type} [Field K]
    [Finite K] [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    Nonempty ((CFSGIndex.lie ⟨.reeG2 a, hv⟩).Group ≃* ↥(ReeTag.G2.reeGamma K a)) := by
  have ha : 1 ≤ a := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  obtain ⟨φ⟩ := CFSG.TauCetiBridge.reeG2Bridge a hv K hK
  obtain ⟨ψ⟩ := ReeTag.nonempty_derivedCentralQuotient_mulEquiv_reeGamma_G2 (K := K) ha hK
  have hΓ := ReeTag.reeGamma_eq_reeFixedGroup (t := ReeTag.G2) (K := K) (a := a)
  refine ⟨φ.symm.trans ?_⟩
  have hΓ' : CFSG.Blueprint.reeFixedGroup .G2 K CFSG.Blueprint.reeG2Perm
      (fun i => if i ∈ CFSG.Blueprint.reeG2Long then 3 ^ a else 3 ^ (a + 1)) =
      ReeTag.G2.reeGamma K a := hΓ.symm
  have e1 : CFSG.Blueprint.DerivedCentralQuotient (CFSG.Blueprint.reeFixedGroup .G2 K
      CFSG.Blueprint.reeG2Perm
        (fun i => if i ∈ CFSG.Blueprint.reeG2Long then 3 ^ a else 3 ^ (a + 1))) ≃*
      CFSG.Blueprint.DerivedCentralQuotient (ReeTag.G2.reeGamma K a) := by
    rw [hΓ']
    exact MulEquiv.refl _
  exact e1.trans ψ

theorem noIrrFFOffender_lie_reeG2 {a : ℕ} (hv : (LieTypeIndex.reeG2 a).Valid) :
    NoIrrFFOffender (CFSGIndex.lie ⟨.reeG2 a, hv⟩).Group := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hEN hE hel _
  have ha : 1 ≤ a := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  let K := GaloisField 3 (2 * a + 1)
  have hK : Nat.card K = 3 ^ (2 * a + 1) := GaloisField.card 3 (2 * a + 1) (by omega)
  have : CharP K ReeTag.G2.prime := by
    show CharP K 3
    infer_instance
  obtain ⟨ψ⟩ := nonempty_reeGamma_equiv hv (K := K) hK
  set Γ := ReeTag.G2.reeGamma K a
  have hΓc : Subgroup.center ↥Γ = ⊥ := ReeTag.center_reeGamma_G2_eq_bot hK
  let e' : ↥L ⧸ Subgroup.center ↥L ≃* ↥Γ ⧸ Subgroup.center ↥Γ :=
    (e.trans ψ).trans ((QuotientGroup.quotientMulEquivOfEq hΓc).trans QuotientGroup.quotientBot).symm
  have hM := (CFSG.LieType.Steinberg.CentralExt.SmallReeClosed.smallRee_hopfMultiplier
    (K := K) hK ha).2
  have hdvd := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hq.1 e'
  have hM1 : Nat.card (CFSG.Open.griessHopfMultiplier (↥Γ ⧸ Subgroup.center ↥Γ)) = 1 :=
    Nat.card_eq_one_iff_unique.2 ⟨hM, ⟨1⟩⟩
  rw [hM1] at hdvd
  have hcenter : Subgroup.center ↥L = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.1 hdvd)
  let θ : ↥L ≃* ↥Γ :=
    ((QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hcenter.symm)).trans
      e).trans ψ
  have hout := (CFSG.ComponentClassification.LiteratureLocal.SmallRee.outer_reeGamma_cyclic
    (K := K) ha hK).2
  have hsup := card_sup_le_of_card_outer hW hq.1 hirr hcenter hEN hel θ hout.le
  have hcard := CFSG.SignalizerFunctorTheorem.CatalogBridge.card_reeGamma_G2 (K := K) hK
  rw [hcard] at hsup
  have hker : θ.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).2 θ.injective
  have hdim := two_pow_le_card_of_reeGamma hW hK θ.toMonoidHom θ.surjective
    (by rw [hker]; exact bot_le) (by rw [hker, Subgroup.card_bot]; norm_num)
  rw [orderOf_two_zmod_three, hK] at hdim
  have hexp : 2 * ((3 ^ (2 * a + 1) - 1) * 3 ^ (2 * a + 1) / (3 - 1)) =
      (3 ^ (2 * a + 1) - 1) * 3 ^ (2 * a + 1) := by
    have heven : 2 ∣ (3 ^ (2 * a + 1) - 1) * 3 ^ (2 * a + 1) := by
      apply Dvd.dvd.mul_right
      have : Odd (3 ^ (2 * a + 1)) := Odd.pow (by decide)
      obtain ⟨k, hk⟩ := this
      exact ⟨k, by omega⟩
    rw [show (3 : ℕ) - 1 = 2 by norm_num, Nat.mul_div_cancel' heven]
  rw [hexp] at hdim
  by_contra hcon
  push Not at hcon
  have hU1 := FFToolkit.card_le_card_sup_of_offender hW hq hirr hEN hE hel hcon
  exact absurd ((hU1.trans hsup).trans_lt ((card_aut_ree_lt ha).trans_le hdim)) (lt_irrefl _)

theorem noFFModule_lie_reeG2 (d : ValidLieTypeIndex) {a : ℕ} (hd : d.1 = .reeG2 a) :
    NoFFModule (CFSGIndex.lie d).Group := by
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  exact noFFModule_of_noIrrFFOffender (noIrrFFOffender_lie_reeG2 hv)

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
