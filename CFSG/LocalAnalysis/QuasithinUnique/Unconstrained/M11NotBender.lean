module

public import CFSG.Open.FusionDefs
public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.M11Order
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiCentralCover
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeThreeModelRegularitySupport
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma114Models
public import Certificates.Certificate43
public import Certificates.Certificate110
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

theorem m11_not_fusionIsBenderGroup :
    ¬ fusionIsBenderGroup (CFSG.Blueprint.NativeSporadic.Carrier .M11) := by
  have hcard : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M11) = 7920 :=
    CFSG.Semidihedral.GL2Recognition.card_nativeM11
  rintro (⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩)
  ·
    have h := Nat.card_congr e.toEquiv
    rw [hcard, CFSG.Walter.psl2_even_card (by omega)] at h
    have hf4 : f ≤ 4 := by
      by_contra hcon
      have h32 : 32 ≤ 2 ^ f :=
        calc 32 = 2 ^ 5 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h1023 : 1023 ≤ (2 ^ f) ^ 2 - 1 := by
        have : 1024 ≤ (2 ^ f) ^ 2 := by nlinarith
        omega
      have := Nat.mul_le_mul h32 h1023
      omega
    interval_cases f <;> norm_num at h
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hK : Nat.card (GaloisField 2 (2 * f)) = 2 ^ (2 * f) :=
      GaloisField.card 2 (2 * f) (by omega)
    have hK' : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
      rw [hK, ← pow_mul, mul_comm]
    have hPSU : Nat.card (CFSG.Open.PSU3 2 f) = 7920 :=
      (Nat.card_congr e.toEquiv.symm).trans hcard
    have hproj : Nat.card (CFSG.Assembly.LowTwoRank.StatedProj
        (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ f) (GaloisField 2 (2 * f)))) = 7920 := by
      rw [← hPSU]
      exact Nat.card_congr (CFSG.ShultStronglyClosedTI.glaSU3EquivNative
        (K := GaloisField 2 (2 * f)) f hf hK).toEquiv
    have hv := CFSG.Semidihedral.Principal.DegreeThreeModel.padicValNat_card_psu3
      (p := 2) (f := f) (K := GaloisField 2 (2 * f)) (by omega) hK'
    rw [hproj] at hv
    have hdvd : 2 ^ (3 * f) ∣ 7920 := by
      have := pow_padicValNat_dvd (p := 2) (n := 7920)
      rwa [hv] at this
    have h64 : 2 ^ 6 ∣ 2 ^ (3 * f) := pow_dvd_pow 2 (by omega)
    have := h64.trans hdvd
    norm_num at this
  ·
    have h := Nat.card_congr e.toEquiv
    rw [hcard, Nat.card_congr (CFSG.ShultStronglyClosedTI.suzukiCoverNativeEquiv a).toEquiv,
      CFSG.BenderSuzuki.lemma114_suzukiMatrixGroup_card_formula a (by omega)] at h
    have h8 : 8 ≤ 2 ^ (2 * a + 1) :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 3 ≤ 2 * a + 1))
    have h64 : 64 ≤ (2 ^ (2 * a + 1)) ^ 2 := by nlinarith
    have h7 : 7 ≤ 2 ^ (2 * a + 1) - 1 := by omega
    have := Nat.mul_le_mul (Nat.mul_le_mul (Nat.add_le_add_right h64 1) h64) h7
    omega

end CFSG.QuasithinUnique
