module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6AutData
import CFSG.GH74.KGroups.A6
public import CFSG.Adapters.LinearFieldTransport
public import CFSG.Quasithin.Recognition.CertF9

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

private theorem a6aut_card_dvd {G : Type} [Group G] [Finite G] (hG : Nat.card G = 1440)
    (S : Subgroup G) (hS : IsPGroup 3 S) : Nat.card S ∣ 3 ^ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (G := S)).1 hS
  have hdvd : 3 ^ k ∣ 1440 := by
    have h := Subgroup.card_subgroup_dvd_card S
    rwa [hk, hG] at h
  have hk2 : k ≤ 2 := by
    by_contra h
    have h27 : 3 ^ 3 ∣ 1440 := (pow_dvd_pow 3 (not_le.1 h)).trans hdvd
    norm_num at h27
  rw [hk]
  exact pow_dvd_pow 3 hk2

theorem a6AutData_proved : A6AutData := by
  intro K _ _ hK S hS
  obtain ⟨eK⟩ := hK
  obtain ⟨eP⟩ := CFSG.GH74.KGroups.A6.equiv_psl_P
  have eF : CFSG.Quasithin.GF9 ≃+* GaloisField 3 2 :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField CFSG.Quasithin.GF9 3 2 (by norm_num)
      CFSG.GH74.KGroups.A6.card_F
  have e := eK.trans
    ((CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv eF (Fin 2)).symm.trans eP)
  have := CFSG.GH74.KGroups.A6.finite_mulAut e
  exact a6aut_card_dvd (CFSG.GH74.KGroups.A6.card_mulAut e) S hS

end CFSG.LocalAnalysis.RankThreeTheoremC
