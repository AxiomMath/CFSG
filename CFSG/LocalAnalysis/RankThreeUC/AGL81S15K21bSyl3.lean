module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K21bSyl3Proof

theorem no_elemAbelian_of_orderOf_nine {P : Type} [Group P] [Finite P]
    (hcard : ∃ k : ℕ, ¬ 3 ∣ k ∧ Nat.card P = 9 * k) (hg : ∃ g : P, orderOf g = 9)
    (E : Subgroup P) (hE : CFSG.Open.IsElemAbelian 3 E) (hc : Nat.card E = 9) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk3, hPk⟩ := hcard
  obtain ⟨g, hg9⟩ := hg
  have hCc : Nat.card (Subgroup.zpowers g) = 9 := by rw [Nat.card_zpowers, hg9]
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hc]; norm_num)
  have hCp : IsPGroup 3 (Subgroup.zpowers g) := IsPGroup.of_card (n := 2) (by rw [hCc]; norm_num)
  have hEi : E.index = k := by
    have h := E.card_mul_index
    rw [hc, hPk] at h
    omega
  have hCi : (Subgroup.zpowers g).index = k := by
    have h := (Subgroup.zpowers g).card_mul_index
    rw [hCc, hPk] at h
    omega
  let S₁ : Sylow 3 P := hEp.toSylow (by rw [hEi]; exact hk3)
  let S₂ : Sylow 3 P := hCp.toSylow (by rw [hCi]; exact hk3)
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq P S₁ S₂
  have hg2 : g ∈ (S₂ : Subgroup P) := by
    rw [IsPGroup.toSylow_coe]
    exact Subgroup.mem_zpowers g
  rw [← hx, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hg2
  have hgE : (MulAut.conj x)⁻¹ • g ∈ E := by
    have h1 : ((S₁ : Subgroup P)) = E := IsPGroup.toSylow_coe _ _
    rwa [h1] at hg2
  have h3 := hE.2 _ hgE
  have h4 : orderOf ((MulAut.conj x)⁻¹ • g) = 9 := by
    rw [MulAut.smul_def]
    rw [MulEquiv.orderOf_eq]
    exact hg9
  have h5 := orderOf_dvd_of_pow_eq_one h3
  rw [h4] at h5
  omega

end K21bSyl3Proof

end CFSG.LocalAnalysis.RankThreeUC.S15
