module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6KFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6SylowProved
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6AutKey
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6Model
import CFSG.GH74.KGroups.A6
public import CFSG.Adapters.LinearFieldTransport
public import CFSG.LocalAnalysis.AGLEmbedding.Signalizer
public import CFSG.Quasithin.Recognition.CertF9

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open scoped MatrixGroups

private theorem isSimpleGroup_of_isRankThreeA6 {K : Type} [Group K] (hK : IsRankThreeA6 K) :
    IsSimpleGroup K := by
  obtain ⟨e⟩ := hK
  have : IsSimpleGroup PSL(2, GaloisField 3 2) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple
      (by rw [GaloisField.card 3 2 (by norm_num)]; norm_num)
  exact e.isSimpleGroup

theorem a6BorelCore_proved : A6BorelCore := by
  intro X _ _ K hKn hC hKA T hTK hTsyl
  have : K.Normal := hKn
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTp : IsPGroup 3 ↥T := (isSylowOf_iff.mp hTsyl).2.1
  obtain ⟨Q, hQ⟩ := hTsyl
  obtain ⟨hQel, hQcard, -⟩ := a6SylowData_proved ↥K hKA Q
  have hKs : IsSimpleGroup ↥K := isSimpleGroup_of_isRankThreeA6 hKA
  obtain ⟨eG⟩ := A6Model.nonempty_equiv hKA
  have hK360 : Nat.card ↥K = 360 := by rw [Nat.card_congr eG.toEquiv, A6Model.psl29_card]
  obtain ⟨eK⟩ := hKA
  obtain ⟨eP⟩ := CFSG.GH74.KGroups.A6.equiv_psl_P
  have eF : CFSG.Quasithin.GF9 ≃+* GaloisField 3 2 :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField CFSG.Quasithin.GF9 3 2 (by norm_num)
      CFSG.GH74.KGroups.A6.card_F
  have e := eK.trans
    ((CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv eF (Fin 2)).symm.trans eP)
  have := CFSG.GH74.KGroups.A6.finite_mulAut e
  have hcard := CFSG.GH74.KGroups.A6.card_mulAut e
  have hQc : ∀ a ∈ (Q : Subgroup ↥K), ∀ b ∈ (Q : Subgroup ↥K), a * b = b * a := by
    have h1 : (Q : Subgroup ↥K) ≤ centralizer ((Q : Subgroup ↥K) : Set ↥K) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr hQel.1
    intro a ha b hb
    exact (mem_centralizer_iff.mp (h1 ha) b hb).symm
  have hkey := aut_eq_one_of_commute (K := ↥K) hK360 hcard
    (fun R hRc hR3 hRn => CFSG.GH74.KGroups.A6.autCentralizer e R ⟨hRc, hR3⟩ hRn)
    (fun B hBc hB3 hBn => CFSG.GH74.KGroups.A6.centralizer3 e B ⟨hBc, hB3⟩ hBn)
    hQc hQel.2 (by simpa using hQcard)
  set N : Subgroup X := normalizer (T : Set X) with hN
  set R : Subgroup X := rankThreePrimeCore 3 N with hR
  have hRN : R ≤ N := CFSG.AGLEmbedding.glbPrimeCore_le 3 N
  have hRcop : Nat.Coprime 3 (Nat.card R) := CFSG.AGLEmbedding.glbPrimeCore_coprime 3 N
  have hNR : N ≤ normalizer (R : Set X) := CFSG.AGLEmbedding.le_normalizer_glbPrimeCore 3 N
  have hTN : T ≤ N := Subgroup.le_normalizer
  have hTR : T ⊓ R = ⊥ := by
    obtain ⟨k, hk⟩ := hTp.exists_card_eq
    exact disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard
      (by rw [hk]; exact Nat.Coprime.pow_left k hRcop))
  refine eq_bot_iff.mpr fun r hr => ?_
  have hrN : r ∈ N := hRN hr
  have hcomm : ∀ t ∈ T, r * t = t * r := by
    intro t ht
    have h1 : r * t * r⁻¹ * t⁻¹ ∈ T :=
      T.mul_mem ((mem_normalizer_iff.mp hrN t).mp ht) (T.inv_mem ht)
    have h2 : r * t * r⁻¹ * t⁻¹ ∈ R := by
      have h3 : t * r⁻¹ * t⁻¹ ∈ R := by
        have := (mem_normalizer_iff.mp (hNR (hTN ht)) r⁻¹).mp (R.inv_mem hr)
        simpa [mul_assoc] using this
      have := R.mul_mem hr h3
      simpa [mul_assoc] using this
    have h4 : r * t * r⁻¹ * t⁻¹ ∈ T ⊓ R := ⟨h1, h2⟩
    rw [hTR, Subgroup.mem_bot] at h4
    calc r * t = (r * t * r⁻¹ * t⁻¹) * (t * r) := by group
      _ = t * r := by rw [h4, one_mul]
  have hcomm' : ∀ t ∈ (Q : Subgroup ↥K), (MulAut.conjNormal r : MulAut ↥K) * MulAut.conj t =
      MulAut.conj t * MulAut.conjNormal r := by
    intro t ht
    have htT : (t : X) ∈ T := hQ ▸ ⟨t, ht, rfl⟩
    have h1 : r * (t : X) * r⁻¹ = t := by rw [hcomm _ htT]; group
    have h2 : r * (t : X)⁻¹ * r⁻¹ = (t : X)⁻¹ := by
      calc r * (t : X)⁻¹ * r⁻¹ = (r * (t : X) * r⁻¹)⁻¹ := by group
        _ = (t : X)⁻¹ := by rw [h1]
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
      Subgroup.coe_inv]
    calc r * ((t : X) * x * (t : X)⁻¹) * r⁻¹
        = (r * (t : X) * r⁻¹) * (r * (x : X) * r⁻¹) * (r * (t : X)⁻¹ * r⁻¹) := by group
      _ = (t : X) * (r * (x : X) * r⁻¹) * (t : X)⁻¹ := by rw [h1, h2]
  have hord : Nat.Coprime 3 (orderOf (MulAut.conjNormal r : MulAut ↥K)) := by
    have h1 : orderOf (MulAut.conjNormal r : MulAut ↥K) ∣ orderOf r :=
      orderOf_map_dvd (MulAut.conjNormal : X →* MulAut ↥K) r
    have h2 : orderOf r ∣ Nat.card R := Subgroup.orderOf_dvd_natCard R hr
    exact Nat.Coprime.coprime_dvd_right (h1.trans h2) hRcop
  have hψ1 := hkey _ hord hcomm'
  have hrK : r ∈ centralizer (K : Set X) := by
    rw [mem_centralizer_iff]
    intro k hk
    have h1 := congrArg (fun φ : MulAut ↥K => ((φ ⟨k, hk⟩ : ↥K) : X)) hψ1
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc k * r = (r * k * r⁻¹) * r := by rw [h1]
      _ = r * k := by group
  rw [hC, Subgroup.mem_bot] at hrK
  exact Subgroup.mem_bot.mpr hrK

end CFSG.LocalAnalysis.RankThreeTheoremC
