module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusFamData
public import CFSG.LocalAnalysis.SectionRank.TwoGenerators

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPLeviSub

open CFSG.Open CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin Matrix
open scoped Pointwise MatrixGroups

instance instFiniteOrthElementaryGroupPlus {r : ℕ} {K : Type} [Field K] [Finite K] :
    Finite ↥(orthElementaryGroup (quadPlus r K)) := finite_orthElementaryGroup

variable {K : Type} [Field K] [CharP K 2]

theorem orthPlus_sl_mulVec_inv_mulVec (C : SL(2, K)) (p : Fin 2 → K) :
    (C : Matrix (Fin 2) (Fin 2) K) *ᵥ (((C⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *ᵥ p) = p := by
  rw [mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, one_mulVec]

theorem commute_plusIotaTwo_plusIotaOne (A B : SL(2, K)) :
    Commute (plusIotaTwo K A) (plusIotaOne K B) := by
  have hO : plusIotaTwo K A * plusIotaOne K B * (plusIotaOne K B * plusIotaTwo K A)⁻¹ ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 2 K) :=
    mul_mem (mul_mem (plusIotaTwo_mem_orthogonalGroup A) (plusIotaOne_mem_orthogonalGroup B))
      (inv_mem (mul_mem (plusIotaOne_mem_orthogonalGroup B) (plusIotaTwo_mem_orthogonalGroup A)))
  have h1 : plusIotaTwo K A * plusIotaOne K B * (plusIotaOne K B * plusIotaTwo K A)⁻¹ = 1 := by
    refine eq_one_of_plusFam hO (fun p hp => ?_) (fun p hp => ?_)
    · have hBp : ((B⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *ᵥ p ≠ 0 :=
        sl_mulVec_ne_zero _ hp
      have hg : (plusIotaOne K B * plusIotaTwo K A)⁻¹ • plusFamOne p =
          plusFamOne (((B⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *ᵥ p) := by
        rw [inv_smul_eq_iff, mul_smul, plusIotaTwo_smul_plusFamOne,
          plusIotaOne_smul_plusFamOne B hBp, orthPlus_sl_mulVec_inv_mulVec]
      rw [mul_smul, mul_smul, hg, plusIotaOne_smul_plusFamOne B hBp, orthPlus_sl_mulVec_inv_mulVec,
        plusIotaTwo_smul_plusFamOne]
    · have hAp : ((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *ᵥ p ≠ 0 :=
        sl_mulVec_ne_zero _ hp
      have hg : (plusIotaOne K B * plusIotaTwo K A)⁻¹ • plusFamTwo p =
          plusFamTwo (((A⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *ᵥ p) := by
        rw [inv_smul_eq_iff, mul_smul, plusIotaTwo_smul_plusFamTwo A hAp,
          plusIotaOne_smul_plusFamTwo, orthPlus_sl_mulVec_inv_mulVec]
      rw [mul_smul, mul_smul, hg, plusIotaOne_smul_plusFamTwo,
        plusIotaTwo_smul_plusFamTwo A hAp, orthPlus_sl_mulVec_inv_mulVec]
  exact (mul_inv_eq_one.1 h1)

variable {r : ℕ}

theorem two_le_pRank_plusElementary [Finite K] (hr : 3 ≤ r) {ρ : ℕ} (hρ : ρ.Prime)
    (hρK : ρ ∣ Nat.card K ^ 2 - 1) :
    2 ≤ CFSG.Open.pRank ρ (⊤ : Subgroup ↥(orthElementaryGroup (quadPlus r K))) := by
  haveI : Fact ρ.Prime := ⟨hρ⟩
  have hdvd : ρ ∣ Nat.card SL(2, K) := by
    rw [LinearFlag.card_SL_eq (by norm_num : 1 ≤ 2)]
    exact Dvd.dvd.mul_left (hρK.trans (Finset.dvd_prod_of_mem (fun j => Nat.card K ^ j - 1)
      (Finset.mem_Icc.2 ⟨le_rfl, le_rfl⟩))) _
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := SL(2, K)) ρ hdvd
  have haρ : a ^ ρ = 1 := ha ▸ pow_orderOf_eq_one a
  have ha1 : a ≠ 1 := fun h => hρ.one_lt.ne' (by rw [← ha, h, orderOf_one])
  have htm : r - 2 + 2 = r := by omega
  set D : Finset ℕ := {r - 2} with hD
  have hDt : ∀ d ∈ D, d ≤ r - 2 := fun d hd => (Finset.mem_singleton.1 hd).le
  have hD₂ : ∀ d ∈ D, 1 ≤ d ∧ d ≤ r - 2 := fun d hd =>
    ⟨by rw [Finset.mem_singleton.1 hd]; omega, hDt d hd⟩
  have hD' : ∀ d ∈ D, d ≤ r := fun d hd => (hDt d hd).trans (by omega)
  have ht : r - 2 = 0 ∨ r - 2 ∈ D := Or.inr (Finset.mem_singleton_self _)
  let φ₂ : SL(2, K) →* ↥(plusFlagStab K r D) :=
    ((plusResExt K htm).comp (plusIotaTwo K)).codRestrict _ fun A =>
      plusResExt_iotaTwo_mem hr htm hDt A
  let φ₁ : SL(2, K) →* ↥(plusFlagStab K r D) :=
    ((plusResExt K htm).comp (plusIotaOne K)).codRestrict _ fun A =>
      plusResExt_iotaOne_mem hr htm hDt A
  let ι : ↥(plusFlagStab K r D) →* ↥(orthElementaryGroup (quadPlus r K)) :=
    Subgroup.inclusion (inf_le_left : plusFlagStab K r D ≤ _)
  have hι : Function.Injective ι := Subgroup.inclusion_injective _
  have hφ₂ : ∀ A, plusFamHom K hr hD₂ hD' ht htm 0 (φ₂ A) = SpecialLinearGroup.toGL A ∧
      plusFamHom K hr hD₂ hD' ht htm 1 (φ₂ A) = 1 := fun A =>
    plusFamHom_iotaTwo hr hD₂ hD' ht htm (plusResExt_iotaTwo_mem hr htm hDt A)
  have hφ₁ : ∀ A, plusFamHom K hr hD₂ hD' ht htm 0 (φ₁ A) = 1 ∧
      plusFamHom K hr hD₂ hD' ht htm 1 (φ₁ A) = SpecialLinearGroup.toGL A := fun A =>
    plusFamHom_iotaOne hr hD₂ hD' ht htm (plusResExt_iotaOne_mem hr htm hDt A)
  have hcomm : Commute (φ₂ a) (φ₁ a) :=
    Subtype.ext (((commute_plusIotaTwo_plusIotaOne a a).map (plusResExt K htm)).eq)
  have hgl : (SpecialLinearGroup.toGL a : GL (Fin 2) K) ≠ 1 := fun h =>
    ha1 (SpecialLinearGroup.toGL_injective (h.trans (map_one _).symm))
  refine CFSG.SectionRank.two_le_pRank_top_of_commute (x := ι (φ₂ a)) (y := ι (φ₁ a)) ?_ ?_
    (hcomm.map ι) ?_ fun n hn => ?_
  · rw [← map_pow, ← map_pow, haρ, map_one, map_one]
  · rw [← map_pow, ← map_pow, haρ, map_one, map_one]
  · intro h
    have h1 : φ₂ a = 1 := hι (h.trans (map_one ι).symm)
    have := (hφ₂ a).1
    rw [h1, map_one] at this
    exact hgl this.symm
  · have h1 : (φ₂ a) ^ n = φ₁ a := hι (by rw [map_pow]; exact hn)
    have h2 := (hφ₁ a).2
    rw [← h1, map_pow, (hφ₂ a).2, one_pow] at h2
    exact hgl h2.symm

theorem orthPlus_not_dvd_sq_sub_one_of_pRank_le_one [Finite K] (hr : 3 ≤ r) {p : ℕ} (hp : p.Prime)
    (hrank : CFSG.Open.pRank p (⊤ : Subgroup ↥(orthElementaryGroup (quadPlus r K))) ≤ 1) :
    ¬ p ∣ Nat.card K ^ 2 - 1 := fun h => by
  have := two_le_pRank_plusElementary hr hp h
  omega

theorem orthPlus_three_dvd_card_sq_sub_one [Finite K] : 3 ∣ Nat.card K ^ 2 - 1 := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hf⟩ : ∃ f : ℕ, Nat.card K = 2 ^ f := by
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩
  rw [hf, ← pow_mul, mul_comm, pow_mul]
  have := Nat.sub_one_dvd_pow_sub_one (2 ^ 2) f
  simpa using this

theorem two_le_pRank_three_plusElementary [Finite K] (hr : 3 ≤ r) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(orthElementaryGroup (quadPlus r K))) :=
  two_le_pRank_plusElementary hr Nat.prime_three orthPlus_three_dvd_card_sq_sub_one

end KPLeviSub

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
