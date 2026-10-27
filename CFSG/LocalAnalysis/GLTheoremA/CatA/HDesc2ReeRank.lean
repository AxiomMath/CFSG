module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Ree
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma114Models
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_TablesA
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.MinParRankOne.ReeWitness
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2ReeGrp

public section


namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution CFSG.Open
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem reeGamma_card_le_three (hK : Nat.card K = 2 ^ (2 * a + 1)) (ha : a = 1)
    {E T : Subgroup ↥(F4.reeGamma K a)} (hE : IsElemAbelian 3 E) (hT2 : IsPGroup 2 T) (hT : T ≠ ⊥)
    (hEN : E ≤ Subgroup.normalizer (T : Set ↥(F4.reeGamma K a))) : Nat.card E ≤ 3 := by
  classical
  subst ha
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hfin : Finite (ModGL F4.tag K) := finite_modGL
  obtain ⟨j, E', hE'P, hE', hcard⟩ := exists_isElemAbelian_le_localParabolic hK hE hT2 hT hEN
  rw [← hcard]
  have hE'p : IsPGroup 3 ↥E' := fun x => ⟨1, Subtype.ext (by simpa using hE'.2 x x.2)⟩
  obtain ⟨jv, hjv⟩ := j
  have hjv2 : jv < 2 := hjv
  rcases (by omega : jv = 0 ∨ jv = 1) with rfl | rfl
  ·
    have hRP : rankOneGroupOne K 1 ≤ F4.reeLocalParabolic K 1 ⟨0, by decide⟩ :=
      CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.MinParRankOne.Ree.rankOneGroupOne_le_reeLocalParabolic hK
    have hidx : ¬ 3 ∣ (rankOneGroupOne K 1).relIndex (F4.reeLocalParabolic K 1 ⟨0, by decide⟩) := by
      intro h3
      have h := Subgroup.relIndex_mul_card (rankOneGroupOne K 1)
        (F4.reeLocalParabolic K 1 ⟨0, by decide⟩)
      rw [inf_eq_left.2 hRP, card_rankOneGroupOne hK, card_reeLocalParabolic_zero hK] at h
      have h' : 3 * (2 ^ (2 * 1 + 1) * ((2 ^ (2 * 1 + 1)) ^ 2 - 1)) ∣
          (2 ^ (2 * 1 + 1)) ^ 12 * (2 ^ (2 * 1 + 1) - 1) ^ 2 * (2 ^ (2 * 1 + 1) + 1) := by
        rw [← h]
        exact Nat.mul_dvd_mul_right h3 _
      revert h'
      norm_num
    obtain ⟨φ, hφ⟩ := exists_injective_hom_of_le hRP hidx hE'P hE'p
    let ψ : ↥E' →* SL2 K := (rankOneEquivSL K 1 hK).symm.toMonoidHom.comp φ
    have hψ : Function.Injective ψ := (rankOneEquivSL K 1 hK).symm.injective.comp hφ
    haveI : CharP K 2 := (inferInstance : CharP K F4.prime)
    have hcomm : IsMulCommutative ψ.range := by
      refine ⟨⟨fun u v => ?_⟩⟩
      obtain ⟨u, x, rfl⟩ := u
      obtain ⟨v, y, rfl⟩ := v
      apply Subtype.ext
      show ψ x * ψ y = ψ y * ψ x
      rw [← map_mul, ← map_mul, hE'.1.is_comm.comm x y]
    have h3 : ∀ x ∈ ψ.range, x ^ 3 = 1 := by
      rintro _ ⟨y, rfl⟩
      rw [← map_pow, show y ^ 3 = 1 from Subtype.ext (hE'.2 y y.2), map_one]
    have hle := SL2Char2.sl2_card_le_three ψ.range hcomm h3
    rw [Nat.card_congr (Equiv.ofInjective ψ hψ)]
    exact hle
  ·
    have hP : ¬ 3 ∣ Nat.card (F4.reeLocalParabolic K 1 ⟨1, by decide⟩) := by
      rw [card_reeLocalParabolic_one hK]
      norm_num
    have := card_eq_one_of_not_dvd hE'P hE'p hP
    omega

theorem reeGamma_card_le_five (hK : Nat.card K = 2 ^ (2 * a + 1)) (ha : a = 2)
    {E T : Subgroup ↥(F4.reeGamma K a)} (hE : IsElemAbelian 5 E) (hT2 : IsPGroup 2 T) (hT : T ≠ ⊥)
    (hEN : E ≤ Subgroup.normalizer (T : Set ↥(F4.reeGamma K a))) : Nat.card E ≤ 5 := by
  classical
  subst ha
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI hfin : Finite (ModGL F4.tag K) := finite_modGL
  obtain ⟨j, E', hE'P, hE', hcard⟩ := exists_isElemAbelian_le_localParabolic hK hE hT2 hT hEN
  rw [← hcard]
  have hE'p : IsPGroup 5 ↥E' := fun x => ⟨1, Subtype.ext (by simpa using hE'.2 x x.2)⟩
  obtain ⟨jv, hjv⟩ := j
  have hjv2 : jv < 2 := hjv
  rcases (by omega : jv = 0 ∨ jv = 1) with rfl | rfl
  ·
    have hP : ¬ 5 ∣ Nat.card (F4.reeLocalParabolic K 2 ⟨0, by decide⟩) := by
      rw [card_reeLocalParabolic_zero hK]
      norm_num
    have := card_eq_one_of_not_dvd hE'P hE'p hP
    omega
  ·
    have hRP : rankOneGroupTwo K 2 ≤ F4.reeLocalParabolic K 2 ⟨1, by decide⟩ :=
      CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.MinParRankOne.Ree.rankOneGroupTwo_le_reeLocalParabolic hK
    have hidx : ¬ 5 ∣ (rankOneGroupTwo K 2).relIndex (F4.reeLocalParabolic K 2 ⟨1, by decide⟩) := by
      intro h5
      have h := Subgroup.relIndex_mul_card (rankOneGroupTwo K 2)
        (F4.reeLocalParabolic K 2 ⟨1, by decide⟩)
      rw [inf_eq_left.2 hRP, card_rankOneGroupTwo (by norm_num) hK, card_reeLocalParabolic_one hK] at h
      have h' : 5 * ((2 ^ (2 * 2 + 1)) ^ 2 * (2 ^ (2 * 2 + 1) - 1) * ((2 ^ (2 * 2 + 1)) ^ 2 + 1)) ∣
          (2 ^ (2 * 2 + 1)) ^ 12 * (2 ^ (2 * 2 + 1) - 1) ^ 2 * ((2 ^ (2 * 2 + 1)) ^ 2 + 1) := by
        rw [← h]
        exact Nat.mul_dvd_mul_right h5 _
      revert h'
      norm_num
    obtain ⟨φ, hφ⟩ := exists_injective_hom_of_le hRP hidx hE'P hE'p
    have hrange : IsPGroup 5 φ.range := hE'p.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
    obtain ⟨Q, hQ⟩ := hrange.exists_le_sylow
    let e : ↥(rankOneGroupTwo K 2) ≃* CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 2 :=
      (rankOneEquivSuzuki K 2 (by norm_num) hK).trans
        (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK)
    haveI : IsCyclic ↥Q :=
      CFSG.BenderSuzuki.lemma114_suzuki_oddSylow_isCyclic_of_equiv e 5 (by norm_num) Q
    let ι : ↥E' →* ↥Q := (Subgroup.inclusion hQ).comp φ.rangeRestrict
    have hrr : Function.Injective φ.rangeRestrict := fun x y h => hφ (congrArg Subtype.val h)
    have hι : Function.Injective ι := (Subgroup.inclusion_injective hQ).comp hrr
    exact card_le_of_embeds_in_cyclic ι hι (by norm_num)
      (fun x => Subtype.ext (by simpa using hE'.2 x x.2))

end CFSG.LocalAnalysis.GLTheoremA.HDesc
