module

public import CFSG.GH74.GLS.LU.Local.SL2Pure
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.MinParRankOne.ReeWitness
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Ree
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2ReeGrp
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma114Models

public section


namespace CFSG.LocalAnalysis.GLTheoremA.T263.DXW

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution CFSG.Open
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA.HDesc

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

private theorem prime_not_dvd_two_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ) :
    ¬ p ∣ 2 ^ k := by
  intro h
  have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h2'
  · exact hp.ne_one h1
  · exact hp2 h2'

private theorem prime_not_dvd_two_pow_mul_pred {p : ℕ} {a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ 2 ^ (2 * a + 1) - 1) (k : ℕ) :
    ¬ p ∣ 2 ^ k * (2 ^ (2 * a + 1) - 1) :=
  hp.not_dvd_mul (prime_not_dvd_two_pow hp hp2 k) hpq

private theorem relIndex_rankOneGroupOne_eq (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (rankOneGroupOne K a).relIndex (F4.reeLocalParabolic K a ⟨0, by decide⟩) =
      (2 ^ (2 * a + 1)) ^ 11 * (2 ^ (2 * a + 1) - 1) := by
  have hRP : rankOneGroupOne K a ≤ F4.reeLocalParabolic K a ⟨0, by decide⟩ :=
    CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.MinParRankOne.Ree.rankOneGroupOne_le_reeLocalParabolic
      hK
  have h := Subgroup.relIndex_mul_card (rankOneGroupOne K a)
    (F4.reeLocalParabolic K a ⟨0, by decide⟩)
  rw [inf_eq_left.2 hRP, card_rankOneGroupOne hK, card_reeLocalParabolic_zero hK] at h
  set Q := 2 ^ (2 * a + 1) with hQ
  have hsq : Q ^ 2 - 1 = (Q - 1) * (Q + 1) := by
    have hs := Nat.sq_sub_sq Q 1
    rw [one_pow] at hs
    exact hs.trans (mul_comm _ _)
  rw [hsq] at h
  set A := Q - 1 with hA
  have hQgt : 1 < Q := by rw [hQ]; exact Nat.one_lt_pow (by omega) (by norm_num)
  have hQpos : 0 < Q := by omega
  have hApos : 0 < A := by rw [hA]; omega
  have hfac : 0 < Q * (A * (Q + 1)) := Nat.mul_pos hQpos (Nat.mul_pos hApos (by omega))
  have key : (rankOneGroupOne K a).relIndex (F4.reeLocalParabolic K a ⟨0, by decide⟩) *
      (Q * (A * (Q + 1))) = (Q ^ 11 * A) * (Q * (A * (Q + 1))) := by
    rw [h]; ring
  exact Nat.mul_right_cancel hfac key

private theorem relIndex_rankOneGroupTwo_eq (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (rankOneGroupTwo K a).relIndex (F4.reeLocalParabolic K a ⟨1, by decide⟩) =
      (2 ^ (2 * a + 1)) ^ 10 * (2 ^ (2 * a + 1) - 1) := by
  have hRP : rankOneGroupTwo K a ≤ F4.reeLocalParabolic K a ⟨1, by decide⟩ :=
    CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.MinParRankOne.Ree.rankOneGroupTwo_le_reeLocalParabolic
      hK
  have h := Subgroup.relIndex_mul_card (rankOneGroupTwo K a)
    (F4.reeLocalParabolic K a ⟨1, by decide⟩)
  rw [inf_eq_left.2 hRP, card_rankOneGroupTwo ha hK, card_reeLocalParabolic_one hK] at h
  set Q := 2 ^ (2 * a + 1) with hQ
  set A := Q - 1 with hA
  have hQgt : 1 < Q := by rw [hQ]; exact Nat.one_lt_pow (by omega) (by norm_num)
  have hQpos : 0 < Q := by omega
  have hApos : 0 < A := by rw [hA]; omega
  have hfac : 0 < Q ^ 2 * A * (Q ^ 2 + 1) :=
    Nat.mul_pos (Nat.mul_pos (Nat.pow_pos hQpos) hApos) (by positivity)
  have key : (rankOneGroupTwo K a).relIndex (F4.reeLocalParabolic K a ⟨1, by decide⟩) *
      (Q ^ 2 * A * (Q ^ 2 + 1)) = (Q ^ 10 * A) * (Q ^ 2 * A * (Q ^ 2 + 1)) := by
    rw [h]; ring
  exact Nat.mul_right_cancel hfac key

private theorem card_le_of_le_reeLocalParabolic_zero (hK : Nat.card K = 2 ^ (2 * a + 1))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ 2 ^ (2 * a + 1) - 1)
    {E' : Subgroup (ModGL F4.tag K)}
    (hE'P : E' ≤ F4.reeLocalParabolic K a ⟨0, by decide⟩) (hE' : IsElemAbelian p E') :
    Nat.card E' ≤ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hE'p : IsPGroup p ↥E' := fun x => ⟨1, Subtype.ext (by simpa using hE'.2 x x.2)⟩
  have hRP : rankOneGroupOne K a ≤ F4.reeLocalParabolic K a ⟨0, by decide⟩ :=
    CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.MinParRankOne.Ree.rankOneGroupOne_le_reeLocalParabolic
      hK
  have hidx : ¬ p ∣ (rankOneGroupOne K a).relIndex (F4.reeLocalParabolic K a ⟨0, by decide⟩) := by
    rw [relIndex_rankOneGroupOne_eq hK, ← pow_mul]
    exact prime_not_dvd_two_pow_mul_pred hp hp2 hpq _
  obtain ⟨φ, hφ⟩ := exists_injective_hom_of_le hRP hidx hE'P hE'p
  let ψ : ↥E' →* SL2 K := (rankOneEquivSL K a hK).symm.toMonoidHom.comp φ
  have hψ : Function.Injective ψ := (rankOneEquivSL K a hK).symm.injective.comp hφ
  haveI : CharP K 2 := (inferInstance : CharP K F4.prime)
  have hpK : (p : K) ≠ 0 := by
    intro h0
    have h2p : 2 ∣ p := (CharP.cast_eq_zero_iff K 2 p).1 h0
    rcases (Nat.dvd_prime hp).mp h2p with h1 | h2
    · exact absurd h1 (by decide)
    · exact hp2 h2.symm
  have hcomm : ∀ x ∈ ψ.range, ∀ y ∈ ψ.range, x * y = y * x := by
    rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    show ψ u * ψ v = ψ v * ψ u
    rw [← map_mul, ← map_mul, hE'.1.is_comm.comm u v]
  have hpow : ∀ x ∈ ψ.range, x ^ p = 1 := by
    rintro _ ⟨y, rfl⟩
    rw [← map_pow, show y ^ p = 1 from Subtype.ext (hE'.2 y y.2), map_one]
  have hle := CFSG.GH74.GLS.LU.Local.sl2_elem_abelian_card_le hp hp2 hpK ψ.range hcomm hpow
  rw [Nat.card_congr (Equiv.ofInjective ψ hψ)]
  exact hle

private theorem card_le_of_le_reeLocalParabolic_one (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ 2 ^ (2 * a + 1) - 1)
    {E' : Subgroup (ModGL F4.tag K)}
    (hE'P : E' ≤ F4.reeLocalParabolic K a ⟨1, by decide⟩) (hE' : IsElemAbelian p E') :
    Nat.card E' ≤ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hfin : Finite (ModGL F4.tag K) := finite_modGL
  have hE'p : IsPGroup p ↥E' := fun x => ⟨1, Subtype.ext (by simpa using hE'.2 x x.2)⟩
  have hRP : rankOneGroupTwo K a ≤ F4.reeLocalParabolic K a ⟨1, by decide⟩ :=
    CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.MinParRankOne.Ree.rankOneGroupTwo_le_reeLocalParabolic
      hK
  have hidx : ¬ p ∣ (rankOneGroupTwo K a).relIndex (F4.reeLocalParabolic K a ⟨1, by decide⟩) := by
    rw [relIndex_rankOneGroupTwo_eq ha hK, ← pow_mul]
    exact prime_not_dvd_two_pow_mul_pred hp hp2 hpq _
  obtain ⟨φ, hφ⟩ := exists_injective_hom_of_le hRP hidx hE'P hE'p
  have hrange : IsPGroup p φ.range := hE'p.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  obtain ⟨Q, hQ⟩ := hrange.exists_le_sylow
  let e : ↥(rankOneGroupTwo K a) ≃* CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a :=
    (rankOneEquivSuzuki K a ha hK).trans
      (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK)
  haveI : IsCyclic ↥Q :=
    CFSG.BenderSuzuki.lemma114_suzuki_oddSylow_isCyclic_of_equiv e p hp2 Q
  let ι : ↥E' →* ↥Q := (Subgroup.inclusion hQ).comp φ.rangeRestrict
  have hrr : Function.Injective φ.rangeRestrict := fun x y h => hφ (congrArg Subtype.val h)
  have hι : Function.Injective ι := (Subgroup.inclusion_injective hQ).comp hrr
  exact card_le_of_embeds_in_cyclic ι hι hp.pos
    (fun x => Subtype.ext (by simpa using hE'.2 x x.2))

theorem reeGamma_card_le_of_not_dvd (hK : Nat.card K = 2 ^ (2 * a + 1)) (ha : 1 ≤ a) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ 2 ^ (2 * a + 1) - 1)
    {E T : Subgroup ↥(F4.reeGamma K a)} (hE : IsElemAbelian p E) (hT2 : IsPGroup 2 T) (hT : T ≠ ⊥)
    (hEN : E ≤ Subgroup.normalizer (T : Set ↥(F4.reeGamma K a))) : Nat.card E ≤ p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hfin : Finite (ModGL F4.tag K) := finite_modGL
  obtain ⟨j, E', hE'P, hE', hcard⟩ := exists_isElemAbelian_le_localParabolic hK hE hT2 hT hEN
  rw [← hcard]
  obtain ⟨jv, hjv⟩ := j
  have hjv2 : jv < 2 := hjv
  rcases (by omega : jv = 0 ∨ jv = 1) with rfl | rfl
  · exact card_le_of_le_reeLocalParabolic_zero hK hp hp2 hpq hE'P hE'
  · exact card_le_of_le_reeLocalParabolic_one ha hK hp hp2 hpq hE'P hE'

end CFSG.LocalAnalysis.GLTheoremA.T263.DXW
