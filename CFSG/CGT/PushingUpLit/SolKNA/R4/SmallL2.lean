module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.Small
public import CFSG.ClassicalInvolution.Q3.TA3LeafL2

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TA3
open CFSG.GorensteinWalter
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo (fieldAut_isCyclic)

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
variable {K : Type} [Field K] [Finite K]

theorem right_eq_one_of_datum_R (hd : TightDatum R S t) (ι : Y →* PGammaL2 K) :
    (ι t).right = 1 := by
  have : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  have : Finite (K ≃+* K) := finite_ringEquiv_self
  obtain ⟨k, hk, ⟨e⟩⟩ := hd.quat
  have : NeZero (2 ^ (k - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  set S₀ : Subgroup Y := (S : Subgroup R).map R.subtype with hS₀
  let e₀ : S₀ ≃* QuaternionGroup (2 ^ (k - 2)) :=
    ((S : Subgroup R).equivMapOfInjective R.subtype R.subtype_injective).symm.trans e
  obtain ⟨v, hvS, hvρ, hv2, hv4⟩ :=
    exists_mem_ker_sq_ne_one (Nat.even_pow.mpr ⟨even_two, by omega⟩) e₀
      (SemidirectProduct.rightHom.comp ι)
  have hvR : v ^ 2 ∈ R := Subgroup.map_subtype_le _ (S₀.pow_mem hvS 2)
  have hord : orderOf (v ^ 2) = 2 := orderOf_eq_prime (by rw [← pow_mul]; exact hv4) hv2
  have hvt : v ^ 2 = t := hd.eq_of_orderOf_eq_two hvR hord
  have h1 : (SemidirectProduct.rightHom.comp ι) t = 1 := by
    rw [← hvt, map_pow, hvρ, one_pow]
  rwa [MonoidHom.comp_apply, SemidirectProduct.rightHom_eq_right] at h1

theorem left_involution_of_datum_R (hd : TightDatum R S t) (ι : Y →* PGammaL2 K)
    (hι : Function.Injective ι) :
    ι t = SemidirectProduct.inl (ι t).left ∧ (ι t).left * (ι t).left = 1 ∧ (ι t).left ≠ 1 := by
  have hιt := eq_inl_left_of_right_eq_one (right_eq_one_of_datum_R hd ι)
  refine ⟨hιt, inl_injective_pGammaL2 ?_, fun h => ?_⟩
  · have ht2 : t * t = 1 := by rw [← pow_two, ← hd.order, pow_orderOf_eq_one]
    rw [map_mul, ← hιt, ← map_mul, ht2, map_one, map_one]
  · have hι1 : ι t = ι 1 := by rw [hιt, h, map_one, map_one]
    have ht := hd.order
    rw [hι hι1, orderOf_one] at ht
    exact absurd ht (by norm_num)

theorem tightEdgeless_of_embedding_R (hK : IsOddPrimePower (Nat.card K)) (hd : TightDatum R S t)
    (ι : Y →* PGammaL2 K) (hι : Function.Injective ι) : TightEdgeless R := by
  have : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  have : Finite (K ≃+* K) := finite_ringEquiv_self
  obtain ⟨hιt, ha, ha1⟩ := left_involution_of_datum_R hd ι hι
  refine TightDatum.edgeless_of_forall hd fun P hP hPC => ?_
  obtain ⟨k, hk, ⟨eP⟩⟩ :=
    Disconnected.AschTight.Sec6Gen.isQuatSub_of_mem_RSet hd.hypOmegaGen hP
  have : NeZero (2 ^ k) := ⟨by positivity⟩
  obtain ⟨w, hwP, hwρ, hw2, hw4⟩ := exists_mem_ker_sq_ne_one
    (Nat.even_pow.mpr ⟨even_two, by omega⟩) eP (SemidirectProduct.rightHom.comp ι)
  have hwr : (ι w).right = 1 := by
    rwa [MonoidHom.comp_apply, SemidirectProduct.rightHom_eq_right] at hwρ
  have hιw := eq_inl_left_of_right_eq_one hwr
  have hab : (ι t).left * (ι w).left = (ι w).left * (ι t).left := by
    have htw : w * t = t * w := Subgroup.mem_centralizer_singleton_iff.mp (hPC hwP)
    apply inl_injective_pGammaL2
    rw [map_mul, map_mul, ← hιt, ← hιw, ← map_mul, ← map_mul, htw]
  have hb4 : (ι w).left ^ 4 = 1 := inl_injective_pGammaL2 (by
    rw [map_pow, ← hιw, ← map_pow, hw4, map_one, map_one])
  have hb2 : (ι w).left ^ 2 ≠ 1 := fun h => hw2 (hι (by
    rw [map_pow, hιw, ← map_pow, h, map_one, map_one]))
  have hba := pgl2_sq_eq_of_commute_of_pow_four hK ha ha1 hab hb4 hb2
  have hwt : w ^ 2 = t := hι (by rw [map_pow, hιw, ← map_pow, hba, ← hιt])
  rw [← hwt]
  exact P.pow_mem hwP 2

theorem smallLeafR_l2 (r : ℕ) : SmallLeafR r SmallL2 := by
  intro Y _ _ _ hnab _ hPF R S t hd _ _
  obtain ⟨p, f, hp, hp2, hf, hadm, K, _, _, hcard, ⟨e₀⟩⟩ := hPF
  obtain ⟨-, -, -, -, h3⟩ := hadm
  have : Fact p.Prime := ⟨hp⟩
  have hKodd : IsOddPrimePower (Nat.card K) := ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hcard⟩
  have hK3 : 3 < Nat.card K := by
    have hq3 : p ^ f ≠ 3 := fun h => h3 (by rw [h])
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hpq : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    omega
  have := genFittingFStar_normal Y
  let e : genFittingFStar Y ≃* PSL2 K :=
    e₀.trans (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have hsurj := pGammaL2ToMulAutPSL2_surjective K hcard hKodd hK3
  have hι := normalPSL2ToPGammaL2_injective (genFittingFStar Y) K hKodd hK3 e
    (Nobq.centralizer_genFittingFStar_eq_bot hnab) hsurj
  exact tightEdgeless_of_embedding_R hKodd hd _ hι

end CFSG.CGT.PushingUpLit.SolKNA.R4
