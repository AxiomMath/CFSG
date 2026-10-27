module

public import CFSG.ClassicalInvolution.Q3.TA3LeafL2Tools
public import CFSG.ClassicalInvolution.Q3.TA3SmallCriteria
public import CFSG.ClassicalInvolution.SmallCases.NobqSmall
public import CFSG.ClassicalInvolution.Q3.TA3SmallDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.GorensteinWalter
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo (fieldAut_isCyclic)
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem inl_injective_pGammaL2 :
    Function.Injective (SemidirectProduct.inl : PGL2 K →* PGammaL2 K) :=
  SemidirectProduct.inl_injective

omit [Finite K] in
theorem eq_inl_left_of_right_eq_one {z : PGammaL2 K} (hz : z.right = 1) :
    z = SemidirectProduct.inl z.left := by
  have h := SemidirectProduct.inl_left_mul_inr_right z
  rw [hz, map_one, mul_one] at h
  exact h.symm

theorem finite_ringEquiv_self : Finite (K ≃+* K) :=
  Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) fun _ _ h => RingEquiv.ext (congrFun h)

theorem tight_right_eq_one_of_odd (hd : TightDatum R S t) (hgen : TightSelfGen R)
    (ι : Y →* PGammaL2 K) {y : Y} (hy : Odd (orderOf y)) : (ι y).right = 1 := by
  have : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  set ρ : Y →* (K ≃+* K) := SemidirectProduct.rightHom.comp ι with hρ
  set S₀ : Subgroup Y := (S : Subgroup R).map R.subtype with hS₀
  have hcomm : ∀ u v : K ≃+* K, u * v = v * u := fun u v =>
    (IsCyclic.isMulCommutative (α := K ≃+* K)).is_comm.comm u v
  have hNn : (S₀.map ρ).Normal := ⟨fun n hn g => by rwa [hcomm g n, mul_inv_cancel_right]⟩
  have hM : (S₀.map ρ).comap ρ = ⊤ :=
    TightDatum.eq_top_of_normal_le hd hgen (hNn.comap ρ) fun s hs => Subgroup.mem_map_of_mem ρ hs
  have hyM : ρ y ∈ S₀.map ρ := by
    have : y ∈ (S₀.map ρ).comap ρ := hM ▸ Subgroup.mem_top y
    exact this
  have h2 : IsPGroup 2 (S₀.map ρ) := (S.isPGroup'.map R.subtype).map ρ
  obtain ⟨k, hk⟩ := h2 ⟨ρ y, hyM⟩
  have hk' : ρ y ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hcop : Nat.Coprime (2 ^ k) (orderOf y) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hy)
  have h1 : orderOf (ρ y) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hk') hcop)
      (orderOf_map_dvd ρ y)
  have h3 : ρ y = 1 := orderOf_eq_one_iff.mp h1
  rwa [hρ, MonoidHom.comp_apply, SemidirectProduct.rightHom_eq_right] at h3

theorem right_eq_one_of_datum (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (ι : Y →* PGammaL2 K) : (ι t).right = 1 := by
  have : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  have : Finite (K ≃+* K) := finite_ringEquiv_self
  obtain ⟨e⟩ := hc.1
  set S₀ : Subgroup Y := (S : Subgroup R).map R.subtype with hS₀
  let e₀ : S₀ ≃* QuaternionGroup 2 :=
    ((S : Subgroup R).equivMapOfInjective R.subtype R.subtype_injective).symm.trans e
  obtain ⟨v, hvS, hvρ, hv2, hv4⟩ :=
    exists_mem_ker_sq_ne_one even_two e₀ (SemidirectProduct.rightHom.comp ι)
  have hvR : v ^ 2 ∈ R := Subgroup.map_subtype_le _ (S₀.pow_mem hvS 2)
  have hord : orderOf (v ^ 2) = 2 := orderOf_eq_prime (by rw [← pow_mul]; exact hv4) hv2
  have hvt : v ^ 2 = t := hd.eq_of_orderOf_eq_two hvR hord
  have h1 : (SemidirectProduct.rightHom.comp ι) t = 1 := by
    rw [← hvt, map_pow, hvρ, one_pow]
  rwa [MonoidHom.comp_apply, SemidirectProduct.rightHom_eq_right] at h1

theorem left_involution_of_datum (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (ι : Y →* PGammaL2 K) (hι : Function.Injective ι) :
    ι t = SemidirectProduct.inl (ι t).left ∧ (ι t).left * (ι t).left = 1 ∧ (ι t).left ≠ 1 := by
  have hιt := eq_inl_left_of_right_eq_one (right_eq_one_of_datum hd hc ι)
  refine ⟨hιt, inl_injective_pGammaL2 ?_, fun h => ?_⟩
  · have ht2 : t * t = 1 := by rw [← pow_two, ← hd.order, pow_orderOf_eq_one]
    rw [map_mul, ← hιt, ← map_mul, ht2, map_one, map_one]
  · have hι1 : ι t = ι 1 := by rw [hιt, h, map_one, map_one]
    have ht := hd.order
    rw [hι hι1, orderOf_one] at ht
    exact absurd ht (by norm_num)

theorem tightEdgeless_of_embedding (hK : IsOddPrimePower (Nat.card K)) (hd : TightDatum R S t)
    (hc : TightCls Y R S t) (ι : Y →* PGammaL2 K) (hι : Function.Injective ι) :
    TightEdgeless R := by
  have : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  have : Finite (K ≃+* K) := finite_ringEquiv_self
  obtain ⟨hιt, ha, ha1⟩ := left_involution_of_datum hd hc ι hι
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

theorem not_tightActs3_of_embedding (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (ι : Y →* PGammaL2 K) (hι : Function.Injective ι) : ¬ TightActs3 R t := by
  obtain ⟨hιt, -, ha1⟩ := left_involution_of_datum hd hc ι hι
  set C := Subgroup.centralizer ({t} : Set Y) with hC
  have hinl : ∀ g : PGL2 K, orderOf (SemidirectProduct.inl g : PGammaL2 K) = orderOf g :=
    fun g => orderOf_injective _ inl_injective_pGammaL2 g
  have hleft : ∀ c : C, Odd (orderOf c) →
      ι c = SemidirectProduct.inl (ι c).left ∧ Odd (orderOf (ι c).left) ∧
        (ι c).left * (ι t).left = (ι t).left * (ι c).left := by
    intro c hco
    rw [← Subgroup.orderOf_coe] at hco
    have hιc := eq_inl_left_of_right_eq_one (tight_right_eq_one_of_odd hd hc.2.1 ι hco)
    refine ⟨hιc, ?_, ?_⟩
    · rwa [← hinl, ← hιc, orderOf_injective ι hι]
    · have h : (c : Y) * t = t * c := Subgroup.mem_centralizer_singleton_iff.mp c.2
      apply inl_injective_pGammaL2
      rw [map_mul, map_mul, ← hιc, ← hιt, ← map_mul, ← map_mul, h]
  have hcomm : ∀ c d : C, Odd (orderOf c) → Odd (orderOf d) → c * d = d * c := by
    intro c d hco hdo
    obtain ⟨hιc, hco', hca⟩ := hleft c hco
    obtain ⟨hιd, hdo', hda⟩ := hleft d hdo
    have hcd := pgl2_commute_of_odd_of_commute ha1 hca hda hco' hdo'
    apply Subtype.ext
    apply hι
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, hιc, hιd, ← map_mul, ← map_mul, hcd]
  let O : Subgroup C :=
    { carrier := {c | Odd (orderOf c)}
      mul_mem' := fun {c d} hco hdo =>
        Odd.of_dvd_nat (hco.mul hdo) (Commute.orderOf_mul_dvd_mul_orderOf (hcomm c d hco hdo))
      one_mem' := by simp
      inv_mem' := fun {c} hco => by simpa [orderOf_inv] using hco }
  have hOn : O.Normal := ⟨fun n hn g => by
    show Odd (orderOf (g * n * g⁻¹))
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hn⟩
  have hOodd : Odd (Nat.card O) := by
    by_contra h
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := O) 2
      (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp h))
    have hzO : Odd (orderOf (z : C)) := z.2
    rw [Subgroup.orderOf_coe, hz] at hzO
    exact absurd hzO (Nat.not_odd_iff_even.mpr even_two)
  have hOle : O ≤ CFSG.oddCore C := le_sSup ⟨hOn, hOodd⟩
  refine TightDatum.not_acts3_of_forall hd fun x hxC k hx3 =>
    ⟨x, ?_, 1, Subgroup.one_mem _, (mul_one x).symm⟩
  have hxO : (⟨x, hxC⟩ : C) ∈ O := by
    show Odd (orderOf (⟨x, hxC⟩ : C))
    rw [Subgroup.orderOf_mk]
    exact Odd.of_dvd_nat (Odd.pow ⟨1, rfl⟩) (orderOf_dvd_of_pow_eq_one hx3)
  exact ⟨⟨x, hxC⟩, hOle hxO, rfl⟩

theorem smallSimpleLeaf_l2 : SmallSimpleLeaf SmallL2 := by
  intro Y _ _ _ _ hnab _ hPF R S t hd hc _
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
  exact Or.inl (Or.inr (Or.inl ⟨tightEdgeless_of_embedding hKodd hd hc _ hι,
    not_tightActs3_of_embedding hd hc _ hι⟩))

end CFSG.ClassicalInvolution.Q3.TA3
