module

public import CFSG.ClassicalInvolution.Q3.TL4Thm6L2A
public import CFSG.ClassicalInvolution.Q3.TL4Thm6Exit
public import CFSG.ClassicalInvolution.Q3.TA3LeafL2
public import CFSG.ClassicalInvolution.Q3.TL4MF164Dat
public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear
public import CFSG.ClassicalInvolution.Q3.TL4MF163Gam
public import CFSG.ClassicalInvolution.Q3.TL4Thm6Defs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Thm6

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.GorensteinWalter Matrix QuaternionGroup

theorem range_le_map_of_comm {Y A : Type} [Group Y] [Finite Y] [Group A] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (hd : TightDatum R S t) (hgen : TightSelfGen R) (φ : Y →* A)
    (hA : ∀ x y : A, x * y = y * x) :
    φ.range ≤ ((S : Subgroup R).map R.subtype).map φ := by
  have hH : (((S : Subgroup R).map R.subtype).map φ).comap φ = ⊤ := by
    refine hd.eq_top_of_conj hgen fun y x hx => ?_
    rw [mem_conjSub_iff] at hx
    show φ x ∈ ((S : Subgroup R).map R.subtype).map φ
    have h1 : φ x = φ (y⁻¹ * x * y) := by
      rw [map_mul, map_mul, map_inv, hA (φ y)⁻¹ (φ x), mul_assoc, inv_mul_cancel, mul_one]
    rw [h1]
    exact Subgroup.mem_map_of_mem φ hx
  rintro _ ⟨y, rfl⟩
  have hy : y ∈ (((S : Subgroup R).map R.subtype).map φ).comap φ := hH ▸ Subgroup.mem_top y
  exact hy

theorem exitIdent_l2 : ExitIdent TA3.SmallL2 := by
  intro Y _ _ _ hnab hPF R S t hd hc
  obtain ⟨p, f, hp, hp2, hf, hsm⟩ := hPF
  have hL : CFSG.Blueprint.LieModel ↥(genFittingFStar Y) .PSL 2 p f := Or.inl ⟨by decide, hsm⟩
  obtain ⟨hadm, K, _, _, hcard, ⟨e₀⟩⟩ := hsm
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
  set ι := normalPSL2ToPGammaL2 (genFittingFStar Y) K hKodd hK3 e hsurj with hιdef
  have hι : Function.Injective ι := normalPSL2ToPGammaL2_injective (genFittingFStar Y) K hKodd
    hK3 e (Nobq.centralizer_genFittingFStar_eq_bot hnab) hsurj
  have hιN := normalPSL2ToPGammaL2_apply_subtype (genFittingFStar Y) K hKodd hK3 e hsurj
  have hmemN : ∀ y : Y, ι y ∈ pGammaL2PSLRange K → y ∈ genFittingFStar Y := by
    intro y hy
    obtain ⟨z, hz⟩ := (mem_pGammaL2PSLRange_iff K _).mp hy
    have h1 : ι y = ι (e.symm z : Y) := by
      rw [hιN, MulEquiv.apply_symm_apply]
      exact hz.symm
    rw [hι h1]
    exact (e.symm z).2
  have hinN : ∀ n ∈ genFittingFStar Y, ι n ∈ pGammaL2PSLRange K := by
    intro n hn
    rw [show ι n = ι ((⟨n, hn⟩ : genFittingFStar Y) : Y) from rfl, hιN]
    exact (mem_pGammaL2PSLRange_iff K _).mpr ⟨_, rfl⟩
  obtain ⟨eS⟩ := hc.1
  set S₀ : Subgroup Y := (S : Subgroup R).map R.subtype with hS₀
  let eQ : S₀ ≃* QuaternionGroup 2 :=
    ((S : Subgroup R).equivMapOfInjective R.subtype R.subtype_injective).symm.trans eS
  let φ : QuaternionGroup 2 →* Y := S₀.subtype.comp eQ.symm.toMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp eQ.symm.injective
  have hS₀R : S₀ ≤ R := Subgroup.map_subtype_le _
  have hφR : ∀ q, φ q ∈ R := fun q => hS₀R (eQ.symm q).2
  have hSφ : ∀ x ∈ S₀, ∃ q, φ q = x := fun x hx => ⟨eQ ⟨x, hx⟩, by simp [φ]⟩
  have : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have : Finite (K ≃+* K) := TA3.finite_ringEquiv_self
  have hrt : (ι t).right = 1 := TA3.right_eq_one_of_datum hd hc ι
  have hpow : ∀ g : PGammaL2 K, (g ^ 2).right = g.right ^ 2 := fun g =>
    map_pow SemidirectProduct.rightHom g 2
  have ht2 : ∀ q, orderOf (φ q) = 2 → φ q = t := fun q h => hd.eq_of_orderOf_eq_two (hφR q) h
  have hφa2 : φ (a 2) = t := ht2 _ (by
    rw [orderOf_injective φ hφ]
    exact orderOf_eq_prime (by decide) (by decide))
  have hr2 : ∀ q, (ι (φ q)).right ^ 2 = 1 := by
    intro q
    rw [← hpow, ← map_pow, ← map_pow]
    rcases MF164.q8_sq q with h | h
    · rw [h, map_one, map_one, SemidirectProduct.one_right]
    · rw [h, hφa2, hrt]
  obtain ⟨q₀, hq₀⟩ := exists_right_ne_one hKodd (ψ := ι.comp φ) (hι.comp hφ)
  have hfe : Even f := by
    have h2 : orderOf ((ι (φ q₀)).right) = 2 := orderOf_eq_prime (hr2 q₀) hq₀
    have hdvd := orderOf_dvd_natCard ((ι (φ q₀)).right)
    rw [h2] at hdvd
    have hcardA : Nat.card (K ≃+* K) = f :=
      (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp K hcard).1
    rw [hcardA] at hdvd
    exact even_iff_two_dvd.mpr hdvd
  have h8 : 8 ∣ Nat.card K - 1 := hcard ▸ eight_dvd_pow_sub_one (hp.odd_of_ne_two hp2) hfe
  have hidxL : (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range.index ≤ 2 :=
    Nat.le_of_dvd (by norm_num)
      ((CFSG.LocalAnalysis.ComponentInitial.card_pgl_quotient_psl_dvd K).trans
        (Nat.gcd_dvd_left 2 _))
  have hcase : ∀ q, (ι (φ q)).right = 1 → (ι (φ q)).left ^ 2 ≠ 1 →
      φ q ∈ genFittingFStar Y := by
    intro q hq hq2
    have hinl := TA3.eq_inl_left_of_right_eq_one hq
    have h4 : (ι (φ q)).left ^ 4 = 1 := by
      apply (SemidirectProduct.inl_injective :
        Function.Injective (SemidirectProduct.inl : PGL2 K →* PGammaL2 K))
      rw [map_pow, ← hinl, ← map_pow, ← map_pow, MF164.q8_pow_four, map_one, map_one, map_one]
    obtain ⟨z, hz⟩ := mem_range_of_pow_four hKodd hK3 h8 hq2 h4
      (MF164.sq_mem_of_index_le_two hidxL _)
    apply hmemN
    rw [hinl, ← hz]
    exact (mem_pGammaL2PSLRange_iff K _).mpr ⟨z, rfl⟩
  obtain ⟨v, hvS, hvρ, hv2, hv4⟩ :=
    TA3.exists_mem_ker_sq_ne_one even_two eQ (SemidirectProduct.rightHom.comp ι)
  obtain ⟨qv, rfl⟩ := hSφ v hvS
  have hvr : (ι (φ qv)).right = 1 := hvρ
  have hvl : (ι (φ qv)).left ^ 2 ≠ 1 := by
    intro h
    apply hv2
    apply hι
    rw [map_pow, TA3.eq_inl_left_of_right_eq_one hvr, ← map_pow, h, map_one, map_one]
  have htN : t ∈ genFittingFStar Y := by
    have hsq : φ qv ^ 2 = t := hd.eq_of_orderOf_eq_two (R.pow_mem (hφR qv) 2)
      (orderOf_eq_prime (by rw [← pow_mul]; exact hv4) hv2)
    rw [← hsq]
    exact Subgroup.pow_mem _ (hcase qv hvr hvl) 2
  have hD : ∀ q, (ι (φ q)).right = 1 → φ q ∈ genFittingFStar Y := by
    intro q hq
    by_cases hq2 : (ι (φ q)).left ^ 2 = 1
    · have h1 : φ q ^ 2 = 1 := by
        apply hι
        rw [map_pow, TA3.eq_inl_left_of_right_eq_one hq, ← map_pow, hq2, map_one, map_one]
      by_cases h1' : φ q = 1
      · rw [h1']
        exact Subgroup.one_mem _
      · rw [ht2 q (orderOf_eq_prime h1 h1')]
        exact htN
    · exact hcase q hq hq2
  set π : Y →* CFSG.ComponentClassification.CatalogueSchreierLinearTwo.SemilinearQuotient K :=
    (QuotientGroup.mk' (pGammaL2PSLRange K)).comp ι with hπ
  have hker : π.ker = genFittingFStar Y := by
    ext y
    rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact ⟨hmemN y, hinN y⟩
  have hπ1 : ∀ q, (ι (φ q)).right = 1 → π (φ q) = 1 := fun q hq => by
    rw [← MonoidHom.mem_ker, hker]
    exact hD q hq
  have hmap : Nat.card (S₀.map π) ≤ 2 := by
    by_cases hall : ∀ q, (ι (φ q)).right = 1
    · have hbot : S₀.map π = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨x, hx, rfl⟩
        obtain ⟨q, rfl⟩ := hSφ x hx
        exact Subgroup.mem_bot.mpr (hπ1 q (hall q))
      rw [hbot, Subgroup.card_bot]
      norm_num
    obtain ⟨u, hu⟩ := not_forall.mp hall
    have hle : S₀.map π ≤ Subgroup.zpowers (π (φ u)) := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨q, rfl⟩ := hSφ x hx
      by_cases hq : (ι (φ q)).right = 1
      · rw [hπ1 q hq]
        exact Subgroup.one_mem _
      have heq := MF163.eq_of_mul_self_eq_one (by rw [← sq]; exact hr2 q)
        (by rw [← sq]; exact hr2 u) hq hu
      have h1 : (ι (φ (u⁻¹ * q))).right = 1 := by
        rw [map_mul, map_mul, map_inv, map_inv, SemidirectProduct.mul_right,
          SemidirectProduct.inv_right, heq, inv_mul_cancel]
      have h2 := hπ1 _ h1
      rw [map_mul, map_mul, map_inv, map_inv, inv_mul_eq_one] at h2
      rw [← h2]
      exact Subgroup.mem_zpowers _
    have hu2 : π (φ u) ^ 2 = 1 := by
      rw [← map_pow, ← map_pow]
      rcases MF164.q8_sq u with h | h
      · rw [h, map_one, map_one]
      · rw [h, hφa2, ← MonoidHom.mem_ker, hker]
        exact htN
    calc Nat.card (S₀.map π) ≤ Nat.card (Subgroup.zpowers (π (φ u))) :=
          Subgroup.card_le_of_le hle
      _ = orderOf (π (φ u)) := Nat.card_zpowers _
      _ ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) hu2
  have hidx : (genFittingFStar Y).index ≤ 2 := by
    rw [← hker, Subgroup.index_ker]
    exact (Subgroup.card_le_of_le (range_le_map_of_comm hd hc.2.1 π
      (CFSG.LocalAnalysis.ComponentInitial.OuterDerived.semilinearQuotient_mul_comm K))).trans
      hmap
  exact Or.inl ⟨p, f, hp, hp2, Or.inl ⟨hfe, lieModel_fstarQuot hnab (Or.inl rfl) hL, hidx⟩⟩

end CFSG.ClassicalInvolution.Q3.TL4.Thm6
