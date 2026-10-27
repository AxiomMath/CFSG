module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsHarrisIdxTools
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitTheorem1

public section

namespace CFSG.ComponentClassification.HarrisLit.N36

open CFSG Subgroup GrSLit.L34Facts
open scoped commutatorElement

variable {G : Type} [Group G]

theorem center_isPGroup [Finite G] (hO : pPrimeCore 2 G = ⊥) : IsPGroup 2 (center G) := by
  intro z
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos z).ne'
  refine ⟨a, ?_⟩
  have hyc : (z : G) ^ (2 ^ a) ∈ center G := (center G).pow_mem z.2 _
  have hN : (zpowers ((z : G) ^ (2 ^ a))).Normal :=
    normal_of_le_center (zpowers_le.mpr hyc)
  have hord : orderOf ((z : G) ^ (2 ^ a)) = b := by
    rw [orderOf_pow' _ (pow_ne_zero _ two_ne_zero), Subgroup.orderOf_coe, hab,
      Nat.gcd_eq_right (dvd_mul_right _ _), Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
  have hcop : Nat.Coprime 2 (Nat.card (zpowers ((z : G) ^ (2 ^ a)))) := by
    rw [Nat.card_zpowers, hord]
    exact (Nat.coprime_two_left).mpr hb
  have hle := le_pPrimeCore_of_normal_coprime hN hcop
  rw [hO, le_bot_iff, zpowers_eq_bot] at hle
  exact Subtype.ext (by rw [SubmonoidClass.coe_pow, hle, OneMemClass.coe_one])

theorem center_ne_bot (hq : IsQuasisimple G) (hns : ¬ IsSimpleGroup G) : center G ≠ ⊥ := by
  intro h
  apply hns
  have := hq.2.1
  exact ((QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot).symm.isSimpleGroup

theorem eq_one_of_quotAut_eq_one [Group.IsPerfect G] {τ : MulAut G} (h : quotAut τ = 1) :
    τ = 1 := by
  apply eq_one_of_mul_inv_mem_center
  intro y
  have hy : (QuotientGroup.mk (τ y) : G ⧸ center G) = QuotientGroup.mk y := by
    rw [← quotAut_mk, h, MulAut.one_apply]
  have h1 := QuotientGroup.eq.mp hy
  have h2 : y * ((τ y)⁻¹ * y)⁻¹ * y⁻¹ ∈ center G := (center G).normal_of_le_center le_rfl
    |>.conj_mem _ ((center G).inv_mem h1) y
  convert h2 using 1
  group

theorem orderOf_quotAut_eq_two (hq : IsQuasisimple G) {τ : MulAut G} (hτ : orderOf τ = 2) :
    orderOf (quotAut τ) = 2 := by
  have : Group.IsPerfect G := hq.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ fun h => ?_
  · have h2 : τ ^ 2 = 1 := by rw [← hτ, pow_orderOf_eq_one]
    rw [pow_two, ← quotAut_mul, ← pow_two, h2, quotAut_one]
  · rw [eq_one_of_quotAut_eq_one h, orderOf_one] at hτ
    exact absurd hτ (by norm_num)

theorem quotAut_mem_innAut_iff [Group.IsPerfect G] (τ : MulAut G) :
    quotAut τ ∈ innAut (G ⧸ center G) ↔ τ ∈ innAut G := by
  refine ⟨mem_innAut_of_quotAut, ?_⟩
  rintro ⟨y, rfl⟩
  exact ⟨QuotientGroup.mk y, (quotAut_conj y).symm⟩

@[expose] def barFix (τ : MulAut G) : Subgroup (G ⧸ center G) :=
  (fixedPoints τ).map (QuotientGroup.mk' (center G))

theorem barFix_le (τ : MulAut G) : barFix τ ≤ fixedPoints (quotAut τ) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_fixedPoints, QuotientGroup.mk'_apply, quotAut_mk, mem_fixedPoints.mp hx]

theorem exists_center_mul {τ : MulAut G} {x : G}
    (hx : (QuotientGroup.mk x : G ⧸ center G) ∈ fixedPoints (quotAut τ)) :
    ∃ c ∈ center G, τ x = c * x := by
  rw [mem_fixedPoints, quotAut_mk] at hx
  have h1 := QuotientGroup.eq.mp hx
  have h2 : (τ x)⁻¹ * x ∈ center G := h1
  refine ⟨((τ x)⁻¹ * x)⁻¹, (center G).inv_mem h2, ?_⟩
  have hc := mem_center_iff.mp ((center G).inv_mem h2) x
  rw [← hc]
  group

theorem commutatorElement_center_mul {c d x y : G} (hc : c ∈ center G) (hd : d ∈ center G) :
    ⁅c * x, d * y⁆ = ⁅x, y⁆ := by
  have h1 : ∀ z, c * z = z * c := fun z => (mem_center_iff.mp hc z).symm
  have h2 : ∀ z, d * z = z * d := fun z => (mem_center_iff.mp hd z).symm
  rw [commutatorElement_def, commutatorElement_def]
  calc c * x * (d * y) * (c * x)⁻¹ * (d * y)⁻¹
      = c * (x * (d * y) * x⁻¹) * c⁻¹ * (d * y)⁻¹ := by group
    _ = x * (d * y) * x⁻¹ * (d * y)⁻¹ := by rw [h1]; group
    _ = d * (x * y * x⁻¹ * y⁻¹) * d⁻¹ := by
        rw [show x * (d * y) = d * (x * y) by rw [← mul_assoc, ← h2 x, mul_assoc]]; group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [h2]; group

theorem commutator_le_barFix (τ : MulAut G) :
    ⁅fixedPoints (quotAut τ), fixedPoints (quotAut τ)⁆ ≤ barFix τ := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  obtain ⟨c, hc, hcx⟩ := exists_center_mul ha
  obtain ⟨d, hd, hdy⟩ := exists_center_mul hb
  refine ⟨⁅x, y⁆, (mem_fixedPoints.mpr ?_ : ⁅x, y⁆ ∈ fixedPoints τ), ?_⟩
  · rw [commutatorElement_def]
    simp only [map_mul, map_inv]
    rw [hcx, hdy, ← commutatorElement_def, commutatorElement_center_mul hc hd,
      commutatorElement_def]
  · simp [commutatorElement_def]

theorem barFix_subgroupOf_normal (τ : MulAut G) :
    ((barFix τ).subgroupOf (fixedPoints (quotAut τ))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_subgroupOf] at hn ⊢
  have hc : ⁅(g : G ⧸ center G), (n : G ⧸ center G)⁆ ∈ barFix τ :=
    commutator_le_barFix τ (commutator_mem_commutator g.2 n.2)
  have he : ((g * n * g⁻¹ : ↥(fixedPoints (quotAut τ))) : G ⧸ center G) =
      ⁅(g : G ⧸ center G), (n : G ⧸ center G)⁆ * (n : G ⧸ center G) := by
    simp [commutatorElement_def]
  rw [he]
  exact (barFix τ).mul_mem hc hn

@[expose] noncomputable def fixHom (τ : MulAut G) :
    ↥(fixedPoints τ) →* ↥(fixedPoints (quotAut τ)) :=
  ((QuotientGroup.mk' (center G)).domRestrict (fixedPoints τ)).codRestrict _ fun x =>
    barFix_le τ ⟨x, x.2, rfl⟩

theorem fixHom_apply (τ : MulAut G) (x : ↥(fixedPoints τ)) :
    (fixHom τ x : G ⧸ center G) = QuotientGroup.mk (x : G) :=
  rfl

theorem range_fixHom (τ : MulAut G) :
    (fixHom τ).range = (barFix τ).subgroupOf (fixedPoints (quotAut τ)) := by
  ext y
  rw [MonoidHom.mem_range, mem_subgroupOf]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.2, rfl⟩
  · rintro ⟨x, hx, hxy⟩
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

theorem inf_center_eq_bot [Finite G] (hO : pPrimeCore 2 G = ⊥) {K : Subgroup G} {p m : ℕ}
    (hL : Blueprint.LieModel (↥K ⧸ pPrimeCore 2 ↥K) .PSL 2 p m) : K ⊓ center G = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs := isSimpleGroup_of_lieModel_psl2 hL
  have hZ := CatLeaf.center_eq_bot_of_simple (nonabelian_of_lieModel_psl2 hL)
  rw [eq_bot_iff]
  rintro z ⟨hzK, hzZ⟩
  rw [mem_bot]
  set k : ↥K := ⟨z, hzK⟩
  have hk : (QuotientGroup.mk k : ↥K ⧸ pPrimeCore 2 ↥K) = 1 := by
    have hc : (QuotientGroup.mk k : ↥K ⧸ pPrimeCore 2 ↥K) ∈ center (↥K ⧸ pPrimeCore 2 ↥K) := by
      rw [mem_center_iff]
      intro w
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (mem_center_iff.mp hzZ (w : G))
    rw [hZ] at hc
    exact hc
  have hkO : k ∈ pPrimeCore 2 ↥K := (QuotientGroup.eq_one_iff k).mp hk
  have hodd : Nat.Coprime 2 (orderOf k) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard _ hkO) pPrimeCore_coprime_card
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp (center_isPGroup hO)) ⟨z, hzZ⟩
  have hkz : orderOf k = orderOf z := (Subgroup.orderOf_coe k).symm
  have hzz : orderOf (⟨z, hzZ⟩ : center G) = orderOf z :=
    (Subgroup.orderOf_coe (⟨z, hzZ⟩ : center G)).symm
  rw [hkz, ← hzz, hj] at hodd
  have hj0 : j = 0 := by
    by_contra h0
    have := Nat.Coprime.coprime_dvd_right (dvd_pow_self 2 h0) hodd
    exact absurd this (by norm_num)
  rw [hj0, pow_zero] at hj
  have := orderOf_eq_one_iff.mp hj
  exact congrArg Subtype.val this

theorem restrict_injective {K : Subgroup G} (hK : K ⊓ center G = ⊥) :
    Function.Injective ((QuotientGroup.mk' (center G)).domRestrict K) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro k hk
  rw [MonoidHom.mem_ker, MonoidHom.domRestrict_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hk
  have h1 : (k : G) ∈ K ⊓ center G := ⟨k.2, hk⟩
  rw [hK, mem_bot] at h1
  exact (mem_bot).mpr (Subtype.ext h1)

theorem nonempty_equiv_bar {K : Subgroup G} (hK : K ⊓ center G = ⊥) :
    Nonempty (↥K ≃* ↥(K.map (QuotientGroup.mk' (center G)))) :=
  ⟨(MonoidHom.ofInjective (restrict_injective hK)).trans
    (MulEquiv.subgroupCongr (MonoidHom.domRestrict_range K _))⟩

theorem isTwoComponentIn_bar [Finite G] {τ : MulAut G} {K : Subgroup G}
    (hK : IsTwoComponentIn K (fixedPoints τ)) (hKZ : K ⊓ center G = ⊥) :
    IsTwoComponentIn (K.map (QuotientGroup.mk' (center G))) (fixedPoints (quotAut τ)) := by
  have hle : K.map (QuotientGroup.mk' (center G)) ≤ fixedPoints (quotAut τ) :=
    (map_mono hK.1).trans (barFix_le τ)
  refine ⟨hle, ?_, ?_⟩
  ·
    set ψ := fixHom τ
    have hmap : (K.subgroupOf (fixedPoints τ)).map ψ =
        (K.map (QuotientGroup.mk' (center G))).subgroupOf (fixedPoints (quotAut τ)) := by
      ext y
      rw [mem_map, mem_subgroupOf]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, hxy⟩
        exact ⟨⟨x, hK.1 hx⟩, hx, Subtype.ext hxy⟩
    have hsub : ((K.subgroupOf (fixedPoints τ)).map ψ.rangeRestrict).IsSubnormal :=
      hK.2.1.map ψ.rangeRestrict_surjective
    have hrange : ψ.range.IsSubnormal := by
      rw [range_fixHom]
      exact (barFix_subgroupOf_normal τ).isSubnormal
    have hle' : (K.subgroupOf (fixedPoints τ)).map ψ ≤ ψ.range := map_le_range ψ _
    have heq : ((K.subgroupOf (fixedPoints τ)).map ψ).subgroupOf ψ.range =
        (K.subgroupOf (fixedPoints τ)).map ψ.rangeRestrict := by
      ext y
      rw [mem_subgroupOf, mem_map, mem_map]
      constructor
      · rintro ⟨x, hx, hxy⟩
        exact ⟨x, hx, Subtype.ext hxy⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
    rw [← hmap]
    exact IsSubnormal.trans hle' (heq ▸ hsub) hrange
  · obtain ⟨e⟩ := nonempty_equiv_bar hKZ
    exact isTwoQuasisimple_of_mulEquiv e hK.2.2

theorem catalog_or_chevalley [Finite G] (hq : IsQuasisimple G) (hO : pPrimeCore 2 G = ⊥)
    {p : ℕ} (h : IsOfType (InClosure (IsSimpleChevalleyOver p)) G) :
    Blueprint.Catalog (G ⧸ center G) ∨ IsSimpleChevalleyOver p (G ⧸ center G) := by
  obtain ⟨-, Y, _, hY, ⟨e⟩⟩ := h
  have hne : pPrimeCore 2 G ≠ ⊤ := by
    rw [hO]
    intro h1
    obtain ⟨x, y, hxy⟩ := hq.2.2
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    have hx : x = 1 := by
      have := mem_top x
      rw [← h1, mem_bot] at this
      exact this
    exact hxy (by rw [hx]; simp)
  have hZ := CatLeaf.fusionZStar_eq_center_of_quasisimple hq hne
  have e' : G ⧸ center G ≃* Y := (QuotientGroup.quotientMulEquivOfEq hZ.symm).trans e
  cases hY with
  | base hb =>
    obtain ⟨t, n, f, hm⟩ := hb
    exact Or.inr ⟨t, n, f, GSThmB.OddQuot.lieModel_of_equiv e'.symm hm⟩
  | blowup _ hcat _ =>
    exact Or.inl ((SectionRank.catalog_congr e').mpr hcat)

end CFSG.ComponentClassification.HarrisLit.N36
