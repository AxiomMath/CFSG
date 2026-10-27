module

public import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient
public import CFSG.CharacterTheory.Semidihedral.Principal.ActualLayerCharacteristicValuation
public import CFSG.Dihedral.FourgroupFixedOrder
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.CharacterTheory.Semidihedral.Principal.LocalParameterFiveSeventeenSupport
public import CFSG.GroupTheory.LocalCores.Components

public section

open scoped Pointwise

namespace CFSG.Semidihedral.Local.OddKernel

open CFSG.Open CFSG.Semidihedral.ActualSimpleLayerLocalPackage
  CFSG.Semidihedral.CoreFreeDihedral

variable {G : Type} [Group G]

theorem quotient_index_ne_two (K : Subgroup G) [K.Normal]
    (hG : ∀ U : Subgroup G, U.index ≠ 2) : ∀ U : Subgroup (G ⧸ K), U.index ≠ 2 := fun U hU =>
  hG (U.comap (QuotientGroup.mk' K)) (by
    have h := Subgroup.index_comap_of_surjective (H := U) (QuotientGroup.mk'_surjective K)
    rw [h]
    exact hU)

theorem inf_eq_bot_of_isPGroup_of_odd [Finite G] {S K : Subgroup G} (hS : IsPGroup 2 S)
    (hK : Odd (Nat.card K)) : S ⊓ K = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxS, hxK⟩
  rw [Subgroup.mem_bot, ← orderOf_eq_one_iff]
  obtain ⟨k, hk⟩ := hS ⟨x, hxS⟩
  have h1 : orderOf x ∣ 2 ^ k := by
    rw [← Subgroup.orderOf_mk x hxS]
    exact orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf x ∣ Nat.card K := by
    rw [← Subgroup.orderOf_mk x hxK]
    exact orderOf_dvd_natCard _
  exact Nat.eq_one_of_dvd_coprimes ((Nat.coprime_two_left.mpr hK).pow_left k) h1 h2

theorem injective_mk_comp_subtype [Finite G] (K : Subgroup G) [K.Normal]
    (hK : Odd (Nat.card K)) {S : Subgroup G} (hS : IsPGroup 2 S) :
    Function.Injective ((QuotientGroup.mk' K).comp S.subtype) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxK : (x : G) ∈ K := (QuotientGroup.eq_one_iff (x : G)).mp hx
  have h : (x : G) ∈ S ⊓ K := ⟨x.2, hxK⟩
  rw [inf_eq_bot_of_isPGroup_of_odd hS hK, Subgroup.mem_bot] at h
  exact Subtype.ext h

section Centralizer

variable (K : Subgroup G) [K.Normal] (t : G)

@[expose] def centralizerMap :
    C t →* C (QuotientGroup.mk' K t) :=
  ((QuotientGroup.mk' K).comp (C t).subtype).codRestrict (C (QuotientGroup.mk' K t)) fun x => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    show QuotientGroup.mk' K (x : G) * QuotientGroup.mk' K t =
      QuotientGroup.mk' K t * QuotientGroup.mk' K (x : G)
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp x.2]

theorem centralizerMap_apply (x : C t) :
    (centralizerMap K t x : G ⧸ K) = QuotientGroup.mk' K x := rfl

theorem centralizerMap_tInC :
    centralizerMap K t (tInC t) = tInC (QuotientGroup.mk' K t) := rfl

theorem centralizer_zpowers_eq (g : G) :
    Subgroup.centralizer ((Subgroup.zpowers g : Subgroup G) : Set G) =
      Subgroup.centralizer ({g} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem centralizerMap_surjective [Finite G] (hK : Odd (Nat.card K)) (ht : orderOf t = 2) :
    Function.Surjective (centralizerMap K t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpt : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  have hK2 : ¬ 2 ∣ Nat.card K := by
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact hK
  have h := map_centralizer_eq_of_coprime 2 K hK2 (Subgroup.zpowers t) hpt
  rw [MonoidHom.map_zpowers, centralizer_zpowers_eq, centralizer_zpowers_eq] at h
  intro y
  have hy : (y : G ⧸ K) ∈ (Subgroup.centralizer ({t} : Set G)).map (QuotientGroup.mk' K) := by
    rw [h]
    exact y.2
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

theorem centralizerMap_ker : (centralizerMap K t).ker = K.subgroupOf (C t) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    exact (QuotientGroup.eq_one_iff (x : G)).mp (congrArg Subtype.val hx)
  · intro hx
    exact Subtype.ext ((QuotientGroup.eq_one_iff (x : G)).mpr hx)

theorem centralizerMap_ker_le [Finite G] (hK : Odd (Nat.card K)) :
    (centralizerMap K t).ker ≤ N t := by
  rw [centralizerMap_ker]
  refine le_sSup ⟨inferInstance, ?_⟩
  refine (Nat.coprime_two_left.mpr hK).coprime_dvd_right ?_
  rw [← Subgroup.card_map_of_injective (C t).subtype_injective, Subgroup.subgroupOf_map_subtype]
  exact Subgroup.card_dvd_of_le inf_le_left

theorem map_N_eq [Finite G] (hK : Odd (Nat.card K)) (ht : orderOf t = 2) :
    (N t).map (centralizerMap K t) = N (QuotientGroup.mk' K t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply pPrimeCore_map_eq_of_coprime_ker 2 _ (centralizerMap_surjective K t hK ht)
  rw [centralizerMap_ker]
  refine (Nat.coprime_two_left.mpr hK).coprime_dvd_right ?_
  rw [← Subgroup.card_map_of_injective (C t).subtype_injective, Subgroup.subgroupOf_map_subtype]
  exact Subgroup.card_dvd_of_le inf_le_left

theorem map_NZ_eq [Finite G] (hK : Odd (Nat.card K)) (ht : orderOf t = 2) :
    (NZ t).map (centralizerMap K t) = NZ (QuotientGroup.mk' K t) := by
  rw [NZ, Subgroup.map_sup, map_N_eq K t hK ht, MonoidHom.map_zpowers, centralizerMap_tInC]

@[expose] def gammaMap : C t →* Gamma (QuotientGroup.mk' K t) :=
  (kappa (QuotientGroup.mk' K t)).comp (centralizerMap K t)

theorem gammaMap_surjective [Finite G] (hK : Odd (Nat.card K)) (ht : orderOf t = 2) :
    Function.Surjective (gammaMap K t) :=
  (QuotientGroup.mk'_surjective _).comp (centralizerMap_surjective K t hK ht)

theorem gammaMap_ker [Finite G] (hK : Odd (Nat.card K)) (ht : orderOf t = 2) :
    (gammaMap K t).ker = NZ t := by
  rw [gammaMap, ← MonoidHom.comap_ker, QuotientGroup.ker_mk', ← map_NZ_eq K t hK ht,
    Subgroup.comap_map_eq, sup_eq_left]
  exact (centralizerMap_ker_le K t hK).trans le_sup_left

@[expose] noncomputable def gammaEquiv [Finite G] (hK : Odd (Nat.card K)) (ht : orderOf t = 2) :
    Gamma t ≃* Gamma (QuotientGroup.mk' K t) :=
  (QuotientGroup.quotientMulEquivOfEq (gammaMap_ker K t hK ht).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (gammaMap_surjective K t hK ht))

theorem gammaEquiv_kappa [Finite G] (hK : Odd (Nat.card K)) (ht : orderOf t = 2) (x : C t) :
    gammaEquiv K t hK ht (kappa t x) = kappa (QuotientGroup.mk' K t) (centralizerMap K t x) :=
  rfl

end Centralizer

theorem centralizer_map_eq_bot_of_mulEquiv {Γ Δ : Type*} [Group Γ] [Group Δ] (θ : Γ ≃* Δ)
    (L : Subgroup Γ) (hL : Subgroup.centralizer (L : Set Γ) = ⊥) :
    Subgroup.centralizer ((L.map θ.toMonoidHom : Subgroup Δ) : Set Δ) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : θ.symm z ∈ Subgroup.centralizer (L : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff] at hz ⊢
    intro l hl
    have h1 := hz (θ l) ⟨l, hl, rfl⟩
    apply θ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h1
  rw [hL, Subgroup.mem_bot] at hz'
  rw [Subgroup.mem_bot]
  simpa using congrArg θ hz'

theorem generalizedFitting_map_of_mulEquiv {Γ Δ : Type} [Group Γ] [Group Δ] [Finite Γ]
    [Finite Δ] (θ : Γ ≃* Δ) [IsSimpleGroup (CFSG.generalizedFitting Γ)]
    (hnonab : ∃ a b : CFSG.generalizedFitting Γ, a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting Γ : Set Γ) = ⊥) :
    (CFSG.generalizedFitting Γ).map θ.toMonoidHom = CFSG.generalizedFitting Δ := by
  set L := CFSG.generalizedFitting Γ
  have hLn : L.Normal := (CFSG.LocalCores.generalized_fitting_characteristic (G := Γ)).2
  let e : L ≃* L.map θ.toMonoidHom := L.equivMapOfInjective θ.toMonoidHom θ.injective
  have : (L.map θ.toMonoidHom).Normal := hLn.map _ θ.surjective
  have : IsSimpleGroup (L.map θ.toMonoidHom) := e.symm.isSimpleGroup
  have hnonab' : ∃ x y : L.map θ.toMonoidHom, x * y ≠ y * x := by
    obtain ⟨a, b, hab⟩ := hnonab
    refine ⟨e a, e b, fun h => hab (e.injective ?_)⟩
    rw [map_mul, map_mul]
    exact h
  have hC := centralizer_map_eq_bot_of_mulEquiv θ L hcentral
  exact (generalizedFitting_eq_of_normal_simple_centralizer_eq_bot _ hnonab' hC).symm

theorem card_eq_card_inf_mul_card_map [Finite G] (K : Subgroup G) [K.Normal] (H : Subgroup G) :
    Nat.card H = Nat.card (K ⊓ H : Subgroup G) * Nat.card (H.map (QuotientGroup.mk' K)) := by
  let f : H →* G ⧸ K := (QuotientGroup.mk' K).comp H.subtype
  have hker : f.ker = K.subgroupOf H := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff (x : G)
  have hrange : f.range = H.map (QuotientGroup.mk' K) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcardker : Nat.card f.ker = Nat.card (K ⊓ H : Subgroup G) := by
    rw [hker, ← Subgroup.card_map_of_injective H.subtype_injective,
      Subgroup.subgroupOf_map_subtype]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hcardker, hrange, mul_comm]

theorem card_inf_centralizer_eq_of_isConj (K : Subgroup G) [K.Normal] {a b : G}
    (h : IsConj a b) :
    Nat.card (K ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) =
      Nat.card (K ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  have hmem : ∀ x : G, x ∈ K ⊓ Subgroup.centralizer ({a} : Set G) →
      g * x * g⁻¹ ∈ K ⊓ Subgroup.centralizer ({b} : Set G) := by
    intro x hx
    obtain ⟨hxK, hxa⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨(inferInstance : K.Normal).conj_mem x hxK g, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hxa ⊢
    rw [← hg]
    calc g * x * g⁻¹ * (g * a * g⁻¹) = g * (x * a) * g⁻¹ := by group
      _ = g * (a * x) * g⁻¹ := by rw [hxa]
      _ = g * a * g⁻¹ * (g * x * g⁻¹) := by group
  have hmem' : ∀ x : G, x ∈ K ⊓ Subgroup.centralizer ({b} : Set G) →
      g⁻¹ * x * g ∈ K ⊓ Subgroup.centralizer ({a} : Set G) := by
    intro x hx
    obtain ⟨hxK, hxb⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨by simpa using (inferInstance : K.Normal).conj_mem x hxK g⁻¹,
      ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hxb ⊢
    have ha : a = g⁻¹ * b * g := by rw [← hg]; group
    rw [ha]
    calc g⁻¹ * x * g * (g⁻¹ * b * g) = g⁻¹ * (x * b) * g := by group
      _ = g⁻¹ * (b * x) * g := by rw [hxb]
      _ = g⁻¹ * b * g * (g⁻¹ * x * g) := by group
  exact Nat.card_congr
    { toFun := fun x => ⟨g * x * g⁻¹, hmem x x.2⟩
      invFun := fun x => ⟨g⁻¹ * x * g, hmem' x x.2⟩
      left_inv := fun x => Subtype.ext (by simp only; group)
      right_inv := fun x => Subtype.ext (by simp only; group) }

theorem centralizer_zpowers_sup (a b : G) :
    Subgroup.centralizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) : Set G) =
      Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) := by
  ext x
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact ⟨(h a (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))).symm,
      (h b (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))).symm⟩
  · rintro ⟨ha, hb⟩ v hv
    have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ Subgroup.centralizer ({x} : Set G) := by
      apply sup_le
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact ha.symm
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact hb.symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hv)

theorem excess_eq_of_odd_kernel [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) (K : Subgroup G) [K.Normal]
    (hK : Odd (Nat.card K)) (p : ℕ) [Fact p.Prime] :
    let π := QuotientGroup.mk' K
    let s₀ : G := fS (s n)
    (padicValNat p (Nat.card G) : ℤ) -
        3 * padicValNat p (Nat.card (Subgroup.centralizer ({t} : Set G))) +
        2 * padicValNat p (Nat.card (Subgroup.centralizer ({t} : Set G) ⊓
          Subgroup.centralizer ({s₀} : Set G) : Subgroup G)) =
      (padicValNat p (Nat.card (G ⧸ K)) : ℤ) -
        3 * padicValNat p (Nat.card (Subgroup.centralizer ({π t} : Set (G ⧸ K)))) +
        2 * padicValNat p (Nat.card (Subgroup.centralizer ({π t} : Set (G ⧸ K)) ⊓
          Subgroup.centralizer ({π s₀} : Set (G ⧸ K)) : Subgroup (G ⧸ K))) := by
  intro π s₀
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hzt, ht2, -, hsC, hs2, hst⟩ := CFSG.Semidihedral.Principal.supplied_t_s_facts hn fS ht
  have hV := CFSG.Semidihedral.Principal.supplied_four_group_isKleinFour hn fS ht
  set V := Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ with hVdef
  have hK2 : ¬ 2 ∣ Nat.card K := by
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact hK
  have hVp : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV.card_four]; norm_num)
  have htp : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2, pow_one])
  have hCt := map_centralizer_eq_of_coprime 2 K hK2 (Subgroup.zpowers t) htp
  rw [MonoidHom.map_zpowers, centralizer_zpowers_eq, centralizer_zpowers_eq] at hCt
  have hCV := map_centralizer_eq_of_coprime 2 K hK2 V hVp
  rw [hVdef, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
    centralizer_zpowers_sup, centralizer_zpowers_sup] at hCV
  have hcardG : Nat.card G = Nat.card K * Nat.card (G ⧸ K) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup K, mul_comm]
  have hcardC := card_eq_card_inf_mul_card_map K (Subgroup.centralizer ({t} : Set G))
  rw [hCt] at hcardC
  have hcardD := card_eq_card_inf_mul_card_map K
    (Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({s₀} : Set G))
  rw [hCV] at hcardD
  have hts : t * s₀ = s₀ * t := (Subgroup.mem_centralizer_singleton_iff.mp hsC).symm
  have ht2' : t ^ 2 = 1 := by rw [← ht2, pow_orderOf_eq_one]
  have hs2' : s₀ ^ 2 = 1 := by rw [← hs2, pow_orderOf_eq_one]
  have hts2 : orderOf (t * s₀) = 2 := by
    apply orderOf_eq_prime
    · rw [Commute.mul_pow hts, ht2', hs2', one_mul]
    · intro h
      apply hst
      have h' : s₀ = t⁻¹ := eq_inv_of_mul_eq_one_right h
      exact h'.trans (inv_eq_of_mul_eq_one_right (by rw [← sq]; exact ht2'))
  have htV : t ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hsV : s₀ ∈ V := Subgroup.mem_sup_right (Subgroup.mem_zpowers s₀)
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have hs1 : s₀ ≠ 1 := by
    intro h
    have hs2'' : orderOf s₀ = 2 := hs2
    rw [h, orderOf_one] at hs2''
    exact absurd hs2'' (by norm_num)
  have hnorm : CFSG.DihedralBlueprint.NormalizedBy K V := fun v _ =>
    Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => (inferInstance : K.Normal).conj_mem x hx v,
      fun hx => by
        have := (inferInstance : K.Normal).conj_mem _ hx v⁻¹
        simpa [mul_assoc] using this⟩
  have hBW := CFSG.DihedralBlueprint.ambient_fourgroup_fixed_order_identity V K hV hK
    (CFSG.FeitThompson.isSolvable_of_odd_natCard K hK) hnorm t s₀ htV hsV ht1 hs1 hst.symm
  rw [hVdef, centralizer_zpowers_sup] at hBW
  have hconj : ∀ x : G, orderOf x = 2 →
      Nat.card (K ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) =
        Nat.card (K ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) := by
    intro x hx
    rw [← hzt]
    exact card_inf_centralizer_eq_of_isConj K
      (CFSG.Semidihedral.InvolutionFusion.ambient_involution_isConj_z n hn S fS hG x hx)
  rw [hconj s₀ hs2, hconj (t * s₀) hts2] at hBW
  have hpos : ∀ H : Subgroup G, Nat.card H ≠ 0 := fun H => Nat.card_pos.ne'
  have hposQ : ∀ H : Subgroup (G ⧸ K), Nat.card H ≠ 0 := fun H => Nat.card_pos.ne'
  have hQ : Nat.card (G ⧸ K) ≠ 0 := Nat.card_pos.ne'
  have v1 : padicValNat p (Nat.card G) = padicValNat p (Nat.card K) +
      padicValNat p (Nat.card (G ⧸ K)) := by
    rw [hcardG, padicValNat.mul (hpos K) hQ]
  have v2 := congrArg (padicValNat p) hcardC
  rw [padicValNat.mul (hpos _) (hposQ _)] at v2
  have v3 := congrArg (padicValNat p) hcardD
  rw [padicValNat.mul (hpos _) (hposQ _)] at v3
  have v4 := congrArg (padicValNat p) hBW
  rw [padicValNat.mul (hpos K) (pow_ne_zero 2 (hpos _)), padicValNat.pow _ 2,
    padicValNat.mul (mul_ne_zero (hpos _) (hpos _)) (hpos _),
    padicValNat.mul (hpos _) (hpos _)] at v4
  simp only [π]
  omega

section Regular

open scoped Classical

open CFSG.Semidihedral.Principal CFSG.TwoRankLowerBound.Helpers
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.Semidihedral.SemilinearOuterQuotient
  CFSG.Semidihedral.SemilinearOddExtensions CFSG.LyonsUnitaryFour

@[expose] def IsRegularSecondPrincipal {X : Type} [Group X] [Fintype X] (n : ℕ)
    (basis : FiniteIrreducibleCharacterBasis X) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (principal : basis.index) (t : X)
    (localBasis : FiniteIrreducibleCharacterBasis (C t)) (localPrincipal : localBasis.index)
    (s : X) (p f : ℕ) (χ₂ : basis.index) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (ρ : Gamma t →* coordinateE F),
    Nat.card F = p ^ f ∧ Function.Injective ρ ∧
    (CFSG.generalizedFitting (Gamma t)).map ρ = specialLayer F ∧ linearLayer F ≤ ρ.range ∧
    ∃ (δ₁ δ₂ δ₃ δ₄ : ℤ) (χ₁ χ₃ χ₄ : basis.index) (ψ ν : ℕ → basis.index),
      ActualPrincipalBlockFamily basis ideal principal t localBasis localPrincipal (Nat.card F)
        (if Nat.card F % 4 = 1 then 1 else -1) (2 ^ (n - 3))
        (fun c => (Nat.card {x : Omega F // ((ρ (kappa t c) : coordinateE F) :
          Equiv.Perm (Omega F)) x = x} : ℂ) - 1)
        δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν ∧
      ActualPrincipalDegreeRelations basis (Nat.card F) δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ∧
      ActualPrincipalCharacteristicValues basis t s p (Nat.card F) (2 ^ (n - 3))
        (if Nat.card F % 4 = 1 then 1 else -1) δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν

theorem isRegularSecondPrincipal_spec {X : Type} [Group X] [Fintype X] {n : ℕ}
    {basis : FiniteIrreducibleCharacterBasis X} {ideal : Ideal ComplexAlgebraicIntegers}
    [ideal.IsMaximal] {principal : basis.index}
    (hprincipal : (basis.representation principal).character = 1) {t : X}
    {localBasis : FiniteIrreducibleCharacterBasis (C t)} {localPrincipal : localBasis.index}
    {s : X} {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) {χ₂ : basis.index}
    (h : IsRegularSecondPrincipal n basis ideal principal t localBasis localPrincipal s p f χ₂) :
    let e : ℤ := if p ^ f % 4 = 1 then 1 else -1
    χ₂ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ∧
      (Module.finrank ℂ (basis.representation χ₂).vector : ℤ) =
        ((p ^ f : ℕ) : ℤ) ^ 2 - e * (p ^ f : ℕ) + 1 ∧
      ∀ l ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        Odd (Module.finrank ℂ (basis.representation l).vector) →
        (Module.finrank ℂ (basis.representation l).vector : ℤ) =
          ((p ^ f : ℕ) : ℤ) ^ 2 - e * (p ^ f : ℕ) + 1 → l = χ₂ := by
  intro e
  unfold IsRegularSecondPrincipal at h
  obtain ⟨F, hF, hFfin, ρ, hFcard, -, -, -, δ₁, δ₂, δ₃, δ₄, χ₁, χ₃, χ₄, ψ, ν, hfam, -, hchar⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hblock, -, hparity, -, -⟩ := hfam
  obtain ⟨-, -, -, -, hf₁, hf₂, hf₃, -, -, -, -, -⟩ := hchar
  rw [hFcard] at hf₁ hf₂ hf₃
  have hq3 : 3 ≤ p ^ f := by
    have hp3 : 3 ≤ p := by
      rcases hp.eq_two_or_odd' with h2 | ⟨m, hm⟩
      · subst h2; exact absurd hpodd (by decide)
      · have := hp.two_le
        omega
    calc 3 ≤ p := hp3
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  have he : e = 1 ∨ e = -1 := by
    simp only [e]
    split_ifs <;> simp
  refine ⟨?_, hf₂, ?_⟩
  · rw [hblock]
    simp
  · intro l hl hodd hdeg
    rcases (hparity l hl).mp hodd with rfl | rfl | rfl | rfl
    · exfalso
      have h1 : Module.finrank ℂ (basis.representation l).vector = 1 := by
        have h2 := congrFun hprincipal 1
        rw [FiniteComplexRepresentation.character, Representation.char_one, Pi.one_apply] at h2
        exact_mod_cast h2
      rw [h1] at hdeg
      have hq : ((p ^ f : ℕ) : ℤ) ≥ 3 := by exact_mod_cast hq3
      rcases he with he | he <;> rw [he] at hdeg <;> push_cast at hdeg <;> nlinarith
    · exfalso
      rw [hf₁] at hdeg
      have hq : ((p ^ f : ℕ) : ℤ) ≥ 3 := by exact_mod_cast hq3
      rcases he with he | he <;> rw [he] at hdeg <;> push_cast at hdeg <;> nlinarith
    · rfl
    · exfalso
      rw [hf₃] at hdeg
      have hq : ((p ^ f : ℕ) : ℤ) ≥ 3 := by exact_mod_cast hq3
      rcases he with he | he <;> rw [he] at hdeg <;> push_cast at hdeg <;> nlinarith

theorem isRegularSecondPrincipal_valuation {X : Type} [Group X] [Fintype X] {n : ℕ}
    {basis : FiniteIrreducibleCharacterBasis X} {ideal : Ideal ComplexAlgebraicIntegers}
    [ideal.IsMaximal] {principal : basis.index} {t : X}
    {localBasis : FiniteIrreducibleCharacterBasis (C t)} {localPrincipal : localBasis.index}
    {s : X} {p f : ℕ} {χ₂ : basis.index}
    (h : IsRegularSecondPrincipal n basis ideal principal t localBasis localPrincipal s p f χ₂) :
    (padicValNat p (Nat.card X) : ℤ) =
      3 * (padicValNat p (Nat.card (Subgroup.centralizer ({t} : Set X))) : ℤ) -
        2 * (padicValNat p (Nat.card (Subgroup.centralizer ({t} : Set X) ⊓
          Subgroup.centralizer ({s} : Set X) : Subgroup X)) : ℤ) := by
  unfold IsRegularSecondPrincipal at h
  obtain ⟨F, hF, hFfin, ρ, -, -, -, -, δ₁, δ₂, δ₃, δ₄, χ₁, χ₃, χ₄, ψ, ν, -, -, hchar⟩ := h
  exact hchar.2.2.2.2.2.2.2.2.2.2.2

end Regular

end CFSG.Semidihedral.Local.OddKernel
