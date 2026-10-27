module

public import CFSG.CharacterTheory.Wreathed.FullCenterOddCore
public import CFSG.CharacterTheory.Semidihedral.Principal.NormalKernelBlockInflation

public section

namespace CFSG.Wreathed

open scoped Classical
open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal

universe u v

section OddElements

abbrev OddElements (E : Type*) [Group E] := {g : E // Odd (orderOf g)}

@[expose] def oddElementsMap {E F : Type*} [Group E] [Group F] (f : E →* F) :
    OddElements E → OddElements F :=
  fun g => ⟨f g.1, g.2.of_dvd_nat (orderOf_map_dvd f g.1)⟩

@[expose] noncomputable def oddPullback {E F : Type*} [Group E] [Group F] (f : E →* F) :
    (OddElements F → ℂ) →ₗ[ℤ] (OddElements E → ℂ) :=
  LinearMap.funLeft ℤ ℂ (oddElementsMap f)

@[expose] def oddRestriction {E : Type*} [Group E] (φ : E → ℂ) : OddElements E → ℂ :=
  fun g => φ g.1

theorem oddPullback_oddRestriction {E F : Type*} [Group E] [Group F] (f : E →* F)
    (φ : F → ℂ) : oddPullback f (oddRestriction φ) = oddRestriction (φ ∘ f) := rfl

theorem oddPullback_comp {E F K : Type*} [Group E] [Group F] [Group K] (f : E →* F)
    (g : F →* K) (φ : OddElements K → ℂ) :
    oddPullback f (oddPullback g φ) = oddPullback (g.comp f) φ := rfl

@[expose] noncomputable def oddRestrictionLattice {E : Type u} [Group E] [Fintype E]
    (basis : FiniteIrreducibleCharacterBasis E) (B : Finset basis.index) :
    Submodule ℤ (OddElements E → ℂ) :=
  Submodule.span ℤ
    ((fun χ => oddRestriction (basis.representation χ).character) '' (B : Set basis.index))

theorem odd_orderOf_of_odd_orderOf_map {E F : Type*} [Group E] [Group F] [Finite E]
    (f : E →* F) (hker : Odd (Nat.card f.ker)) (g : E) (hg : Odd (orderOf (f g))) :
    Odd (orderOf g) := by
  have hk : g ^ orderOf (f g) ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
  have hodd : Odd (orderOf (g ^ orderOf (f g))) :=
    hker.of_dvd_nat (Subgroup.orderOf_dvd_natCard f.ker hk)
  have hdvd : orderOf g ∣ orderOf (f g) * orderOf (g ^ orderOf (f g)) := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul, pow_orderOf_eq_one]
  exact (hg.mul hodd).of_dvd_nat hdvd

theorem oddElementsMap_surjective {E F : Type*} [Group E] [Group F] [Finite E] (f : E →* F)
    (hf : Function.Surjective f) (hker : Odd (Nat.card f.ker)) :
    Function.Surjective (oddElementsMap f) := by
  rintro ⟨y, hy⟩
  obtain ⟨g, rfl⟩ := hf y
  exact ⟨⟨g, odd_orderOf_of_odd_orderOf_map f hker g hy⟩, rfl⟩

theorem oddPullback_injective {E F : Type*} [Group E] [Group F] [Finite E] (f : E →* F)
    (hf : Function.Surjective f) (hker : Odd (Nat.card f.ker)) :
    Function.Injective (oddPullback f) :=
  LinearMap.funLeft_injective_of_surjective _ _ _ (oddElementsMap_surjective f hf hker)

variable {E Q : Type u} [Group E] [Fintype E] [Group Q] [Fintype Q]

theorem exists_inflation_equiv (π : E →* Q) (hπ : Function.Surjective π)
    (basis : FiniteIrreducibleCharacterBasis E) (quotientBasis : FiniteIrreducibleCharacterBasis Q)
    (B : Finset basis.index) (BQ : Finset quotientBasis.index)
    (hB : ∀ χ, χ ∈ B ↔ ∃ θ ∈ BQ,
      (basis.representation χ).character = (quotientBasis.representation θ).character ∘ π) :
    ∃ Φ : BQ ≃ B, ∀ θ,
      (basis.representation (Φ θ)).character = (quotientBasis.representation θ).character ∘ π := by
  have hlift : ∀ θ : BQ, ∃ χ : B,
      (basis.representation χ).character = (quotientBasis.representation θ).character ∘ π := by
    intro θ
    obtain ⟨χ, hχ⟩ := exists_inflated_label π hπ basis quotientBasis θ
    exact ⟨⟨χ, (hB χ).mpr ⟨θ, θ.2, hχ⟩⟩, hχ⟩
  choose f hf using hlift
  have hinj : Function.Injective f := by
    intro θ θ' h
    have hcomp : (quotientBasis.representation θ).character ∘ π =
        (quotientBasis.representation θ').character ∘ π := by
      rw [← hf, ← hf, h]
    have hchar : (quotientBasis.representation θ).character =
        (quotientBasis.representation θ').character := by
      funext q
      obtain ⟨g, rfl⟩ := hπ q
      exact congrFun hcomp g
    exact Subtype.ext (quotientBasis.distinct hchar)
  have hsurj : Function.Surjective f := by
    intro χ
    obtain ⟨θ, hθ, hχθ⟩ := (hB χ).mp χ.2
    refine ⟨⟨θ, hθ⟩, Subtype.ext (basis.distinct ?_)⟩
    change (basis.representation (f ⟨θ, hθ⟩)).character = (basis.representation χ).character
    rw [hf, hχθ]
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

theorem oddRestrictionLattice_map_oddPullback (π : E →* Q)
    (basis : FiniteIrreducibleCharacterBasis E) (quotientBasis : FiniteIrreducibleCharacterBasis Q)
    (B : Finset basis.index) (BQ : Finset quotientBasis.index) (Φ : BQ ≃ B)
    (hΦ : ∀ θ,
      (basis.representation (Φ θ)).character = (quotientBasis.representation θ).character ∘ π) :
    (oddRestrictionLattice quotientBasis BQ).map (oddPullback π) =
      oddRestrictionLattice basis B := by
  rw [oddRestrictionLattice, oddRestrictionLattice, Submodule.map_span]
  congr 1
  ext φ
  simp only [Set.mem_image, Finset.mem_coe]
  constructor
  · rintro ⟨_, ⟨θ, hθ, rfl⟩, rfl⟩
    refine ⟨Φ ⟨θ, hθ⟩, (Φ ⟨θ, hθ⟩).2, ?_⟩
    rw [hΦ]
    rfl
  · rintro ⟨χ, hχ, rfl⟩
    refine ⟨_, ⟨(Φ.symm ⟨χ, hχ⟩ : quotientBasis.index), (Φ.symm ⟨χ, hχ⟩).2, rfl⟩, ?_⟩
    have h := hΦ (Φ.symm ⟨χ, hχ⟩)
    rw [Equiv.apply_symm_apply] at h
    change oddRestriction ((quotientBasis.representation _).character ∘ π) = _
    rw [← h]

@[expose] noncomputable def oddRestrictionLatticeEquiv (π : E →* Q) (hπ : Function.Surjective π)
    (hker : Odd (Nat.card π.ker)) (basis : FiniteIrreducibleCharacterBasis E)
    (quotientBasis : FiniteIrreducibleCharacterBasis Q) (B : Finset basis.index)
    (BQ : Finset quotientBasis.index)
    (hmap : (oddRestrictionLattice quotientBasis BQ).map (oddPullback π) =
      oddRestrictionLattice basis B) :
    oddRestrictionLattice quotientBasis BQ ≃ₗ[ℤ] oddRestrictionLattice basis B :=
  (Submodule.equivMapOfInjective (oddPullback π) (oddPullback_injective π hπ hker) _).trans
    (LinearEquiv.ofEq _ _ hmap)

theorem oddRestrictionLatticeEquiv_coe (π : E →* Q) (hπ : Function.Surjective π)
    (hker : Odd (Nat.card π.ker)) (basis : FiniteIrreducibleCharacterBasis E)
    (quotientBasis : FiniteIrreducibleCharacterBasis Q) (B : Finset basis.index)
    (BQ : Finset quotientBasis.index)
    (hmap : (oddRestrictionLattice quotientBasis BQ).map (oddPullback π) =
      oddRestrictionLattice basis B)
    (φ : oddRestrictionLattice quotientBasis BQ) :
    (oddRestrictionLatticeEquiv π hπ hker basis quotientBasis B BQ hmap φ :
      OddElements E → ℂ) = oddPullback π φ := rfl

end OddElements

variable {G : Type u} [Group G]

theorem orderOf_wreathModelHom_a (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    orderOf (wreathModelHom S e (Original.a (2 ^ n))) = 2 ^ n := by
  rw [orderOf_injective _ (wreathModelHom_injective S e), Original.orderOf_a]

theorem wreathModelHom_x_eq (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    wreathModelHom S e (Original.x (2 ^ n)) =
      wreathModelHom S e (Original.a (2 ^ n)) ^ (2 ^ n / 2) := by
  rw [Original.x, map_pow]

theorem exists_zpow_eq_involution [Finite G] (n : ℕ) (hn : 1 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (j : ℤ) (hj : ¬ ((2 ^ n : ℕ) : ℤ) ∣ j) :
    ∃ k : ℤ, (wreathModelHom S e (Original.a (2 ^ n)) ^ j) ^ k =
      wreathModelHom S e (Original.x (2 ^ n)) := by
  set a := wreathModelHom S e (Original.a (2 ^ n)) with ha_def
  have ha : orderOf a = 2 ^ n := orderOf_wreathModelHom_a n S e
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hhalf : 2 ^ (k + 1) / 2 = 2 ^ k := by
    rw [pow_succ, Nat.mul_div_cancel _ (by norm_num)]
  have hxorder : orderOf (a ^ (2 ^ (k + 1) / 2)) = 2 := by
    rw [hhalf, orderOf_pow_of_dvd (by positivity) (by rw [ha]; exact pow_dvd_pow 2 k.le_succ), ha,
      pow_succ, Nat.mul_div_cancel_left _ (by positivity)]
  have hjdvd : orderOf (a ^ j) ∣ 2 ^ (k + 1) := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← ha,
      pow_orderOf_eq_one, one_zpow]
  obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hjdvd
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hi
    apply hj
    rw [← ha]
    exact orderOf_dvd_iff_zpow_eq_one.mpr hi
  let K := Subgroup.zpowers a
  have hjK : a ^ j ∈ K := Subgroup.zpow_mem_zpowers a j
  have hxK : a ^ (2 ^ (k + 1) / 2) ∈ K := Subgroup.npow_mem_zpowers a _
  have hle : Subgroup.zpowers (⟨a ^ (2 ^ (k + 1) / 2), hxK⟩ : K) ≤
      Subgroup.zpowers (⟨a ^ j, hjK⟩ : K) := by
    rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers, Nat.card_zpowers,
      Subgroup.orderOf_mk, Subgroup.orderOf_mk, hxorder, hi]
    exact dvd_pow_self 2 hi0
  obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp (hle (Subgroup.mem_zpowers _))
  refine ⟨l, ?_⟩
  rw [wreathModelHom_x_eq, ← ha_def]
  have h := congrArg Subtype.val hl
  simpa only [SubgroupClass.coe_zpow] using h

abbrev centralSylowPowerCentralizer (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (j : ℤ) :
    Subgroup G :=
  Subgroup.centralizer {wreathModelHom S e (Original.a (2 ^ n)) ^ j}

theorem centralizer_zpow_le_involutionCentralizer [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (j : ℤ) (hj : ¬ ((2 ^ n : ℕ) : ℤ) ∣ j) :
    centralSylowPowerCentralizer n S e j ≤ involutionCentralizer n S e := by
  obtain ⟨k, hk⟩ := exists_zpow_eq_involution n (by omega) S e j hj
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  change g ∈ Subgroup.centralizer {wreathModelHom S e (Original.x (2 ^ n))}
  rw [Subgroup.mem_centralizer_singleton_iff, ← hk]
  exact (Commute.zpow_right (show Commute g (wreathModelHom S e (Original.a (2 ^ n)) ^ j) from
    hg) k).eq

@[expose] noncomputable def centralSylowPowerMap [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (j : ℤ) (hj : ¬ ((2 ^ n : ℕ) : ℤ) ∣ j) :
    centralSylowPowerCentralizer n S e j →* centralizerOddCoreQuotient n S e :=
  (centralizerOddCoreMap n S e).comp
    (Subgroup.inclusion (centralizer_zpow_le_involutionCentralizer n hn S e j hj))

section GroupTheory

variable [Finite G] (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (j : ℤ)

include hn in
theorem involutionCentralizer_eq_oddCore_mul_centralSylowPower
    (g : involutionCentralizer n S e) :
    ∃ r ∈ centralizerOddCore n S e, ∃ c : involutionCentralizer n S e,
      (c : G) ∈ centralSylowPowerCentralizer n S e j ∧ g = r * c := by
  obtain ⟨r, hr, c, hc, rfl⟩ := (wreathed_centralizer_full_center_odd_core n hn S e).factorization g
  refine ⟨r, hr, c, ?_, rfl⟩
  have hA : wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)
      (Original.a (2 ^ n)) ∈ centralizerFullCenter n hn S e := by
    rw [centralizerFullCenter_eq_zpowers]
    exact Subgroup.mem_zpowers _
  have hcomm := congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hc _ hA)
  have hcommG : Commute (wreathModelHom S e (Original.a (2 ^ n))) (c : G) := hcomm
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (hcommG.zpow_left j).symm.eq

variable (hj : ¬ ((2 ^ n : ℕ) : ℤ) ∣ j)

theorem centralSylowPowerMap_surjective :
    Function.Surjective (centralSylowPowerMap n hn S e j hj) := by
  intro h
  obtain ⟨g, rfl⟩ := centralizerOddCoreMap_surjective n S e h
  obtain ⟨r, hr, c, hc, rfl⟩ :=
    involutionCentralizer_eq_oddCore_mul_centralSylowPower n hn S e j g
  refine ⟨⟨c, hc⟩, ?_⟩
  have hr1 : centralizerOddCoreMap n S e r = 1 := (QuotientGroup.eq_one_iff r).mpr hr
  rw [map_mul, hr1, one_mul]
  rfl

theorem centralSylowPowerMap_ker_eq_comap :
    (centralSylowPowerMap n hn S e j hj).ker = (centralizerOddCore n S e).comap
      (Subgroup.inclusion (centralizer_zpow_le_involutionCentralizer n hn S e j hj)) := by
  ext c
  rw [MonoidHom.mem_ker, Subgroup.mem_comap]
  exact QuotientGroup.eq_one_iff _

theorem centralSylowPowerMap_ker :
    (centralSylowPowerMap n hn S e j hj).ker =
      CFSG.oddCore (centralSylowPowerCentralizer n S e j) := by
  apply le_antisymm
  · refine le_sSup ⟨inferInstance, ?_⟩
    have hdvd : Nat.card (centralSylowPowerMap n hn S e j hj).ker ∣
        Nat.card (centralizerOddCore n S e) := by
      rw [centralSylowPowerMap_ker_eq_comap]
      exact Subgroup.card_comap_dvd_of_injective _ _ (Subgroup.inclusion_injective _)
    exact (centralizerOddCore_card_odd n S e).of_dvd_nat hdvd
  · have hmap : (CFSG.oddCore (centralSylowPowerCentralizer n S e j)).map
        (centralSylowPowerMap n hn S e j hj) ≤
          CFSG.oddCore (centralizerOddCoreQuotient n S e) := by
      refine le_sSup ⟨Subgroup.Normal.map inferInstance _
        (centralSylowPowerMap_surjective n hn S e j hj), ?_⟩
      exact (weakClosure_oddCore_card _).of_dvd_nat (Subgroup.card_map_dvd _ _)
    rw [centralizerOddCoreQuotient_oddCore_eq_bot, le_bot_iff, Subgroup.map_eq_bot_iff] at hmap
    exact hmap

include hn hj in
theorem centralizerOddCore_inf_centralSylowPower :
    (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype ⊓
        centralSylowPowerCentralizer n S e j =
      (CFSG.oddCore (centralSylowPowerCentralizer n S e j)).map
        (centralSylowPowerCentralizer n S e j).subtype := by
  rw [← centralSylowPowerMap_ker n hn S e j hj, centralSylowPowerMap_ker_eq_comap]
  ext g
  constructor
  · rintro ⟨⟨r, hr, rfl⟩, hg⟩
    exact ⟨⟨r, hg⟩, hr, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨⟨Subgroup.inclusion (centralizer_zpow_le_involutionCentralizer n hn S e j hj) c, hc,
      rfl⟩, c.2⟩

theorem exists_centralSylowPower_quotient_equiv :
    ∃ η : centralSylowPowerCentralizer n S e j ⧸ CFSG.oddCore (centralSylowPowerCentralizer n S e j)
        ≃* centralizerOddCoreQuotient n S e, ∀ c : centralSylowPowerCentralizer n S e j,
      η c = centralizerOddCoreMap n S e
        (Subgroup.inclusion (centralizer_zpow_le_involutionCentralizer n hn S e j hj) c) := by
  refine ⟨(QuotientGroup.quotientMulEquivOfEq (centralSylowPowerMap_ker n hn S e j hj).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (centralSylowPowerMap_surjective n hn S e j hj)),
    fun c => ?_⟩
  rfl

end GroupTheory

section Blocks

variable [Fintype G]

structure CentralSylowPowerQuotientData (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (j : ℤ) (hj : ¬ ((2 ^ n : ℕ) : ℤ) ∣ j)
    [Fintype (centralizerOddCoreQuotient n S e)] (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal]
    (basisN : FiniteIrreducibleCharacterBasis (involutionCentralizer n S e))
    (basisH : FiniteIrreducibleCharacterBasis (centralizerOddCoreQuotient n S e))
    (basisC : FiniteIrreducibleCharacterBasis (centralSylowPowerCentralizer n S e j))
    (principalN : basisN.index) (principalH : basisH.index) (principalC : basisC.index) :
    Prop where
  le_involutionCentralizer : centralSylowPowerCentralizer n S e j ≤ involutionCentralizer n S e
  factorization : ∀ g : involutionCentralizer n S e, ∃ r ∈ centralizerOddCore n S e,
    ∃ c : involutionCentralizer n S e, (c : G) ∈ centralSylowPowerCentralizer n S e j ∧ g = r * c
  odd_core_centralizer : ∀ g : G,
    g ∈ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype ⊓
        centralSylowPowerCentralizer n S e j ↔
      g ∈ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype ∧
        g * wreathModelHom S e (Original.a (2 ^ n)) ^ j =
          wreathModelHom S e (Original.a (2 ^ n)) ^ j * g
  odd_core_inter : (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype ⊓
      centralSylowPowerCentralizer n S e j =
    (CFSG.oddCore (centralSylowPowerCentralizer n S e j)).map
      (centralSylowPowerCentralizer n S e j).subtype
  map_surjective : Function.Surjective (centralSylowPowerMap n hn S e j hj)
  map_ker : (centralSylowPowerMap n hn S e j hj).ker =
    CFSG.oddCore (centralSylowPowerCentralizer n S e j)
  map_ker_ambient : (centralSylowPowerMap n hn S e j hj).ker.map
      (centralSylowPowerCentralizer n S e j).subtype =
    (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype ⊓
      centralSylowPowerCentralizer n S e j
  quotient_equiv : ∃ η : centralSylowPowerCentralizer n S e j ⧸
      CFSG.oddCore (centralSylowPowerCentralizer n S e j) ≃* centralizerOddCoreQuotient n S e,
    ∀ c : centralSylowPowerCentralizer n S e j, η c = centralizerOddCoreMap n S e
      (Subgroup.inclusion (centralizer_zpow_le_involutionCentralizer n hn S e j hj) c)
  principal_block_inflation : ∀ χ,
    χ ∈ coefficientBlock basisN (localizedComplexIntegerRing ideal) principalN ↔
      ∃ θ ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
        (basisN.representation χ).character =
          (basisH.representation θ).character ∘ centralizerOddCoreMap n S e
  power_principal_block_inflation : ∀ ψ,
    ψ ∈ coefficientBlock basisC (localizedComplexIntegerRing ideal) principalC ↔
      ∃ θ ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
        (basisC.representation ψ).character =
          (basisH.representation θ).character ∘ centralSylowPowerMap n hn S e j hj
  correspondence : ∃ (Φ : coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH ≃
        coefficientBlock basisN (localizedComplexIntegerRing ideal) principalN)
      (Ψ : coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH ≃
        coefficientBlock basisC (localizedComplexIntegerRing ideal) principalC)
      (ρ : coefficientBlock basisN (localizedComplexIntegerRing ideal) principalN ≃
        coefficientBlock basisC (localizedComplexIntegerRing ideal) principalC)
      (eHN : oddRestrictionLattice basisH
          (coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH) ≃ₗ[ℤ]
        oddRestrictionLattice basisN
          (coefficientBlock basisN (localizedComplexIntegerRing ideal) principalN))
      (eHC : oddRestrictionLattice basisH
          (coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH) ≃ₗ[ℤ]
        oddRestrictionLattice basisC
          (coefficientBlock basisC (localizedComplexIntegerRing ideal) principalC))
      (eNC : oddRestrictionLattice basisN
          (coefficientBlock basisN (localizedComplexIntegerRing ideal) principalN) ≃ₗ[ℤ]
        oddRestrictionLattice basisC
          (coefficientBlock basisC (localizedComplexIntegerRing ideal) principalC)),
    (∀ θ, (basisN.representation (Φ θ)).character =
      (basisH.representation θ).character ∘ centralizerOddCoreMap n S e) ∧
    (∀ θ, (basisC.representation (Ψ θ)).character =
      (basisH.representation θ).character ∘ centralSylowPowerMap n hn S e j hj) ∧
    (∀ χ, (basisC.representation (ρ χ)).character = (basisN.representation χ).character ∘
      Subgroup.inclusion (centralizer_zpow_le_involutionCentralizer n hn S e j hj)) ∧
    (∀ χ, (basisC.representation (ρ χ)).character 1 = (basisN.representation χ).character 1) ∧
    (∀ χ : coefficientBlock basisN (localizedComplexIntegerRing ideal) principalN,
      Representation.IsIrreducible ((basisN.representation χ).representation.comp
        (Subgroup.inclusion (centralizer_zpow_le_involutionCentralizer n hn S e j hj)))) ∧
    (∀ θ, ρ (Φ θ) = Ψ θ) ∧
    (∀ φ, (eHN φ : OddElements (involutionCentralizer n S e) → ℂ) =
      oddPullback (centralizerOddCoreMap n S e) φ) ∧
    (∀ φ, (eHC φ : OddElements (centralSylowPowerCentralizer n S e j) → ℂ) =
      oddPullback (centralSylowPowerMap n hn S e j hj) φ) ∧
    (∀ φ, (eNC φ : OddElements (centralSylowPowerCentralizer n S e j) → ℂ) =
      oddPullback (Subgroup.inclusion (centralizer_zpow_le_involutionCentralizer n hn S e j hj))
        φ) ∧
    (∀ φ, eNC (eHN φ) = eHC φ) ∧
    (∀ (ι : Type v) (b : Module.Basis ι ℤ (oddRestrictionLattice basisN
        (coefficientBlock basisN (localizedComplexIntegerRing ideal) principalN))) (i : ι),
      ((b.map eNC) i : OddElements (centralSylowPowerCentralizer n S e j) → ℂ) =
        oddPullback (Subgroup.inclusion (centralizer_zpow_le_involutionCentralizer n hn S e j hj))
          (b i)) ∧
    (∀ (ι : Type v) (b : Module.Basis ι ℤ (oddRestrictionLattice basisH
        (coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH))) (i : ι),
      ((b.map eHN) i : OddElements (involutionCentralizer n S e) → ℂ) =
          oddPullback (centralizerOddCoreMap n S e) (b i) ∧
        ((b.map eHC) i : OddElements (centralSylowPowerCentralizer n S e j) → ℂ) =
          oddPullback (centralSylowPowerMap n hn S e j hj) (b i)) ∧
    (∀ (ι : Type v) (b : Module.Basis ι ℤ (oddRestrictionLattice basisN
        (coefficientBlock basisN (localizedComplexIntegerRing ideal) principalN)))
      (χ : coefficientBlock basisN (localizedComplexIntegerRing ideal) principalN)
      (h₁ : oddRestriction (basisC.representation (ρ χ)).character ∈ oddRestrictionLattice basisC
        (coefficientBlock basisC (localizedComplexIntegerRing ideal) principalC))
      (h₂ : oddRestriction (basisN.representation χ).character ∈ oddRestrictionLattice basisN
        (coefficientBlock basisN (localizedComplexIntegerRing ideal) principalN)),
      (b.map eNC).repr ⟨_, h₁⟩ = b.repr ⟨_, h₂⟩) ∧
    (∀ (ι : Type v) (b : Module.Basis ι ℤ (oddRestrictionLattice basisH
        (coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH)))
      (θ : coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH)
      (h₁ : oddRestriction (basisN.representation (Φ θ)).character ∈ oddRestrictionLattice basisN
        (coefficientBlock basisN (localizedComplexIntegerRing ideal) principalN))
      (h₂ : oddRestriction (basisC.representation (Ψ θ)).character ∈ oddRestrictionLattice basisC
        (coefficientBlock basisC (localizedComplexIntegerRing ideal) principalC))
      (h₃ : oddRestriction (basisH.representation θ).character ∈ oddRestrictionLattice basisH
        (coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH)),
      (b.map eHN).repr ⟨_, h₁⟩ = b.repr ⟨_, h₃⟩ ∧ (b.map eHC).repr ⟨_, h₂⟩ = b.repr ⟨_, h₃⟩)

theorem central_sylow_powers_share_odd_quotient_and_principal_block (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (j : ℤ) (hj : ¬ ((2 ^ n : ℕ) : ℤ) ∣ j)
    [Fintype (centralizerOddCoreQuotient n S e)] (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basisN : FiniteIrreducibleCharacterBasis (involutionCentralizer n S e))
    (basisH : FiniteIrreducibleCharacterBasis (centralizerOddCoreQuotient n S e))
    (basisC : FiniteIrreducibleCharacterBasis (centralSylowPowerCentralizer n S e j))
    (principalN : basisN.index) (hprincipalN : (basisN.representation principalN).character = 1)
    (principalH : basisH.index) (hprincipalH : (basisH.representation principalH).character = 1)
    (principalC : basisC.index) (hprincipalC : (basisC.representation principalC).character = 1) :
    CentralSylowPowerQuotientData.{u, v} n hn S e j hj ideal basisN basisH basisC principalN
      principalH principalC := by
  set hCjN := centralizer_zpow_le_involutionCentralizer n hn S e j hj
  set π := centralizerOddCoreMap n S e with hπdef
  set πj := centralSylowPowerMap n hn S e j hj with hπjdef
  have hπ : Function.Surjective π := centralizerOddCoreMap_surjective n S e
  have hπj : Function.Surjective πj := centralSylowPowerMap_surjective n hn S e j hj
  have hπker : π.ker = centralizerOddCore n S e := QuotientGroup.ker_mk' _
  have hπjker : πj.ker = CFSG.oddCore (centralSylowPowerCentralizer n S e j) :=
    centralSylowPowerMap_ker n hn S e j hj
  have hRodd : Odd (Nat.card π.ker) := by
    rw [hπker]
    exact centralizerOddCore_card_odd n S e
  have hRjodd : Odd (Nat.card πj.ker) := by
    rw [hπjker]
    exact weakClosure_oddCore_card _
  have hπcomp : πj = π.comp (Subgroup.inclusion hCjN) := rfl
  obtain ⟨hN1, -, -, hN4⟩ := normal_prime_kernel_principal_block_inflation_of_surjective π hπ
    basisN ideal 2 hRodd.not_two_dvd_nat basisH principalN hprincipalN principalH hprincipalH
  obtain ⟨hC1, -, -, -⟩ := normal_prime_kernel_principal_block_inflation_of_surjective πj hπj
    basisC ideal 2 hRjodd.not_two_dvd_nat basisH principalC hprincipalC principalH hprincipalH
  obtain ⟨Φ, hΦ⟩ := exists_inflation_equiv π hπ basisN basisH _ _ hN1
  obtain ⟨Ψ, hΨ⟩ := exists_inflation_equiv πj hπj basisC basisH _ _ hC1
  set ρ := Φ.symm.trans Ψ with hρdef
  have hρ : ∀ χ, (basisC.representation (ρ χ)).character =
      (basisN.representation χ).character ∘ Subgroup.inclusion hCjN := by
    intro χ
    have h1 := hΨ (Φ.symm χ)
    have h2 := hΦ (Φ.symm χ)
    rw [Equiv.apply_symm_apply] at h2
    change (basisC.representation (Ψ (Φ.symm χ))).character = _
    rw [h1, h2, hπcomp]
    rfl
  have hmapN := oddRestrictionLattice_map_oddPullback π basisN basisH _ _ Φ hΦ
  have hmapC := oddRestrictionLattice_map_oddPullback πj basisC basisH _ _ Ψ hΨ
  set eHN := oddRestrictionLatticeEquiv π hπ hRodd basisN basisH _ _ hmapN with heHN
  set eHC := oddRestrictionLatticeEquiv πj hπj hRjodd basisC basisH _ _ hmapC with heHC
  set eNC := eHN.symm.trans eHC with heNC
  have heNC_coe : ∀ φ, (eNC φ : OddElements (centralSylowPowerCentralizer n S e j) → ℂ) =
      oddPullback (Subgroup.inclusion hCjN) φ := by
    intro φ
    obtain ⟨ψ, rfl⟩ := eHN.surjective φ
    rw [heNC, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rfl
  refine ⟨hCjN, involutionCentralizer_eq_oddCore_mul_centralSylowPower n hn S e j,
    fun g => by rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff],
    centralizerOddCore_inf_centralSylowPower n hn S e j hj, hπj, hπjker, ?_,
    exists_centralSylowPower_quotient_equiv n hn S e j hj, hN1, hC1,
    ⟨Φ, Ψ, ρ, eHN, eHC, eNC, hΦ, hΨ, hρ, fun χ => ?_, fun χ => ?_, fun θ => ?_,
      fun φ => rfl, fun φ => rfl, heNC_coe, fun φ => ?_, fun ι b i => ?_, fun ι b i => ⟨rfl, rfl⟩,
      fun ι b χ h₁ h₂ => ?_, fun ι b θ h₁ h₂ h₃ => ⟨?_, ?_⟩⟩⟩
  · rw [hπjker, ← centralizerOddCore_inf_centralSylowPower n hn S e j hj]
  · rw [hρ χ]
    simp
  ·
    have hker : π.ker ≤ MonoidHom.ker (basisN.representation χ).representation :=
      (hN4 χ).mpr ⟨Φ.symm χ, by
        have h := hΦ (Φ.symm χ)
        rw [Equiv.apply_symm_apply] at h
        exact h⟩
    rw [hπker] at hker
    let ρ' : Representation ℂ (centralizerOddCoreQuotient n S e)
        (basisN.representation χ).vector :=
      QuotientGroup.lift (centralizerOddCore n S e) (basisN.representation χ).representation hker
    have hcomp : ρ'.comp π = (basisN.representation χ).representation := by
      ext g v
      rfl
    have hirr : ρ'.IsIrreducible := by
      apply CFSG.LyonsUnitaryFour.isIrreducible_of_comp_surjective π hπ
      rw [hcomp]
      exact basisN.irreducible χ
    have hres : (basisN.representation χ).representation.comp (Subgroup.inclusion hCjN) =
        ρ'.comp πj := by
      rw [hπcomp, ← MonoidHom.comp_assoc, hcomp]
    rw [hres]
    exact CFSG.LyonsUnitaryFour.isIrreducible_comp_surjective πj hπj ρ' hirr
  · rw [hρdef, Equiv.trans_apply, Equiv.symm_apply_apply]
  · rw [heNC, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  · rw [Module.Basis.map_apply, heNC_coe]
  · rw [Module.Basis.map_repr, LinearEquiv.trans_apply]
    congr 1
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [heNC_coe]
    change oddRestriction (basisC.representation (ρ χ)).character =
      oddPullback (Subgroup.inclusion hCjN) (oddRestriction (basisN.representation χ).character)
    rw [oddPullback_oddRestriction, hρ χ]
  · rw [Module.Basis.map_repr, LinearEquiv.trans_apply]
    congr 1
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    change oddRestriction (basisN.representation (Φ θ)).character =
      oddPullback π (oddRestriction (basisH.representation θ).character)
    rw [oddPullback_oddRestriction, hΦ θ]
  · rw [Module.Basis.map_repr, LinearEquiv.trans_apply]
    congr 1
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    change oddRestriction (basisC.representation (Ψ θ)).character =
      oddPullback πj (oddRestriction (basisH.representation θ).character)
    rw [oddPullback_oddRestriction, hΨ θ]

end Blocks

end CFSG.Wreathed
