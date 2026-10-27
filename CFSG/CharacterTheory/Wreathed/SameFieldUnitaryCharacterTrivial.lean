module

public import CFSG.CharacterTheory.Wreathed.SameFieldUnitaryAssembly
public import CFSG.GroupTheory.LocalCores.Layer

public section

open scoped Classical

namespace CFSG.Wreathed.SameFieldUnitary

open CFSG.Wreathed.ActualProjectiveLayer CFSG.Wreathed.OriginalStationarityCoverageCriterion
  CFSG.Wreathed.SmallerRecognitionOriginalField CFSG.TwoRankLowerBound.Helpers
  CFSG.Wreathed.FullDefectLabels

theorem eq_one_of_isPerfect {H A : Type*} [Group H] [CommGroup A] [Group.IsPerfect H]
    (φ : H →* A) (h : H) : φ h = 1 :=
  (MonoidHom.mem_ker).mp (Abelianization.commutator_subset_ker φ Group.IsPerfect.mem_commutator)

theorem orderOf_normalizerMonoidHom_congr {G : Type*} [Group G] {U U' : Subgroup G} (h : U = U')
    {g : G} (hg : g ∈ Subgroup.normalizer (U : Set G))
    (hg' : g ∈ Subgroup.normalizer (U' : Set G)) :
    orderOf (U.normalizerMonoidHom ⟨g, hg⟩) = orderOf (U'.normalizerMonoidHom ⟨g, hg'⟩) := by
  subst h
  rfl

open CFSG.Wreathed.PrimewiseConfinedCentralCore in
theorem characterTrivial_of_wreathed
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hrec : SmallerWreathedRecognition G)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq5 : 5 ≤ p ^ f)
    (hq3 : p ^ f % 4 = 3)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (centralizerSimpleLayer n hn S e)
      .PSL 2 p f)
    (hst : OriginalAllPrimeStationarity n S e) (hcov : OriginalAllPrimeCoverage n S e)
    (θ : Subgroup.centralizer ({wreathModelHom S e (Original.x (2 ^ n))} : Set G) →* ℂˣ)
    (hθS : ∀ c : Subgroup.centralizer ({wreathModelHom S e (Original.x (2 ^ n))} : Set G),
      (c : G) ∈ (S : Subgroup G) → θ c = 1)
    (hθT : ∀ g ∈ Subgroup.normalizer ((Subgroup.closure {wreathModelHom S e (Original.x (2 ^ n)),
        wreathModelHom S e (Original.x2 (2 ^ n))} : Subgroup G) : Set G),
      ∀ c c' : Subgroup.centralizer ({wreathModelHom S e (Original.x (2 ^ n))} : Set G),
        (c : G) ∈ Subgroup.centralizer ((Subgroup.closure
          {wreathModelHom S e (Original.x (2 ^ n)), wreathModelHom S e (Original.x2 (2 ^ n))} :
            Subgroup G) : Set G) →
        (c' : G) = g * c * g⁻¹ → θ c' = θ c) :
    ∀ c : Subgroup.centralizer ({wreathModelHom S e (Original.x (2 ^ n))} : Set G), θ c = 1 := by
  let _ : Fintype G := Fintype.ofFinite G
  have hp2 : p ≠ 2 := fun h => by rw [h] at hpodd; exact (Nat.not_odd_iff_even.mpr even_two) hpodd
  obtain ⟨D, -, -, hDm, hDx, hDz, -, -, -, -⟩ :=
    exists_dValueData hnonab hrec n hn S e hfour p f hp hpodd hf hq5 hq3 hmodel hst hcov
  have hDU := U_eq_modelBase S e D hDx hDz hDm
  set s : G := wreathModelHom S e (Original.s (2 ^ n)) with hs
  set t : G := wreathModelHom S e (Original.t (2 ^ n)) with ht
  have hst' : s * t = wreathModelHom S e (Original.a (2 ^ n)) := by
    rw [hs, ht, Original.a, map_mul]
  have hxst : (s * t) ^ (2 ^ n / 2) = wreathModelHom S e (Original.x (2 ^ n)) := by
    rw [hst', Original.x, map_pow]
  have hsz : s ^ (2 ^ n / 2) = wreathModelHom S e (Original.x2 (2 ^ n)) := by
    rw [hs, Original.x2, map_pow]
  set E := BaseFourCentralizerStructure.ambientOddCore
    (Subgroup.centralizer ((S : Subgroup G) : Set G)) with hE
  have hxS : wreathModelHom S e (Original.x (2 ^ n)) ∈ (S : Subgroup G) :=
    BrauerWong.wreathModelHom_mem S e _
  have hEN : E ≤ Subgroup.centralizer ({wreathModelHom S e (Original.x (2 ^ n))} : Set G) :=
    fun y hy =>
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxS)
      (BaseFourCentralizerStructure.ambientOddCore_le _ hy)
  have hθE : ∀ y : E, θ ⟨y, hEN y.2⟩ = 1 := by
    obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
    obtain ⟨eb⟩ := finiteIrreducibleCharacterBasis_exists (G := E)
    obtain ⟨nb⟩ := finiteIrreducibleCharacterBasis_exists
      (G := Subgroup.normalizer ((S : Subgroup G) : Set G))
    obtain ⟨ideal, hmax, hmem⟩ := (CFSG.BlockBasics.residue_prime_existence _ Nat.prime_two).1
    have : CharP (ComplexAlgebraicIntegers ⧸ ideal) 2 :=
      (CFSG.BlockBasics.residue_prime_existence _ Nat.prime_two).2 ideal hmax hmem
    set principal := LinearLocalTwistMoment.principalCharacterLabel basis
    have hprincipal := LinearLocalTwistMoment.principalCharacterLabel_character basis
    let θE : E →* ℂˣ := θ.comp (Subgroup.inclusion hEN)
    obtain ⟨ℓ, hℓ⟩ := CompatibleFamily.exists_linear_label eb θE
    obtain ⟨ℓ₀, hℓ₀⟩ := CompatibleFamily.exists_linear_label eb 1
    obtain ⟨hinfl, -, -, -, -, hblock, -, hinj, hprinc⟩ :=
      full_defect_block_canonical_sylow_centralizer_labels basis ideal n hn S e nb eb principal
        hprincipal
    obtain ⟨θhat, hθhat, -⟩ := hinfl ℓ
    obtain ⟨θhat₀, hθhat₀, -⟩ := hinfl ℓ₀
    obtain ⟨B, hB, hBdef⟩ := hblock ℓ θhat hθhat
    obtain ⟨σ, υ, g, hA⟩ := AdaptedBaseFusion.exists_isAdaptedBase S e hnonab hn
    have hgT : g ∈ Subgroup.normalizer ((Subgroup.closure {wreathModelHom S e (Original.x (2 ^ n)),
        wreathModelHom S e (Original.x2 (2 ^ n))} : Subgroup G) : Set G) := by
      have h : g ∈ Subgroup.normalizer ((Subgroup.closure {D.x, D.z} : Subgroup G) : Set G) :=
        D.normalizer_U_le (by rw [hDU]; exact hA.mem_normalizer)
      rwa [hDx, hDz] at h
    obtain ⟨-, hfam⟩ :=
      CompatibleFamilies.compatible_centralizer_families_and_invariant_local_extensions hnonab
        n hn S e eb
    have hU : modelBase S e = Subgroup.closure {s, t} :=
      BaseFourCentralizerStructure.modelBase_eq_actual_generated S e
    have hg' : g ∈ Subgroup.normalizer ((Subgroup.closure {s, t} : Subgroup G) : Set G) := by
      rw [← hU]
      exact hA.mem_normalizer
    have hord : orderOf ((Subgroup.closure {s, t}).normalizerMonoidHom ⟨g, hg'⟩) = 3 := by
      rw [← orderOf_normalizerMonoidHom_congr hU hA.mem_normalizer hg']
      exact hA.orderOf_conj
    obtain ⟨⟨θt, hθt⟩, hiff⟩ := hfam g hg' hord ℓ
    have hNeq : Subgroup.centralizer ({(s * t) ^ (2 ^ n / 2)} : Set G) =
        Subgroup.centralizer ({wreathModelHom S e (Original.x (2 ^ n))} : Set G) := by rw [hxst]
    let lam : Subgroup.centralizer ({(s * t) ^ (2 ^ n / 2)} : Set G) →* ℂˣ :=
      θ.comp (MulEquiv.subgroupCongr hNeq).toMonoidHom
    have hlam : ∀ (v : Subgroup.centralizer ({(s * t) ^ (2 ^ n / 2)} : Set G))
        (c : Subgroup.centralizer ({wreathModelHom S e (Original.x (2 ^ n))} : Set G)),
        (v : G) = c → lam v = θ c := by
      intro v c hvc
      show θ (MulEquiv.subgroupCongr hNeq v) = θ c
      congr 1
      exact Subtype.ext hvc
    have hψ := ((hiff θt hθt).1).mpr ⟨lam, fun v y hvy => by
        rw [hℓ y, hlam v ⟨y, hEN y.2⟩ hvy]
        rfl,
      fun v hv => by rw [hlam v ⟨v, hNeq ▸ v.2⟩ rfl]; exact hθS _ hv,
      fun c c' hc hc' => by
        rw [hlam c ⟨c, hNeq ▸ c.2⟩ rfl, hlam c' ⟨c', hNeq ▸ c'.2⟩ rfl]
        refine hθT g⁻¹ (Subgroup.inv_mem _ hgT) _ _ ?_ ?_
        · show (c : G) ∈ _
          rw [← hxst, ← hsz]
          exact hc
        · show (c' : G) = g⁻¹ * c * g⁻¹⁻¹
          rw [inv_inv]
          exact hc'⟩
    rw [hst'] at hθt
    have hflat : FlatWreathedBlock basis ideal S e B :=
      ⟨hBdef, eb, ℓ, nb, θhat, hθhat, hB, θt, hθt, hψ⟩
    obtain ⟨-, -, -, hprin, -⟩ := conditional_every_flat_block_has_one_linear_character hnonab n hn
      S e hfour p f hp hp2 hf hmodel ideal basis B hflat eb ℓ nb θhat hθhat hB g
      hA.mem_normalizer hA.orderOf_conj
    obtain ⟨hBB, -⟩ := hprin principal hprincipal
    have hBmem : B ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal := by
      rw [← hBB]
      exact coefficientBlock_self_mem _ _ _
    have hres : centralCharacterResidueHom basis ideal principal =
        centralCharacterResidueHom basis ideal B :=
      (sameCoefficientBlock_iff_centralCharacterResidueHom_eq basis ideal _ _).mp
        ((coefficientBlock_mem_iff _ _ _ _).mp hBmem)
    have hchar₀ : (eb.representation ℓ₀).character = 1 := funext fun k => by
      rw [hℓ₀ k]
      simp
    have hℓeq : ℓ = ℓ₀ := hinj ℓ ℓ₀ θhat θhat₀ hθhat hθhat₀ (by
      rw [hB, ← hres, hprinc ℓ₀ θhat₀ hchar₀ hθhat₀])
    intro y
    have h := hℓ y
    rw [hℓeq, hℓ₀ y] at h
    show θE y = 1
    apply Units.ext
    rw [← h]
    simp
  have hconf :=
    ComponentCoverConfinement.stationarity_and_original_coverage_confine_all_odd_core_elements
      hnonab n hn S e hfour p f hp hpodd hf hq5 hmodel hrec hst hcov
  obtain ⟨-, ⟨φJ, -⟩, -, -, -, hRcent, -, -, -, -, -, -, -, JS, hJSset, ⟨μ, hμ⟩, -⟩ :=
    original_primewise_coverage_and_confinement_give_central_cyclic_odd_core
      hnonab n hn S e hfour p f hp hp2 hf hmodel hcov (fun r hr hr1 => (hconf r hr hr1).1)
  have : Group.IsPerfect (CFSG.layer (centralizerOddCoreQuotient n S e)) :=
    CFSG.LocalCores.layer_isPerfect
  have hJperf := Group.IsPerfect.ofSurjective (f := φJ.symm.toMonoidHom) φJ.symm.surjective
  let N := involutionCentralizer n S e
  let A : Subgroup G := (centralizerOddCore n S e).map N.subtype
  have hAcent : ∀ a ∈ A, ∀ g ∈ N, g * a = a * g := by
    rintro _ ⟨r, hr, rfl⟩ g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (hRcent hr) ⟨g, hg⟩)
  let K := Subgroup.centralizer ((S : Subgroup G) : Set G)
  have hKN : K ≤ N := Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxS)
  have hAK : A ≤ K := fun a ha => Subgroup.mem_centralizer_iff.mpr fun g hg =>
    hAcent a ha g (sylow_le_involutionCentralizer n hn S e hg)
  have hnorm : (A.subgroupOf K).Normal := ⟨fun a ha k => by
    have hc : (k : G) * a = a * k := hAcent a ha k (hKN k.2)
    have hka : k * a * k⁻¹ = a := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hc, mul_inv_cancel_right]
    rw [hka]
    exact ha⟩
  have hodd : Odd (Nat.card (A.subgroupOf K)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv,
      Subgroup.card_map_of_injective N.subtype_injective]
    exact centralizerOddCore_card_odd n S e
  have hle := CFSG.ABGLocalTools.le_oddCore_of_normal hnorm hodd
  have hAE : ∀ r : centralizerOddCore n S e, ((r : N) : G) ∈ E := fun r =>
    ⟨⟨_, hAK ⟨r, r.2, rfl⟩⟩, hle (Subgroup.mem_subgroupOf.mpr ⟨r, r.2, rfl⟩), rfl⟩
  intro c
  let θ' : N →* ℂˣ := θ
  let c' : N := c
  obtain ⟨⟨r, j'⟩, hrj⟩ : ∃ w, μ w = c' := ⟨μ.symm c', μ.apply_symm_apply c'⟩
  have hc' : c' = (r : N) * (j' : N) := by rw [← hrj, hμ]
  have hj'mem : ((j' : N)) ∈ ((JS : Set N)) := j'.2
  rw [hJSset] at hj'mem
  obtain ⟨j, hj, s₀, hs₀, hjs⟩ := Set.mem_mul.mp hj'mem
  show θ' c' = 1
  rw [hc', ← hjs, map_mul, map_mul]
  have h1 : θ' (r : N) = 1 := hθE ⟨_, hAE r⟩
  have h2 : θ' j = 1 := eq_one_of_isPerfect (θ'.comp (Subgroup.subtype _)) ⟨j, hj⟩
  have h3 : θ' s₀ = 1 := by
    apply hθS
    have hs₀' : s₀ ∈ (centralizerSylow n hn S e : Subgroup N) := hs₀
    rw [centralizerSylow, Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hs₀'
    exact hs₀'
  rw [h1, h2, h3, one_mul, one_mul]

theorem wreathedCharacterTrivial
    : WreathedCharacterTrivialStatement := by
  intro G _ _ _ hnonab hrec n hn S e hfour p f hp hpodd hf hq5 hq3 hmodel hst hcov θ hθS hθT
  exact characterTrivial_of_wreathed hnonab hrec n hn S e hfour p f hp hpodd hf hq5 hq3 hmodel
    hst hcov θ hθS hθT

theorem unitaryBranch_of_dValueCore
    (hcore : DValueCoreStatement) :
    CFSG.Wreathed.RecognitionFromGaps.UnitaryBranchStatement :=
  unitaryBranch_of_core hcore wreathedCharacterTrivial

end CFSG.Wreathed.SameFieldUnitary
