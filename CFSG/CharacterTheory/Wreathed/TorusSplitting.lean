module

public import CFSG.CharacterTheory.Wreathed.TorusSplittingSupport
public import CFSG.CharacterTheory.Wreathed.TorusSplittingLocal
public import CFSG.CharacterTheory.Wreathed.ConditionalCorrectedThreeCycle
public import CFSG.CharacterTheory.Wreathed.SylowCentralizerOddFieldFactor
public import CFSG.CharacterTheory.Wreathed.TorusSplittingTransfer

public section

open scoped Classical

namespace CFSG.Wreathed.TorusSplitting

open CFSG.Semidihedral.OddFieldLift CFSG.Semidihedral.SemilinearOddExtensions
  CFSG.Wreathed.ActualProjectiveLayer CFSG.Wreathed.BaseFourCentralizerStructure
  CFSG.Wreathed.OddFieldTorus CFSG.ComponentClassification.CatalogueSchreierLinearTwo

variable {G : Type} [Group G]

abbrev torusCore (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) : Subgroup G :=
  ambientOddCore (Subgroup.centralizer
    (Subgroup.closure {wreathModelHom S e (Original.s (2 ^ n)) ^ (2 ^ n / 2),
      wreathModelHom S e (Original.t (2 ^ n)) ^ (2 ^ n / 2)} : Set G))

theorem torusCore_le (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    torusCore n S e ≤ involutionCentralizer n S e := by
  have h := CompatibleFamilies.oddCore_four_le_centralizer S e
  rw [CompatibleFamilies.x_eq_modelHom S e] at h
  exact h

@[expose] def torusFixedCore (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) : Subgroup G :=
  (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype ⊓
    Subgroup.centralizer
      (Subgroup.closure {wreathModelHom S e (Original.s (2 ^ n)) ^ (2 ^ n / 2),
        wreathModelHom S e (Original.t (2 ^ n)) ^ (2 ^ n / 2)} : Set G)

instance torusFixedCore_normal (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    ((torusFixedCore n S e).subgroupOf (torusCore n S e)).Normal := by
  refine ⟨fun y hy k => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hy ⊢
  obtain ⟨⟨r, hr, hry⟩, hyC⟩ := hy
  have hkN : (k : G) ∈ involutionCentralizer n S e := torusCore_le n S e k.2
  have hkC : (k : G) ∈ Subgroup.centralizer
      (Subgroup.closure {wreathModelHom S e (Original.s (2 ^ n)) ^ (2 ^ n / 2),
        wreathModelHom S e (Original.t (2 ^ n)) ^ (2 ^ n / 2)} : Set G) :=
    ambientOddCore_le _ k.2
  refine ⟨⟨⟨k, hkN⟩ * r * (⟨k, hkN⟩ : involutionCentralizer n S e)⁻¹,
    (inferInstance : (centralizerOddCore n S e).Normal).conj_mem r hr _, ?_⟩, ?_⟩
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hry]
    rfl
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hkC hyC) (Subgroup.inv_mem _ hkC)

@[expose] noncomputable def fieldCharacter [Finite G] (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (F : Type) [Field F] [Finite F] (sigmaGroup : Subgroup (F ≃+* F))
    (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
    (hrange : ρ.range = Gamma F sigmaGroup) : involutionCentralizer n S e →* sigmaGroup :=
  (CFSG.Wreathed.SylowCentralizerOddField.fieldProjection F sigmaGroup).comp
    ((ρ.codRestrict (Gamma F sigmaGroup) fun g => hrange ▸ MonoidHom.mem_range.mpr ⟨g, rfl⟩).comp
      ((centralizerFullQuotientMap n hn S e).comp (centralizerOddCoreMap n S e)))

theorem centralizer_four_le (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup.centralizer
      (Subgroup.closure {wreathModelHom S e (Original.s (2 ^ n)) ^ (2 ^ n / 2),
        wreathModelHom S e (Original.t (2 ^ n)) ^ (2 ^ n / 2)} : Set G) ≤
      involutionCentralizer n S e := by
  change _ ≤ Subgroup.centralizer {wreathModelHom S e (Original.x (2 ^ n))}
  refine Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ?_)
  rw [← BrauerWong.modelHom_x2_mul_t_half S e]
  refine Subgroup.mul_mem _ (Subgroup.subset_closure ?_) (Subgroup.subset_closure ?_)
  · left
    rw [Original.x2, map_pow]
  · right
    rw [map_pow]
    exact Set.mem_singleton _

theorem torusFixedCore_le_torusCore [Finite G] (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) : torusFixedCore n S e ≤ torusCore n S e := by
  set C := Subgroup.centralizer
    (Subgroup.closure {wreathModelHom S e (Original.s (2 ^ n)) ^ (2 ^ n / 2),
      wreathModelHom S e (Original.t (2 ^ n)) ^ (2 ^ n / 2)} : Set G) with hC
  have hCN : C ≤ involutionCentralizer n S e := centralizer_four_le n S e
  have hAC : torusFixedCore n S e ≤ C := inf_le_right
  have hnormal : ((torusFixedCore n S e).subgroupOf C).Normal := by
    refine ⟨fun a ha c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    obtain ⟨⟨r, hr, hra⟩, haC⟩ := ha
    refine ⟨⟨⟨c, hCN c.2⟩ * r * (⟨c, hCN c.2⟩ : involutionCentralizer n S e)⁻¹,
      (inferInstance : (centralizerOddCore n S e).Normal).conj_mem r hr _, ?_⟩, ?_⟩
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hra]
      rfl
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ c.2 haC) (Subgroup.inv_mem _ c.2)
  have hodd : Odd (Nat.card ((torusFixedCore n S e).subgroupOf C)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv]
    have hRodd : Odd (Nat.card ((centralizerOddCore n S e).map
        (involutionCentralizer n S e).subtype)) := by
      rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
      exact CFSG.ComponentClassification.OddCore.odd_card _
    exact hRodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hle : (torusFixedCore n S e).subgroupOf C ≤ CFSG.oddCore C :=
    le_sSup (show _ ∈ {K : Subgroup C | K.Normal ∧ Odd (Nat.card K)} from ⟨hnormal, hodd⟩)
  intro a ha
  exact ⟨⟨a, hAC ha⟩, hle (Subgroup.mem_subgroupOf.mpr ha), rfl⟩

theorem boundaryProduct_le_ker [Finite G] (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (F : Type) [Field F] [Finite F] (sigmaGroup : Subgroup (F ≃+* F))
    (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
    (hrange : ρ.range = Gamma F sigmaGroup) (η : G)
    (hη : CompatibleFamilies.boundaryCommutator S e η ≤
      (fieldCharacter n hn S e F sigmaGroup ρ hrange).ker.map
        (involutionCentralizer n S e).subtype) :
    CompatibleFamilies.boundaryProduct S e η ≤
      (fieldCharacter n hn S e F sigmaGroup ρ hrange).ker.map
        (involutionCentralizer n S e).subtype := by
  unfold CompatibleFamilies.boundaryProduct
  rw [CompatibleFamilies.x_eq_modelHom S e]
  exact sup_le hη (Subgroup.map_mono (commutator_le_ker_of_comm _
    (fieldAut_subgroup_comm sigmaGroup)))

theorem sigma_card_eq_one_of_le_ker [Finite G] (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (F : Type) [Field F] [Finite F] (sigmaGroup : Subgroup (F ≃+* F))
    (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
    (hcard : Nat.card F = p ^ f) (hodd : Odd (Nat.card sigmaGroup))
    (hρ : Function.Injective ρ) (hrange : ρ.range = Gamma F sigmaGroup)
    (hE : ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G)) ≤
      (fieldCharacter n hn S e F sigmaGroup ρ hrange).ker.map
        (involutionCentralizer n S e).subtype) :
    Nat.card sigmaGroup = 1 := by
  let ρ' : centralizerFullQuotient n hn S e →* Gamma F sigmaGroup :=
    ρ.codRestrict (Gamma F sigmaGroup) fun g => hrange ▸ MonoidHom.mem_range.mpr ⟨g, rfl⟩
  let φ : centralizerOddCoreQuotient n S e →* Gamma F sigmaGroup :=
    ρ'.comp (centralizerFullQuotientMap n hn S e)
  have hφker : φ.ker = centralizerFullCenterImage n hn S e := by
    ext h
    rw [MonoidHom.mem_ker]
    constructor
    · intro h1
      have h2 : ρ (centralizerFullQuotientMap n hn S e h) = ρ 1 := by
        rw [map_one]
        exact congrArg Subtype.val h1
      exact (QuotientGroup.eq_one_iff h).mp (hρ h2)
    · intro hh
      have h1 : centralizerFullQuotientMap n hn S e h = 1 := (QuotientGroup.eq_one_iff h).mpr hh
      change ρ' (centralizerFullQuotientMap n hn S e h) = 1
      rw [h1, map_one]
  have hφsurj : Function.Surjective φ := by
    intro y
    have hy : (y : coordinateE F) ∈ ρ.range := by
      rw [hrange]
      exact y.2
    obtain ⟨g, hg⟩ := hy
    obtain ⟨h, rfl⟩ := centralizerFullQuotientMap_surjective n hn S e g
    exact ⟨h, Subtype.ext hg⟩
  have hR : Odd (Nat.card (centralizerOddCore n S e)) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  obtain ⟨-, -, -, htop, -⟩ :=
    CFSG.Wreathed.SylowCentralizerOddField.original_sylow_centralizer_sees_entire_odd_field_factor
      (N := involutionCentralizer n S e) n hn (centralizerSylow n hn S e)
      (centralizerCoordinates n hn S e) (centralizerOddCore n S e) hR p f hp
      (hp.odd_of_ne_two hpodd) hf F hcard sigmaGroup hodd φ hφsurj
      (hφker.trans (centralizerOddCoreQuotient_center_eq_fullCenterImage n hn S e).symm).le
      ⟨n, (congrArg (fun K : Subgroup (centralizerOddCoreQuotient n S e) => Nat.card K)
        hφker).trans (centralizerFullCenterImage_card n hn S e)⟩
      (CFSG.Wreathed.SylowCentralizerOddField.fieldProjection F sigmaGroup)
      (CFSG.Wreathed.SylowCentralizerOddField.fieldProjection_mul F sigmaGroup)
  have hSN := sylow_le_involutionCentralizer n hn S e
  have hCSN : Subgroup.centralizer ((S : Subgroup G) : Set G) ≤ involutionCentralizer n S e :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (BrauerWong.wreathModelHom_mem S e _))
  have hker : ∀ σ : sigmaGroup, σ = 1 := by
    intro σ
    have hσ : σ ∈ (⊤ : Subgroup sigmaGroup) := Subgroup.mem_top σ
    rw [← htop] at hσ
    obtain ⟨y, ⟨c, hc, rfl⟩, rfl⟩ := hσ
    have hcG := mem_ambientOddCore_of_mem_oddCore (involutionCentralizer n S e) (S : Subgroup G)
      hSN hCSN c hc
    obtain ⟨y', hy', hy'eq⟩ := hE hcG
    have hyy : y' = (c : involutionCentralizer n S e) := Subtype.ext hy'eq
    rw [hyy] at hy'
    exact hy'
  exact Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (hker a).trans (hker b).symm⟩, ⟨1⟩⟩

theorem compatible_actual_torus_splitting_eliminates_odd_field_factor
    [Finite G]
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f)
    (F : Type) [Field F] [Finite F] (sigmaGroup : Subgroup (F ≃+* F))
    (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
    (hcard : Nat.card F = p ^ f) (hodd : Odd (Nat.card sigmaGroup))
    (hρ : Function.Injective ρ)
    (_hlayer : (centralizerSimpleLayer n hn S e).map ρ = specialLayer F)
    (hrange : ρ.range = Gamma F sigmaGroup)
    (WF : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
    (hWF : ∀ g, g ∈ WF ↔ g ∈ torus F ∧ Odd (orderOf g))
    (W₀ : Subgroup G) (hW₀ : W₀ ≤ torusCore n S e)
    (hW₀n : ∀ k ∈ torusCore n S e, ∀ y ∈ W₀, k * y * k⁻¹ ∈ W₀) (hW₀c : IsCyclic W₀)
    (hW₀A : W₀ ⊓ torusFixedCore n S e = ⊥)
    (hW₀Ac : ∀ y ∈ W₀, ∀ z ∈ torusFixedCore n S e, y * z = z * y)
    (hwW : ∀ y ∈ W₀, wreathModelHom S e (Original.z (2 ^ n)) * y *
      (wreathModelHom S e (Original.z (2 ^ n)))⁻¹ = y⁻¹)
    (hwA : ∀ z ∈ torusFixedCore n S e, wreathModelHom S e (Original.z (2 ^ n)) * z =
      z * wreathModelHom S e (Original.z (2 ^ n)))
    (ζ : torusCore n S e ⧸ (torusFixedCore n S e).subgroupOf (torusCore n S e) ≃*
      WF ⋊[(oddTorusAction WF hWF).comp sigmaGroup.subtype] sigmaGroup)
    (hζω : ∀ k : torusCore n S e, SemidirectProduct.rightHom (ζ (QuotientGroup.mk k)) =
      fieldCharacter n hn S e F sigmaGroup ρ hrange ⟨k, torusCore_le n S e k.2⟩)
    (hζW : ∀ k : torusCore n S e, (k : G) ∈ W₀ ⊔ torusFixedCore n S e ↔
      ζ (QuotientGroup.mk k) ∈ (SemidirectProduct.inl : WF →*
        WF ⋊[(oddTorusAction WF hWF).comp sigmaGroup.subtype] sigmaGroup).range) :
    let T : Subgroup G := Subgroup.closure
      {wreathModelHom S e (Original.s (2 ^ n)) ^ (2 ^ n / 2),
        wreathModelHom S e (Original.t (2 ^ n)) ^ (2 ^ n / 2)}
    let kerω : Subgroup G :=
      (fieldCharacter n hn S e F sigmaGroup ρ hrange).ker.map (involutionCentralizer n S e).subtype
    Nat.card sigmaGroup = 1 ∧
      torusCore n S e ⊓ kerω = W₀ ⊔ torusFixedCore n S e ∧
      (∀ g ∈ Subgroup.normalizer (T : Set G), ∀ b ∈ W₀ ⊔ torusFixedCore n S e,
        g * b * g⁻¹ ∈ W₀ ⊔ torusFixedCore n S e) ∧
      (∀ g ∈ Subgroup.normalizer (T : Set G), ∀ k ∈ torusCore n S e,
        g * k * g⁻¹ * k⁻¹ ∈ W₀ ⊔ torusFixedCore n S e) ∧
      (∀ (η : G) (hη : η ∈ Subgroup.normalizer (modelBase S e : Set G)),
        orderOf ((modelBase S e).normalizerMonoidHom ⟨η, hη⟩) = 3 →
          CompatibleFamilies.boundaryCommutator S e η ≤ kerω) ∧
      ρ.range = linearLayer F := by
  intro T kerω
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstruct := sylow_and_base_four_group_centralizer_structure n hn S e
  have hT : modelT n S e = T := hstruct.four_coordinates
  have hcomm := fieldAut_subgroup_comm sigmaGroup
  have hCN : Subgroup.centralizer (T : Set G) ≤ involutionCentralizer n S e :=
    centralizer_four_le n S e
  have hC₀C : torusCore n S e ≤ Subgroup.centralizer (T : Set G) := ambientOddCore_le _
  have hA₀C₀ : torusFixedCore n S e ≤ torusCore n S e := torusFixedCore_le_torusCore n S e
  have hBC₀ : W₀ ⊔ torusFixedCore n S e ≤ torusCore n S e := sup_le hW₀ hA₀C₀
  have hBker : ∀ k : torusCore n S e, (k : G) ∈ W₀ ⊔ torusFixedCore n S e ↔
      fieldCharacter n hn S e F sigmaGroup ρ hrange ⟨k, torusCore_le n S e k.2⟩ = 1 :=
    mem_ker_iff_of_compatible ζ ((fieldCharacter n hn S e F sigmaGroup ρ hrange).comp
      (Subgroup.inclusion (torusCore_le n S e))) hζω hζW
  have hmemB : ∀ g ∈ torusCore n S e, ∀ hgN : g ∈ involutionCentralizer n S e,
      fieldCharacter n hn S e F sigmaGroup ρ hrange ⟨g, hgN⟩ = 1 →
        g ∈ W₀ ⊔ torusFixedCore n S e :=
    fun g hg _ h => (hBker ⟨g, hg⟩).mpr h
  have hBω : ∀ g ∈ W₀ ⊔ torusFixedCore n S e, ∀ hgN : g ∈ involutionCentralizer n S e,
      fieldCharacter n hn S e F sigmaGroup ρ hrange ⟨g, hgN⟩ = 1 :=
    fun g hg _ => (hBker ⟨g, hBC₀ hg⟩).mp hg
  have hker : torusCore n S e ⊓ kerω = W₀ ⊔ torusFixedCore n S e := by
    ext g
    constructor
    · rintro ⟨hg, ⟨y, hy, rfl⟩⟩
      exact hmemB _ hg y.2 hy
    · intro hg
      exact ⟨hBC₀ hg, ⟨⟨g, torusCore_le n S e (hBC₀ hg)⟩, hBω g hg _, rfl⟩⟩
  have hBle : W₀ ⊔ torusFixedCore n S e ≤ kerω := by
    rw [← hker]
    exact inf_le_right
  have hcent := centralizes_derived_iff ζ _
    (semidirect_derived_centralizer hp hpodd hf hcard sigmaGroup hodd WF hWF) hζW
  have hNT_C : ∀ g ∈ Subgroup.normalizer (T : Set G), ∀ c ∈ Subgroup.centralizer (T : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (T : Set G) :=
    fun g hg c hc => conj_mem_centralizer_of_mem_normalizer hg hc
  have hNT_C₀ : ∀ g ∈ Subgroup.normalizer (T : Set G), ∀ k ∈ torusCore n S e,
      g * k * g⁻¹ ∈ torusCore n S e :=
    fun g hg k hk => ambientOddCore_conj_mem _ (normalizer_le_normalizer_centralizer T hg) hk
  have hKodd : Odd (Nat.card (torusCore n S e)) := by
    have h := hstruct.oddCore_odd
    rw [hT] at h
    exact h
  have hconjB : ∀ c ∈ involutionCentralizer n S e, (∀ k ∈ torusCore n S e,
      c * k * c⁻¹ ∈ torusCore n S e) → ∀ b ∈ W₀ ⊔ torusFixedCore n S e,
        c * b * c⁻¹ ∈ W₀ ⊔ torusFixedCore n S e := by
    intro c hc hcK b hb
    have hbN : b ∈ involutionCentralizer n S e := torusCore_le n S e (hBC₀ hb)
    refine hmemB _ (hcK b (hBC₀ hb)) (Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hbN)
      (Subgroup.inv_mem _ hc)) ?_
    have h := map_conj_of_comm (fieldCharacter n hn S e F sigmaGroup ρ hrange) hcomm ⟨c, hc⟩
      ⟨b, hbN⟩
    rw [hBω b hb hbN] at h
    exact h
  have hcommB : ∀ c ∈ involutionCentralizer n S e, (∀ k ∈ torusCore n S e,
      c * k * c⁻¹ ∈ torusCore n S e) → ∀ k ∈ torusCore n S e,
        c * k * c⁻¹ * k⁻¹ ∈ W₀ ⊔ torusFixedCore n S e := by
    intro c hc hcK k hk
    have hkN : k ∈ involutionCentralizer n S e := torusCore_le n S e hk
    refine hmemB _ (Subgroup.mul_mem _ (hcK k hk) (Subgroup.inv_mem _ hk))
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hkN)
        (Subgroup.inv_mem _ hc)) (Subgroup.inv_mem _ hkN)) ?_
    exact map_commutatorElement_of_comm (fieldCharacter n hn S e F sigmaGroup ρ hrange) hcomm
      ⟨c, hc⟩ ⟨k, hkN⟩
  have hCT : ∀ c ∈ Subgroup.centralizer (T : Set G), ∀ k ∈ torusCore n S e,
      c * k * c⁻¹ ∈ torusCore n S e :=
    fun c hc => hNT_C₀ c (Subgroup.centralizer_le_normalizer _ hc)
  have hwN : wreathModelHom S e (Original.z (2 ^ n)) ∈ involutionCentralizer n S e :=
    sylow_le_involutionCentralizer n hn S e (BrauerWong.wreathModelHom_mem S e _)
  have hwT := swap_mem_normalizer_four S e
  have hV4 : IsKleinFour T := by
    have h := hstruct.kleinFour
    rw [hT] at h
    exact h
  have hCV : Subgroup.centralizer (T : Set G) = torusCore n S e ⊔ modelBase S e := by
    have h := hstruct.base_split
    rw [hT] at h
    exact h
  have hUeq : modelBase S e = Subgroup.zpowers (wreathModelHom S e (Original.s (2 ^ n))) ⊔
      Subgroup.zpowers (wreathModelHom S e (Original.t (2 ^ n))) :=
    hstruct.base_coordinates.trans (closure_pair_eq_sup _ _)
  obtain ⟨b, -, a, haM, haord, -, -, hwa, hgen⟩ := cycling_lift_in_normalizer n hn (2 ^ n) rfl _ _
    (actual_orderOf_s S e) (actual_orderOf_t S e) (actual_s_t_commute S e) (zpowers_disjoint S e)
    (modelBase S e) T (torusCore n S e) hUeq rfl hV4 hNT_C₀ hKodd hCV
    (card_four_normalizer_quotient hnonab hn S e) _ hwT (actual_orderOf_swap S e)
    (actual_swap_conj_s S e) (actual_swap_conj_t S e)
  have hw2 : wreathModelHom S e (Original.z (2 ^ n)) * wreathModelHom S e (Original.z (2 ^ n)) =
      1 := by
    rw [← map_mul, wreath_z_mul_self, map_one]
  have haodd : Odd (orderOf a) := by
    rw [haord]
    exact Odd.pow (by decide)
  obtain ⟨hBn, htriv⟩ := boundary_invariance_in_subgroup (Subgroup.normalizer (T : Set G))
    (Subgroup.centralizer (T : Set G)) (torusCore n S e) (Subgroup.centralizer_le_normalizer _)
    hC₀C hNT_C hNT_C₀ hKodd _ a hwT haM hw2 haodd hwa hgen (torusFixedCore n S e) W₀ hA₀C₀ hW₀
    (fun k hk x hx => Subgroup.mem_subgroupOf.mp ((torusFixedCore_normal n S e).conj_mem
      ⟨x, hA₀C₀ hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨k, hk⟩))
    hW₀n hW₀c hW₀A hW₀Ac
    (fun c hc => hconjB c (hCN hc) (hCT c hc))
    (fun x hx => hcommB x (torusCore_le n S e hx) fun k hk =>
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hk) (Subgroup.inv_mem _ hx))
    (fun c hc => hcommB c (hCN hc) (hCT c hc))
    (fun x hx => by rw [hwA x hx, mul_inv_cancel_right]; exact hx)
    (fun x hx => by rw [hwW x hx]; exact Subgroup.inv_mem _ hx) hwA
    (hcommB _ hwN fun k hk => hNT_C₀ _ hwT k hk) hcent
  have hηB : ∀ η ∈ Subgroup.normalizer (T : Set G),
      CompatibleFamilies.boundaryCommutator S e η ≤ W₀ ⊔ torusFixedCore n S e := by
    intro η hη
    rw [CompatibleFamilies.boundaryCommutator, Subgroup.closure_le]
    rintro _ ⟨c, hc, rfl⟩
    have h1 := htriv η⁻¹ (Subgroup.inv_mem _ hη) c hc
    rw [inv_inv] at h1
    have hcT : c⁻¹ ∈ Subgroup.normalizer (T : Set G) :=
      Subgroup.inv_mem _ (Subgroup.centralizer_le_normalizer _ (hC₀C hc))
    have h2 := hBn c⁻¹ hcT _ h1
    rw [inv_inv] at h2
    have h3 : c⁻¹ * (η⁻¹ * c * η) = c⁻¹ * (η⁻¹ * c * η * c⁻¹) * c := by group
    rw [h3]
    exact h2
  have hηker : ∀ (η : G) (hη : η ∈ Subgroup.normalizer (modelBase S e : Set G)),
      orderOf ((modelBase S e).normalizerMonoidHom ⟨η, hη⟩) = 3 →
        CompatibleFamilies.boundaryCommutator S e η ≤ kerω := by
    intro η hη _
    have hηT : η ∈ Subgroup.normalizer (T : Set G) := by
      have h := modelBase_normalizer_le_modelT_normalizer n (by omega) S e hη
      rw [hT] at h
      exact h
    exact (hηB η hηT).trans hBle
  have hE : ambientOddCore (Subgroup.centralizer ((S : Subgroup G) : Set G)) ≤ kerω := by
    have : Fintype G := Fintype.ofFinite G
    obtain ⟨σ, υ, η, hA⟩ := AdaptedBaseFusion.exists_isAdaptedBase S e hnonab hn
    have hex : ∃ (η : G) (hη : η ∈ Subgroup.normalizer ((Subgroup.closure
        {wreathModelHom S e (Original.s (2 ^ n)), wreathModelHom S e (Original.t (2 ^ n))} :
          Subgroup G) : Set G)),
        orderOf ((Subgroup.closure {wreathModelHom S e (Original.s (2 ^ n)),
          wreathModelHom S e (Original.t (2 ^ n))}).normalizerMonoidHom ⟨η, hη⟩) = 3 ∧
        η ∈ Subgroup.normalizer (T : Set G) := by
      rw [← hstruct.base_coordinates]
      refine ⟨η, hA.mem_normalizer, hA.orderOf_conj, ?_⟩
      have h := modelBase_normalizer_le_modelT_normalizer n (by omega) S e hA.mem_normalizer
      rw [hT] at h
      exact h
    obtain ⟨η', hη', hord', hη'T⟩ := hex
    obtain ⟨-, hEle⟩ :=
      ConditionalCorrectedThreeCycle.conditional_corrected_three_cycle_commutator_index_one
        hnonab n hn S e hfour p f hp hpodd hf hmodel η' hη' hord'
    exact hEle.trans (boundaryProduct_le_ker n hn S e F sigmaGroup ρ hrange η'
      ((hηB η' hη'T).trans hBle))
  have hsig := sigma_card_eq_one_of_le_ker n hn S e p f hp hpodd hf F sigmaGroup ρ hcard hodd hρ
    hrange hE
  have hbot : sigmaGroup = ⊥ := Subgroup.eq_bot_of_card_eq _ hsig
  have hrangeL : ρ.range = linearLayer F := by
    rw [hrange, hbot]
    change linearLayer F ⊔ liftedField F ⊥ = linearLayer F
    rw [liftedField, Subgroup.map_bot, sup_bot_eq]
  exact ⟨hsig, hker, hBn, htriv, hηker, hrangeL⟩

end CFSG.Wreathed.TorusSplitting
