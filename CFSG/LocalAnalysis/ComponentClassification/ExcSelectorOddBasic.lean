module

public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddInner
public import CFSG.LieType.Chevalley.CoordinateFieldFixedOddComponents
public import CFSG.LieType.Chevalley.GraphFixedOddComponents
public import CFSG.LieType.Chevalley.GraphFixedSchreier
public import CFSG.LieType.Chevalley.TrialityAllCharTorusCoordinates
public import CFSG.LocalAnalysis.ComponentInitial.SolvableCoreComponents
public import CFSG.Milestones.OO_odd_order_solvable
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate2022
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LieType.AlgebraicGroups.OddG2F4E8AllInvolutionComponents
public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitRankOne
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication

public noncomputable section

namespace CFSG.ComponentClassification.ExcSelector

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Components

variable {G : Type} [Group G]

theorem isPComponent_two_subgroupOf {L F : Subgroup G} [Finite F]
    (hL : Assembly.IsComponentOf L F) : CFSG.IsPComponent 2 (L.subgroupOf F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (LocalAnalysis.ComponentInitial.solvable_prime_core_ordinary_components 2
    Nat.prime_two ?_).1 _ (OddToralOrdinary.isComponent_subgroupOf_of_isComponentOf hL)
  exact CFSG.Milestones.odd_order_solvable
    (Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (G := F) (p := 2)))

theorem not_smallType_of_subgroupEquiv {C' : Type} [Group C'] {F : Subgroup G}
    {F' : Subgroup C'} (e : F ≃* F')
    (hX : ∀ M : Subgroup C', Assembly.IsComponentOf M F' → ¬ SmallType M) {L : Subgroup G}
    (hL : Assembly.IsComponentOf L F) : ¬ SmallType L := by
  have h1 : Assembly.IsComponentOf (L.comap F.subtype) ⊤ := by
    refine isComponentOf_comap_of_injective F.subtype Subtype.val_injective ?_
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  set ψ : F →* C' := F'.subtype.comp e.toMonoidHom with hψ
  have hψi : Function.Injective ψ := Subtype.val_injective.comp e.injective
  have h2 := isComponentOf_map_of_injective ψ hψi h1
  have htop : (⊤ : Subgroup F).map ψ = F' := by
    rw [← MonoidHom.range_eq_map, hψ, MonoidHom.range_comp, MonoidHom.range_eq_top.2
      e.surjective, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [htop] at h2
  have hLF : L ≤ F.subtype.range := by rw [Subgroup.range_subtype]; exact hL.1
  have e₁ : L ≃* L.comap F.subtype :=
    (((L.comap F.subtype).equivMapOfInjective _ Subtype.val_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hLF))).symm
  have e₂ := (L.comap F.subtype).equivMapOfInjective ψ hψi
  exact fun hs => hX _ h2 ((smallType_congr (e₁.trans e₂)).1 hs)

end Components

section Simple

variable {X : Type} [Group X] {F : Type} [Field F]

theorem not_smallType_of_center_eq_bot_of_sl2 [Finite F] (hF : ringChar F ≠ 2)
    (hZ : center X = ⊥) (φ : SL2 F →* X) (hφ : Function.Injective φ) : ¬ SmallType X :=
  not_smallType_of_sl2 hF φ hφ (by
    rw [hZ, Subgroup.mem_bot]
    exact fun h => neg_one_ne_one_sl2 hF (hφ (h.trans (map_one φ).symm)))

variable {K : Type} [Field K]

theorem ringChar_subfield_ne_two (hK : ringChar K ≠ 2) (S : Subfield K) : ringChar S ≠ 2 := by
  intro h
  have h0 : ((2 : ℕ) : S) = 0 := by
    rw [← h]
    exact ringChar.Nat.cast_ringChar
  apply Ring.two_ne_zero hK
  have := congrArg S.subtype h0
  rw [map_natCast, map_zero] at this
  exact_mod_cast this

theorem adjointGroup_odd_not_smallType {τ : Tag} [Finite K] (hK : ringChar K ≠ 2) :
    ¬ SmallType (adjointGroup τ K) := by
  have i : Fin τ.rank := ⟨0, by cases τ <;> decide⟩
  exact not_smallType_of_center_eq_bot_of_sl2 hK center_adjointGroup_eq_bot
    ((simpleRootSL2 τ K i).codRestrict _ (simpleRootSL2_mem_adjointGroup i))
    (fun A B h => simpleRootSL2_injective hK i (congrArg Subtype.val h))

theorem sl2Map_injective {F' : Type} [Field F'] (f : F →+* F') :
    Function.Injective (Matrix.SpecialLinearGroup.map f : SL2 F →* SL2 F') := by
  intro A B h
  ext i j
  have := congrArg (fun M : SL2 F' => (M : Matrix (Fin 2) (Fin 2) F') i j) h
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply] at this
  exact f.injective this

theorem orbitRankOneHom_E6_singleton_injective' (hK : ringChar K ≠ 2) (σ : K →+* K)
    (a : Fin TwistTag.E6.foldedTag.rank) (ha : (TwistTag.E6.orbit a).card = 1) :
    Function.Injective (orbitRankOneHom TwistTag.E6 K σ a) := by
  obtain ⟨R, hRu, -, hRH, hRW, -, -, -, -, hRformula⟩ :=
    exceptional_fixed_rank_one_central_image TwistTag.E6 K σ a
  have hR : R = orbitRankOneHom TwistTag.E6 K σ a :=
    SL2_hom_ext (fun s => by rw [hRu, orbitRankOneHom_uSL])
      (fun u => by rw [hRH, orbitRankOneHom_HSL]) (by rw [hRW, orbitRankOneHom_WSL])
  have hform : ∀ g, R g = simpleRootSL2 TwistTag.E6.tag K (TwistTag.E6.orbitMin a)
      (Matrix.SpecialLinearGroup.map (orbitField TwistTag.E6 K σ a).subtype g) := by
    intro g
    rw [hRformula (simpleRootSL2 TwistTag.E6.tag K) (fun i c => simpleRootSL2_uSL i c)
      (fun i u => simpleRootSL2_HSL i u) (fun i => simpleRootSL2_WSL i) g, ha]
    simp only [List.range_one, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, pow_zero, Equiv.Perm.coe_one, id_eq]
    rfl
  rw [← hR]
  intro A B hAB
  rw [hform, hform] at hAB
  exact sl2Map_injective _ (simpleRootSL2_injective hK _ hAB)

theorem graphFixedRootGroup_E6_odd_not_smallType [Finite K] (hK : ringChar K ≠ 2)
    (σ : K →+* K) (hσ : Function.Surjective σ) :
    ¬ SmallType (graphFixedRootGroup TwistTag.E6 K σ) := by
  set a := TwistTag.E6.orbitIndex (⟨1, by decide⟩ : Fin TwistTag.E6.tag.rank)
  have ha : (TwistTag.E6.orbit a).card = 1 := by decide
  exact not_smallType_of_center_eq_bot_of_sl2 (ringChar_subfield_ne_two hK _)
    (center_graphFixedRootGroup_eq_bot hσ)
    ((orbitRankOneHom TwistTag.E6 K σ a).codRestrict _ fun A => range_orbitRankOneHom_le a ⟨A, rfl⟩)
    (fun A B h => orbitRankOneHom_E6_singleton_injective' hK σ a ha (congrArg Subtype.val h))

theorem graphFixedRootGroup_D4_odd_not_smallType [Finite K] (hK : ringChar K ≠ 2)
    (σ : K ≃+* K) (hσ : σ ^ 3 = 1) :
    ¬ SmallType (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  set a : Fin TwistTag.D4.foldedTag.rank := ⟨0, by decide⟩
  exact not_smallType_of_center_eq_bot_of_sl2 (ringChar_subfield_ne_two hK _)
    (exceptional_fixed_center_trivial TwistTag.D4 K σ)
    ((orbitRankOneHom TwistTag.D4 K σ.toRingHom a).codRestrict _
      fun A => range_orbitRankOneHom_le a ⟨A, rfl⟩)
    (fun A B h => orbitRankOneHom_injective_D4 hσ a (congrArg Subtype.val h))

theorem entrywiseFixedGroup_component_not_smallType {τ : Tag} [Finite K] (hK : ringChar K ≠ 2)
    (σ : K ≃+* K) {L : Subgroup (ModGL τ K)}
    (hL : Assembly.IsComponentOf L (entrywiseFixedGroup τ σ)) : ¬ SmallType L := by
  obtain ⟨-, -, -, hJΓ, -, hJn, hcomm⟩ := Chevalley_coordinate_field_fixed_normal_subgroup τ K σ
  have hk2 := ringChar_fixSubfield_ne_two hK σ
  have hs := (odd_pinned_Chevalley_p_components τ (fixSubfield σ) hk2).1
  have eJ : adjointGroup τ (fixSubfield σ) ≃* fixedFieldImage τ σ :=
    (adjointGroup τ (fixSubfield σ)).equivMapOfInjective _ (baseChangeGL_injective _)
  have : IsSimpleGroup (fixedFieldImage τ σ) := (MulEquiv.isSimpleGroup_congr eJ).1 hs
  have hsolv : Group.IsSolvable (entrywiseFixedGroup τ σ ⧸
      (fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)) :=
    Group.isSolvable_of_comm hcomm
  rw [eq_of_isComponentOf_of_normal_simple hJΓ hJn hsolv hL, ← smallType_congr eJ]
  exact adjointGroup_odd_not_smallType hk2

end Simple

end CFSG.ComponentClassification.ExcSelector
