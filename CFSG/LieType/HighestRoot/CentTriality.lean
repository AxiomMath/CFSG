module

public import CFSG.LieType.HighestRoot.CentChevalley
public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Twin
public import CFSG.LieType.Steinberg.TwistedD4.RankOne
public import CFSG.ClassicalInvolution.ModelFacts.Families
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.Universal.Unitary.Roots
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.LieType.HighestRoot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.G2D4Models
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K]

@[expose] noncomputable def td4Incl
    (σ : K →+* K) : twistedGroup σ →* ModGL d4 K :=
  (adjointGroup d4 K).subtype.comp (twistedGroup σ).subtype

theorem td4Incl_injective
    (σ : K →+* K) : Function.Injective (td4Incl σ) :=
  Subtype.val_injective.comp Subtype.val_injective

theorem td4Incl_apply
    (σ : K →+* K) (x : twistedGroup σ) :
    td4Incl σ x = ((x : adjointGroup d4 K) : ModGL d4 K) := rfl

theorem mem_normalizer_of_map_injective' {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Function.Injective f) {L : Subgroup G} {g : G}
    (h : f g ∈ Subgroup.normalizer ((L.map f : Subgroup H) : Set H)) :
    g ∈ Subgroup.normalizer (L : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at h ⊢
  intro y
  have := h (f y)
  rw [Subgroup.mem_map_iff_mem hf, show f g * f y * (f g)⁻¹ = f (g * y * g⁻¹) by simp,
    Subgroup.mem_map_iff_mem hf] at this
  exact this

theorem map_td4Incl_twistedRootGroup
    (σ : K →+* K) {β : Fin (Tag.rank .G2) → ℤ}
    (hβ : IsRoot .G2 β) :
    (twistedRootGroup σ β).map (td4Incl σ) =
      (twistedRootSubgroupD4 σ β).map (adjointGroup d4 K).subtype := by
  unfold twistedRootGroup td4Incl
  rw [← Subgroup.map_map,
    Subgroup.map_subgroupOf_eq_of_le (twistedRootSubgroupD4_le_twistedGroup σ hβ)]

theorem map_td4Incl_rankOne_long
    (σ : K →+* K) :
    (rankOne (twistedRootGroup σ) (ng 0)).map (td4Incl σ) =
      nodeGroupTD4 σ (Pi.single (nd 2) 1) := by
  rw [rankOne, Subgroup.map_sup, map_td4Incl_twistedRootGroup σ (isRoot_single .G2 (ng 0)),
    map_td4Incl_twistedRootGroup σ (isRoot_neg_single .G2 (ng 0)), ← proj_neg_single_two,
    ← proj_single_two, map_twistedRootSubgroupD4_eq σ (isRoot_single d4 (nd 2)),
    map_twistedRootSubgroupD4_eq σ (IsRoot.neg (isRoot_single d4 (nd 2)))]
  rfl

theorem aLongTD4_eq_signTuple : aLongTD4 K = signTuple d4 K (nd 2) := by
  funext j
  simp only [signTuple]
  fin_cases j
  · rw [show d4.cartan (nd 2) (nd 0) = -1 by decide]
    simp [aLongTD4]
    rfl
  · rw [show d4.cartan (nd 2) (nd 1) = -1 by decide]
    simp [aLongTD4]
    rfl
  · rw [show d4.cartan (nd 2) (nd 2) = 2 by decide]
    simp [aLongTD4]
    rfl
  · rw [show d4.cartan (nd 2) (nd 3) = -1 by decide]
    simp [aLongTD4]
    rfl

theorem td4Incl_eq_of_mem
    (hK : ringChar K ≠ 2) {σ : K →+* K} {z : twistedGroup σ}
    (hz : z ∈ rankOne (twistedRootGroup σ) (ng 0)) (h2 : orderOf z = 2) :
    td4Incl σ z = rootDiagUnit d4 (aLongTD4 K) := by
  have hmem : td4Incl σ z ∈ rootSubgroup d4 K (Pi.single (nd 2) 1) ⊔
      rootSubgroup d4 K (-Pi.single (nd 2) 1) := by
    have h := nodeGroupTD4_le_rootSpan σ (Pi.single (nd 2) 1)
      (map_td4Incl_rankOne_long σ ▸ Subgroup.mem_map_of_mem (td4Incl σ) hz)
    have he : td4Orb (Pi.single (nd 2) 1) ∪ td4Orb (-Pi.single (nd 2) 1) =
        {Pi.single (nd 2) 1, -Pi.single (nd 2) 1} := by
      simp [td4Orb, rho_single, rho_neg_single, rhoPerm_two, Set.union_def, Set.insert_def]
    rwa [he, rootSpan_pair_eq] at h
  have h2' : orderOf (td4Incl σ z) = 2 := by
    rwa [orderOf_injective (td4Incl σ) (td4Incl_injective σ)]
  rw [aLongTD4_eq_signTuple, ← torusElt_neg_one_eq]
  exact eq_torusElt_neg_one hK (nd 2) hmem h2'

theorem centralizer_le_normalizer_td4
    (hK : ringChar K ≠ 2) {σ : K →+* K}
    (hσ : ∀ c, σ (σ (σ c)) = c)
    (hgF : ∀ g : twistedGroup σ, td4Incl σ g ∈ graphFixedRootGroup TwistTag.D4 K σ)
    {z : twistedGroup σ} (hz : z ∈ rankOne (twistedRootGroup σ) (ng 0)) (h2 : orderOf z = 2) :
    Subgroup.centralizer ({z} : Set (twistedGroup σ)) ≤
      Subgroup.normalizer (rankOne (twistedRootGroup σ) (ng 0) : Set (twistedGroup σ)) := by
  intro g hg
  have hK1 : (-1 : Kˣ) ≠ 1 := fun h =>
    Ring.neg_one_ne_one_of_char_ne_two hK (by simpa using congrArg Units.val h)
  have hga : td4Incl σ g ∈
      Subgroup.centralizer ({rootDiagUnit d4 (aLongTD4 K)} : Set (ModGL d4 K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← td4Incl_eq_of_mem hK hz h2, ← map_mul,
      ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 hg]
  have h := mem_normalizer_nodeGroup_long σ hσ hK1 (hgF g) hga
  rw [← map_td4Incl_rankOne_long] at h
  exact mem_normalizer_of_map_injective' (td4Incl_injective σ) h

end CFSG.LieType.HighestRoot
