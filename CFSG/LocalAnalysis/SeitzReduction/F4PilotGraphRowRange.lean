module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphRowGen
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTGraphTwistedFamily
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphParamANorm

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open CFSG.Quasithin (perfectCore)

local instance f4PilotGraphRowRangeNeZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance f4PilotGraphRowRangeNeZeroRankE6 : NeZero Tag.E6.rank := ⟨by decide⟩

section Sup

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

theorem le_sup_neighbourCore [Finite K] (hq : 4 ≤ Nat.card K) (e : L ≃* adjointGroup .F4 K) :
    L ≤ neighbourCore e .X ⊔ neighbourCore e .Y := by
  have hct := CFSG.LieType.Steinberg.Adjoint.f4_isCTGroupDatum K
  have hgen : ⨆ J, (CFSG.LieType.Steinberg.Adjoint.f4Datum K).leviAmalgam J = ⊤ :=
    CFSG.LieType.CurtisTits.iSup_leviAmalgam_eq_top
      (CFSG.LieType.RootSystem.isCTRootSystem
        (CFSG.LieType.Steinberg.Adjoint.f4Datum K).isFiniteType
        (CFSG.LieType.Steinberg.Adjoint.f4Datum K).divisible) hct
  set φ : adjointGroup .F4 K →* G := L.subtype.comp e.symm.toMonoidHom with hφdef
  have hone : ∀ j : Fin (Tag.rank .F4),
      (CFSG.LieType.CurtisTits.rankOne (CFSG.LieType.Steinberg.Adjoint.f4Datum K).rootGroup j).map
        φ ≤ neighbourCore e .X ⊔ neighbourCore e .Y := by
    intro j
    have h1 : (CFSG.LieType.CurtisTits.rankOne
        (CFSG.LieType.Steinberg.Adjoint.f4Datum K).rootGroup j).map φ =
        modelToG e (rootSpan .F4 K (amalgamRoots {j})) := by
      rw [← CFSG.LieType.CurtisTits.levi_singleton, levi_f4Datum_eq, modelToG, Subgroup.map_map]
    rw [h1]
    refine (modelToG_rootSpan_le_pieceCore_of_perfect e {j}
      (commutator_rootSpan_amalgamRoots_eq_of_four_le hq {j})).trans ?_
    by_cases h0 : j = 0
    · subst h0
      exact (pieceCore_le_neighbourCore e .Y zero_subset_Y).trans le_sup_right
    · refine (pieceCore_le_neighbourCore e .X ?_).trans le_sup_left
      exact subset_nodes_X_of_zero_not_mem (by simpa [Finset.mem_singleton, eq_comm] using h0)
  have hle : (⨆ J, (CFSG.LieType.Steinberg.Adjoint.f4Datum K).leviAmalgam J).map φ ≤
      neighbourCore e .X ⊔ neighbourCore e .Y := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun J => ?_
    change (⨆ j ∈ J.1, CFSG.LieType.CurtisTits.rankOne
      (CFSG.LieType.Steinberg.Adjoint.f4Datum K).rootGroup j).map φ ≤ _
    rw [Subgroup.map_iSup]
    refine iSup_le fun j => ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun _ => hone j
  intro l hl
  have hmem : e ⟨l, hl⟩ ∈ ⨆ J, (CFSG.LieType.Steinberg.Adjoint.f4Datum K).leviAmalgam J :=
    hgen ▸ mem_top _
  have hφl : φ (e ⟨l, hl⟩) = l := by
    rw [hφdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rfl
  rw [← hφl]
  exact hle (mem_map_of_mem φ hmem)

theorem pieceSpan_le_sup_neighbourCore [Finite G] [Finite K] (hq : 4 ≤ Nat.card K)
    (e : L ≃* adjointGroup .F4 K) :
    pieceSpan e ≤ neighbourCore e .X ⊔ neighbourCore e .Y := by
  have hL := le_sup_neighbourCore hq e
  have h03 : pieceCore e {0, 3} ≤ neighbourCore e .X ⊔ neighbourCore e .Y := by
    refine (pieceCore_le_neighbourCore e .X' (by decide)).trans ?_
    rw [neighbourCore_X'_eq_map_conj]
    rintro _ ⟨g, hg, rfl⟩
    have hn : ((e.symm (n1242 K) : L) : G) ∈ neighbourCore e .X ⊔ neighbourCore e .Y :=
      hL (e.symm (n1242 K)).2
    change ((e.symm (n1242 K) : L) : G) * g * ((e.symm (n1242 K) : L) : G)⁻¹ ∈ _
    exact mul_mem (mul_mem hn (mem_sup_left hg)) (inv_mem hn)
  refine iSup_le fun J => ?_
  by_cases h0 : (0 : Fin (Tag.rank .F4)) ∈ J.1
  · by_cases h3 : (3 : Fin (Tag.rank .F4)) ∈ J.1
    · rw [eq_pair_zero_three J.2 h0 h3]
      exact h03
    · exact (pieceCore_le_neighbourCore e .Y (subset_nodes_Y_of_three_not_mem h3)).trans
        le_sup_right
  · exact (pieceCore_le_neighbourCore e .X (subset_nodes_X_of_zero_not_mem h0)).trans le_sup_left

theorem range_sup_eq_pieceSpan_of_neighbourCore' [Finite G] [Finite K] (hq : 4 ≤ Nat.card K)
    (e : L ≃* adjointGroup .F4 K) {A B : Subgroup G} {N₁ N₂ : AmalgamNeighbour}
    (hN : (N₁ = .X ∧ N₂ = .Y) ∨ (N₁ = .Y ∧ N₂ = .X)) (hA : A = neighbourCore e N₁)
    (hB : B = neighbourCore e N₂) (hX : neighbourCore e .X ≤ pieceSpan e)
    (hY : neighbourCore e .Y ≤ pieceSpan e) : A ⊔ B = pieceSpan e := by
  have h := le_antisymm (sup_le hX hY) (pieceSpan_le_sup_neighbourCore hq e)
  rcases hN with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [hA, hB, h]
  · rw [hA, hB, sup_comm, h]

end Sup

section Graph

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K CFSG.LieType.Ree.ReeTag.F4.prime]

theorem pieceCore_trans_graphAutF4_symm (e : L ≃* adjointGroup .F4 K)
    (J : Finset (Fin (Tag.rank .F4))) :
    pieceCore (e.trans (graphAutF4 K).symm) J = pieceCore e (nodePermPow 1 J) := by
  rw [pieceCore_def, pieceCore_def]
  exact congrArg centralizerPerfectCore (leviTorusG_trans_graphAutF4_symm e J)

theorem pieceSpan_trans_graphAutF4_symm (e : L ≃* adjointGroup .F4 K) :
    pieceSpan (e.trans (graphAutF4 K).symm) = pieceSpan e := by
  refine le_antisymm (iSup_le fun J => ?_) (iSup_le fun J => ?_)
  · rw [pieceCore_trans_graphAutF4_symm]
    exact le_iSup (fun J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2} => pieceCore e J.1)
      ⟨nodePermPow 1 J.1, (card_nodePermPow 1 J.1).trans_le J.2⟩
  · have h := pieceCore_trans_graphAutF4_symm e (nodePermPow 1 J.1)
    rw [nodePermPow_nodePermPow] at h
    rw [← h]
    exact le_iSup (fun J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2} =>
      pieceCore (e.trans (graphAutF4 K).symm) J.1)
      ⟨nodePermPow 1 J.1, (card_nodePermPow 1 J.1).trans_le J.2⟩

end Graph

section Linear

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem map_sl6BlockA_le_pieceCore (e : L ≃* adjointGroup .F4 K)
    {Φ : Matrix.SpecialLinearGroup (Fin 6) K →* G} (hr : Φ.range = neighbourCore e .X)
    (hn : ∀ s, Φ (sp6ToSL6 s) = levi6Hom e (RingEquiv.refl K) s) :
    (sl6BlockA K).map Φ ≤ pieceCore e {1, 2} := by
  have hperf : ⁅(sl6BlockA K).map Φ, (sl6BlockA K).map Φ⁆ = (sl6BlockA K).map Φ := by
    rw [← map_commutator, commutator_sl6BlockA]
  refine le_centralizerPerfectCore hperf ?_
  rw [le_centralizer_iff]
  have hT : leviTorusG e {1, 2} ≤ (leviTorusG e {1, 2} ⊓ neighbourLeviG e .X) ⊔
      centralizer (neighbourCore e .X : Set G) := by
    rw [← leviTorusG_sup_centralizer_eq e one_two_subset_X]
    exact le_sup_left
  refine hT.trans (sup_le ?_ ?_)
  · rw [← map_levi6Hom_sp6TorusA e (RingEquiv.refl K)]
    rintro _ ⟨s, hs, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    rw [← hn s]
    have h := mem_centralizer_iff.1 (sl6BlockA_le_centralizer hb) (sp6ToSL6 s) ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, h]
  · refine centralizer_le ?_
    rw [← hr]
    exact map_le_range Φ _

theorem levi6Hom_mem (e : L ≃* adjointGroup .F4 K) {F : Type} [Field F] (ε : F ≃+* K)
    (s : CFSG.Assembly.LowTwoRank.StatedSp 3 F) : levi6Hom e ε s ∈ L := by
  simp only [levi6Hom, MonoidHom.comp_apply, coe_subtype]
  exact SetLike.coe_mem _

theorem neighbourCore_X_le_pieceSpan_of_normalized (hq : 4 ≤ Nat.card K)
    (e : L ≃* adjointGroup .F4 K) {Φ : Matrix.SpecialLinearGroup (Fin 6) K →* G}
    (hr : Φ.range = neighbourCore e .X)
    (hn : ∀ s, Φ (sp6ToSL6 s) = levi6Hom e (RingEquiv.refl K) s) :
    neighbourCore e .X ≤ pieceSpan e := by
  rw [← hr, MonoidHom.range_eq_map, ← range_sp6ToSL6_sup_sl6BlockA, Subgroup.map_sup]
  refine sup_le ?_ ((map_sl6BlockA_le_pieceCore e hr hn).trans ?_)
  · rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
    rw [hn s]
    exact le_pieceSpan hq e (levi6Hom_mem e _ s)
  · exact le_iSup (fun J : {J : Finset (Fin (Tag.rank .F4)) // J.card ≤ 2} => pieceCore e J.1)
      ⟨{1, 2}, by decide⟩

theorem neighbourCore_X_le_pieceSpan_of_isLeviNormalizedA (hq : 4 ≤ Nat.card K)
    (e₁ : L ≃* adjointGroup .F4 K) {ΦA : e6ScLevi K e6A5Nodes →* G}
    (hr : ΦA.range = neighbourCore e₁ .X) (hn : IsLeviNormalizedA e₁ ΦA) :
    neighbourCore e₁ .X ≤ pieceSpan e₁ ∧
      (sl6BlockA K).map (ΦA.comp (graphParamEquiv K (RingEquiv.refl K)).toMonoidHom) ≤
        pieceCore e₁ {1, 2} := by
  have hr' : (ΦA.comp (graphParamEquiv K (RingEquiv.refl K)).toMonoidHom).range =
      neighbourCore e₁ .X := by
    rw [MonoidHom.range_comp,
      MonoidHom.range_eq_top.2 (graphParamEquiv K (RingEquiv.refl K)).surjective,
      ← MonoidHom.range_eq_map, hr]
  have hn' : ∀ s, (ΦA.comp (graphParamEquiv K (RingEquiv.refl K)).toMonoidHom) (sp6ToSL6 s) =
      levi6Hom e₁ (RingEquiv.refl K) s := fun s => hn s
  exact ⟨neighbourCore_X_le_pieceSpan_of_normalized hq e₁ hr' hn',
    map_sl6BlockA_le_pieceCore e₁ hr' hn'⟩

end Linear

section Constructors

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]

open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup sigma)

theorem isTwistedE6GraphRowParam_of_neighbourCore' (hq : 4 ≤ Nat.card K) {k : Type} [Field k]
    {θ : k →+* k} {e : L ≃* adjointGroup .F4 K} {t : G}
    {ΦX : twLevi k θ AmalgamNeighbour.X.nodes →* G}
    {ΦY : twLevi k θ AmalgamNeighbour.Y.nodes →* G}
    (htw : (∀ x : twLevi k θ {1, 2}, twLeviRestrict ΦX one_two_subset_X x =
        twLeviRestrict ΦY one_two_subset_Y x) ∨
      (∀ x y : twLevi k θ {1, 2}, (y : fixedGroup k θ) = sigmaHat θ x →
        twLeviRestrict ΦX one_two_subset_X x = twLeviRestrict ΦY one_two_subset_Y y))
    (hconjX : ∀ x y : twLevi k θ AmalgamNeighbour.X.nodes,
      (y : fixedGroup k θ) = sigmaHat θ x → t * ΦX x * t⁻¹ = ΦX y)
    (hconjY : ∀ x y : twLevi k θ AmalgamNeighbour.Y.nodes,
      (y : fixedGroup k θ) = sigmaHat θ x → t * ΦY x * t⁻¹ = ΦY y)
    (hcomm : ∀ a b, Commute (twLeviRestrict ΦY zero_subset_Y a)
      (twLeviRestrict ΦX three_subset_X b))
    {N₁ N₂ : AmalgamNeighbour} (hN : (N₁ = .X ∧ N₂ = .Y) ∨ (N₁ = .Y ∧ N₂ = .X))
    (hXr : ΦX.range = neighbourCore e N₁) (hYr : ΦY.range = neighbourCore e N₂)
    (hX : neighbourCore e .X ≤ pieceSpan e) (hY : neighbourCore e .Y ≤ pieceSpan e) :
    IsTwistedE6GraphRowParam e t ΦX ΦY where
  agree_or_twist := htw
  conjX := hconjX
  conjY := hconjY
  comm := hcomm
  range_sup := range_sup_eq_pieceSpan_of_neighbourCore' hq e hN hXr hYr hX hY

end Constructors

end CFSG.SeitzReduction.F4Pilot
