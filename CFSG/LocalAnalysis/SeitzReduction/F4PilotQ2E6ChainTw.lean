module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6ChainModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup twistedRootGroup rho proj_single
  proj_neg_single rho_single rho_neg_single twistSign_single twistSign_neg_single
  mem_twistedRootGroup_iff_of_pair commute_xm)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.Timmesfeld.LieEmbed (a5Root c3ToF4 c3ToF4_single)
open CFSG.LieType.Ree (ReeTag)
open CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer
  (fixedField_charP fixedField_finite)

local instance f4PilotQ2E6ChainTwNeZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance f4PilotQ2E6ChainTwNeZeroRankE6 : NeZero Tag.E6.rank := ⟨by decide⟩

@[expose] def rootA5Top : Fin (Tag.rank .E6) → ℤ := ![1, 0, 1, 1, 1, 1]

theorem a5Root_graphSwapPerm_zero_three :
    a5Root (graphSwapPerm.symm 0) (graphSwapPerm.symm 3) = rootA5Top ∧
      a5Root (graphSwapPerm.symm 3) (graphSwapPerm.symm 0) = -rootA5Top := by
  decide +kernel

section Twisted

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (h : UnitaryFieldData 2 f F)

theorem commute_xm_of_rootFinset {γ δ : Fin (Tag.rank .E6) → ℤ} (hδ : δ ∈ rootFinset .E6)
    (hγ : γ ∈ rootFinset .E6) (hne : δ + γ ≠ 0) (hn : δ + γ ∉ rootFinset .E6) (c d : F) :
    Commute (e6Data_valid.xm F δ c) (e6Data_valid.xm F γ d) :=
  commute_xm (mem_rootFinset.1 hδ) (mem_rootFinset.1 hγ) hne (fun hr => hn (mem_rootFinset.2 hr))
    c d

theorem chainTw_rho_zero : rho (Pi.single (0 : Fin (Tag.rank .E6)) 1) = Pi.single 5 1 := by
  rw [rho_single]
  congr 1

theorem chainTw_rho_neg_zero : rho (-Pi.single (0 : Fin (Tag.rank .E6)) 1) = -Pi.single 5 1 := by
  rw [rho_neg_single]
  congr 2

theorem chainTw_rho_zero_ne : rho (Pi.single (0 : Fin (Tag.rank .E6)) 1) ≠ Pi.single 0 1 := by
  rw [chainTw_rho_zero]
  intro e
  have := congrFun e 5
  simp at this

theorem chainTw_rho_neg_zero_ne :
    rho (-Pi.single (0 : Fin (Tag.rank .E6)) 1) ≠ -Pi.single 0 1 := by
  rw [chainTw_rho_neg_zero]
  intro e
  have := congrFun e 5
  simp at this

theorem chainTw_mem_twistedRootGroup_three (g : fixedGroup F h.barEquiv.toRingHom) :
    g ∈ twistedRootGroup F h.barEquiv.toRingHom (Pi.single 3 1) ↔
      ∃ c, (g : e6Data_valid.minGroup F) = e6Data_valid.xm F (Pi.single 0 1) c *
        e6Data_valid.xm F (Pi.single 5 1) (h.barEquiv.toRingHom c) := by
  rw [mem_twistedRootGroup_iff_of_pair h.barEquiv.toRingHom (isRoot_single .E6 0)
    (by rw [proj_single]; rfl) chainTw_rho_zero_ne]
  simp only [chainTw_rho_zero, twistSign_single, Int.cast_one, one_mul]

theorem chainTw_mem_twistedRootGroup_neg_three (g : fixedGroup F h.barEquiv.toRingHom) :
    g ∈ twistedRootGroup F h.barEquiv.toRingHom (-Pi.single 3 1) ↔
      ∃ c, (g : e6Data_valid.minGroup F) = e6Data_valid.xm F (-Pi.single 0 1) c *
        e6Data_valid.xm F (-Pi.single 5 1) (h.barEquiv.toRingHom c) := by
  rw [mem_twistedRootGroup_iff_of_pair h.barEquiv.toRingHom (isRoot_neg_single .E6 0)
    (by rw [proj_neg_single]; rfl) chainTw_rho_neg_zero_ne]
  simp only [chainTw_rho_neg_zero, twistSign_neg_single, Int.cast_one, one_mul]

theorem twLevi_three_le_centralizer {y : fixedGroup F h.barEquiv.toRingHom}
    (h1 : ∀ c, Commute (e6Data_valid.xm F (Pi.single 0 1) c) (y : e6Data_valid.minGroup F))
    (h2 : ∀ c, Commute (e6Data_valid.xm F (Pi.single 5 1) c) (y : e6Data_valid.minGroup F))
    (h3 : ∀ c, Commute (e6Data_valid.xm F (-Pi.single 0 1) c) (y : e6Data_valid.minGroup F))
    (h4 : ∀ c, Commute (e6Data_valid.xm F (-Pi.single 5 1) c) (y : e6Data_valid.minGroup F)) :
    twLevi F h.barEquiv.toRingHom {3} ≤
      centralizer ({y} : Set (fixedGroup F h.barEquiv.toRingHom)) := by
  dsimp only [twLevi]
  rw [CFSG.LieType.CurtisTits.levi_singleton, CFSG.LieType.CurtisTits.rankOne]
  refine sup_le (fun g hg => ?_) (fun g hg => ?_)
  · obtain ⟨c, hc⟩ := (chainTw_mem_twistedRootGroup_three h g).1 hg
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]
    exact ((h1 c).mul_left (h2 _)).eq
  · obtain ⟨c, hc⟩ := (chainTw_mem_twistedRootGroup_neg_three h g).1 hg
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]
    exact ((h3 c).mul_left (h4 _)).eq

theorem twLevi_two_le_centralizer {y : fixedGroup F h.barEquiv.toRingHom}
    (h1 : ∀ c, Commute (e6Data_valid.xm F (Pi.single 2 1) c) (y : e6Data_valid.minGroup F))
    (h2 : ∀ c, Commute (e6Data_valid.xm F (Pi.single 4 1) c) (y : e6Data_valid.minGroup F))
    (h3 : ∀ c, Commute (e6Data_valid.xm F (-Pi.single 2 1) c) (y : e6Data_valid.minGroup F))
    (h4 : ∀ c, Commute (e6Data_valid.xm F (-Pi.single 4 1) c) (y : e6Data_valid.minGroup F)) :
    twLevi F h.barEquiv.toRingHom {2} ≤
      centralizer ({y} : Set (fixedGroup F h.barEquiv.toRingHom)) := by
  dsimp only [twLevi]
  rw [CFSG.LieType.CurtisTits.levi_singleton, CFSG.LieType.CurtisTits.rankOne]
  refine sup_le (fun g hg => ?_) (fun g hg => ?_)
  · obtain ⟨c, hc⟩ := (rigA3_mem_twistedRootGroup_two h g).1 hg
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]
    exact ((h1 c).mul_left (h2 _)).eq
  · obtain ⟨c, hc⟩ := (rigA3_mem_twistedRootGroup_neg_two h g).1 hg
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]
    exact ((h3 c).mul_left (h4 _)).eq

end Twisted

section Align

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (h : UnitaryFieldData 2 f F)
  {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .F4 K}

theorem rootGroup_le_alignedTw_of {J : Finset (Fin (Tag.rank .F4))}
    (hJ : J ⊆ AmalgamNeighbour.X.nodes) {σ : Fin (Tag.rank .F4) → ℤ} (hσ : IsRoot .F4 σ)
    {ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G}
    (hy : ∀ c : K, ∃ y : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes,
      ΦX y = ((e.symm (Adjoint.f4Par K σ c) : L) : G) ∧
        twLevi F h.barEquiv.toRingHom J ≤ centralizer
          ({(y : fixedGroup F h.barEquiv.toRingHom)} : Set (fixedGroup F h.barEquiv.toRingHom))) :
    (Adjoint.f4Datum K).rootGroup σ ≤ alignedSubgroup e (twLeviRestrict ΦX hJ).range := by
  intro l hl
  obtain ⟨c, rfl⟩ := (Adjoint.mem_rootGroup_iff hσ l).1 hl
  obtain ⟨y, hyΦ, hyc⟩ := hy c
  rw [alignedSubgroup, Subgroup.mem_comap, mem_centralizer_iff]
  rintro _ ⟨z, rfl⟩
  change twLeviRestrict ΦX hJ z * ((e.symm (Adjoint.f4Par K σ c) : L) : G) =
    ((e.symm (Adjoint.f4Par K σ c) : L) : G) * twLeviRestrict ΦX hJ z
  rw [← hyΦ, twLeviRestrict_apply, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact mem_centralizer_singleton_iff.1 (hyc z.2)

theorem coe_twParamEquiv_uEmbed6_x_root221 (c : h.fixedField) :
    (((twParamEquiv h (uEmbed6 h (Sp.x 3 h.fixedField ![2, 2, 1] c)) :
      twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
        fixedGroup F h.barEquiv.toRingHom) : e6Data_valid.minGroup F) =
      e6Data_valid.xm F rootA5Top (c : F) := by
  have := fixedField_finite h
  have := fixedField_charP h
  rw [coe_twParamEquiv_uEmbed6, sp6ToSL6_x_root221, map_transvection,
    graphParamHom_transvection, a5Root_graphSwapPerm_zero_three.1]
  rfl

theorem coe_twParamEquiv_uEmbed6_x_neg_root221 (c : h.fixedField) :
    (((twParamEquiv h (uEmbed6 h (Sp.x 3 h.fixedField (-![2, 2, 1]) c)) :
      twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
        fixedGroup F h.barEquiv.toRingHom) : e6Data_valid.minGroup F) =
      e6Data_valid.xm F (-rootA5Top) (c : F) := by
  have := fixedField_finite h
  have := fixedField_charP h
  rw [coe_twParamEquiv_uEmbed6, sp6ToSL6_x_neg_root221, map_transvection,
    graphParamHom_transvection, a5Root_graphSwapPerm_zero_three.2]
  rfl

variable (ε : h.fixedField ≃+* K)

theorem f4RootPairAlign_a2_le_alignedTw_three
    {ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G}
    (hn : IsLeviNormalizedU h ε e ΦX) :
    f4RootPairAlign K (Pi.single 1 1) ≤
      alignedSubgroup e (twLeviRestrict ΦX three_subset_X).range := by
  rw [f4RootPairAlign]
  refine sup_le (rootGroup_le_alignedTw_of h three_subset_X (isRoot_single _ 1) fun c => ?_)
    (rootGroup_le_alignedTw_of h three_subset_X (isRoot_neg_single _ 1) fun c => ?_)
  · refine ⟨twParamEquiv h (uEmbed6 h (Sp.x 3 h.fixedField (Pi.single 2 1) (ε.symm c))), ?_, ?_⟩
    · rw [hn, levi6Hom_x_alignTw, c3ToF4_single, ε.apply_symm_apply]
      rfl
    · have hy := coe_twParamEquiv_uEmbed6_x_single_two h (ε.symm c)
      refine twLevi_three_le_centralizer h (fun d => ?_) (fun d => ?_) (fun d => ?_)
        (fun d => ?_) <;>
      (rw [hy]; exact commute_xm_of_rootFinset (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel) _ _)
  · refine ⟨twParamEquiv h (uEmbed6 h (Sp.x 3 h.fixedField (-Pi.single 2 1) (ε.symm c))), ?_, ?_⟩
    · rw [hn, levi6Hom_x_alignTw, map_neg, c3ToF4_single, ε.apply_symm_apply]
      rfl
    · have hy := coe_twParamEquiv_uEmbed6_x_neg_single_two h (ε.symm c)
      refine twLevi_three_le_centralizer h (fun d => ?_) (fun d => ?_) (fun d => ?_)
        (fun d => ?_) <;>
      (rw [hy]; exact commute_xm_of_rootFinset (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel) _ _)

theorem f4RootPairAlign_e1e2_le_alignedTw_two
    {ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G}
    (hn : IsLeviNormalizedU h ε e ΦX) :
    f4RootPairAlign K rootE1mE2Align ≤
      alignedSubgroup e (twLeviRestrict ΦX two_subset_X).range := by
  rw [f4RootPairAlign]
  refine sup_le (rootGroup_le_alignedTw_of h two_subset_X isRoot_rootE1mE2Align fun c => ?_)
    (rootGroup_le_alignedTw_of h two_subset_X (IsRoot.neg isRoot_rootE1mE2Align) fun c => ?_)
  · refine ⟨twParamEquiv h (uEmbed6 h (Sp.x 3 h.fixedField ![2, 2, 1] (ε.symm c))), ?_, ?_⟩
    · rw [hn, levi6Hom_x_alignTw, c3ToF4_root221, ε.apply_symm_apply]
    · have hy := coe_twParamEquiv_uEmbed6_x_root221 h (ε.symm c)
      refine twLevi_two_le_centralizer h (fun d => ?_) (fun d => ?_) (fun d => ?_)
        (fun d => ?_) <;>
      (rw [hy]; exact commute_xm_of_rootFinset (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel) _ _)
  · refine ⟨twParamEquiv h (uEmbed6 h (Sp.x 3 h.fixedField (-![2, 2, 1]) (ε.symm c))), ?_, ?_⟩
    · rw [hn, levi6Hom_x_alignTw, map_neg, c3ToF4_root221, ε.apply_symm_apply]
    · have hy := coe_twParamEquiv_uEmbed6_x_neg_root221 h (ε.symm c)
      refine twLevi_two_le_centralizer h (fun d => ?_) (fun d => ?_) (fun d => ?_)
        (fun d => ?_) <;>
      (rw [hy]; exact commute_xm_of_rootFinset (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel) _ _)

end Align

end CFSG.SeitzReduction.F4Pilot
