module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerYLevi
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassesReps
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotHR6X

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Ree

local instance twistedE6PilotCentralizerUDescentNeZeroTw : NeZero TwistTag.E6.tag.rank :=
  ⟨by decide⟩

local instance twistedE6PilotCentralizerUDescentNeZero : NeZero Tag.E6.rank := ⟨by decide⟩

local instance twistedE6PilotCentralizerUDescentNeZeroF4 : NeZero Tag.F4.rank := ⟨by decide⟩

section Twist

variable
  {K : Type} [Field K]

theorem twistHom_eq_baseChangeGL_of_mem_id
    (σ : K →+* K) {g : ModGL TwistTag.E6.tag K}
    (hg : g ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K)) :
    twistHom TwistTag.E6 K σ g = baseChangeGL σ g := by
  have hP := (mem_twistedFixedGroup_id_iff.1 hg).2
  rw [twistHom_apply]
  change diagramMap TwistTag.E6 K * Units.map (entrywiseHom σ) g * (diagramMap TwistTag.E6 K)⁻¹ =
    Units.map (entrywiseHom σ) g
  have hPσ := units_map_entrywiseHom_diagramMap (t := TwistTag.E6) (K := K) σ
  calc diagramMap TwistTag.E6 K * Units.map (entrywiseHom σ) g * (diagramMap TwistTag.E6 K)⁻¹
      = Units.map (entrywiseHom σ) (diagramMap TwistTag.E6 K) * Units.map (entrywiseHom σ) g *
          (Units.map (entrywiseHom σ) (diagramMap TwistTag.E6 K))⁻¹ := by rw [hPσ]
    _ = Units.map (entrywiseHom σ)
          (diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹) := by
        rw [map_mul, map_mul, map_inv]
    _ = Units.map (entrywiseHom σ) g := by rw [hP, mul_inv_cancel_right]

end Twist

section Graph


@[expose] noncomputable def adjointBaseChangeF4 {K' K : Type} [Field K'] [Field K]
    (f : K' →+* K) : adjointGroup .F4 K' →* adjointGroup .F4 K :=
  ((baseChangeGL f).comp (adjointGroup .F4 K').subtype).codRestrict _ fun x =>
    baseChangeGL_mem_adjointGroup f x.2

theorem adjointBaseChangeF4_pinnedX {K' K : Type} [Field K'] [Field K] (f : K' →+* K)
    (γ : Fin Tag.F4.rank → ℤ) (d : K') :
    adjointBaseChangeF4 f ⟨pinnedX .F4 K' γ d, pinnedX_mem_adjointGroup γ d⟩ =
      ⟨pinnedX .F4 K γ (f d), pinnedX_mem_adjointGroup γ (f d)⟩ :=
  Subtype.ext (baseChangeGL_pinnedX f γ d)


variable {K' K : Type} [Field K'] [Finite K'] [CharP K' ReeTag.F4.prime] [Field K] [Finite K]
  [CharP K ReeTag.F4.prime]

theorem graphAutF4_adjointBaseChangeF4_pinnedX (f : K' →+* K) {γ : Fin Tag.F4.rank → ℤ}
    (hγ : IsRoot .F4 γ) (d : K') :
    ReeTag.F4.finiteExceptionalAut K
        (adjointBaseChangeF4 f ⟨pinnedX .F4 K' γ d, pinnedX_mem_adjointGroup γ d⟩) =
      adjointBaseChangeF4 f
        (ReeTag.F4.finiteExceptionalAut K' ⟨pinnedX .F4 K' γ d, pinnedX_mem_adjointGroup γ d⟩) := by
  rw [adjointBaseChangeF4_pinnedX]
  have hsl : γ ∈ ReeTag.F4.shortRoots ∪ ReeTag.F4.longRoots := by
    rw [ReeTag.shortRoots_union_longRoots]
    exact hγ
  rcases hsl with hs | hl
  · have e1 := congrArg Subtype.val (finiteExceptionalAut_pinnedX_short (K := K) hs (f d))
    have e2 := congrArg Subtype.val (finiteExceptionalAut_pinnedX_short (K := K') hs d)
    have m : pinnedX ReeTag.F4.tag K (ReeTag.F4.dualRoot γ) ((f d) ^ 2) =
        baseChangeGL f (pinnedX ReeTag.F4.tag K' (ReeTag.F4.dualRoot γ) (d ^ 2)) := by
      rw [baseChangeGL_pinnedX, map_pow]
    exact Subtype.ext (e1.trans (m.trans (congrArg (baseChangeGL f) e2.symm)))
  · have e1 := congrArg Subtype.val (finiteExceptionalAut_pinnedX_long (K := K) hl (f d))
    have e2 := congrArg Subtype.val (finiteExceptionalAut_pinnedX_long (K := K') hl d)
    have m : pinnedX ReeTag.F4.tag K (ReeTag.F4.dualRoot γ) (f d) =
        baseChangeGL f (pinnedX ReeTag.F4.tag K' (ReeTag.F4.dualRoot γ) d) := by
      rw [baseChangeGL_pinnedX]
    exact Subtype.ext (e1.trans (m.trans (congrArg (baseChangeGL f) e2.symm)))

theorem graphAutF4_adjointBaseChangeF4 (f : K' →+* K) {x : adjointGroup .F4 K'}
    (hx : x ∈ F4Pilot.C3Levi K') :
    ReeTag.F4.finiteExceptionalAut K (adjointBaseChangeF4 f x) =
      adjointBaseChangeF4 f (ReeTag.F4.finiteExceptionalAut K' x) := by
  have hle : F4Pilot.C3Levi K' ≤ MonoidHom.eqLocus
      ((ReeTag.F4.finiteExceptionalAut K).toMonoidHom.comp (adjointBaseChangeF4 f))
      ((adjointBaseChangeF4 f).comp (ReeTag.F4.finiteExceptionalAut K').toMonoidHom) := by
    rw [F4Pilot.C3Levi_eq_closure, closure_le]
    rintro _ ⟨γ, hγ, c, rfl⟩
    have e : f4Par K' γ c = ⟨pinnedX .F4 K' γ
        (((rootOperatorFamily .F4).pinnedFamilySign γ : K') * c),
        pinnedX_mem_adjointGroup _ _⟩ := Subtype.ext (F4Pilot.coe_f4Par_eq_pinnedX hγ.1 c)
    rw [SetLike.mem_coe, e]
    exact graphAutF4_adjointBaseChangeF4_pinnedX f hγ.1 _
  exact hle hx

end Graph

section Descent


variable {k K : Type} [Field k] [Finite k] [CharP k 2] [Field K] [Finite K] [CharP K 2]
  [Algebra k K]

omit
  [Finite K] [Field k] [Finite k] [CharP k 2] [Algebra k K] in
theorem coe_yLeviF4EquivB3Levi (g : E6Pilot.yLeviF4 K) :
    (((E6Pilot.yLeviF4EquivB3Levi K g : F4Pilot.B3Levi K) : adjointGroup .F4 K) : ModGL .F4 K) =
      e6FixedToF4 K ⟨(g : ModGL .E6 K), E6Pilot.yLeviF4_le_yGamma g.2⟩ :=
  rfl

theorem exists_baseChangeGL_eq_of_mem_yLeviF4 (σ : K →+* K)
    (hfix : ∀ x : K, σ x = x ↔ x ∈ Set.range (algebraMap k K)) {g : ModGL .E6 K}
    (hg : g ∈ E6Pilot.yLeviF4 K) (hσg : baseChangeGL σ g = g) :
    ∃ g₀ ∈ E6Pilot.yLeviF4 k, baseChangeGL (algebraMap k K) g₀ = g := by
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  have : CharP k ReeTag.F4.prime := ‹CharP k 2›
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have hgΓ := E6Pilot.yLeviF4_le_yGamma hg
  set b : F4Pilot.B3Levi K := E6Pilot.yLeviF4EquivB3Levi K ⟨g, hg⟩ with hb
  have hbcoe : ((b : adjointGroup .F4 K) : ModGL .F4 K) = e6FixedToF4 K ⟨g, hgΓ⟩ := rfl
  set c : F4Pilot.C3Levi K := (F4Pilot.c3LeviEquivB3Levi K).symm b with hc
  have hcb : F4Pilot.graphAutF4 K (c : adjointGroup .F4 K) = (b : adjointGroup .F4 K) := by
    rw [← F4Pilot.coe_c3LeviEquivB3Levi, hc, MulEquiv.apply_symm_apply]
  have hσc : F4Pilot.c3LeviBaseChange σ c = c := by
    apply Subtype.ext
    apply (F4Pilot.graphAutF4 K).injective
    have e1 : ((F4Pilot.c3LeviBaseChange σ c : F4Pilot.C3Levi K) : adjointGroup .F4 K) =
        adjointBaseChangeF4 σ (c : adjointGroup .F4 K) := Subtype.ext rfl
    rw [e1]
    have h3 : F4Pilot.graphAutF4 K (adjointBaseChangeF4 σ (c : adjointGroup .F4 K)) =
        adjointBaseChangeF4 σ (F4Pilot.graphAutF4 K (c : adjointGroup .F4 K)) :=
      graphAutF4_adjointBaseChangeF4 σ c.2
    rw [h3, hcb]
    apply Subtype.ext
    change baseChangeGL σ ((b : adjointGroup .F4 K) : ModGL .F4 K) =
      ((b : adjointGroup .F4 K) : ModGL .F4 K)
    rw [hbcoe, ← e6FixedToF4_baseChangeGL σ ⟨g, hgΓ⟩]
    congr 1
    exact Subtype.ext hσg
  have hmem : c ∈ MonoidHom.eqLocus (F4Pilot.c3LeviBaseChange σ) (MonoidHom.id _) := hσc
  rw [← F4Pilot.map_c3LeviBaseChange_eq_eqLocus (algebraMap k K) σ hfix] at hmem
  obtain ⟨c₀, -, hc₀⟩ := hmem
  set b₀ : F4Pilot.B3Levi k := F4Pilot.c3LeviEquivB3Levi k c₀ with hb₀
  set g₀ : E6Pilot.yLeviF4 k := (E6Pilot.yLeviF4EquivB3Levi k).symm b₀ with hg₀
  refine ⟨g₀, g₀.2, ?_⟩
  have hg₀Γ := E6Pilot.yLeviF4_le_yGamma g₀.2
  have key : e6FixedToF4 K ⟨baseChangeGL (algebraMap k K) (g₀ : ModGL .E6 k),
      baseChangeGL_mem_twistedFixedGroup (algebraMap k K) hg₀Γ⟩ = e6FixedToF4 K ⟨g, hgΓ⟩ := by
    rw [e6FixedToF4_baseChangeGL (algebraMap k K) ⟨(g₀ : ModGL .E6 k), hg₀Γ⟩]
    have h1 : e6FixedToF4 k ⟨(g₀ : ModGL .E6 k), hg₀Γ⟩ =
        ((b₀ : adjointGroup .F4 k) : ModGL .F4 k) := by
      rw [← coe_yLeviF4EquivB3Levi, hg₀, MulEquiv.apply_symm_apply]
    rw [h1, ← hbcoe, ← hcb]
    have h2 : (b₀ : adjointGroup .F4 k) = F4Pilot.graphAutF4 k (c₀ : adjointGroup .F4 k) :=
      F4Pilot.coe_c3LeviEquivB3Levi c₀
    have h4 : adjointBaseChangeF4 (algebraMap k K) (c₀ : adjointGroup .F4 k) =
        (c : adjointGroup .F4 K) := by
      rw [← hc₀]
      rfl
    have h3 := congrArg Subtype.val (graphAutF4_adjointBaseChangeF4 (algebraMap k K) c₀.2)
    rw [h4] at h3
    rw [h2]
    exact h3.symm
  have := e6FixedToF4Group_injective (K := K) h2K
    (a₁ := ⟨_, baseChangeGL_mem_twistedFixedGroup (algebraMap k K) hg₀Γ⟩) (a₂ := ⟨g, hgΓ⟩)
    (Subtype.ext key)
  exact congrArg Subtype.val this

end Descent

section Levi


section Defs

variable {K : Type} [Field K]

@[expose] noncomputable def uLevi (σ : K →+* K) : Subgroup (ModGL TwistTag.E6.tag K) :=
  E6Pilot.yLeviF4 K ⊓ graphFixedRootGroup TwistTag.E6 K σ

@[expose] noncomputable def uRadical (σ : K →+* K) : Subgroup (ModGL TwistTag.E6.tag K) :=
  parabolicRadical TwistTag.E6.tag K E6Pilot.nodes16 ⊓ graphFixedRootGroup TwistTag.E6 K σ

end Defs

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem baseChangeGL_yLeviF4Gens_mem_C0 [CharP K 2] {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c)
    (hσι : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c) {g : ModGL .E6 k}
    (hg : g ∈ E6Pilot.yLeviF4Gens k) :
    baseChangeGL (algebraMap k K) g ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  have hfix : ∀ i : Fin TwistTag.E6.tag.rank, TwistTag.E6.perm i = i → ∀ c : k,
      xUnit TwistTag.E6.tag K i (algebraMap k K c) ∈ graphFixedRootGroup TwistTag.E6 K σ ∧
        yUnit TwistTag.E6.tag K i (algebraMap k K c) ∈ graphFixedRootGroup TwistTag.E6 K σ := by
    intro i hi c
    constructor
    · rw [← pinnedX_single]
      exact pinnedX_mem_graphFixedRootGroup_of_fixed σ (isRoot_single _ _)
        (by rw [permLattice_single, hi]) (hσι c)
    · rw [← pinnedX_neg_single]
      exact pinnedX_mem_graphFixedRootGroup_of_fixed σ (isRoot_neg_single _ _)
        (by rw [permLattice_neg_single, hi]) (hσι c)
  have hpair : ∀ c : k,
      xUnit TwistTag.E6.tag K 2 (algebraMap k K c) * xUnit TwistTag.E6.tag K 4 (algebraMap k K c) ∈
          graphFixedRootGroup TwistTag.E6 K σ ∧
        yUnit TwistTag.E6.tag K 2 (algebraMap k K c) *
          yUnit TwistTag.E6.tag K 4 (algebraMap k K c) ∈ graphFixedRootGroup TwistTag.E6 K σ := by
    intro c
    have h24 : TwistTag.E6.perm 2 = 4 := by decide
    constructor
    · have e : xUnit TwistTag.E6.tag K 2 (algebraMap k K c) *
          xUnit TwistTag.E6.tag K 4 (algebraMap k K c) =
            twistedE6PairX σ (Pi.single 2 1) (algebraMap k K c) := by
        rw [twistedE6PairX, permLattice_single, h24, hσι, pinnedX_single, pinnedX_single]
      rw [e]
      exact twistedE6PairX_mem_graphFixedRootGroup hσσ (isRoot_single _ _) _
    · have e : yUnit TwistTag.E6.tag K 2 (algebraMap k K c) *
          yUnit TwistTag.E6.tag K 4 (algebraMap k K c) =
            twistedE6PairX σ (-Pi.single 2 1) (algebraMap k K c) := by
        rw [twistedE6PairX, permLattice_neg_single, h24, hσι, pinnedX_neg_single,
          pinnedX_neg_single]
      rw [e]
      exact twistedE6PairX_mem_graphFixedRootGroup hσσ (isRoot_neg_single _ _) _
  obtain ⟨j, hj, c, rfl | rfl⟩ := hg
  · rcases (by decide : ∀ j : Fin Tag.F4.rank, j ≠ 3 → j = 0 ∨ j = 1 ∨ j = 2) j hj with
      rfl | rfl | rfl
    · rw [E6Pilot.f4OrbitXUnit_zero, baseChangeGL_xUnit]
      exact (hfix 1 (by decide) c).1
    · rw [E6Pilot.f4OrbitXUnit_one, baseChangeGL_xUnit]
      exact (hfix 3 (by decide) c).1
    · rw [E6Pilot.f4OrbitXUnit_two, map_mul, baseChangeGL_xUnit, baseChangeGL_xUnit]
      exact (hpair c).1
  · rcases (by decide : ∀ j : Fin Tag.F4.rank, j ≠ 3 → j = 0 ∨ j = 1 ∨ j = 2) j hj with
      rfl | rfl | rfl
    · rw [E6Pilot.f4OrbitYUnit_zero, baseChangeGL_yUnit]
      exact (hfix 1 (by decide) c).2
    · rw [E6Pilot.f4OrbitYUnit_one, baseChangeGL_yUnit]
      exact (hfix 3 (by decide) c).2
    · rw [E6Pilot.f4OrbitYUnit_two, map_mul, baseChangeGL_yUnit, baseChangeGL_yUnit]
      exact (hpair c).2


theorem uLevi_eq_map (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    uLevi σ = (E6Pilot.yLeviF4 k).map (baseChangeGL (algebraMap k K)) := by
  have := finite_of_card hK
  have := charP_two_of_card hf hK
  have := Nat.finite_of_card_ne_zero (show Nat.card k ≠ 0 by rw [hk]; positivity)
  have hk2 : (2 : k) = 0 := E6GraphHighestRoot.two_eq_zero_of_card hf hk
  have : CharP k 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero hk2
  have hσσ := apply_apply_eq hK hσ
  have hfix : ∀ x : K, σ x = x ↔ x ∈ Set.range (algebraMap k K) := sigma_eq_self_iff hk hσ
  have hσι : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c := fun c => (hfix _).2 ⟨c, rfl⟩
  refine le_antisymm (fun g hg => ?_) ?_
  · obtain ⟨hgL, hgC⟩ := mem_inf.1 hg
    have hF : twistHom TwistTag.E6 K σ g = g :=
      ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 (graphFixedRootGroup_le _ _ _ hgC)).2
    rw [twistHom_eq_baseChangeGL_of_mem_id σ (E6Pilot.yLeviF4_le_yGamma hgL)] at hF
    obtain ⟨g₀, hg₀, rfl⟩ := exists_baseChangeGL_eq_of_mem_yLeviF4 σ hfix hgL hF
    exact ⟨g₀, hg₀, rfl⟩
  · rw [E6Pilot.yLeviF4, MonoidHom.map_closure]
    refine (closure_le (uLevi σ)).2 ?_
    rintro _ ⟨g, hg, rfl⟩
    refine mem_inf.2 ⟨?_, baseChangeGL_yLeviF4Gens_mem_C0 hσσ hσι hg⟩
    obtain ⟨j, hj, c, rfl | rfl⟩ := hg
    · rcases (by decide : ∀ j : Fin Tag.F4.rank, j ≠ 3 → j = 0 ∨ j = 1 ∨ j = 2) j hj with
        rfl | rfl | rfl
      · rw [E6Pilot.f4OrbitXUnit_zero, baseChangeGL_xUnit]
        exact (E6Pilot.simple_mem_yLeviF4 _).1
      · rw [E6Pilot.f4OrbitXUnit_one, baseChangeGL_xUnit]
        exact (E6Pilot.simple_mem_yLeviF4 _).2.2.1
      · rw [E6Pilot.f4OrbitXUnit_two, map_mul, baseChangeGL_xUnit, baseChangeGL_xUnit]
        exact (E6Pilot.simple_mem_yLeviF4 _).2.2.2.2.1
    · rcases (by decide : ∀ j : Fin Tag.F4.rank, j ≠ 3 → j = 0 ∨ j = 1 ∨ j = 2) j hj with
        rfl | rfl | rfl
      · rw [E6Pilot.f4OrbitYUnit_zero, baseChangeGL_yUnit]
        exact (E6Pilot.simple_mem_yLeviF4 _).2.1
      · rw [E6Pilot.f4OrbitYUnit_one, baseChangeGL_yUnit]
        exact (E6Pilot.simple_mem_yLeviF4 _).2.2.2.1
      · rw [E6Pilot.f4OrbitYUnit_two, map_mul, baseChangeGL_yUnit, baseChangeGL_yUnit]
        exact (E6Pilot.simple_mem_yLeviF4 _).2.2.2.2.2

noncomputable def uLeviEquiv (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ↥(E6Pilot.yLeviF4 k) ≃* ↥(uLevi σ) :=
  ((E6Pilot.yLeviF4 k).equivMapOfInjective _ (baseChangeGL_injective (algebraMap k K))).trans
    (MulEquiv.subgroupCongr (uLevi_eq_map hf hk hK hσ).symm)

theorem lieModel_uLevi (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) : LieModel (uLevi σ) .PSp 3 2 f := by
  have := Nat.finite_of_card_ne_zero (show Nat.card k ≠ 0 by rw [hk]; positivity)
  have hk2 : (2 : k) = 0 := E6GraphHighestRoot.two_eq_zero_of_card hf hk
  have : CharP k 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero hk2
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
    ((E6Pilot.yLeviF4EquivB3Levi k).symm.trans (uLeviEquiv hf hk hK hσ))
    (F4Pilot.lieModel_B3Levi hk)

theorem isSimpleGroup_uLevi (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    IsSimpleGroup (uLevi σ) := by
  have := Nat.finite_of_card_ne_zero (show Nat.card k ≠ 0 by rw [hk]; positivity)
  have hk2 : (2 : k) = 0 := E6GraphHighestRoot.two_eq_zero_of_card hf hk
  have : CharP k 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero hk2
  have := F4Pilot.isSimpleGroup_B3Levi (K := k)
  exact ((E6Pilot.yLeviF4EquivB3Levi k).symm.trans (uLeviEquiv hf hk hK hσ)).symm.isSimpleGroup

theorem isPerfect_uLevi (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    Group.IsPerfect (uLevi σ) := by
  have := Nat.finite_of_card_ne_zero (show Nat.card k ≠ 0 by rw [hk]; positivity)
  have hk2 : (2 : k) = 0 := E6GraphHighestRoot.two_eq_zero_of_card hf hk
  have : CharP k 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero hk2
  have : Group.IsPerfect (F4Pilot.B3Levi k) :=
    ⟨(F4Pilot.isQuasisimple_open_B3Levi (K := k)).1⟩
  exact Group.IsPerfect.ofSurjective
    (f := ((E6Pilot.yLeviF4EquivB3Levi k).symm.trans (uLeviEquiv hf hk hK hσ)).toMonoidHom)
    (MulEquiv.surjective _)

end Levi

end CFSG.SeitzReduction.TwistedE6Pilot
