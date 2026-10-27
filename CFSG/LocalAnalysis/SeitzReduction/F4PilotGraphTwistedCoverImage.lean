module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviYMinus
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTGraphTwistedFamily

public section

namespace CFSG.SeitzReduction.F4Pilot

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.SeitzReduction.TwistedE6Pilot
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail (tailModelEquiv tailModelEquiv_inl
  tailModelEquiv_inr_inl tailModelEquiv_inr_inr)
open CFSG.ComponentClassification.UnbalancedCatalog (semilinCentralizer descentField
  mem_descentField)

section Eichler

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eichler_eq_eichler_neg_of_isotropic {u w : V} (hu : Q u = 0) (hw : Q w = 0)
    (huw : polar Q u w = 0) : eichler Q u w = eichler Q w (-u) := by
  have hwu : polar Q w (-u) = 0 := by rw [polar_neg_right, polar_comm, huw, neg_zero]
  refine LinearEquiv.ext fun x => ?_
  rw [eichler_apply hu huw, eichler_apply hw hwu, hw, QuadraticMap.map_neg, hu,
    polar_neg_right]
  module

end Eichler

section Descent

variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F}
  (hσσ : ∀ c, σ (σ c) = c) {ω : F} (hω : σ ω ≠ ω)

omit [CharP F 2] in
include hσσ hω in
theorem d4DescentEquiv_eq_eichler {u w : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ}
    (hu : quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω) u = 0)
    (hw : polar (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω)) u w = 0)
    (x : ↥(TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 F) ⊓ semilinCentralizer (d4Tau σ)))
    (hx : (x : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] _) =
      eichler (quadPlus 4 F) (d4Iota σ ω u) (d4Iota σ ω w)) :
    ((d4DescentEquiv hσσ hω x : _) :
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ) ≃ₗ[descentField σ] _) =
      eichler (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω)) u w := by
  have hu' : quadPlus 4 F (d4Iota σ ω u) = 0 := by
    rw [quadPlus_d4Iota hσσ, hu]
    rfl
  have hw' : polar (quadPlus 4 F) (d4Iota σ ω u) (d4Iota σ ω w) = 0 := by
    rw [polar_quadPlus_d4Iota hσσ, hw]
    rfl
  have key := d4Iota_d4DescentEquiv_inj hσσ hω
    (g := ⟨eichler (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω)) u w,
      eichler_mem_orthogonalGroup _ u w⟩) (x := x) (fun v => by
      rw [hx]
      change d4Iota σ ω (eichler _ u w v) = eichler (quadPlus 4 F) _ _ (d4Iota σ ω v)
      rw [eichler_apply hu hw, eichler_apply hu' hw', map_sub, map_add, map_smul, map_smul,
        polar_quadPlus_d4Iota hσσ, polar_quadPlus_d4Iota hσσ, quadPlus_d4Iota hσσ,
        Subfield.smul_def, Subfield.smul_def]
      push_cast
      rfl)
  rw [key]

omit [Finite F] [CharP F 2] in
theorem d4Iota_single_inl (i : Fin (4 - 1)) :
    d4Iota σ ω (Pi.single (Sum.inl i) 1) = Pi.single (Sum.inl ⟨i.val, by omega⟩) 1 := by
  funext s
  rcases s with j | j
  · rw [d4Iota_apply, d4IotaFun]
    by_cases hj : (j : ℕ) < 4 - 1
    · rw [dite_eq_left hj]
      by_cases hij : j = ⟨i.val, by omega⟩
      · have e : (⟨j, hj⟩ : Fin (4 - 1)) = i := Fin.ext (by simp [hij])
        rw [e, hij]
        simp
      · have : (⟨j, hj⟩ : Fin (4 - 1)) ≠ i := fun h => hij (by rw [← h])
        simp [hij, this]
    · rw [dite_eq_right hj]
      have : j ≠ ⟨i.val, by omega⟩ := fun h => hj (by rw [h]; exact i.isLt)
      simp [this]
  · rw [d4Iota_apply, d4IotaFun]
    by_cases hj : (j : ℕ) < 4 - 1
    · rw [dite_eq_left hj]
      simp
    · rw [dite_eq_right hj]
      simp

omit [Finite F] [CharP F 2] in
theorem d4Iota_single_inr (i : Fin (4 - 1)) :
    d4Iota σ ω (Pi.single (Sum.inr (Sum.inl i)) 1) = Pi.single (Sum.inr ⟨i.val, by omega⟩) 1 := by
  funext s
  rcases s with j | j
  · rw [d4Iota_apply, d4IotaFun]
    by_cases hj : (j : ℕ) < 4 - 1
    · rw [dite_eq_left hj]
      simp
    · rw [dite_eq_right hj]
      simp
  · rw [d4Iota_apply, d4IotaFun]
    by_cases hj : (j : ℕ) < 4 - 1
    · rw [dite_eq_left hj]
      by_cases hij : j = ⟨i.val, by omega⟩
      · have e : (⟨j, hj⟩ : Fin (4 - 1)) = i := Fin.ext (by simp [hij])
        rw [e, hij]
        simp
      · have : (⟨j, hj⟩ : Fin (4 - 1)) ≠ i := fun h => hij (by rw [← h])
        simp [hij, this]
    · rw [dite_eq_right hj]
      have : j ≠ ⟨i.val, by omega⟩ := fun h => hj (by rw [h]; exact i.isLt)
      simp [this]

omit [Finite F] [CharP F 2] in
theorem d4Iota_tail (a : Fin 2 → descentField σ) :
    d4Iota σ ω (tailModelEquiv (4 - 1) (descentField σ) (Fin 2) (0, a)) =
      ((a 0 : F) + (a 1 : F) * ω) • Pi.single (Sum.inl 3) 1 +
        ((a 0 : F) + (a 1 : F) * σ ω) • Pi.single (Sum.inr 3) 1 := by
  funext s
  rcases s with j | j
  · rw [d4Iota_apply, d4IotaFun]
    by_cases hj : (j : ℕ) < 4 - 1
    · rw [dite_eq_left hj, tailModelEquiv_inl]
      have : j ≠ 3 := fun h => by rw [h] at hj; simp at hj
      simp [this]
    · rw [dite_eq_right hj, tailModelEquiv_inr_inr, tailModelEquiv_inr_inr]
      have : j = 3 := eq_three_of_not_lt hj
      subst this
      simp
  · rw [d4Iota_apply, d4IotaFun]
    by_cases hj : (j : ℕ) < 4 - 1
    · rw [dite_eq_left hj, tailModelEquiv_inr_inl]
      have : j ≠ 3 := fun h => by rw [h] at hj; simp at hj
      simp [this]
    · rw [dite_eq_right hj, tailModelEquiv_inr_inr, tailModelEquiv_inr_inr]
      have : j = 3 := eq_three_of_not_lt hj
      subst this
      simp

end Descent

section Isogeny

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup twistedRootGroup mem_twistedRootGroup_iff
  proj_single proj_neg_single rho_single rho_neg_single orbitMap_firstNode firstNode rhoPerm)

theorem firstNode_mem_setD {j : Fin (Tag.rank .F4)} (hj : j ∈ AmalgamNeighbour.Y.nodes) :
    firstNode j ∈ setD ∧ rhoPerm (firstNode j) ∈ setD := by
  have key : ∀ j ∈ AmalgamNeighbour.Y.nodes, ∃ k k' : Fin 4,
      firstNode j = jD k ∧ rhoPerm (firstNode j) = jD k' := by decide
  obtain ⟨k, k', h1, h2⟩ := key j hj
  exact ⟨h1 ▸ d4_jD_mem_setD k, h2 ▸ d4_jD_mem_setD k'⟩

variable {F : Type} [Field F] [Finite F]

variable (F) in
noncomputable abbrev e6IsogenyM : e6Data_valid.minGroup F →* ModGL Tag.E6 F :=
  (adjointGroup TwistTag.E6.tag F).subtype.comp (e6IsogenyT F)

theorem e6IsogenyM_xm_single (a : Fin (Tag.rank .E6)) (c : F) :
    e6IsogenyM F (e6Data_valid.xm F (Pi.single a 1) c) = xUnit Tag.E6 F a c := by
  change ((e6Isogeny F (e6Data_valid.xm F (Pi.single a 1) c) : adjointGroup _ F) :
    ModGL Tag.E6 F) = _
  rw [e6Isogeny_xm_single, eltElement_simpleRoot_E6]
  rfl

theorem e6IsogenyM_xm_neg_single (a : Fin (Tag.rank .E6)) (c : F) :
    e6IsogenyM F (e6Data_valid.xm F (-Pi.single a 1) c) = yUnit Tag.E6 F a c := by
  change ((e6Isogeny F (e6Data_valid.xm F (-Pi.single a 1) c) : adjointGroup _ F) :
    ModGL Tag.E6 F) = _
  rw [e6Isogeny_xm_neg_single, eltElement_neg_simpleRoot_E6]
  rfl

theorem rootGroup_le_comap_d4Levi {a : Fin (Tag.rank .E6)} (ha : a ∈ setD)
    {γ : Fin (Tag.rank .E6) → ℤ} (hγ : γ = Pi.single a 1 ∨ γ = -Pi.single a 1) :
    e6Data_valid.rootGroup F γ ≤ (d4Levi F).comap (e6IsogenyM F) := by
  intro x hx
  obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup F).1 hx
  rcases hγ with rfl | rfl
  · rw [Subgroup.mem_comap, e6IsogenyM_xm_single]
    exact Subgroup.subset_closure ⟨a, ha, c, Or.inl rfl⟩
  · rw [Subgroup.mem_comap, e6IsogenyM_xm_neg_single]
    exact Subgroup.subset_closure ⟨a, ha, c, Or.inr rfl⟩

theorem e6IsogenyM_mem_d4Levi (θ : F →+* F) {x : fixedGroup F θ}
    (hx : x ∈ twLevi F θ AmalgamNeighbour.Y.nodes) :
    e6IsogenyM F (x : e6Data_valid.minGroup F) ∈ d4Levi F := by
  have hle : twLevi F θ AmalgamNeighbour.Y.nodes ≤
      (d4Levi F).comap ((e6IsogenyM F).comp (fixedGroup F θ).subtype) := by
    refine iSup₂_le fun j hj => sup_le ?_ ?_
    · intro g hg
      rw [mem_twistedRootGroup_iff θ (isRoot_single .E6 (firstNode j))
        ((proj_single _).trans (by rw [orbitMap_firstNode])), rho_single] at hg
      exact sup_le (rootGroup_le_comap_d4Levi (firstNode_mem_setD hj).1 (Or.inl rfl))
        (rootGroup_le_comap_d4Levi (firstNode_mem_setD hj).2 (Or.inl rfl)) hg
    · intro g hg
      rw [mem_twistedRootGroup_iff θ (isRoot_neg_single .E6 (firstNode j))
        ((proj_neg_single _).trans (by rw [orbitMap_firstNode])), rho_neg_single] at hg
      exact sup_le (rootGroup_le_comap_d4Levi (firstNode_mem_setD hj).1 (Or.inr rfl))
        (rootGroup_le_comap_d4Levi (firstNode_mem_setD hj).2 (Or.inr rfl)) hg
  exact hle hx

variable (F) in
@[expose] noncomputable def twCoverIsog (θ : F →+* F) :
    twLevi F θ AmalgamNeighbour.Y.nodes →* ↥(d4Levi F ⊓ d4Gamma θ) :=
  (((e6IsogenyM F).comp (fixedGroup F θ).subtype).comp
    (twLevi F θ AmalgamNeighbour.Y.nodes).subtype).codRestrict _
    fun x => ⟨e6IsogenyM_mem_d4Levi θ x.2,
      e6IsogenyT_mem_twistedFixedGroup θ (x : fixedGroup F θ).2⟩

theorem ker_twCoverIsog_le_center (θ : F →+* F) :
    (twCoverIsog F θ).ker ≤ Subgroup.center (twLevi F θ AmalgamNeighbour.Y.nodes) := by
  intro x hx
  have h1 : ((x : fixedGroup F θ) : e6Data_valid.minGroup F) ∈ (e6IsogenyT F).ker := by
    rw [MonoidHom.mem_ker]
    have h := congrArg (fun g : ↥(d4Levi F ⊓ d4Gamma θ) => (g : ModGL Tag.E6 F))
      ((MonoidHom.mem_ker).1 hx)
    exact Subtype.ext h
  have hz := ker_e6IsogenyT_le_center F h1
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro y
  exact Subtype.ext (Subtype.ext (hz _))

end Isogeny

section Images

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup twistedRootGroup proj_single proj_neg_single
  rho_single rho_neg_single rhoPerm orbitMap xFixed xPair xFixed_val xPair_val xFixed_mem xPair_mem
  twistSign_single twistSign_neg_single)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit (rootElt rootElt_eps_sub_eps'
  rootElt_neg_eps_add_eps' rootElt_eps_add_eps' rootElt_neg_eps_sub_eps')

local instance f4PilotGraphTwistedCoverImageNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

theorem orbitMap_jD_rhoPerm_jD :
    orbitMap (jD 0) = 0 ∧ orbitMap (jD 1) = 1 ∧ orbitMap (jD 2) = 2 ∧
      rhoPerm (jD 0) = jD 0 ∧ rhoPerm (jD 1) = jD 1 ∧ rhoPerm (jD 2) = jD 3 := by
  decide

theorem rho_smul_single_jD_two_ne
    {s : ℤ} (hs : s = 1 ∨ s = -1) :
    CFSG.LieType.Steinberg.TwistedE6.rho (s • Pi.single (jD 2) 1) ≠ s • Pi.single (jD 2) 1 := by
  obtain ⟨-, -, -, -, -, r2⟩ := orbitMap_jD_rhoPerm_jD
  have hne : jD 3 ≠ jD 2 := by decide
  intro h
  rcases hs with rfl | rfl
  · rw [one_smul, rho_single, r2] at h
    have := congrFun h (jD 3)
    simp [hne] at this
  · rw [neg_one_smul, rho_neg_single, r2] at h
    have := congrFun h (jD 3)
    simp [hne] at this

variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F}

omit
  [Finite F] [CharP F 2] in
theorem mem_twLevi_Y_of_mem {θ : F →+* F} {j : Fin (Tag.rank .F4)}
    (hj : j ∈ AmalgamNeighbour.Y.nodes) {g : fixedGroup F θ}
    (hg : g ∈ twistedRootGroup F θ (Pi.single j 1) ∨ g ∈ twistedRootGroup F θ (-Pi.single j 1)) :
    g ∈ twLevi F θ AmalgamNeighbour.Y.nodes :=
  CFSG.LieType.CurtisTits.rankOne_le_levi _ hj
    (hg.elim (fun h => Subgroup.mem_sup_left h) (fun h => Subgroup.mem_sup_right h))

omit
  [Finite F] [CharP F 2] in
theorem exists_twLevi_xm_fixed {k : Fin 4} (hk : k = 0 ∨ k = 1) {s : ℤ} (hs : s = 1 ∨ s = -1)
    {c : F} (hc : σ c = c) :
    ∃ x : twLevi F (σ : F →+* F) AmalgamNeighbour.Y.nodes,
      ((x : fixedGroup F (σ : F →+* F)) : e6Data_valid.minGroup F) =
        e6Data_valid.xm F (s • Pi.single (jD k) 1) c := by
  obtain ⟨h0, h1, -, r0, r1, -⟩ := orbitMap_jD_rhoPerm_jD
  have hroot : IsRoot .E6 (s • Pi.single (jD k) 1 : Fin (Tag.rank .E6) → ℤ) := by
    rcases hs with rfl | rfl
    · rw [one_smul]; exact isRoot_single .E6 (jD k)
    · rw [neg_one_smul]; exact isRoot_neg_single .E6 (jD k)
  have hrho : rhoPerm (jD k) = jD k := by rcases hk with rfl | rfl <;> assumption
  have hfix : CFSG.LieType.Steinberg.TwistedE6.rho (s • Pi.single (jD k) 1) =
      s • Pi.single (jD k) 1 := by
    rcases hs with rfl | rfl
    · rw [one_smul, rho_single, hrho]
    · rw [neg_one_smul, rho_neg_single, hrho]
  have hj : orbitMap (jD k) ∈ AmalgamNeighbour.Y.nodes := by
    rcases hk with rfl | rfl
    · rw [h0]; decide
    · rw [h1]; decide
  have hc' : (σ : F →+* F) c = c := hc
  refine ⟨⟨xFixed (σ : F →+* F) hroot hfix c hc', mem_twLevi_Y_of_mem hj ?_⟩,
    xFixed_val (σ : F →+* F) hroot hfix c hc'⟩
  have hm := xFixed_mem (σ : F →+* F) hroot hfix c hc'
  rcases hs with rfl | rfl
  · have hp : CFSG.LieType.Steinberg.TwistedE6.proj (1 • Pi.single (jD k) 1) =
        Pi.single (orbitMap (jD k)) 1 := by rw [one_smul, proj_single]
    exact Or.inl (hp ▸ hm)
  · have hp : CFSG.LieType.Steinberg.TwistedE6.proj ((-1 : ℤ) • Pi.single (jD k) 1) =
        -Pi.single (orbitMap (jD k)) 1 := by rw [neg_one_smul, proj_neg_single]
    exact Or.inr (hp ▸ hm)

omit
  [Finite F] [CharP F 2] in
theorem exists_twLevi_xm_pair (hσσ : ∀ c, σ (σ c) = c) {s : ℤ} (hs : s = 1 ∨ s = -1) (c : F) :
    ∃ x : twLevi F (σ : F →+* F) AmalgamNeighbour.Y.nodes,
      ((x : fixedGroup F (σ : F →+* F)) : e6Data_valid.minGroup F) =
        e6Data_valid.xm F (s • Pi.single (jD 2) 1) c *
          e6Data_valid.xm F (s • Pi.single (jD 3) 1) (σ c) := by
  obtain ⟨-, -, h2, -, -, r2⟩ := orbitMap_jD_rhoPerm_jD
  have hroot : IsRoot .E6 (s • Pi.single (jD 2) 1 : Fin (Tag.rank .E6) → ℤ) := by
    rcases hs with rfl | rfl
    · rw [one_smul]; exact isRoot_single .E6 (jD 2)
    · rw [neg_one_smul]; exact isRoot_neg_single .E6 (jD 2)
  have hne := rho_smul_single_jD_two_ne hs
  have hj : orbitMap (jD 2) ∈ AmalgamNeighbour.Y.nodes := by rw [h2]; decide
  have hσσ' : ∀ c, (σ : F →+* F) ((σ : F →+* F) c) = c := hσσ
  refine ⟨⟨xPair (σ : F →+* F) hσσ' hroot hne c, mem_twLevi_Y_of_mem hj ?_⟩, ?_⟩
  · have hm := xPair_mem (σ : F →+* F) hσσ' hroot hne c
    rcases hs with rfl | rfl
    · have hp : CFSG.LieType.Steinberg.TwistedE6.proj (1 • Pi.single (jD 2) 1) =
          Pi.single (orbitMap (jD 2)) 1 := by rw [one_smul, proj_single]
      exact Or.inl (hp ▸ hm)
    · have hp : CFSG.LieType.Steinberg.TwistedE6.proj ((-1 : ℤ) • Pi.single (jD 2) 1) =
          -Pi.single (orbitMap (jD 2)) 1 := by rw [neg_one_smul, proj_neg_single]
      exact Or.inr (hp ▸ hm)
  · change (xPair (σ : F →+* F) hσσ' hroot hne c : e6Data_valid.minGroup F) = _
    rw [xPair_val]
    rcases hs with rfl | rfl
    · rw [one_smul, one_smul, rho_single, r2, twistSign_single, Int.cast_one, one_mul]
      rfl
    · rw [neg_one_smul, neg_one_smul, rho_neg_single, r2, twistSign_neg_single, Int.cast_one,
        one_mul]
      rfl

end Images

section Phi

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit (rootElt rootElt_eps_sub_eps'
  rootElt_neg_eps_add_eps' rootElt_eps_add_eps' rootElt_neg_eps_sub_eps')

variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F}
  (hσσ : ∀ c, σ (σ c) = c) {ω : F} (hω : σ ω ≠ ω)

theorem d4FixedPsi_twCoverIsog {x : twLevi F (σ : F →+* F) AmalgamNeighbour.Y.nodes}
    {h : d4Levi F}
    (hx : e6IsogenyM F ((x : fixedGroup F (σ : F →+* F)) : e6Data_valid.minGroup F) =
      (h : ModGL Tag.E6 F)) :
    (d4FixedPsi hσσ (twCoverIsog F (σ : F →+* F) x) : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] _) =
      d4Psi F h := by
  rw [coe_d4FixedPsi]
  congr 1
  exact Subtype.ext hx

variable (σ) in
@[expose] noncomputable def twCoverPhi :
    twLevi F (σ : F →+* F) AmalgamNeighbour.Y.nodes →*
      elementaryGroup (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω)) :=
  (d4FixedEquiv hσσ hω).toMonoidHom.comp (twCoverIsog F (σ : F →+* F))

theorem coe_twCoverPhi (x : twLevi F (σ : F →+* F) AmalgamNeighbour.Y.nodes) :
    (twCoverPhi σ hσσ hω x).val =
      (d4DescentEquiv hσσ hω (d4FixedPsi hσσ (twCoverIsog F (σ : F →+* F) x))).val :=
  rfl

theorem eichler_mem_range_twCoverPhi
    {u w : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → descentField σ}
    (hu : quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω) u = 0)
    (hw : polar (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω)) u w = 0)
    {x : twLevi F (σ : F →+* F) AmalgamNeighbour.Y.nodes}
    (hx : (d4FixedPsi hσσ (twCoverIsog F (σ : F →+* F) x) : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] _) =
      eichler (quadPlus 4 F) (d4Iota σ ω u) (d4Iota σ ω w)) :
    eichler (quadMinus 4 (descentField σ) (d4MinusB hσσ ω) (d4MinusC hσσ ω)) u w ∈
      (twCoverPhi σ hσσ hω).range.map
        (elementaryGroup (quadMinus 4 (descentField σ) (d4MinusB hσσ ω)
          (d4MinusC hσσ ω))).subtype :=
  ⟨twCoverPhi σ hσσ hω x, ⟨x, rfl⟩,
    (coe_twCoverPhi hσσ hω x).trans (d4DescentEquiv_eq_eichler hσσ hω hu hw _ hx)⟩

end Phi

end CFSG.SeitzReduction.F4Pilot
