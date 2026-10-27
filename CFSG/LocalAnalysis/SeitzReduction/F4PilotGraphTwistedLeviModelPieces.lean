module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinFinalA3
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedLeviComm
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedPerfect
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedRange

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.EvenSmallLie CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.Minuscule
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup twistedRootGroup mem_twistedRootGroup_iff
  proj_single proj_neg_single rho_single rho_neg_single orbitMap_firstNode firstNode rhoPerm)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear)
open CFSG.Quasithin (perfectCore)

local instance f4PilotGraphTwistedLeviModelPiecesNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

local instance f4PilotGraphTwistedLeviModelPiecesNeZeroRankE6 : NeZero Tag.E6.rank :=
  ⟨by decide⟩

section Levi


variable {k : Type} [Field k]

theorem rootGroup_le_e6ScLevi {S : Finset (Fin (Tag.rank .E6))} {a : Fin (Tag.rank .E6)}
    (ha : a ∈ S) {γ : Fin (Tag.rank .E6) → ℤ} (hγ : γ = Pi.single a 1 ∨ γ = -Pi.single a 1) :
    e6Data_valid.rootGroup k γ ≤ e6ScLevi k S := by
  intro g hg
  obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hg
  have hle := CFSG.LieType.CurtisTits.levi_mono (e6Datum k).rootGroup
    (Finset.singleton_subset_iff.2 ha)
  rcases hγ with rfl | rfl
  · exact hle (xm_single_mem_scLevi a c)
  · exact hle (xm_neg_single_mem_scLevi a c)

theorem twLevi_le_comap_e6ScLevi (θ : k →+* k) {J : Finset (Fin (Tag.rank .F4))}
    {S : Finset (Fin (Tag.rank .E6))}
    (hJS : ∀ j ∈ J, firstNode j ∈ S ∧ rhoPerm (firstNode j) ∈ S) :
    twLevi k θ J ≤ (e6ScLevi k S).comap (fixedGroup k θ).subtype := by
  refine iSup₂_le fun j hj => sup_le ?_ ?_
  · intro g hg
    rw [mem_twistedRootGroup_iff θ (isRoot_single .E6 (firstNode j))
      ((proj_single _).trans (by rw [orbitMap_firstNode])), rho_single] at hg
    exact sup_le (rootGroup_le_e6ScLevi (hJS j hj).1 (Or.inl rfl))
      (rootGroup_le_e6ScLevi (hJS j hj).2 (Or.inl rfl)) hg
  · intro g hg
    rw [mem_twistedRootGroup_iff θ (isRoot_neg_single .E6 (firstNode j))
      ((proj_neg_single _).trans (by rw [orbitMap_firstNode])), rho_neg_single] at hg
    exact sup_le (rootGroup_le_e6ScLevi (hJS j hj).1 (Or.inr rfl))
      (rootGroup_le_e6ScLevi (hJS j hj).2 (Or.inr rfl)) hg

theorem coe_mem_e6ScLevi_A3 (θ : k →+* k) {x : fixedGroup k θ} (hx : x ∈ twLevi k θ {1, 2}) :
    (x : e6Data_valid.minGroup k) ∈ e6ScLevi k e6A3Nodes :=
  twLevi_le_comap_e6ScLevi θ (by decide) hx

theorem coe_mem_e6ScLevi_zero_five (θ : k →+* k) {x : fixedGroup k θ} (hx : x ∈ twLevi k θ {3}) :
    (x : e6Data_valid.minGroup k) ∈ e6ScLevi k {0, 5} :=
  twLevi_le_comap_e6ScLevi θ (by decide) hx

theorem e6ScLevi_zero_five_le_map_centralizer [Finite k] [CharP k 2] :
    e6ScLevi k {0, 5} ≤ (centralizer (((sp6Torus3 (⊤ : Subgroup kˣ)).map (sp6ToSL6 (F := k))) :
      Set (Matrix.SpecialLinearGroup (Fin 6) k))).map (graphParamHom k (RingEquiv.refl k)) := by
  refine iSup₂_le fun j hj => ?_
  have hj' : j = 0 ∨ j = 5 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    exact hj
  exact (CFSG.LieType.CurtisTits.rankOne_le_levi _ (Finset.mem_singleton_self j)).trans
    (e6ScLevi_end_le_map_centralizer hj')

end Levi

section Param


variable {f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 f F)

theorem coe_twParamEquiv_eq (g : uGroup6 h) :
    (((twParamEquiv h g : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
      fixedGroup F h.barEquiv.toRingHom) : e6Data_valid.minGroup F) =
        graphParamHom F (RingEquiv.refl F) (gramSUToSL h _ g) :=
  rfl

theorem gramSUToSL_twParamEquiv_symm_mem
    (y : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes)
    (hy : (y : fixedGroup F h.barEquiv.toRingHom) ∈ twLevi F h.barEquiv.toRingHom {1, 2}) :
    gramSUToSL h _ ((twParamEquiv h).symm y) ∈ blockSpecialLinear (K := F) lin6BlockA := by
  have h1 := coe_mem_e6ScLevi_A3 _ hy
  rw [e6ScLevi_A3_eq_map_blockSpecialLinear] at h1
  obtain ⟨b, hb, hby⟩ := h1
  have h3 : graphParamHom F (RingEquiv.refl F) (gramSUToSL h _ ((twParamEquiv h).symm y)) =
      ((y : fixedGroup F h.barEquiv.toRingHom) : e6Data_valid.minGroup F) := by
    rw [← coe_twParamEquiv_eq, MulEquiv.apply_symm_apply]
  have hb' : b = gramSUToSL h _ ((twParamEquiv h).symm y) :=
    graphParamHom_injective _ (hby.trans h3.symm)
  rw [← hb']
  exact hb

theorem coe_twParamEquiv_uEmbed6_torus3 (p : h.fixedFieldˣ × h.fixedFieldˣ) :
    (((twParamEquiv h (uEmbed6 h (sp6Diag _ (sp6ParamT3 _ p))) :
      twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
        fixedGroup F h.barEquiv.toRingHom) : e6Data_valid.minGroup F) =
      graphParamHom F (RingEquiv.refl F) (sp6ToSL6 (sp6Diag F (sp6ParamT3 F
        (((Units.map (h.fixedField.subtype : h.fixedField →* F)).prodMap
          (Units.map (h.fixedField.subtype : h.fixedField →* F))) p)))) := by
  rw [coe_twParamEquiv_eq, gramSUToSL_uEmbed6_sp6Diag, sp6ToSL6_sp6Diag]
  congr 2

theorem commute_twLevi_three_twParam {x : fixedGroup F h.barEquiv.toRingHom}
    (hx : x ∈ twLevi F h.barEquiv.toRingHom {3}) {s : StatedSp 3 h.fixedField}
    (hs : s ∈ sp6Torus3 (⊤ : Subgroup h.fixedFieldˣ)) :
    Commute x ((twParamEquiv h (uEmbed6 h s) :
      twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
        fixedGroup F h.barEquiv.toRingHom) := by
  obtain ⟨p, -, rfl⟩ := hs
  obtain ⟨m, hm, hmx⟩ := e6ScLevi_zero_five_le_map_centralizer
    (coe_mem_e6ScLevi_zero_five _ hx)
  have hT : sp6ToSL6 (sp6Diag F (sp6ParamT3 F
      (((Units.map (h.fixedField.subtype : h.fixedField →* F)).prodMap
        (Units.map (h.fixedField.subtype : h.fixedField →* F))) p))) ∈
      (sp6Torus3 (⊤ : Subgroup Fˣ)).map (sp6ToSL6 (F := F)) :=
    ⟨_, ⟨_, Subgroup.mem_prod.2 ⟨mem_top _, mem_top _⟩, rfl⟩, rfl⟩
  have hc := mem_centralizer_iff.1 hm _ hT
  show x * _ = _ * x
  apply Subtype.ext
  simp only [Subgroup.coe_mul, MonoidHom.comp_apply]
  rw [coe_twParamEquiv_uEmbed6_torus3, ← hmx, ← map_mul, ← map_mul, hc]

end Param

section Perfect


variable {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)

open CFSG.LieType.Steinberg.TwistedE6 (hHat hHatE hPairE hHatE_le_fixedGroup nd nf) in
include hθ in
theorem exists_mem_hHat_three (t : kˣ) :
    ∃ h₀ ∈ hHat k θ (nf 3), (h₀ : e6Data_valid.minGroup k) =
      e6Data_valid.hm k (nd 0) t * e6Data_valid.hm k (nd 5) (Units.map (θ : k →* k) t) :=
  have hmem : e6Data_valid.hm k (nd 0) t * e6Data_valid.hm k (nd 5) (Units.map (θ : k →* k) t) ∈
      hHatE k θ (nf 3) :=
    (⟨t, rfl⟩ : _ ∈ (hPairE θ (nd 0) (nd 5)).range)
  ⟨⟨_, hHatE_le_fixedGroup θ hθ (nf 3) hmem⟩, Subgroup.mem_subgroupOf.2 hmem, rfl⟩

open CFSG.LieType.Steinberg.TwistedE6 (nd) in
include hθ in
theorem commutator_twLevi_three {t : kˣ} (ht : ((t ^ (2 : ℤ) : kˣ) : k) ≠ 1) :
    ⁅twLevi k θ {3}, twLevi k θ {3}⁆ = twLevi k θ {3} := by
  rw [twLevi, CFSG.LieType.CurtisTits.levi_singleton]
  exact commutator_rankOne_pair θ hθ (a := nd 0) (b := nd 5) (by decide) (by decide) rfl
    (by decide) (exists_mem_hHat_three θ hθ) ht

end Perfect

section Pieces


variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {h : UnitaryFieldData 2 f F}
  {ε : h.fixedField ≃+* K}

theorem twParam_block_injective
    {ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G}
    (hk : ΦX.ker ≤ center (twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes)) :
    Function.Injective ((ΦX.comp (twParamEquiv h).toMonoidHom).comp
      ((blockSpecialLinear (K := F) lin6BlockA).comap (gramSUToSL h _)).subtype) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : twParamEquiv h g ∈ center (twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :=
    hk hg
  have h2 : (g : uGroup6 h) ∈ center (uGroup6 h) := by
    rw [← Subgroup.map_center_eq (twParamEquiv h).symm]
    exact ⟨_, h1, (twParamEquiv h).symm_apply_apply _⟩
  have hnq : ¬(6 = 3 ∧ 2 ^ f = 2) := by omega
  have h3 := gramSUToSL_mem_center h (isPrimeFormGram_graphGram6 F) (by norm_num) hnq h2
  have hbot := inf_center_eq_bot_of_le_blockSpecialLinear (F := F) (j := 0) (by decide)
    (le_refl (blockSpecialLinear (K := F) lin6BlockA))
  have h4 : gramSUToSL h _ (g : uGroup6 h) ∈
      blockSpecialLinear (K := F) lin6BlockA ⊓ center _ := ⟨g.2, h3⟩
  rw [hbot, mem_bot] at h4
  apply Subtype.ext
  exact gramSUToSL_injective h _ (h4.trans (map_one _).symm)

variable [Finite G]

theorem pieceCore_one_two_eq_map (hf : 2 ≤ f) {e₁ : L ≃* adjointGroup .F4 K}
    {ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G}
    (hr : ΦX.range = neighbourCore e₁ .X)
    (hk : ΦX.ker ≤ center (twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes))
    (hn : IsLeviNormalizedU h ε e₁ ΦX) :
    pieceCore e₁ {1, 2} = ((blockSpecialLinear (K := F) lin6BlockA).comap
      (gramSUToSL h _)).map (ΦX.comp (twParamEquiv h).toMonoidHom) := by
  classical
  have := finite_gramSU h ((graphGram6 F : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)
  have hF := uPiece_four_le_card h hf
  have hq := uPiece_four_le_pow hf
  obtain ⟨a₀, ha₀, hsq⟩ := uPiece_exists_mem_units h hf
  set Θ := twParamEquiv h with hΘ
  set Ψ : uGroup6 h →* G := ΦX.comp Θ.toMonoidHom with hΨ
  have hrΨ : Ψ.range = neighbourCore e₁ .X := by
    rw [hΨ, MonoidHom.range_comp, MonoidHom.range_eq_top.2 Θ.surjective,
      ← MonoidHom.range_eq_map, hr]
  have hkΨ : Ψ.ker ≤ center (uGroup6 h) := by
    intro x hx
    have h1 : Θ x ∈ center (twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) := hk hx
    rw [← Subgroup.map_center_eq Θ.symm]
    exact ⟨Θ x, h1, Θ.symm_apply_apply x⟩
  have hnΨ : Ψ.comp (uEmbed6 h) = levi6Hom e₁ ε := MonoidHom.ext fun s => hn s
  have h12 : leviTorusG e₁ {1, 2} ⊓ neighbourLeviG e₁ .X =
      ((sp6TorusA (⊤ : Subgroup h.fixedFieldˣ)).map (uEmbed6 h)).map Ψ := by
    rw [← map_levi6Hom_sp6TorusA e₁ ε, ← hnΨ, ← Subgroup.map_map]
  have hnq : ¬(6 = 3 ∧ 2 ^ f = 2) := by omega
  have hjZ : ∀ z ∈ center (uGroup6 h),
      gramSUToSL h _ z ∈ center (SpecialLinearGroup (Fin 6) F) :=
    fun z hz => gramSUToSL_mem_center h (isPrimeFormGram_graphGram6 F) (by norm_num) hnq hz
  have hj := gramSUToSL_injective h ((graphGram6 F : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)
  have hrig := rigid_of_rigid_map _ hj hjZ ((sp6TorusA (⊤ : Subgroup h.fixedFieldˣ)).map
    (uEmbed6 h)) (by rw [uPiece_map_torusA6 h]; exact rigid_lin6 (.inl rfl) ha₀ hsq)
  have hM := pieceCore_eq_map_of_cover' e₁ hrΨ hkΨ (by decide) h12 hrig
  have hC := isPermGram_graphGram6 F
  have hperf := (hC.natCard_and_commutator_range_inf_blockSpecialLinear h (I := lin6BlockA)
    (by decide) (by decide) ⟨fun _ => hq, fun _ => by omega⟩).2
  set j := gramSUToSL h ((graphGram6 F : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) with hjdef
  have hcomap : ∀ B : Subgroup (SpecialLinearGroup (Fin 6) F),
      ⁅j.range ⊓ B, j.range ⊓ B⁆ = j.range ⊓ B →
        ⁅B.comap j, B.comap j⁆ = B.comap j := by
    intro B hB
    apply Subgroup.map_injective hj
    rw [Subgroup.map_commutator, Subgroup.map_comap_eq, hB]
  have hP := uPiece_perfectCore_centralizer_eq_comap _ hj _
    (by rw [uPiece_map_torusA6 h]; exact perfectCore_centralizer_lin6TorusA hF ha₀ hsq)
    (hcomap _ hperf)
  rw [hP] at hM
  exact hM

omit
  [Finite G] in
theorem range_twLeviRestrict_three_le_pieceCore (hf : 2 ≤ f) {e₁ : L ≃* adjointGroup .F4 K}
    {ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G}
    (hr : ΦX.range = neighbourCore e₁ .X) (hn : IsLeviNormalizedU h ε e₁ ΦX) :
    (twLeviRestrict ΦX three_subset_X).range ≤ pieceCore e₁ {3} := by
  obtain ⟨t, -, ht⟩ := exists_barFixed_unit_sq_ne_one h hf
  have hP := commutator_twLevi_three h.barEquiv.toRingHom h.bar_bar ht
  have hperf' := commutator_range_of_commutator_eq hP (twLeviRestrict ΦX three_subset_X)
  refine le_centralizerPerfectCore hperf' ?_
  rintro _ ⟨x, rfl⟩
  set g := twLeviRestrict ΦX three_subset_X x with hg
  have hgE : g ∈ neighbourCore e₁ .X := by
    rw [← hr]
    exact ⟨_, rfl⟩
  have hT : leviTorusG e₁ {3} ⊓ neighbourLeviG e₁ .X ≤ centralizer ({g} : Set G) := by
    rw [← map_levi6Hom_sp6Torus3 e₁ ε]
    rintro _ ⟨s, hs, rfl⟩
    rw [mem_centralizer_singleton_iff, ← hn s, hg, twLeviRestrict_apply, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (commute_twLevi_three_twParam h x.2 hs).eq.symm
  have hC : centralizer (neighbourCore e₁ .X : Set G) ≤ centralizer ({g} : Set G) := by
    intro z hz
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.1 hz g hgE).symm
  have hle : leviTorusG e₁ {3} ≤ centralizer ({g} : Set G) := by
    refine (le_sup_left (b := centralizer (neighbourCore e₁ .X : Set G))).trans ?_
    rw [leviTorusG_sup_centralizer_eq e₁ three_subset_X]
    exact sup_le hT hC
  rw [mem_centralizer_iff]
  intro z hz
  exact mem_centralizer_singleton_iff.1 (hle hz)

end Pieces

section PiecesY


variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {k : Type} [Field k] {θ : k →+* k}

theorem range_twLeviRestrict_le_pieceCore_of_commute {e₂ : L ≃* adjointGroup .F4 K}
    {ε' : K ≃+* K} {ΦY : twLevi k θ AmalgamNeighbour.Y.nodes →* G}
    (hrY : ΦY.range = neighbourCore e₂ .X)
    {ι' : StatedSp 3 K →* twLevi k θ AmalgamNeighbour.Y.nodes} {s₀ : StatedSp 3 K}
    (hnY : ∀ s, ΦY (ι' s) = levi6Hom e₂ ε' (s₀ * s * s₀⁻¹))
    {J : Finset (Fin (Tag.rank .F4))} (hJ : J ⊆ AmalgamNeighbour.Y.nodes)
    {J' : Finset (Fin (Tag.rank .F4))} (hJ' : J' ⊆ AmalgamNeighbour.X.nodes)
    {T : Subgroup (StatedSp 3 K)}
    (hT : T.map (levi6Hom e₂ ε') = leviTorusG e₂ J' ⊓ neighbourLeviG e₂ .X)
    (hcomm : ∀ x : twLevi k θ J, ∀ s ∈ T,
      Commute (⟨x, CFSG.LieType.CurtisTits.levi_mono _ hJ x.2⟩ :
        twLevi k θ AmalgamNeighbour.Y.nodes) (ι' (s₀⁻¹ * s * s₀)))
    (hperf : ⁅twLevi k θ J, twLevi k θ J⁆ = twLevi k θ J) :
    (twLeviRestrict ΦY hJ).range ≤ pieceCore e₂ J' := by
  have hperf' := commutator_range_of_commutator_eq hperf (twLeviRestrict ΦY hJ)
  refine le_centralizerPerfectCore hperf' ?_
  rintro _ ⟨x, rfl⟩
  set g := twLeviRestrict ΦY hJ x with hg
  have hgE : g ∈ neighbourCore e₂ .X := by
    rw [← hrY]
    exact ⟨_, rfl⟩
  have hTc : leviTorusG e₂ J' ⊓ neighbourLeviG e₂ .X ≤ centralizer ({g} : Set G) := by
    rw [← hT]
    rintro _ ⟨s, hs, rfl⟩
    have e1 : levi6Hom e₂ ε' s = ΦY (ι' (s₀⁻¹ * s * s₀)) := by
      rw [hnY]
      congr 1
      group
    rw [mem_centralizer_singleton_iff, e1, hg, twLeviRestrict_apply, ← map_mul, ← map_mul,
      (hcomm x s hs).eq]
  have hC : centralizer (neighbourCore e₂ .X : Set G) ≤ centralizer ({g} : Set G) := by
    intro z hz
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.1 hz g hgE).symm
  have hle : leviTorusG e₂ J' ≤ centralizer ({g} : Set G) := by
    refine (le_sup_left (b := centralizer (neighbourCore e₂ .X : Set G))).trans ?_
    rw [leviTorusG_sup_centralizer_eq e₂ hJ']
    exact sup_le hTc hC
  rw [mem_centralizer_iff]
  intro z hz
  exact mem_centralizer_singleton_iff.1 (hle hz)

end PiecesY

end CFSG.SeitzReduction.F4Pilot
