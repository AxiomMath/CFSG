module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerYLeviBasic

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint

local instance e6CentralizerYLeviNeZeroRankF4 : NeZero Tag.F4.rank := ⟨by decide⟩

theorem closure_subgroupOf_eq {G : Type*} [Group G] {H : Subgroup G} {S : Set G} (hS : S ⊆ H) :
    (closure S).subgroupOf H = closure (H.subtype ⁻¹' S) := by
  apply map_injective H.subtype_injective
  have hr : S ∩ Set.range H.subtype = S :=
    Set.inter_eq_left.2 fun x hx => ⟨(⟨x, hS hx⟩ : H), rfl⟩
  rw [subgroupOf_map_subtype, inf_of_le_left ((closure_le _).2 hS), MonoidHom.map_closure,
    Set.image_preimage_eq_inter_range, hr]

section Graph

variable {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def yGamma : Subgroup (ModGL .E6 K) :=
  twistedFixedGroup TwistTag.E6 K (RingHom.id K)

theorem yLeviF4Gens_subset_yGamma : yLeviF4Gens K ⊆ yGamma K := by
  rintro _ ⟨j, -, c, rfl | rfl⟩
  · exact f4OrbitXUnit_mem j c
  · exact f4OrbitYUnit_mem j c

theorem yLeviF4_le_yGamma : yLeviF4 K ≤ yGamma K :=
  (closure_le _).2 yLeviF4Gens_subset_yGamma

variable (K) in
@[expose] noncomputable def yPsi [CharP K 2] : ↥(yGamma K) ≃* ↥(adjointGroup .F4 K) :=
  e6FixedF4Equiv K CharTwo.two_eq_zero

theorem coe_yPsi_f4OrbitXUnit [CharP K 2] (j : Fin Tag.F4.rank) (c : K) :
    (yPsi K ⟨f4OrbitXUnit K j c, f4OrbitXUnit_mem j c⟩ : ModGL .F4 K) = xUnit .F4 K j c :=
  (coe_e6FixedF4Equiv CharTwo.two_eq_zero _).trans
    (e6FixedToF4_f4OrbitXUnit CharTwo.two_eq_zero j c)

theorem coe_yPsi_f4OrbitYUnit [CharP K 2] (j : Fin Tag.F4.rank) (c : K) :
    (yPsi K ⟨f4OrbitYUnit K j c, f4OrbitYUnit_mem j c⟩ : ModGL .F4 K) = yUnit .F4 K j c :=
  (coe_e6FixedF4Equiv CharTwo.two_eq_zero _).trans
    (e6FixedToF4_f4OrbitYUnit CharTwo.two_eq_zero j c)

theorem B3Levi_eq_closure :
    F4Pilot.B3Levi K = closure ((adjointGroup .F4 K).subtype ⁻¹'
      simpleGens .F4 K {j | j ≠ (3 : Fin Tag.F4.rank)}) := by
  have e : F4Pilot.b3LeviRoots = parabolicRoots .F4 {j | j ≠ (3 : Fin Tag.F4.rank)} := by
    ext γ
    simp only [F4Pilot.b3LeviRoots, parabolicRoots, Set.mem_ofPred_eq, ne_eq, not_not,
      forall_eq]
    rfl
  rw [F4Pilot.B3Levi, e, rootSpan_parabolicRoots_eq_closure]
  refine closure_subgroupOf_eq ?_
  rintro _ ⟨j, -, c, rfl | rfl⟩
  · exact xUnit_mem_adjointGroup j c
  · exact yUnit_mem_adjointGroup j c

theorem map_yPsi_yLeviF4 [CharP K 2] :
    ((yLeviF4 K).subgroupOf (yGamma K)).map (yPsi K).toMonoidHom = F4Pilot.B3Levi K := by
  rw [B3Levi_eq_closure, yLeviF4, closure_subgroupOf_eq yLeviF4Gens_subset_yGamma,
    MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨x, ⟨j, hj, c, hx | hx⟩, rfl⟩
    · have hx' : x = ⟨f4OrbitXUnit K j c, f4OrbitXUnit_mem j c⟩ := Subtype.ext hx
      subst hx'
      exact ⟨j, hj, c, Or.inl (coe_yPsi_f4OrbitXUnit j c)⟩
    · have hx' : x = ⟨f4OrbitYUnit K j c, f4OrbitYUnit_mem j c⟩ := Subtype.ext hx
      subst hx'
      exact ⟨j, hj, c, Or.inr (coe_yPsi_f4OrbitYUnit j c)⟩
  · rintro ⟨j, hj, c, hg | hg⟩
    · refine ⟨⟨f4OrbitXUnit K j c, f4OrbitXUnit_mem j c⟩, ⟨j, hj, c, Or.inl rfl⟩, ?_⟩
      exact Subtype.ext ((coe_yPsi_f4OrbitXUnit j c).trans hg.symm)
    · refine ⟨⟨f4OrbitYUnit K j c, f4OrbitYUnit_mem j c⟩, ⟨j, hj, c, Or.inr rfl⟩, ?_⟩
      exact Subtype.ext ((coe_yPsi_f4OrbitYUnit j c).trans hg.symm)

variable (K) in
@[expose] noncomputable def yLeviF4EquivB3Levi [CharP K 2] :
    ↥(yLeviF4 K) ≃* ↥(F4Pilot.B3Levi K) :=
  (subgroupOfEquivOfLe yLeviF4_le_yGamma).symm.trans
    ((((yLeviF4 K).subgroupOf (yGamma K)).equivMapOfInjective (yPsi K).toMonoidHom
      (yPsi K).injective).trans (MulEquiv.subgroupCongr map_yPsi_yLeviF4))

end Graph

section Main

variable {K : Type} [Field K]

variable [CharP K 2]

variable (K) in
@[expose] noncomputable def yLeviEquivYLeviF4 : ↥(yLevi K) ≃* ↥(yLeviF4 K) :=
  (subgroupOfEquivOfLe yLeviGL_le_adjointGroup).trans
    ((MulEquiv.subgroupCongr yLeviGL_eq_map_yLeviF4).trans
      ((yLeviF4 K).equivMapOfInjective _
        (MulAut.conj (e6RepConj K 1 : ModGL .E6 K)).injective).symm)

variable (K) in
@[expose] noncomputable def yLeviEquivB3Levi : ↥(yLevi K) ≃* ↥(F4Pilot.B3Levi K) :=
  (yLeviEquivYLeviF4 K).trans (yLeviF4EquivB3Levi K)

theorem isSimpleGroup_yLevi [Finite K] : IsSimpleGroup (yLevi K) :=
  have := F4Pilot.isSimpleGroup_B3Levi (K := K)
  (yLeviEquivB3Levi K).isSimpleGroup

theorem center_yLevi_eq_bot [Finite K] : center (yLevi K) = ⊥ := by
  rw [← map_center_eq (yLeviEquivB3Levi K).symm, F4Pilot.center_B3Levi_eq_bot, Subgroup.map_bot]

theorem isQuasisimple_open_yLevi [Finite K] : CFSG.Open.IsQuasisimple (yLevi K) := by
  obtain ⟨h1, h2⟩ := F4Pilot.isQuasisimple_open_B3Levi (K := K)
  refine ⟨?_, ?_⟩
  · have e := map_commutator_eq (f := (yLeviEquivB3Levi K).symm.toMonoidHom)
    rw [h1, Subgroup.map_top_of_surjective _ (yLeviEquivB3Levi K).symm.surjective,
      MonoidHom.range_eq_top.2 (yLeviEquivB3Levi K).symm.surjective, ← _root_.commutator_def] at e
    exact e.symm
  · have := h2
    exact (QuotientGroup.congr _ _ (yLeviEquivB3Levi K)
      (map_center_eq (yLeviEquivB3Levi K))).isSimpleGroup

theorem commutator_yLevi_eq [Finite K] : ⁅yLevi K, yLevi K⁆ = yLevi K := by
  rw [← Subgroup.map_subtype_commutator, (isQuasisimple_open_yLevi (K := K)).1,
    ← MonoidHom.range_eq_map, range_subtype]

theorem eq_bot_of_normal_isPGroup_yLevi [Finite K] :
    ∀ N : Subgroup (yLevi K), N.Normal → IsPGroup 2 N → N = ⊥ := by
  intro N hN hp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (yLevi K) := Subtype.finite
  have hs := isSimpleGroup_yLevi (K := K)
  rcases hs.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    have hp' : IsPGroup 2 (yLevi K) := by
      rw [h] at hp
      exact hp.of_equiv Subgroup.topEquiv
    have hnt : Nontrivial (yLevi K) := (isSimpleGroup_yLevi (K := K)).toNontrivial
    have hc := hp'.center_nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot _).1 hc center_yLevi_eq_bot

theorem lieModel_yLevi {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    CFSG.Blueprint.LieModel (yLevi K) .PSp 3 2 f :=
  CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (yLeviEquivB3Levi K).symm
    (F4Pilot.lieModel_B3Levi hK)

end Main

end CFSG.SeitzReduction.E6Pilot
