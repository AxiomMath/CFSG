module

public import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.Defs
public import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.SevenLevi
public import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.SevenGroup
public import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.SevenStab

public section

namespace CFSG.AGLEmbedding.TrialityTwo

open QuadraticMap Module CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin
open CFSG.ClassicalGroups.Orthogonal CFSG.AGLEmbedding.TrialityTwo.Seven

variable {K : Type} [Field K]

namespace Seven

noncomputable abbrev lin (h : StatedOmega (StatedQuadPlus 4 K)) :
    (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K) :=
  toLinEquiv (Fin 4 ⊕ Fin 4) K h.val

theorem lin_mem_commutator (h : StatedOmega (StatedQuadPlus 4 K)) :
    lin h ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K),
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K)⁆ :=
  (statedOmega_eq_comap (coe_quadPlus 4 K)).le h.2

theorem commutator_le_orthogonalGroup :
    ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K),
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K)⁆ ≤
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) :=
  Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem lin_mem_orthogonalGroup (h : StatedOmega (StatedQuadPlus 4 K)) :
    lin h ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) :=
  commutator_le_orthogonalGroup (lin_mem_commutator h)

noncomputable abbrev endo (h : StatedOmega (StatedQuadPlus 4 K)) :
    Module.End K (Fin 4 ⊕ Fin 4 → K) :=
  (lin h : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K))

theorem endo_isometry (h : StatedOmega (StatedQuadPlus 4 K)) (v : Fin 4 ⊕ Fin 4 → K) :
    quadPlus 4 K (endo h v) = quadPlus 4 K v :=
  map_of_mem (lin_mem_orthogonalGroup h) v

theorem endo_pow_eq_one {g : StatedOmega (StatedQuadPlus 4 K)} (hg : orderOf g = 7) :
    endo g ^ 7 = 1 := by
  have hg7 : g ^ 7 = 1 := hg ▸ pow_orderOf_eq_one g
  have hl : lin g ^ 7 = 1 := by
    rw [← map_pow, ← Subgroup.coe_pow, hg7, Subgroup.coe_one, map_one]
  refine LinearMap.ext fun v => ?_
  rw [Module.End.pow_apply, Module.End.one_apply]
  change (⇑(lin g))^[7] v = v
  rw [← LinearEquiv.coe_pow, hl, LinearEquiv.coe_one, id]

theorem endo_ne_one {g : StatedOmega (StatedQuadPlus 4 K)} (hg : orderOf g = 7) : endo g ≠ 1 := by
  intro h
  have hl : lin g = 1 := LinearEquiv.ext fun v => by
    have := LinearMap.congr_fun h v
    simpa using this
  have hg1 : g = 1 := Subtype.ext ((toLinEquiv (Fin 4 ⊕ Fin 4) K).injective (by
    rw [Subgroup.coe_one, map_one]; exact hl))
  rw [hg1, orderOf_one] at hg
  exact absurd hg (by norm_num)

theorem finrank_eight : finrank K (Fin 4 ⊕ Fin 4 → K) = 8 := by
  rw [finrank_split]

theorem exists_solid :
    ∃ T : Submodule K (Fin 4 ⊕ Fin 4 → K), finrank K T = 4 ∧ ∀ x ∈ T, quadPlus 4 K x = 0 :=
  ⟨flag 4 K 4, finrank_flag le_rfl, fun _ hx => quadPlus_eq_zero_of_mem_flag hx⟩

theorem fixedObjects_eq (g : StatedOmega (StatedQuadPlus 4 K)) :
    fixedObjects g = fixedSet (quadPlus 4 K) (endo g) := by
  ext W
  simp only [fixedObjects, fixedSet, Set.mem_ofPred_eq, IsSingularPoint, singularSubspaces,
    statedDerivedSubspaceAction_apply, ← coe_quadPlus 4 K]

theorem mem_stab_iff (hK : Nat.card K = 2) {g : StatedOmega (StatedQuadPlus 4 K)}
    (hg : orderOf g = 7) (F : Frame (quadPlus 4 K) (endo g))
    (h : StatedOmega (StatedQuadPlus 4 K)) :
    h ∈ fixedObjectsStabilizer g ↔ lin h ∈ levStab (quadPlus 4 K) (endo g) F := by
  have hiff := forall_map_eq_iff hK (endo_pow_eq_one hg) (endo_ne_one hg) (endo_isometry g)
    (nondegenerate_polarBilin_quadPlus 4 K) finrank_eight F (lin h)
  rw [mem_levStab, ← hiff, ← fixedObjects_eq]
  simp only [fixedObjectsStabilizer, Subgroup.mem_iInf, mem_statedDerivedSubspaceStabilizer]
  exact ⟨fun hW => ⟨lin_mem_orthogonalGroup h, fun W hW' => hW W hW'⟩,
    fun hW W hW' => hW.2 W hW'⟩

section Iso

variable (hK : Nat.card K = 2) {g : StatedOmega (StatedQuadPlus 4 K)}
  (hg : orderOf g = 7) (F : Frame (quadPlus 4 K) (endo g))

@[expose] noncomputable def stabToLev :
    fixedObjectsStabilizer g →* levStab (quadPlus 4 K) (endo g) F where
  toFun h := ⟨lin h.1, (mem_stab_iff hK hg F h.1).1 h.2⟩
  map_one' := Subtype.ext (by
    change toLinEquiv (Fin 4 ⊕ Fin 4) K ((1 : StatedOmega (StatedQuadPlus 4 K)) : GL _ K) = 1
    rw [Subgroup.coe_one, map_one])
  map_mul' a b := Subtype.ext (by
    change toLinEquiv (Fin 4 ⊕ Fin 4) K ((a.1 * b.1 : StatedOmega (StatedQuadPlus 4 K)) : GL _ K) =
      toLinEquiv (Fin 4 ⊕ Fin 4) K (a.1 : GL _ K) * toLinEquiv (Fin 4 ⊕ Fin 4) K (b.1 : GL _ K)
    rw [Subgroup.coe_mul, map_mul])

theorem stabToLev_injective : Function.Injective (stabToLev hK hg F) := by
  intro a b hab
  have h := congrArg Subtype.val hab
  exact Subtype.ext (Subtype.ext ((toLinEquiv (Fin 4 ⊕ Fin 4) K).injective h))

@[expose] noncomputable def stabHom : fixedObjectsStabilizer g →* GL (Fin 3) K :=
  (restrictGL (V := Fin 4 ⊕ Fin 4 → K) (Q := quadPlus 4 K) (t := endo g) finrank_split
    (endo_pow_eq_one hg) (two_eq_zero_of_card hK) (endo_isometry g) F).comp (stabToLev hK hg F)

include hK in
theorem leviConj_mem_commutator (A : GL (Fin 3) K) :
    leviConj F A ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K),
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K)⁆ := by
  have : Group.IsPerfect (GL (Fin 3) K) := isPerfect_of_isLThreeTwo (isLThreeTwo_GL_of_card hK)
  have : Group.IsPerfect (leviConj F).range := Group.IsPerfect.range _
  have hRO : (leviConj F).range ≤ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) := by
    rintro _ ⟨B, rfl⟩
    exact leviConj_mem F B
  have hmem : leviConj F A ∈ (leviConj F).range := ⟨A, rfl⟩
  rw [← Subgroup.commutator_eq_self (H := (leviConj F).range)] at hmem
  exact Subgroup.commutator_mono hRO hRO hmem

theorem stabHom_bijective : Function.Bijective (stabHom hK hg F) := by
  have h7 := endo_pow_eq_one hg
  have h2 := two_eq_zero_of_card hK
  have hQt := endo_isometry g
  refine ⟨(restrictGL_injective finrank_split h7 h2 hQt F).comp (stabToLev_injective hK hg F),
    fun A => ?_⟩
  set M : GL (Fin 4 ⊕ Fin 4) K := (toLinEquiv (Fin 4 ⊕ Fin 4) K).symm (leviConj F A) with hM
  have hMlin : toLinEquiv (Fin 4 ⊕ Fin 4) K M = leviConj F A := by
    rw [hM, MulEquiv.apply_symm_apply]
  have hMΩ : M ∈ StatedOmega (StatedQuadPlus 4 K) := by
    rw [statedOmega_eq_comap (coe_quadPlus 4 K), Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
      hMlin]
    exact leviConj_mem_commutator hK F A
  have hMH : (⟨M, hMΩ⟩ : StatedOmega (StatedQuadPlus 4 K)) ∈ fixedObjectsStabilizer g := by
    rw [mem_stab_iff hK hg F]
    change toLinEquiv (Fin 4 ⊕ Fin 4) K M ∈ _
    rw [hMlin]
    exact leviConj_mem_levStab F h7 h2 hQt A
  refine ⟨⟨⟨M, hMΩ⟩, hMH⟩, ?_⟩
  have hs : stabToLev hK hg F ⟨⟨M, hMΩ⟩, hMH⟩ =
      ⟨leviConj F A, leviConj_mem_levStab F h7 h2 hQt A⟩ :=
    Subtype.ext hMlin
  change restrictGL finrank_split h7 h2 hQt F (stabToLev hK hg F ⟨⟨M, hMΩ⟩, hMH⟩) = A
  rw [hs]
  exact restrictGL_leviConj F h7 h2 hQt A

@[expose] noncomputable def stabEquiv : fixedObjectsStabilizer g ≃* GL (Fin 3) K :=
  MulEquiv.ofBijective (stabHom hK hg F) (stabHom_bijective hK hg F)

end Iso

end Seven

open Seven

theorem sevenFixedRigid_holds : SevenFixedRigid := by
  intro K _ _ hK g hg
  obtain ⟨F⟩ := exists_frame hK (endo_pow_eq_one hg) (endo_ne_one hg) (endo_isometry g)
    (nondegenerate_polarBilin_quadPlus 4 K) finrank_eight exists_solid
  set e := stabEquiv hK hg F
  have hL : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsLThreeTwo
      (fixedObjectsStabilizer g) := by
    obtain ⟨d, hd, ⟨f⟩⟩ := isLThreeTwo_GL_of_card hK
    exact ⟨d, hd, ⟨e.trans f⟩⟩
  have hg7 : g ^ 7 = 1 := hg ▸ pow_orderOf_eq_one g
  refine ⟨fun hbot => ?_, ?_, fun β hβ h3 => ?_⟩
  · have h := self_mem_fixedObjectsStabilizer g
    rw [hbot, Subgroup.mem_bot] at h
    rw [h, orderOf_one] at hg
    exact absurd hg (by norm_num)
  · have := isPerfect_of_isLThreeTwo hL
    exact Subgroup.commutator_eq_self
  · refine eq_one_of_mulAut hL (fun z hz => ?_) (Subtype.ext (by
      rw [Subgroup.coe_pow]; exact hg7)) (fun h1 => ?_) β hβ h3
    · have hez : (e z) ^ 21 = 1 := by rw [← map_pow, hz, map_one]
      rcases pow_seven_or_pow_three_of_GL hK (e z) hez with h | h
      · exact .inl (e.injective (by rw [map_pow, h, map_one]))
      · exact .inr (e.injective (by rw [map_pow, h, map_one]))
    · have h1' : g = 1 := congrArg Subtype.val h1
      rw [h1', orderOf_one] at hg
      exact absurd hg (by norm_num)

end CFSG.AGLEmbedding.TrialityTwo
