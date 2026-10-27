module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.TwoBasic
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.TwoInputs
import CFSG.Adapters.LieModelSimple

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Thm3A
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups

section Simple

theorem isSimpleGroup_of_isQuasisimple {X : Type} [Group X] (hq : CFSG.Open.IsQuasisimple X)
    (hZ : Subgroup.center X = ⊥) : IsSimpleGroup X := by
  haveI := hq.2
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup

theorem isQuasisimple_of_valid {c : CompData} (hV : c.Valid) (hne : c ≠ CompData.sl23) :
    CFSG.Open.IsQuasisimple c.G := by
  rcases hV with ⟨t, n, hfund, hadm, rfl⟩ | rfl | rfl
  · exact ModelFacts.isQuasisimple_modelUniv t n 3 1 Nat.prime_three hfund hadm
  · exact absurd rfl hne
  · exact Q3W.isQuasisimple_m11

end Simple

section Shape

@[expose] def LieDatum {Y : Type} [Group Y] (L M : Subgroup Y) : Prop :=
  ∃ (c : CompData) (_ : c.Valid) (_ : c ≠ CompData.sl23) (φ : c.G →* ↥L),
    Function.Surjective φ ∧ φ.ker ≤ Subgroup.center c.G ∧
    ∃ F ∈ c.fund, Nat.card ↥(F.map φ) = 24 ∧ M ≤ (F.map φ).map L.subtype ∧
      Nonempty (↥((F.map φ).map L.subtype) ≃* SL(2, ZMod 3))

@[expose] def E3aDatum {Y : Type} [Group Y] (L M : Subgroup Y) (z : Y) : Prop :=
  ∃ hz : z ∈ omegaGen (lOrbit L M), E3aShape ↥(omegaGen (lOrbit L M)) ∧
    Subgroup.Normal ((M.subgroupOf (omegaGen (lOrbit L M))).subgroupOf
      (Subgroup.centralizer ({⟨z, hz⟩} : Set ↥(omegaGen (lOrbit L M)))))

variable {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)}

theorem genFittingFStar_ne_bot (hF : FStarSimple Y) : genFittingFStar Y ≠ ⊥ := by
  haveI : IsSimpleGroup ↥(genFittingFStar Y) := hF.1
  have : Nontrivial ↥(genFittingFStar Y) := IsSimpleGroup.toNontrivial
  exact (Subgroup.nontrivial_iff_ne_bot _).mp this

theorem eq_genFittingFStar_of_isSimpleGroup (hF : FStarSimple Y) {X : Subgroup Y}
    (hLX : genFittingFStar Y ≤ X) [IsSimpleGroup ↥X] : X = genFittingFStar Y :=
  eq_of_le_of_isSimpleGroup (genFittingFStar_normal Y) (genFittingFStar_ne_bot hF) hLX

theorem lie_case
    (hF : FStarSimple Y) (hΦ : TypeRHyp Φ) {M : Subgroup Y} (hM : M ∈ Φ) {z : Y}
    (hz : IsUniqueInvolution M z) (hzH : z ∈ omegaGen (lOrbit (genFittingFStar Y) M))
    (h : OrbitLie ↥(omegaGen (lOrbit (genFittingFStar Y) M))
      (M.subgroupOf (omegaGen (lOrbit (genFittingFStar Y) M))) ⟨z, hzH⟩) :
    omegaGen (lOrbit (genFittingFStar Y) M) = genFittingFStar Y ∧ Nat.card M = 8 ∧
      LieDatum (genFittingFStar Y) M := by
  set L := genFittingFStar Y with hL
  set H := omegaGen (lOrbit L M) with hH
  haveI : IsSimpleGroup ↥L := hF.1
  have hC := centralizer_eq_bot_of_fStarSimple hF
  have hMne : M ≠ ⊥ := fun h => hz.ne_one (Subgroup.mem_bot.mp (h ▸ hz.mem))
  have hLH : L ≤ H := le_omegaGen_lOrbit (genFittingFStar_normal Y) hC hMne
  have hMH : M ≤ H := le_omegaGen mem_lOrbit_self
  obtain ⟨c, hV, hne, φ, hs, hk, F, hFf, hMF, h24, hcl⟩ := h
  have hq : CFSG.Open.IsQuasisimple ↥H :=
    isQuasisimple_of_centralQuotient (isQuasisimple_of_valid hV hne) φ hs hk
  haveI : IsSimpleGroup ↥H := isSimpleGroup_of_isQuasisimple hq (center_eq_bot_of_le hC hLH)
  have hHL : H = L := eq_genFittingFStar_of_isSimpleGroup hF hLH
  have hMΛ : M ≤ (F.map φ).map H.subtype := by
    have := Subgroup.map_mono (f := H.subtype) hMF
    rwa [Subgroup.map_subgroupOf_eq_of_le hMH] at this
  obtain ⟨eΛ'⟩ := nonempty_sl23_of_classical hcl h24
  let eΛ : ↥((F.map φ).map H.subtype) ≃* SL(2, ZMod 3) :=
    ((F.map φ).equivMapOfInjective H.subtype H.subtype_injective).symm.trans eΛ'
  refine ⟨hHL, card_eq_eight_of_le hΦ hM hMΛ eΛ, ?_⟩
  let e : ↥H ≃* ↥L := MulEquiv.subgroupCongr hHL
  have hmap : (F.map (e.toMonoidHom.comp φ)).map L.subtype = (F.map φ).map H.subtype := by
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  refine ⟨c, hV, hne, e.toMonoidHom.comp φ, e.surjective.comp hs, ?_, F, hFf, ?_, ?_, ?_⟩
  · intro x hx
    apply hk
    have h1 : e (φ x) = e 1 := by rw [map_one]; exact hx
    exact e.injective h1
  · rw [← Subgroup.map_map, Subgroup.card_map_of_injective e.injective, h24]
  · rw [hmap]
    exact hMΛ
  · rw [hmap]
    exact ⟨eΛ⟩

theorem thm6Exit_cases (hF : FStarSimple Y) {X : Subgroup Y} (hLX : genFittingFStar Y ≤ X)
    (h : TL4.Thm6Exit ↥X) :
    (CFSG.Blueprint.LieModel ↥(genFittingFStar Y) .PSL 3 3 1 ∨
        CFSG.Blueprint.LieModel ↥(genFittingFStar Y) .PSU 3 3 1 ∨
        CFSG.Blueprint.NativeSporadic.IsSporadic ↥(genFittingFStar Y) .M12) ∨
      (E3aShape ↥X ∧ IsE3aGroup ↥(genFittingFStar Y)) := by
  haveI : IsSimpleGroup ↥(genFittingFStar Y) := hF.1
  obtain ⟨eF⟩ := nonempty_fStarQuot_equiv (genFittingFStar_normal Y) hF.2
    (centralizer_eq_bot_of_fStarSimple hF) hLX
  rcases h with ⟨p, f, hp, hp2, ⟨hfe, hl2, hidx⟩ | ⟨hl3 | hu3, hidx⟩⟩ | ⟨⟨e⟩, -⟩
  · exact Or.inr ⟨⟨p, f, hp, hp2, Or.inl ⟨hfe, hl2, hidx⟩⟩,
      ⟨p, f, hp, hp2, Or.inl ⟨hfe, hl2.of_mulEquiv eF⟩⟩⟩
  · by_cases h3 : p ^ f = 3
    · obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff Nat.prime_three).mp h3
      exact Or.inl (Or.inl (hl3.of_mulEquiv eF))
    · exact Or.inr ⟨⟨p, f, hp, hp2, Or.inr ⟨Or.inl hl3, h3, hidx⟩⟩,
        ⟨p, f, hp, hp2, Or.inr ⟨Or.inl (hl3.of_mulEquiv eF), h3⟩⟩⟩
  · by_cases h3 : p ^ f = 3
    · obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff Nat.prime_three).mp h3
      exact Or.inl (Or.inr (Or.inl (hu3.of_mulEquiv eF)))
    · exact Or.inr ⟨⟨p, f, hp, hp2, Or.inr ⟨Or.inr hu3, h3, hidx⟩⟩,
        ⟨p, f, hp, hp2, Or.inr ⟨Or.inr (hu3.of_mulEquiv eF), h3⟩⟩⟩
  · exact Or.inl (Or.inr (Or.inr ⟨eF.symm.trans e⟩))

theorem m12_case (hF : FStarSimple Y) {X : Subgroup Y}
    (hLX : genFittingFStar Y ≤ X) (e : ↥X ≃* CFSG.Blueprint.NativeSporadic.Carrier .M12) :
    CFSG.Blueprint.NativeSporadic.IsSporadic ↥(genFittingFStar Y) .M12 := by
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M12) :=
    CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
  haveI : IsSimpleGroup ↥X := e.isSimpleGroup
  exact ⟨(MulEquiv.subgroupCongr (eq_genFittingFStar_of_isSimpleGroup hF hLX)).symm.trans e⟩

theorem twin_case (hF : FStarSimple Y) {X : Subgroup Y} (hLX : genFittingFStar Y ≤ X)
    (h : IsTwinGroup ↥X) : X = genFittingFStar Y ∧ IsTwinGroup ↥(genFittingFStar Y) := by
  haveI : IsSimpleGroup ↥X := by
    rcases h with h | h
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
  have hXL := eq_genFittingFStar_of_isSimpleGroup hF hLX
  refine ⟨hXL, ?_⟩
  rcases h with h | h
  · exact Or.inl (h.of_mulEquiv (MulEquiv.subgroupCongr hXL))
  · exact Or.inr (h.of_mulEquiv (MulEquiv.subgroupCongr hXL))

theorem orbit_shape
    (hF : FStarSimple Y) (hΦ : TypeRHyp Φ) {M : Subgroup Y}
    (hM : M ∈ Φ) {z : Y} (hz : IsUniqueInvolution M z)
    (hzH : z ∈ omegaGen (lOrbit (genFittingFStar Y) M))
    (hI : OrbitIdent ↥(omegaGen (lOrbit (genFittingFStar Y) M))
      (M.subgroupOf (omegaGen (lOrbit (genFittingFStar Y) M))) ⟨z, hzH⟩) :
    (CFSG.Blueprint.LieModel ↥(genFittingFStar Y) .PSL 3 3 1 ∨
        CFSG.Blueprint.LieModel ↥(genFittingFStar Y) .PSU 3 3 1 ∨
        CFSG.Blueprint.NativeSporadic.IsSporadic ↥(genFittingFStar Y) .M12) ∨
      (OrbitLie ↥(omegaGen (lOrbit (genFittingFStar Y) M))
          (M.subgroupOf (omegaGen (lOrbit (genFittingFStar Y) M))) ⟨z, hzH⟩ ∧
        Nat.card M = 8 ∧ LieDatum (genFittingFStar Y) M) ∨
      (IsE3aGroup ↥(genFittingFStar Y) ∧ E3aDatum (genFittingFStar Y) M z) ∨
      (omegaGen (lOrbit (genFittingFStar Y) M) = genFittingFStar Y ∧
        IsTwinGroup ↥(genFittingFStar Y)) := by
  have hMne : M ≠ ⊥ := fun h => hz.ne_one (Subgroup.mem_bot.mp (h ▸ hz.mem))
  haveI : IsSimpleGroup ↥(genFittingFStar Y) := hF.1
  have hLH : genFittingFStar Y ≤ omegaGen (lOrbit (genFittingFStar Y) M) :=
    le_omegaGen_lOrbit (genFittingFStar_normal Y) (centralizer_eq_bot_of_fStarSimple hF) hMne
  rcases hI with hlie | ⟨-, -, h6, hn⟩ | ⟨-, ⟨e⟩, -⟩ | ⟨ht, -⟩
  · obtain ⟨-, h8, hd⟩ := lie_case hF hΦ hM hz hzH hlie
    exact Or.inr (Or.inl ⟨hlie, h8, hd⟩)
  · rcases thm6Exit_cases hF hLH h6 with h | ⟨hsh, he3⟩
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl ⟨he3, hzH, hsh, hn⟩))
  · exact Or.inl (Or.inr (Or.inr (m12_case hF hLH e)))
  · exact Or.inr (Or.inr (Or.inr (twin_case hF hLH ht)))

end Shape

section Pairs

variable {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)}

theorem mem_lOrbit_of_twin (hTO : TwinOddCore) (hTQ : TwinQ8Class) (hΦ : TypeRHyp Φ)
    {L K J : Subgroup Y} (hK : K ∈ Φ) (hJ : J ∈ Φ) (hKL : K ≤ L) (hJL : J ≤ L)
    (ht : IsTwinGroup ↥L) : J ∈ lOrbit L K := by
  have hq : ∀ {M : Subgroup Y}, M ∈ Φ → M ≤ L →
      Nonempty (↥(M.subgroupOf L) ≃* QuaternionGroup 2) := by
    intro M hM hML
    obtain ⟨z, hz⟩ := (hΦ.hyp.omega1 M hM).1
    have hz' := isUniqueInvolution_subgroupOf hz hML
    have hz2 : orderOf (⟨z, hML hz.mem⟩ : ↥L) = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hz'.sq) hz'.ne_one
    exact nonempty_q8_of_oddCore_centralizer_eq_bot (typeRHyp_conjClass_subgroupOf hΦ hM hML)
      (CoreAssembly.mem_conjClass_self _) hz' (hTO ↥L ht _ hz2)
  obtain ⟨x, hx⟩ := hTQ ↥L ht (K.subgroupOf L) (J.subgroupOf L) (hq hK hKL) (hq hJ hJL)
    (typeRHyp_conjClass_subgroupOf hΦ hK hKL).hyp (typeRHyp_conjClass_subgroupOf hΦ hJ hJL).hyp
  refine ⟨x, x.2, ?_⟩
  change conjSub x (K.subgroupOf L) = J.subgroupOf L at hx
  rw [conjSub_subgroupOf] at hx
  have hle : conjSub (x : Y) K ≤ L := by
    have := conjSub_mono (n := (x : Y)) hKL
    rwa [conjSub_eq_self_of_mem x.2] at this
  have h := Subgroup.subgroupOf_inj.mp hx
  rwa [inf_eq_left.mpr hle, inf_eq_left.mpr hJL] at h

end Pairs

section Main

variable {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)}

theorem members_q8 (hOC : SocleOddCore) (hF : FStarSimple Y) (hΦ : TypeRHyp Φ)
    (hs : CFSG.Blueprint.LieModel ↥(genFittingFStar Y) .PSL 3 3 1 ∨
      CFSG.Blueprint.LieModel ↥(genFittingFStar Y) .PSU 3 3 1 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic ↥(genFittingFStar Y) .M12) :
    ∀ M ∈ Φ, Nonempty (↥M ≃* QuaternionGroup 2) := by
  intro M hM
  obtain ⟨z, hz⟩ := (hΦ.hyp.omega1 M hM).1
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  exact nonempty_q8_of_oddCore_centralizer_eq_bot hΦ hM hz
    (hOC Y _ (genFittingFStar_normal Y) (centralizer_eq_bot_of_fStarSimple hF) hs z hz2)

theorem twoOrbit_of_cases (hE3 : E3aOneClass) (hCT : CoincTwin)
    (hOC : SocleOddCore) (hTO : TwinOddCore) (hL3 : L33Q8Class) (hU3 : U33Q8Classes)
    (hM12 : M12Q8Classes) (hTQ : TwinQ8Class) (hO : classicalInvolutionOddCore Y = ⊥)
    (h2 : NoNormalTwo Y) (hF : FStarSimple Y) (hΦ : TypeRHyp Φ) (hgen : omegaGen Φ = ⊤)
    (hid : ∀ M ∈ Φ, ∀ z : Y, IsUniqueInvolution M z →
      ∃ hzH : z ∈ omegaGen (lOrbit (genFittingFStar Y) M),
        OrbitIdent ↥(omegaGen (lOrbit (genFittingFStar Y) M))
          (M.subgroupOf (omegaGen (lOrbit (genFittingFStar Y) M))) ⟨z, hzH⟩)
    {K J : Subgroup Y} (hK : K ∈ Φ) (hJ : J ∈ Φ) (hJK : J ∉ lOrbit (genFittingFStar Y) K)
    (hLE : ∀ M ∈ Φ, ∀ z : Y, IsUniqueInvolution M z →
      ∀ hzH : z ∈ omegaGen (lOrbit (genFittingFStar Y) M),
        OrbitLie ↥(omegaGen (lOrbit (genFittingFStar Y) M))
          (M.subgroupOf (omegaGen (lOrbit (genFittingFStar Y) M))) ⟨z, hzH⟩ →
        ¬ IsE3aGroup ↥(genFittingFStar Y))
    (hLL : ∀ zK zJ : Y, IsUniqueInvolution K zK → IsUniqueInvolution J zJ →
      (∃ hz : zK ∈ omegaGen (lOrbit (genFittingFStar Y) K),
        OrbitLie ↥(omegaGen (lOrbit (genFittingFStar Y) K))
          (K.subgroupOf (omegaGen (lOrbit (genFittingFStar Y) K))) ⟨zK, hz⟩) →
      (∃ hz : zJ ∈ omegaGen (lOrbit (genFittingFStar Y) J),
        OrbitLie ↥(omegaGen (lOrbit (genFittingFStar Y) J))
          (J.subgroupOf (omegaGen (lOrbit (genFittingFStar Y) J))) ⟨zJ, hz⟩) →
      J ∈ lOrbit (genFittingFStar Y) K) :
    TwoOrbitModelS7 Y ∧ Φ = {T : Subgroup Y | Nonempty (↥T ≃* QuaternionGroup 2)} := by
  have hLn : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  have hC := centralizer_eq_bot_of_fStarSimple hF
  have hlo : ∀ {M T : Subgroup Y}, M ∈ Φ → T ∈ lOrbit (genFittingFStar Y) M → T ∈ Φ :=
    fun hM hT => lOrbit_subset hΦ.hyp.conjInvariant hM hT
  have hsoc : (CFSG.Blueprint.LieModel ↥(genFittingFStar Y) .PSL 3 3 1 ∨
      CFSG.Blueprint.LieModel ↥(genFittingFStar Y) .PSU 3 3 1 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic ↥(genFittingFStar Y) .M12) →
      TwoOrbitModelS7 Y ∧ Φ = {T : Subgroup Y | Nonempty (↥T ≃* QuaternionGroup 2)} := by
    intro hs
    have hq8 := members_q8 hOC hF hΦ hs
    have hsub : Φ ⊆ {T : Subgroup Y | Nonempty (↥T ≃* QuaternionGroup 2)} := hq8
    rcases hs with hs | hs | hs
    · exact absurd (hL3 Y _ hLn hC hs K J (hq8 K hK) (hq8 J hJ)) hJK
    · obtain ⟨hidx, hall⟩ := hU3 Y _ hLn hC hs K J (hq8 K hK) (hq8 J hJ) hJK
      refine ⟨Or.inl ⟨_, hLn, hidx, hs, hC⟩, le_antisymm hsub fun T hT => ?_⟩
      rcases hall T hT with h | h
      · exact hlo hK h
      · exact hlo hJ h
    · obtain ⟨hin, hall⟩ := hM12 Y _ hLn hC hs
      have hYL : genFittingFStar Y = ⊤ := by
        rw [eq_top_iff, ← hgen]
        exact iSup₂_le fun M hM => hin M (hq8 M hM)
      refine ⟨Or.inr ?_, le_antisymm hsub fun T hT => ?_⟩
      · obtain ⟨e⟩ := hs
        exact ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hYL.symm)).trans e⟩
      · rcases hall K J (hq8 K hK) (hq8 J hJ) hJK T hT with h | h
        · exact hlo hK h
        · exact hlo hJ h
  obtain ⟨zK, hzK⟩ := (hΦ.hyp.omega1 K hK).1
  obtain ⟨zJ, hzJ⟩ := (hΦ.hyp.omega1 J hJ).1
  obtain ⟨hzKH, hIK⟩ := hid K hK zK hzK
  obtain ⟨hzJH, hIJ⟩ := hid J hJ zJ hzJ
  have hlie : ∀ {M : Subgroup Y}, LieDatum (genFittingFStar Y) M →
      IsLieImage3 ↥(genFittingFStar Y) := by
    rintro M ⟨c, hV, hne, φ, hs, hk, -⟩
    exact ⟨c, hV, hne, φ, hs, hk⟩
  rcases orbit_shape hF hΦ hK hzK hzKH hIK with hs | ⟨hoK, -, hlK⟩ | ⟨heK, hdK⟩ | ⟨hHK, htK⟩
  · exact hsoc hs
  · rcases orbit_shape hF hΦ hJ hzJ hzJH hIJ with hs | ⟨hoJ, -, -⟩ | ⟨heJ, -⟩ | ⟨-, htJ⟩
    · exact hsoc hs
    · exact absurd (hLL zK zJ hzK hzJ ⟨hzKH, hoK⟩ ⟨hzJH, hoJ⟩) hJK
    · exact absurd heJ (hLE K hK zK hzK hzKH hoK)
    · exact absurd (hlie hlK) (hCT _ htJ).1
  · rcases orbit_shape hF hΦ hJ hzJ hzJH hIJ with hs | ⟨hoJ, -, -⟩ | ⟨-, hdJ⟩ | ⟨-, htJ⟩
    · exact hsoc hs
    · exact absurd heK (hLE J hJ zJ hzJ hzJH hoJ)
    · exact absurd (hE3 Y hO h2 hF Φ hΦ K hK J hJ zK zJ hzK hzJ hdK hdJ) hJK
    · exact absurd heK (hCT _ htJ).2
  · rcases orbit_shape hF hΦ hJ hzJ hzJH hIJ with hs | ⟨-, -, hlJ⟩ | ⟨heJ, -⟩ | ⟨hHJ, -⟩
    · exact hsoc hs
    · exact absurd (hlie hlJ) (hCT _ htK).1
    · exact absurd heJ (hCT _ htK).2
    · have hKL : K ≤ genFittingFStar Y := hHK ▸ le_omegaGen mem_lOrbit_self
      have hJL : J ≤ genFittingFStar Y := hHJ ▸ le_omegaGen mem_lOrbit_self
      exact absurd (mem_lOrbit_of_twin hTO hTQ hΦ hK hJ hKL hJL htK) hJK

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident
