module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205GVertex
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf30Setup

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.Q3CH
  CFSG.ClassicalInvolution.Balance

section Struct

variable {G : Type} [Group G] [Finite G]

structure VertexW (K K' R R' : Subgroup G) (z t a c : G) : Prop where
  nonabelian : ∃ x y : G, x * y ≠ y * x
  hyp : HypOmegaGen (CoreAssembly.conjClass K)
  twoGroup : IsPGroup 2 (↥K ⧸ classicalInvolutionOddCore ↥K)
  card8 : Nat.card ↥R = 8
  hzK : IsUniqueInvolution K z
  hzK' : IsUniqueInvolution K' z
  mem_K' : K' ∈ CoreAssembly.conjClass K
  ne : K' ≠ K
  hR : IsSylow2In R K
  hR' : IsSylow2In R' K'
  t_mem : t ∈ R ⊔ R'
  tsq : t * t = 1
  zt : z * t = t * z
  mem : c ∈ Subgroup.closure ({z, t, a} : Set G)
  sq : c * c = 1
  ne_one : c ≠ 1
  z_ne : z ≠ c
  z_cent : z ∈ Subgroup.centralizer ({c} : Set G)
  t_cent : t ∈ Subgroup.centralizer ({c} : Set G)
  tqK : c ∈ Balance.Bootstrap.trivialOnQuot K
  tqK' : c ∈ Balance.Bootstrap.trivialOnQuot K'
  R_le : R ≤ Subgroup.centralizer ({c} : Set G)
  R'_le : R' ≤ Subgroup.centralizer ({c} : Set G)
  card_lt : Nat.card ↥(Subgroup.centralizer ({c} : Set G)) < Nat.card G
  gen : Subgroup.closure ({z, t, a} : Set G) = Subgroup.closure ({z, t, c} : Set G)

end Struct

section Lemmas

variable {G : Type} [Group G] [Finite G] {K K' R R' : Subgroup G} {z t a c : G}

theorem VertexW.isElemAbelian_B (hw : VertexW K K' R R' z t a c) :
    IsElemAbelian 2 (Subgroup.closure ({z, t, a} : Set G)) := by
  rw [hw.gen]
  exact isElemAbelian_closure_three hw.hzK.sq hw.tsq hw.sq hw.zt
    (Subgroup.mem_centralizer_singleton_iff.mp hw.z_cent)
    (Subgroup.mem_centralizer_singleton_iff.mp hw.t_cent)

theorem VertexW.typeRHyp (hw : VertexW K K' R R' z t a c) :
    TypeRHyp (CoreAssembly.conjClass K) where
  hyp := hw.hyp
  twoGroup := by
    rintro L ⟨g, rfl⟩
    let e : ↥K ≃* ↥(conjSub g K) :=
      K.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    exact hw.twoGroup.of_equiv (QuotientGroup.congr _ _ e
      (CFSG.ComponentClassification.OddCore.equiv_invariant e))
  sylow := fun L hL P hP => Out.nonempty_equiv_q8'
    (Sec6Gen.isQuatSub_of_mem_RSet hw.hyp (mem_RSet_of_isSylow2In hL hP))
    (by rw [hw.hyp.omega3 L hL K (CoreAssembly.mem_conjClass_self K) P R hP hw.hR, hw.card8])

theorem VertexW.isPGroup_zpowers (hw : VertexW K K' R R' z t a c) :
    IsPGroup 2 ↥(Subgroup.zpowers c) :=
  CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hw.sq

theorem frameKa_mem_omegaAFamW (hw : VertexW K K' R R' z t a c) :
    frameKa K c ∈
      omegaAFam (CoreAssembly.conjClass K) (Subgroup.centralizer ({c} : Set G)) :=
  ⟨tightCore (K ⊓ Subgroup.centralizer ({c} : Set G)),
    ⟨K, CoreAssembly.mem_conjClass_self K, ⟨R, hw.hR, hw.R_le⟩, rfl⟩,
    (tightCore_le _).trans inf_le_right, rfl⟩

theorem frameKa'_mem_omegaAFamW (hw : VertexW K K' R R' z t a c) :
    frameKa K' c ∈
      omegaAFam (CoreAssembly.conjClass K) (Subgroup.centralizer ({c} : Set G)) :=
  ⟨tightCore (K' ⊓ Subgroup.centralizer ({c} : Set G)),
    ⟨K', hw.mem_K', ⟨R', hw.hR', hw.R'_le⟩, rfl⟩,
    (tightCore_le _).trans inf_le_right, rfl⟩

theorem z_mem_frameKaW (hw : VertexW K K' R R' z t a c) :
    (⟨z, hw.z_cent⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈ frameKa K c := by
  have hz1 : z ≠ 1 := hw.hzK.ne_one
  have hle : Subgroup.zpowers z ≤ K ⊓ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.zpowers_le.mpr ⟨hw.hzK.mem, hw.z_cent⟩
  have hz : z ∈ tightCore (K ⊓ Subgroup.centralizer ({c} : Set G)) :=
    le_tightCore_of_isPGroup hle (isPGroup_zpowers_of_mul_self_eq_one hw.hzK.sq hz1)
      (Subgroup.mem_zpowers z)
  exact Subgroup.mem_subgroupOf.mpr hz

theorem z_mem_frameKa'W (hw : VertexW K K' R R' z t a c) :
    (⟨z, hw.z_cent⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈ frameKa K' c := by
  have hz1 : z ≠ 1 := hw.hzK.ne_one
  have hle : Subgroup.zpowers z ≤ K' ⊓ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.zpowers_le.mpr ⟨hw.hzK'.mem, hw.z_cent⟩
  have hz : z ∈ tightCore (K' ⊓ Subgroup.centralizer ({c} : Set G)) :=
    le_tightCore_of_isPGroup hle (isPGroup_zpowers_of_mul_self_eq_one hw.hzK.sq hz1)
      (Subgroup.mem_zpowers z)
  exact Subgroup.mem_subgroupOf.mpr hz

theorem exists_not_comm_of_movedByAllW (hw : VertexW K K' R R' z t a c)
    {L : Subgroup (Balance.OddQuot c)}
    (hmov : MovedByAll (Subgroup.closure ({z, t, a} : Set G)) c L) :
    ∃ y ∈ L, Balance.oddQuotMk c ⟨z, hw.z_cent⟩ * y ≠ y * Balance.oddQuotMk c ⟨z, hw.z_cent⟩ := by
  have hzB : z ∈ Subgroup.closure ({z, t, a} : Set G) := Subgroup.subset_closure (by simp)
  exact hmov _ (Balance.oddQuotMk_mem_modOdd hzB hw.z_cent)
    (Lemma52Proof.oddQuotMk_not_mem_zpowers hw.isElemAbelian_B hw.mem hw.ne_one hzB
      hw.hzK.ne_one hw.z_ne hw.z_cent)

theorem isUniqueInvolution_frameKaW (hw : VertexW K K' R R' z t a c) :
    IsUniqueInvolution (frameKa K c)
      (⟨z, hw.z_cent⟩ : ↥(Subgroup.centralizer ({c} : Set G))) := by
  have hz : z ∈ tightCore (K ⊓ Subgroup.centralizer ({c} : Set G)) :=
    Subgroup.mem_subgroupOf.mp (z_mem_frameKaW hw)
  exact isUniqueInvolution_subgroupOf (isUniqueInvolution_mono hw.hzK
    ((tightCore_le _).trans inf_le_left) hz) ((tightCore_le _).trans inf_le_right)

theorem isUniqueInvolution_frameKa'W (hw : VertexW K K' R R' z t a c) :
    IsUniqueInvolution (frameKa K' c)
      (⟨z, hw.z_cent⟩ : ↥(Subgroup.centralizer ({c} : Set G))) := by
  have hz : z ∈ tightCore (K' ⊓ Subgroup.centralizer ({c} : Set G)) :=
    Subgroup.mem_subgroupOf.mp (z_mem_frameKa'W hw)
  exact isUniqueInvolution_subgroupOf (isUniqueInvolution_mono hw.hzK'
    ((tightCore_le _).trans inf_le_left) hz) ((tightCore_le _).trans inf_le_right)

theorem isUniqueInvolution_map_of_odd_coreW
    {M : Subgroup ↥(Subgroup.centralizer ({c} : Set G))}
    {u : ↥(Subgroup.centralizer ({c} : Set G))} (hu : IsUniqueInvolution M u) :
    IsUniqueInvolution
      (M.map (QuotientGroup.mk' (classicalInvolutionOddCore ↥(Subgroup.centralizer ({c} : Set G)))))
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(Subgroup.centralizer ({c} : Set G))) u) := by
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥(Subgroup.centralizer ({c} : Set G)))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  exact isUniqueInvolution_map_mk_of_odd
    (Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_left)) hu

theorem frameKa_map_mem_aStarW (hw : VertexW K K' R R' z t a c)
    {M₀ : Subgroup ↥(Subgroup.centralizer ({c} : Set G))}
    (hM₀ : M₀ = frameKa K c ∨ M₀ = frameKa K' c) :
    (frameKa K c).map (QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(Subgroup.centralizer ({c} : Set G)))) ∈
      aStar (oddQuotientFamily (omegaAFam (CoreAssembly.conjClass K)
        (Subgroup.centralizer ({c} : Set G))))
        (M₀.map (QuotientGroup.mk' (classicalInvolutionOddCore
          ↥(Subgroup.centralizer ({c} : Set G))))) ∧
    (frameKa K' c).map (QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(Subgroup.centralizer ({c} : Set G)))) ∈
      aStar (oddQuotientFamily (omegaAFam (CoreAssembly.conjClass K)
        (Subgroup.centralizer ({c} : Set G))))
        (M₀.map (QuotientGroup.mk' (classicalInvolutionOddCore
          ↥(Subgroup.centralizer ({c} : Set G))))) := by
  have h1 := isUniqueInvolution_map_of_odd_coreW (isUniqueInvolution_frameKaW hw)
  have h2 := isUniqueInvolution_map_of_odd_coreW (isUniqueInvolution_frameKa'W hw)
  have m1 : (frameKa K c).map (QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(Subgroup.centralizer ({c} : Set G)))) ∈
      oddQuotientFamily (omegaAFam (CoreAssembly.conjClass K)
        (Subgroup.centralizer ({c} : Set G))) := ⟨_, frameKa_mem_omegaAFamW hw, rfl⟩
  have m2 : (frameKa K' c).map (QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(Subgroup.centralizer ({c} : Set G)))) ∈
      oddQuotientFamily (omegaAFam (CoreAssembly.conjClass K)
        (Subgroup.centralizer ({c} : Set G))) := ⟨_, frameKa'_mem_omegaAFamW hw, rfl⟩
  rcases hM₀ with rfl | rfl
  · exact ⟨self_mem_aStar _, mem_aStar_of_twins m2 h1 h2⟩
  · exact ⟨mem_aStar_of_twins m1 h2 h1, self_mem_aStar _⟩

theorem oddQuotMk_t_memW (hw : VertexW K K' R R' z t a c) {T : Subgroup (Balance.OddQuot c)}
    (h₁ : (frameKa K c).map (Balance.oddQuotMk c) ≤ T)
    (h₂ : (frameKa K' c).map (Balance.oddQuotMk c) ≤ T) :
    Balance.oddQuotMk c ⟨t, hw.t_cent⟩ ∈ T := by
  have hR : R.subgroupOf (Subgroup.centralizer ({c} : Set G)) ≤ frameKa K c := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (le_tightCore_of_isPGroup (le_inf hw.hR.1 hw.R_le) hw.hR.2.1
      (Subgroup.mem_subgroupOf.mp hx))
  have hR' : R'.subgroupOf (Subgroup.centralizer ({c} : Set G)) ≤ frameKa K' c := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (le_tightCore_of_isPGroup (le_inf hw.hR'.1 hw.R'_le) hw.hR'.2.1
      (Subgroup.mem_subgroupOf.mp hx))
  have hsup : (R ⊔ R').subgroupOf (Subgroup.centralizer ({c} : Set G)) ≤
      frameKa K c ⊔ frameKa K' c := by
    rw [Subgroup.subgroupOf_sup hw.R_le hw.R'_le]
    exact sup_le_sup hR hR'
  have ht : (⟨t, hw.t_cent⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈
      (R ⊔ R').subgroupOf (Subgroup.centralizer ({c} : Set G)) :=
    Subgroup.mem_subgroupOf.mpr hw.t_mem
  have hmap : (frameKa K c ⊔ frameKa K' c).map (Balance.oddQuotMk c) ≤ T := by
    rw [Subgroup.map_sup]
    exact sup_le h₁ h₂
  exact hmap (Subgroup.mem_map_of_mem _ (hsup ht))

theorem modOdd_B_le_sup_centerW (hw : VertexW K K' R R' z t a c)
    {T : Subgroup (Balance.OddQuot c)}
    (hzT : Balance.oddQuotMk c ⟨z, hw.z_cent⟩ ∈ T)
    (htT : Balance.oddQuotMk c ⟨t, hw.t_cent⟩ ∈ T) :
    Balance.modOdd c (Subgroup.closure ({z, t, a} : Set G)) ≤
      T ⊔ Subgroup.center (Balance.OddQuot c) := by
  have hcC : c ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hcS : Balance.oddQuotMk c ⟨c, hcC⟩ ∈ T ⊔ Subgroup.center (Balance.OddQuot c) := by
    refine Subgroup.mem_sup_right ?_
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨w', rfl⟩ : ∃ w', Balance.oddQuotMk c w' = w :=
      QuotientGroup.mk'_surjective _ w
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp w'.2)
  have hgen : Subgroup.closure ({z, t, a} : Set G) ≤
      ((T ⊔ Subgroup.center (Balance.OddQuot c)).comap (Balance.oddQuotMk c)).map
        (Subgroup.centralizer ({c} : Set G)).subtype := by
    rw [hw.gen]
    refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    rcases hg with h | h | h
    · exact ⟨⟨z, hw.z_cent⟩, Subgroup.mem_comap.mpr (Subgroup.mem_sup_left hzT), h.symm⟩
    · exact ⟨⟨t, hw.t_cent⟩, Subgroup.mem_comap.mpr (Subgroup.mem_sup_left htT), h.symm⟩
    · exact ⟨⟨c, hcC⟩, Subgroup.mem_comap.mpr hcS, (Set.mem_singleton_iff.mp h).symm⟩
  intro x hx
  obtain ⟨k, hk, rfl⟩ := Balance.mem_modOdd_iff.mp hx
  obtain ⟨s, hs, hsk⟩ := hgen hk
  have hsk' : s = k := Subtype.ext hsk
  rw [← hsk']
  exact Subgroup.mem_comap.mp hs

end Lemmas

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
