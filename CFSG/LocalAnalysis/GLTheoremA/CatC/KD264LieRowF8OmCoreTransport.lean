module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8OmCoreAbs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Om

open CFSG.Open CFSG.GroupTheory.WeirSylow CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

local notation "Ω[" Q "]" =>
  ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆

@[expose] def OmCoreSingle (T : Type) [Group T] [Finite T] : Prop :=
  ∀ E : Subgroup T, IsElemAbelian 3 E →
    (∀ E' : Subgroup T, IsElemAbelian 3 E' → CFSG.Open.pRank 3 E' ≤ CFSG.Open.pRank 3 E) →
      ∃ c ∈ E, c ≠ 1 ∧ ∃ L : Subgroup T, L ≤ Subgroup.centralizer ({c} : Set T) ∧
        CFSG.Open.IsSubnormal L (Subgroup.centralizer ({c} : Set T)) ∧
        CFSG.Open.IsQuasisimple ↥L ∧ 3 ∣ Nat.card (↥L ⧸ Subgroup.center ↥L)

theorem centralizer_singleton_map_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (x : G) :
    (Subgroup.centralizer ({x} : Set G)).map (e : G →* H) =
      Subgroup.centralizer ({e x} : Set H) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    have := hz x (Set.mem_singleton _)
    show e x * e z = e z * e x
    rw [← map_mul, ← map_mul, this]
  · intro hy
    rw [Subgroup.mem_centralizer_iff] at hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    have h1 := hy (e x) (Set.mem_singleton _)
    apply e.injective
    simp only [map_mul]
    simpa using h1

theorem omCoreSingle_of_mulEquiv {T T' : Type} [Group T] [Finite T] [Group T'] [Finite T']
    (e : T ≃* T') (h : OmCoreSingle T') : OmCoreSingle T := by
  intro E hE hmax
  have hp : Nat.Prime 3 := Nat.prime_three
  set E' : Subgroup T' := E.map (e : T →* T') with hE'
  have hE'el : IsElemAbelian 3 E' := isElemAbelian_of_map 3 e hE
  have hpE : CFSG.Open.pRank 3 E' = CFSG.Open.pRank 3 E := pRank_map_mulEquiv 3 e E
  have hmax' : ∀ E'' : Subgroup T', IsElemAbelian 3 E'' →
      CFSG.Open.pRank 3 E'' ≤ CFSG.Open.pRank 3 E' := by
    intro E'' hE''
    have h1 := hmax (E''.map (e.symm : T' →* T)) (isElemAbelian_of_map 3 e.symm hE'')
    have h2 := pRank_map_mulEquiv 3 e.symm E''
    rw [hpE]
    omega
  obtain ⟨c', hc'E, hc'1, L', hL'c, hL'sub, hL'q, hL'dvd⟩ := h E' hE'el hmax'
  obtain ⟨x, hx, hxc⟩ := Subgroup.mem_map.1 hc'E
  have hxeq : e.symm c' = x := by rw [← hxc]; exact e.symm_apply_apply x
  refine ⟨x, hx, ?_, L'.map (e.symm : T' →* T), ?_, ?_, ?_, ?_⟩
  · intro h1
    apply hc'1
    rw [← hxc, h1, map_one]
  · rintro _ ⟨y, hy, rfl⟩
    have h1 := hL'c hy
    have h2 : e.symm y ∈ (Subgroup.centralizer ({c'} : Set T')).map (e.symm : T' →* T) :=
      Subgroup.mem_map_of_mem _ h1
    rw [centralizer_singleton_map_mulEquiv e.symm c', hxeq] at h2
    exact h2
  · have := CFSG.SignalizerFunctorTheorem.TransportA.isSubnormal_map e.symm hL'sub
    rw [centralizer_singleton_map_mulEquiv e.symm c', hxeq] at this
    exact this
  · exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (MulEquiv.subgroupMap e.symm L') hL'q
  · rw [← om_card_quotient_center_mulEquiv e.symm L']
    exact hL'dvd

section Derived

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem omCoreSingle_derived (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : Module.finrank (ZMod 2) V = 8) (hnp : ¬ IsPlusType Q) :
    OmCoreSingle ↥(Ω[Q]) := by
  intro E hE hmax
  have hp : Nat.Prime 3 := Nat.prime_three
  set Ê : Subgroup (V ≃ₗ[ZMod 2] V) := E.map (Ω[Q]).subtype with hÊ
  have hÊle : Ê ≤ Ω[Q] := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hÊel : IsElemAbelian 3 Ê := CFSG.SectionRank.isElemAbelian_map hE (Ω[Q]).subtype
  have hcardÊ : Nat.card Ê = Nat.card E :=
    Subgroup.card_map_of_injective (f := (Ω[Q]).subtype) Subtype.val_injective
  have hmaxc : ∀ E' : Subgroup (V ≃ₗ[ZMod 2] V), E' ≤ Ω[Q] → IsElemAbelian 3 E' →
      Nat.card E' ≤ Nat.card Ê := by
    intro E' hE'Ω hE'el
    have hE''el : IsElemAbelian 3 (E'.subgroupOf (Ω[Q])) :=
      om_isElemAbelian_of_map_injective (Ω[Q]).subtype Subtype.val_injective (by
        rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hE'Ω]
        exact hE'el)
    have h1 := hmax _ hE''el
    obtain ⟨k, hk⟩ := om_exists_card_eq_pow hp hE''el
    obtain ⟨k', hk'⟩ := om_exists_card_eq_pow hp hE
    rw [om_pRank_eq_of_card hp hE''el hk, om_pRank_eq_of_card hp hE hk'] at h1
    have : Nat.card E' = Nat.card (E'.subgroupOf (Ω[Q])) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'Ω).toEquiv).symm
    rw [this, hcardÊ, hk, hk']
    exact Nat.pow_le_pow_right (by norm_num) h1
  obtain ⟨c, hcÊ, hc1, L, hL1, hL2, hL3, hL4⟩ :=
    omCoreSingle_abstract hQ hdim hnp hÊle hÊel hmaxc
  have hLΩ : L ≤ Ω[Q] := hL1.trans inf_le_left
  obtain ⟨y, hyE, hyc⟩ := Subgroup.mem_map.1 hcÊ
  have hyc' : (y : V ≃ₗ[ZMod 2] V) = c := hyc
  refine ⟨y, hyE, ?_, L.subgroupOf (Ω[Q]), ?_, ?_, ?_, ?_⟩
  · intro h1
    apply hc1
    rw [← hyc', h1]
    rfl
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    have hxL : (x : V ≃ₗ[ZMod 2] V) ∈ L := Subgroup.mem_subgroupOf.1 hx
    have := (Subgroup.mem_centralizer_iff.1 (hL1 hxL).2) c (Set.mem_singleton _)
    apply Subtype.ext
    show (y : V ≃ₗ[ZMod 2] V) * (x : V ≃ₗ[ZMod 2] V) = (x : V ≃ₗ[ZMod 2] V) * (y : V ≃ₗ[ZMod 2] V)
    rw [hyc']
    exact this
  · have hcent : Subgroup.centralizer ({y} : Set ↥(Ω[Q])) =
        (Ω[Q] ⊓ Subgroup.centralizer ({c} : Set (V ≃ₗ[ZMod 2] V))).subgroupOf (Ω[Q]) := by
      ext x
      simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
        Set.mem_singleton_iff, forall_eq]
      constructor
      · intro h
        refine ⟨x.2, ?_⟩
        rw [← hyc']
        exact congrArg Subtype.val h
      · rintro ⟨-, h⟩
        apply Subtype.ext
        show (y : V ≃ₗ[ZMod 2] V) * (x : V ≃ₗ[ZMod 2] V) = (x : V ≃ₗ[ZMod 2] V) * (y : V ≃ₗ[ZMod 2] V)
        rw [hyc']
        exact h
    rw [hcent]
    exact omIsSubnormal_subgroupOf_of_conj inf_le_left hL1 hL2
  · exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hLΩ).symm hL3
  · have e := Subgroup.subgroupOfEquivOfLe hLΩ
    rw [Nat.card_congr (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).toEquiv]
    exact hL4

end Derived

section Transport

open CFSG.Adapters.RankTwoModelTransports (glCongr statedProjCongr glCongr_statedScalars)

theorem omCoreSingle_minus_two (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    OmCoreSingle (StatedProj (StatedOmega (StatedQuadMinus 4 K b c))) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  let σ : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hK').symm
  have hZ2 : Nat.card (ZMod 2) = 2 := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  have hirr' : ∀ s : ZMod 2, s ^ 2 + σ b * s + σ c ≠ 0 := by
    intro s hs
    apply hirr (σ.symm s)
    apply σ.injective
    rw [map_add, map_add, map_mul, map_pow, RingEquiv.apply_symm_apply, map_zero]
    exact hs
  let e1 : StatedProj (StatedOmega (StatedQuadMinus 4 K b c)) ≃*
      StatedProj (StatedOmega (StatedQuadMinus 4 (ZMod 2) (σ b) (σ c))) :=
    statedProjCongr (glCongr σ)
      (CFSG.ClassicalInvolution.Upgrade.map_statedOmega σ
        (fun v => CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp σ rfl rfl v))
      (glCongr_statedScalars σ)
  let e2 := (omStatedProjEquivOfCardTwo hZ2
    (StatedOmega (StatedQuadMinus 4 (ZMod 2) (σ b) (σ c)))).symm
  let e3 := CFSG.ComponentClassification.RankTwoClassical.statedOmegaEquivCommutator
    (quadMinus 4 (ZMod 2) (σ b) (σ c)) (coe_quadMinus 4 (ZMod 2) (σ b) (σ c))
  refine omCoreSingle_of_mulEquiv ((e1.trans e2).trans e3) ?_
  have hn1 : 1 ≤ 4 := by norm_num
  exact omCoreSingle_derived (Q := quadMinus 4 (ZMod 2) (σ b) (σ c))
    (nondegenerate_polarBilin_quadMinus_of_finite 4 (ZMod 2) hirr')
    (by simpa using finrank_quadMinus_space hn1) (not_isPlusType_quadMinus hn1 hirr')

theorem omCoreSingle_matrixProj {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (hn1 : 1 ≤ 4) (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    OmCoreSingle (matrixProjectiveDerived (coordinateQuadMinus 4 K hn1 b c)) :=
  omCoreSingle_of_mulEquiv
    (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinateMinusWitnessEquiv K hn1 b c
      (MulEquiv.refl _)).symm (omCoreSingle_minus_two K hK b c hirr)

end Transport

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Om

end
