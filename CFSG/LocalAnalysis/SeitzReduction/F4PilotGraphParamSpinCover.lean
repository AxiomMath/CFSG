module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphParamSpin
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusCentrallyClosed
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphPiecesLift

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Spin (cartanD isFiniteType_cartanD quadPlus)
open CFSG.LieType.RootSystem (roots)
open scoped commutatorElement

section Transport

variable {F K : Type} [Field F] [Field K] {G : Type} [Group G]

@[expose] noncomputable def spinTransportPar (ε : F ≃+* K) (Φ : spinGroup (quadPlus 4 F) →* G)
    (γ : Fin 4 → ℤ) (c : K) : G :=
  Φ (SpinPlus.x 4 F three_le_rank_D4 γ (ε.symm c))

theorem spinTransportPar_add (ε : F ≃+* K) (Φ : spinGroup (quadPlus 4 F) →* G) {γ : Fin 4 → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanD 4) ∅) (c d : K) :
    spinTransportPar ε Φ γ (c + d) = spinTransportPar ε Φ γ c * spinTransportPar ε Φ γ d := by
  rw [spinTransportPar, spinTransportPar, spinTransportPar, map_add,
    (SpinPlus.isParametrization (K := F) three_le_rank_D4 γ hγ).2.1, map_mul]

theorem commutatorFormula_spinTransportPar (ε : F ≃+* K) (Φ : spinGroup (quadPlus 4 F) →* G)
    (O : CommOrder (SpinPlus.Φ 4 K three_le_rank_D4)) :
    CommutatorFormula (spinTransportPar ε Φ) O SpinPlus.commC := by
  intro α hα β hβ hαβ c d
  obtain ⟨OF⟩ := nonempty_commOrder_ofCartan
    (CFSG.LieType.Universal.Spin.plusDatum 4 F three_le_rank_D4).isFiniteType
    (Dv := (CFSG.LieType.Universal.Spin.plusDatum 4 F three_le_rank_D4).divisible) rfl
  have hαF : α ∈ (SpinPlus.Φ 4 F three_le_rank_D4).roots := hα
  have hβF : β ∈ (SpinPlus.Φ 4 F three_le_rank_D4).roots := hβ
  have hF := SpinPlus.commutatorFormula three_le_rank_D4 OF α hαF β hβF hαβ (ε.symm c)
    (ε.symm d)
  have hcomm : ⁅spinTransportPar ε Φ α c, spinTransportPar ε Φ β d⁆ =
      Φ ⁅SpinPlus.x 4 F three_le_rank_D4 α (ε.symm c),
        SpinPlus.x 4 F three_le_rank_D4 β (ε.symm d)⁆ := (map_commutatorElement Φ _ _).symm
  by_cases hr : α + β ∈ (SpinPlus.Φ 4 K three_le_rank_D4).roots
  · have hrF : α + β ∈ (SpinPlus.Φ 4 F three_le_rank_D4).roots := hr
    rw [(SpinPlus.commOrder_list_eq three_le_rank_D4 OF hαF hβF hαβ).1 hrF, List.map_singleton,
      List.prod_singleton, one_smul, one_smul, pow_one, pow_one] at hF
    rw [(SpinPlus.commOrder_list_eq three_le_rank_D4 O hα hβ hαβ).1 hr, List.map_singleton,
      List.prod_singleton, one_smul, one_smul, pow_one, pow_one, hcomm, hF, spinTransportPar,
      map_mul, map_mul, map_intCast]
  · have hrF : α + β ∉ (SpinPlus.Φ 4 F three_le_rank_D4).roots := hr
    rw [(SpinPlus.commOrder_list_eq three_le_rank_D4 OF hαF hβF hαβ).2 hrF, List.map_nil,
      List.prod_nil] at hF
    rw [(SpinPlus.commOrder_list_eq three_le_rank_D4 O hα hβ hαβ).2 hr, List.map_nil,
      List.prod_nil, hcomm, hF, map_one]

variable
  [Finite K] [CharP K 2]

@[expose] noncomputable def spinTransport (ε : F ≃+* K) (Φ : spinGroup (quadPlus 4 F) →* G) :
    spinGroup (quadPlus 4 K) →* G :=
  liftOfPresentationB (SpinPlus.presentationB three_le_rank_D4) (d4Order K)
    (SpinPlus.commutatorFormula three_le_rank_D4 (d4Order K))
    (fun _ hγ c d => spinTransportPar_add ε Φ hγ c d)
    (commutatorFormula_spinTransportPar ε Φ (d4Order K))

omit [CharP K 2] in
theorem spinTransport_x (ε : F ≃+* K) (Φ : spinGroup (quadPlus 4 F) →* G) {γ : Fin 4 → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanD 4) ∅) (c : K) :
    spinTransport ε Φ (SpinPlus.x 4 K three_le_rank_D4 γ c) =
      Φ (SpinPlus.x 4 F three_le_rank_D4 γ (ε.symm c)) :=
  liftOfPresentationB_apply _ _ _ _ _ hγ c

omit [CharP K 2] in
theorem range_spinTransport (ε : F ≃+* K) (Φ : spinGroup (quadPlus 4 F) →* G) :
    (spinTransport ε Φ).range = Φ.range := by
  apply le_antisymm
  · rw [MonoidHom.range_eq_map, ← closure_spinX_four_eq_top, MonoidHom.map_closure,
      closure_le]
    rintro _ ⟨_, ⟨γ, hγ, c, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, spinTransport_x ε Φ hγ c]
    exact ⟨_, rfl⟩
  · rw [MonoidHom.range_eq_map, ← closure_spinX_four_eq_top, MonoidHom.map_closure,
      closure_le]
    rintro _ ⟨_, ⟨γ, hγ, c, rfl⟩, rfl⟩
    refine ⟨SpinPlus.x 4 K three_le_rank_D4 γ (ε c), ?_⟩
    rw [spinTransport_x ε Φ hγ, RingEquiv.symm_apply_apply]

theorem spinTransport_injective (ε : F ≃+* K) {Φ : spinGroup (quadPlus 4 F) →* G}
    (hΦ : Function.Injective Φ) : Function.Injective (spinTransport ε Φ) := by
  have hr : (Pi.single 0 1 : Fin 4 → ℤ) ∈ roots (isFiniteType_cartanD 4) ∅ :=
    (SpinPlus.Φ 4 K three_le_rank_D4).single_mem 0
  set x0 : F → spinGroup (quadPlus 4 F) := SpinPlus.x 4 F three_le_rank_D4 (Pi.single 0 1)
    with hx0
  have hadd := (SpinPlus.isParametrization (K := F) three_le_rank_D4 _ hr).2.1
  have h0 : x0 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    calc x0 0 = (x0 0)⁻¹ * (x0 0 * x0 0) := by group
      _ = (x0 0)⁻¹ * x0 0 := by rw [← h]
      _ = 1 := inv_mul_cancel _
  have hne : ∃ g, spinTransport ε Φ g ≠ 1 := by
    refine ⟨SpinPlus.x 4 K three_le_rank_D4 (Pi.single 0 1) 1, fun h => ?_⟩
    rw [spinTransport_x ε Φ hr, map_one ε.symm] at h
    have h1 : x0 1 = x0 0 := by
      rw [h0]
      exact hΦ (h.trans (map_one Φ).symm)
    exact one_ne_zero ((SpinPlus.isParametrization (K := F) three_le_rank_D4 _ hr).2.2 h1)
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← center_spinGroup_quadPlus_four_eq_bot]
  exact CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
    (CFSG.LieType.Universal.Spin.isQuasisimple_spinGroup_quadPlus three_le_rank_D4) hne

end Transport

theorem statedClassicalModel_of_lieModel_POmegaPlus {S : Type} [Group S] {n p f : ℕ}
    (h : LieModel S .POmegaPlus n p f) : StatedClassicalModel S .POmegaPlus n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

section Cover

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_spin8_cover_neighbourCore {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .F4 K) {N : AmalgamNeighbour} (hN : N ≠ .X')
    (h : HR8Kind e t f N .omegaPlus8) :
    ∃ ΦY : spinGroup (quadPlus 4 K) →* G, ΦY.range = neighbourCore e N ∧
      Function.Injective ΦY := by
  obtain ⟨S, _, hS, ρ, hρ, hker⟩ :=
    exists_surjective_neighbourCore_of_hr8Kind_graph hw hf e hN (by decide) (by decide) h
  obtain ⟨-, F, _, _, hF, ⟨εS⟩⟩ := statedClassicalModel_of_lieModel_POmegaPlus hS
  have : CharP F 2 := charP_two_of_natCard_eq_two_pow hF
  have hF4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  set η : S ≃* spinGroup (quadPlus 4 F) :=
    (εS.trans (CFSG.LieType.Universal.Spin.spinQuotientCenterEquivQuadPlus
      three_le_rank_D4).symm).trans
      ((QuotientGroup.quotientMulEquivOfEq center_spinGroup_quadPlus_four_eq_bot).trans
        QuotientGroup.quotientBot) with hη
  set π : neighbourCore e N →* spinGroup (quadPlus 4 F) := η.toMonoidHom.comp ρ with hπ
  have hπs : Function.Surjective π := η.surjective.comp hρ
  have hπker : π.ker ≤ center (neighbourCore e N) := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact η.map_eq_one_iff.mp hx
  have hperf : Group.IsPerfect (neighbourCore e N) :=
    isPerfect_iff.mpr (commutator_centralizerPerfectCore _)
  obtain ⟨σ, hσ⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed.spinPlus_exists_section_of_central
      three_le_rank_D4 hF4 hπs hπker
  have hπinj : Function.Injective π := injective_of_section_of_perfect π hπker σ hσ
  set Φ₀ : spinGroup (quadPlus 4 F) →* G :=
    (neighbourCore e N).subtype.comp (MulEquiv.ofBijective π ⟨hπinj, hπs⟩).symm.toMonoidHom
    with hΦ₀
  have hΦ₀r : Φ₀.range = neighbourCore e N := by
    rw [hΦ₀, MonoidHom.range_comp,
      MonoidHom.range_eq_top.2 (MulEquiv.ofBijective π ⟨hπinj, hπs⟩).symm.surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  have hΦ₀i : Function.Injective Φ₀ :=
    (neighbourCore e N).subtype_injective.comp (MulEquiv.ofBijective π ⟨hπinj, hπs⟩).symm.injective
  have : Fintype F := Fintype.ofFinite F
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card F = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, hw.card_eq]
  set ε : F ≃+* K := FiniteField.ringEquivOfCardEq hc
  exact ⟨spinTransport ε Φ₀, (range_spinTransport ε Φ₀).trans hΦ₀r,
    spinTransport_injective ε hΦ₀i⟩

end Cover

end CFSG.SeitzReduction.F4Pilot
