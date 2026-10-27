module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2RowField
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2FieldModel
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2PairTables
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2SwapChainModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
  CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open CFSG.SeitzReduction.SymplecticPilot (nsTorusSp nsElt complSp spBlock)

section Model

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem centralizerPerfectCore_nsTorusSp_zero_of_four_le (hF : 4 ≤ Nat.card F) :
    centralizerPerfectCore (nsTorusSp F (0 : Fin 3)) = complSp F (0 : Fin 3) := by
  rw [centralizerPerfectCore, SymplecticPilot.nsTorusSp, Subgroup.zpowers_eq_closure,
    Subgroup.centralizer_closure]
  set H := centralizer ({nsElt (K := F) (0 : Fin 3)} : Set (StatedSp 3 F)) with hH
  have hcomm : ⁅H, H⁆ ≤ complSp F (0 : Fin 3) := by
    refine commutator_le.2 fun g hg g' hg' => ?_
    rw [commutatorElement_def]
    exact SymplecticPilot.commutator_mem_complSp_of_commute_nsElt
      (mem_centralizer_singleton_iff.1 hg) (mem_centralizer_singleton_iff.1 hg')
  have hle : complSp F (0 : Fin 3) ≤ H := fun y hy =>
    SymplecticPilot.mem_centralizer_nsElt_of_mem_complSp hy
  have hperf : ⁅complSp F (0 : Fin 3), complSp F (0 : Fin 3)⁆ = complSp F (0 : Fin 3) := by
    rw [← SymplecticPilot.spBlock_compl_singleton]
    exact SymplecticPilot.commutator_spBlock_eq hF _
  apply le_antisymm
  · calc perfectCore H = ⁅perfectCore H, perfectCore H⁆ := (perfectCore_perfect H).symm
      _ ≤ ⁅H, H⁆ := commutator_mono (perfectCore_le H) (perfectCore_le H)
      _ ≤ _ := hcomm
  · exact le_perfectCore_of_perfect hle hperf

theorem card_complSp_zero_of_card_four (hF : Nat.card F = 4) :
    Nat.card (complSp F (0 : Fin 3)) = 979200 := by
  have hN : (({0}ᶜ : Finset (Fin 3))).card = 2 := by decide
  rw [← SymplecticPilot.spBlock_compl_singleton,
    ← Nat.card_congr (SymplecticPilot.spBlockEquiv ({0}ᶜ : Finset (Fin 3))).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hN, hF]
  decide

end Model

section Field


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem statedSpMap_nsElt {F : Type} [Field F] (ι : K →+* F) (k : Fin 3) :
    statedSpMap ι 3 (nsElt (K := K) k) = nsElt (K := F) k :=
  SymplecticPilot.spFieldMap_nsElt ι k

theorem map_statedSpMap_nsTorusSp {F : Type} [Field F] (ι : K →+* F) (k : Fin 3) :
    (nsTorusSp K k).map (statedSpMap ι 3) = nsTorusSp F k := by
  rw [SymplecticPilot.nsTorusSp, SymplecticPilot.nsTorusSp, MonoidHom.map_zpowers,
    statedSpMap_nsElt]

theorem card_centralizerPerfectCore_std_field [Finite K] [CharP K 2] {t : G}
    (hw : F4Work L K t 1) (e : L ≃* adjointGroup .F4 K) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) (hF : TwoKindAt e t X₀ .field) :
    Nat.card (centralizerPerfectCore (subgroupToG e (X₀ ⊔ stdX K))) =
      twoDiagPieceOrder .field := by
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  have hX₀' : Nat.card X₀ = Nat.card K + 1 := by rw [hX₀, hK2]
  obtain ⟨F, _, _, _, hF4, ⟨ψ₀⟩⟩ :=
    nonempty_statedSp_mulEquiv_centralizerPerfectCore_nonsplit_F4_two hw e hXJ hcyc hX₀ hF
  obtain ⟨K₂, _, _, _, σ, hK₂, hσ, -, hk⟩ := exists_quadraticFrobenius_F4 (f := 1) le_rfl
  have hK₂4 : Nat.card K₂ = 4 := by rw [hK₂]; norm_num
  have : Finite (fixSubfield σ) := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  let := Fintype.ofFinite K
  let := Fintype.ofFinite (fixSubfield σ)
  let := Fintype.ofFinite K₂
  let := Fintype.ofFinite F
  have hcF : Fintype.card K₂ = Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK₂4, hF4]
  have hcK : Fintype.card (fixSubfield σ) = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hk, hK2, pow_one]
  set β : fixSubfield σ ≃+* K := FiniteField.ringEquivOfCardEq hcK with hβ
  set ι : K →+* K₂ := (fixSubfield σ).subtype.comp (β.symm : K →+* fixSubfield σ) with hι
  have hfix : ∀ x : K₂, σ x = x ↔ x ∈ Set.range ι := by
    intro x
    rw [apply_eq_iff_mem_range_fixSubfield_subtype]
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨β y, ?_⟩
      simp [hι]
    · rintro ⟨y, rfl⟩
      exact ⟨β.symm y, rfl⟩
  set X : Subgroup G := subgroupToG e X₀ with hXdef
  set M : Subgroup G := centralizerPerfectCore X with hMdef
  have hXL : X ≤ L := map_subtype_le _
  have htN : t ∈ normalizer (M : Set G) :=
    normalizer_le_normalizer_centralizerPerfectCore X
      (centralizer_le_normalizer X (centralizer_le hXL hw.mem_centralizer))
  have ht : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  have hθθ : M.normalizerMonoidHom ⟨t, htN⟩ * M.normalizerMonoidHom ⟨t, htN⟩ = 1 := by
    rw [← map_mul, show (⟨t, htN⟩ : normalizer (M : Set G)) * ⟨t, htN⟩ = 1 from
      Subtype.ext ht, map_one]
  obtain ⟨-, -, hX₀D⟩ := centralizer_nonsplit hXJ hcyc hX₀'
  have hDH : subgroupToG e (C3Levi K) ≤ centralizer (X : Set G) :=
    map_map_symm_le_centralizer e hX₀D
  have hDperf : ⁅subgroupToG e (C3Levi K), subgroupToG e (C3Levi K)⁆ = subgroupToG e (C3Levi K) :=
    isPerfect_iff.mp (isQuasisimple_map_C3Levi e).1
  have hDM : subgroupToG e (C3Levi K) ≤ M := le_perfectCore_of_perfect hDH hDperf
  set ε₀ : StatedSp 3 K →* G := L.subtype.comp (e.symm.toMonoidHom.comp (c3LeviHom K)) with hε₀
  have hε₀r : ε₀.range = subgroupToG e (C3Levi K) := by
    rw [hε₀, MonoidHom.range_comp, MonoidHom.range_comp, range_c3LeviHom]
    rfl
  have hε₀M : ∀ g, ε₀ g ∈ M := fun g => hDM (hε₀r ▸ ⟨g, rfl⟩)
  set ε : StatedSp 3 K →* M := ε₀.codRestrict M hε₀M with hε
  have hεinj : Function.Injective ε := by
    intro g₁ g₂ h
    apply c3LeviHom_injective (K := K)
    apply e.symm.injective
    apply Subtype.ext
    exact congrArg (fun z : M => (z : G)) h
  have hεr : ε.range = perfectCore (MonoidHom.eqLocus
      (M.normalizerMonoidHom ⟨t, htN⟩).toMonoidHom (MonoidHom.id M)) := by
    apply map_injective M.subtype_injective
    rw [CFSG.Quasithin.map_perfectCore, map_eqLocus_normalizerMonoidHom htN,
      perfectCore_centralizerPerfectCore_inf_centralizer_nonsplit_F4 hw e hXJ hcyc hX₀',
      ← hε₀r, MonoidHom.map_range]
    rfl
  set ψ : StatedSp 3 K₂ ≃* M := (statedSpCongr (FiniteField.ringEquivOfCardEq hcF) 3).trans ψ₀
  obtain ⟨ψ', hψ'⟩ := exists_mulEquiv_statedSpMap_eq_of_involution ι hσ hfix ψ hθθ ε hεinj hεr
  have hcomp : (M.subtype.comp ψ'.toMonoidHom).comp (statedSpMap ι 3) = ε₀ := by
    ext g
    change ((ψ' (statedSpMap ι 3 g) : M) : G) = ε₀ g
    rw [hψ' g]
    rfl
  have hYmap : subgroupToG e (stdX K) =
      ((nsTorusSp K₂ (0 : Fin 3)).map ψ'.toMonoidHom).map M.subtype := by
    rw [← map_statedSpMap_nsTorusSp ι, Subgroup.map_map, Subgroup.map_map, hcomp, stdX,
      subgroupToG, Subgroup.map_map, Subgroup.map_map]
    rfl
  have hYM : subgroupToG e (stdX K) ≤ M := by
    rw [hYmap]
    exact map_subtype_le _
  have hYsub : (subgroupToG e (stdX K)).subgroupOf M =
      (nsTorusSp K₂ (0 : Fin 3)).map ψ'.toMonoidHom := by
    rw [hYmap]
    exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  rw [subgroupToG_sup, centralizerPerfectCore_sup_eq_map hYM, hYsub,
    ← map_centralizerPerfectCore ψ',
    centralizerPerfectCore_nsTorusSp_zero_of_four_le (by rw [hK₂4]),
    Subgroup.card_map_of_injective M.subtype_injective,
    Subgroup.card_map_of_injective ψ'.injective, card_complSp_zero_of_card_four hK₂4]
  rfl

end Field

end CFSG.SeitzReduction.F4Pilot
