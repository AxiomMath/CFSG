module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphParamSpinRoots
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphParamSLGraph
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusCenter

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Universal.Spin (cartanD isFiniteType_cartanD quadPlus)
open CFSG.LieType.RootSystem (roots)
open CFSG.LieType.Steinberg.TwistedE6 (sigma)
open scoped commutatorElement

theorem three_le_rank_D4 : 3 ≤ 4 := by norm_num

local instance f4PilotGraphParamSpinNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

theorem d4Embed_add_ne_zero {α β : Fin 4 → ℤ} (h : α + β ≠ 0) : d4Embed α + d4Embed β ≠ 0 := by
  rw [← d4Embed_add, ← d4Embed_zero]
  exact fun h' => h (d4Embed_injective h')

theorem commC_cast_eq_one_D4 {K : Type} [Field K] [CharP K 2] (α β : Fin 4 → ℤ) (p : ℕ × ℕ) :
    ((SpinPlus.commC α β p : ℤ) : K) = 1 :=
  intCast_eq_one_of_sign_charTwo (Int.natAbs_eq_iff.1 (SpinPlus.commC_natAbs α β p) |>.imp
    (by simp) (by simp))

theorem exists_d4Node_eq : ∀ j ∈ e6D4Nodes, ∃ k : Fin 4, d4Node k = j := by
  decide

theorem d4Node_mem : ∀ k : Fin 4, d4Node k ∈ e6D4Nodes := by
  decide

theorem d4Embed_neg_single (k : Fin 4) : d4Embed (-Pi.single k 1) = -Pi.single (d4Node k) 1 := by
  rw [d4Embed_neg, d4Embed_single]

section Levi


variable (K : Type) [Field K]

@[expose] noncomputable def d4Par (γ : Fin 4 → ℤ) (c : K) : e6Data_valid.minGroup K :=
  e6Data_valid.xm K (d4Embed γ) c

variable {K}

theorem d4Par_add (γ : Fin 4 → ℤ) (c d : K) : d4Par K γ (c + d) = d4Par K γ c * d4Par K γ d :=
  e6Data_valid.xm_add K _ c d

theorem commutator_d4Par_of_mem [CharP K 2] {α β : Fin 4 → ℤ}
    (hα : α ∈ roots (isFiniteType_cartanD 4) ∅) (hβ : β ∈ roots (isFiniteType_cartanD 4) ∅)
    (hne : α + β ≠ 0) (hr : α + β ∈ roots (isFiniteType_cartanD 4) ∅) (c d : K) :
    ⁅d4Par K α c, d4Par K β d⁆ = d4Par K (α + β) (c * d) := by
  obtain ⟨hroot, -⟩ := e6Data_valid.commutator_xm K (isRoot_d4Embed hα) (isRoot_d4Embed hβ)
    (d4Embed_add_ne_zero hne)
  obtain ⟨σ, hσ, h⟩ := hroot (by rw [← d4Embed_add]; exact isRoot_d4Embed hr)
  have hσ1 : σ = 1 := by
    rcases hσ with h1 | h1
    · exact h1
    · rw [h1, CharTwo.neg_eq]
  rw [d4Par, d4Par, h, hσ1, one_mul, ← d4Embed_add]
  rfl

theorem commutator_d4Par_of_not_mem {α β : Fin 4 → ℤ}
    (hα : α ∈ roots (isFiniteType_cartanD 4) ∅) (hβ : β ∈ roots (isFiniteType_cartanD 4) ∅)
    (hne : α + β ≠ 0) (hr : α + β ∉ roots (isFiniteType_cartanD 4) ∅) (c d : K) :
    ⁅d4Par K α c, d4Par K β d⁆ = 1 := by
  obtain ⟨-, hnot⟩ := e6Data_valid.commutator_xm K (isRoot_d4Embed hα) (isRoot_d4Embed hβ)
    (d4Embed_add_ne_zero hne)
  exact hnot (by rw [← d4Embed_add, isRoot_d4Embed_iff]; exact hr) c d

theorem commutatorFormula_d4Par [CharP K 2] (O : CommOrder (SpinPlus.Φ 4 K three_le_rank_D4)) :
    CommutatorFormula (d4Par K) O SpinPlus.commC := by
  intro α hα β hβ hαβ c d
  by_cases hr : α + β ∈ (SpinPlus.Φ 4 K three_le_rank_D4).roots
  · rw [(SpinPlus.commOrder_list_eq three_le_rank_D4 O hα hβ hαβ).1 hr, List.map_singleton,
      List.prod_singleton, one_smul, one_smul, pow_one, pow_one,
      commutator_d4Par_of_mem hα hβ hαβ hr, commC_cast_eq_one_D4, one_mul]
  · rw [(SpinPlus.commOrder_list_eq three_le_rank_D4 O hα hβ hαβ).2 hr, List.map_nil,
      List.prod_nil]
    exact commutator_d4Par_of_not_mem hα hβ hαβ hr c d

end Levi

section Hom


variable (K : Type) [Field K] [Finite K] [CharP K 2]

noncomputable def d4Order : CommOrder (SpinPlus.Φ 4 K three_le_rank_D4) :=
  Classical.choice (SpinPlus.conclusionB (K := K) three_le_rank_D4).2.1

@[expose] noncomputable def spinToE6Sc : spinGroup (quadPlus 4 K) →* e6Data_valid.minGroup K :=
  liftOfPresentationB (SpinPlus.presentationB three_le_rank_D4) (d4Order K)
    (SpinPlus.commutatorFormula three_le_rank_D4 (d4Order K)) (fun γ _ c d => d4Par_add γ c d)
    (commutatorFormula_d4Par (d4Order K))

variable {K}

theorem spinToE6Sc_x {γ : Fin 4 → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanD 4) ∅) (c : K) :
    spinToE6Sc K (SpinPlus.x 4 K three_le_rank_D4 γ c) = e6Data_valid.xm K (d4Embed γ) c :=
  liftOfPresentationB_apply _ _ _ _ _ hγ c

omit [Finite K] [CharP K 2]
  in
theorem iSup_rankOne_spin_eq_top :
    ⨆ k : Fin 4, CFSG.LieType.CurtisTits.rankOne
      (CFSG.LieType.Universal.Spin.plusRootGroup 4 K three_le_rank_D4) k = ⊤ := by
  refine eq_top_iff.2 ?_
  rw [← CFSG.LieType.CurtisTits.iSup_leviAmalgam_eq_top
    (CFSG.LieType.RootSystem.isCTRootSystem (isFiniteType_cartanD 4) ∅)
    (SpinPlus.isCTGroupDatum (K := K) three_le_rank_D4)]
  exact iSup_le fun J => iSup₂_le fun j _ => le_iSup (fun k => CFSG.LieType.CurtisTits.rankOne
    (CFSG.LieType.Universal.Spin.plusRootGroup 4 K three_le_rank_D4) k) j

theorem range_spinToE6Sc : (spinToE6Sc K).range = e6ScLevi K e6D4Nodes := by
  have hsingle : ∀ k : Fin 4, (Pi.single k 1 : Fin 4 → ℤ) ∈ roots (isFiniteType_cartanD 4) ∅ :=
    fun k => (SpinPlus.Φ 4 K three_le_rank_D4).single_mem k
  have hneg : ∀ k : Fin 4, (-Pi.single k 1 : Fin 4 → ℤ) ∈ roots (isFiniteType_cartanD 4) ∅ :=
    fun k => by
      have := (CFSG.LieType.RootSystem.isCTRootSystem (isFiniteType_cartanD 4) ∅).smul_mem
        ((CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartanD 4)).toCoxeterSystem.simple k)
        _ (hsingle k)
      rwa [(CFSG.LieType.RootSystem.isCTRootSystem (isFiniteType_cartanD 4) ∅).simple_single]
        at this
  apply le_antisymm
  · rw [MonoidHom.range_eq_map, ← iSup_rankOne_spin_eq_top, Subgroup.map_iSup]
    refine iSup_le fun k => ?_
    have hrank : CFSG.LieType.CurtisTits.rankOne (e6Datum K).rootGroup (d4Node k) ≤
        e6ScLevi K e6D4Nodes := CFSG.LieType.CurtisTits.rankOne_le_levi _ (d4Node_mem k)
    rw [CFSG.LieType.CurtisTits.rankOne, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨c, rfl⟩ := ((SpinPlus.isParametrization (K := K) three_le_rank_D4 _
        (hsingle k)).1 g).1 hg
      refine hrank (mem_sup_left ?_)
      rw [spinToE6Sc_x (hsingle k), d4Embed_single]
      exact e6Data_valid.xm_mem_rootGroup K _ c
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨c, rfl⟩ := ((SpinPlus.isParametrization (K := K) three_le_rank_D4 _
        (hneg k)).1 g).1 hg
      refine hrank (mem_sup_right ?_)
      rw [spinToE6Sc_x (hneg k), d4Embed_neg_single]
      exact e6Data_valid.xm_mem_rootGroup K _ c
  · refine iSup₂_le fun j hj => ?_
    obtain ⟨k, rfl⟩ := exists_d4Node_eq j hj
    refine sup_le ?_ ?_
    · intro g hg
      obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup K).1 hg
      exact ⟨SpinPlus.x 4 K three_le_rank_D4 (Pi.single k 1) c, by
        rw [spinToE6Sc_x (hsingle k), d4Embed_single]⟩
    · intro g hg
      obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup K).1 hg
      exact ⟨SpinPlus.x 4 K three_le_rank_D4 (-Pi.single k 1) c, by
        rw [spinToE6Sc_x (hneg k), d4Embed_neg_single]⟩

omit [Finite K]
  in
theorem center_spinGroup_quadPlus_four_eq_bot :
    center (spinGroup (quadPlus 4 K)) = ⊥ := by
  obtain ⟨-, h1, h2⟩ := CFSG.LieType.Universal.Spin.spinToStatedProj_quadPlus (n := 4) (K := K)
    three_le_rank_D4
  rw [← h2, h1]
  exact CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed.comap_statedScalars_quadPlus_eq_bot
    three_le_rank_D4 CharTwo.two_eq_zero

theorem exists_spinToE6Sc_ne_one : ∃ g, spinToE6Sc K g ≠ 1 := by
  have hr : (Pi.single 0 1 : Fin 4 → ℤ) ∈ roots (isFiniteType_cartanD 4) ∅ :=
    (SpinPlus.Φ 4 K three_le_rank_D4).single_mem 0
  refine ⟨SpinPlus.x 4 K three_le_rank_D4 (Pi.single 0 1) 1, fun h => ?_⟩
  rw [spinToE6Sc_x hr, ← e6Data_valid.xm_zero K (d4Embed (Pi.single 0 1))] at h
  exact one_ne_zero (e6Data_valid.xm_injective K (isRoot_d4Embed hr) h)

theorem spinToE6Sc_injective : Function.Injective (spinToE6Sc K) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← center_spinGroup_quadPlus_four_eq_bot]
  exact CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
    (CFSG.LieType.Universal.Spin.isQuasisimple_spinGroup_quadPlus three_le_rank_D4)
    exists_spinToE6Sc_ne_one

variable (K) in
@[expose] noncomputable def spinEquivD4 : spinGroup (quadPlus 4 K) ≃* e6ScLevi K e6D4Nodes :=
  (MonoidHom.ofInjective spinToE6Sc_injective).trans (MulEquiv.subgroupCongr range_spinToE6Sc)

theorem coe_spinEquivD4 (g : spinGroup (quadPlus 4 K)) :
    ((spinEquivD4 K g : e6ScLevi K e6D4Nodes) : e6Data_valid.minGroup K) = spinToE6Sc K g :=
  rfl

end Hom

section Graph


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem sigma_spinToE6Sc_x {γ : Fin 4 → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanD 4) ∅) (c : K) :
    sigma K (RingHom.id K) (spinToE6Sc K (SpinPlus.x 4 K three_le_rank_D4 γ c)) =
      spinToE6Sc K (SpinPlus.x 4 K three_le_rank_D4 (d4Swap γ) c) := by
  rw [spinToE6Sc_x hγ, spinToE6Sc_x (d4Swap_mem_roots hγ),
    CFSG.LieType.Steinberg.TwistedE6.sigma_xm (RingHom.id K) (isRoot_d4Embed hγ), rho_d4Embed,
    intCast_eq_one_of_sign_charTwo (CFSG.LieType.Steinberg.TwistedE6.twistSign_eq_one_or _),
    one_mul, RingHom.id_apply]

omit [Finite K] [CharP K 2]
  in
theorem closure_spinX_four_eq_top :
    closure {g : spinGroup (quadPlus 4 K) | ∃ γ ∈ roots (isFiniteType_cartanD 4) ∅, ∃ c : K,
      SpinPlus.x 4 K three_le_rank_D4 γ c = g} = ⊤ := by
  rw [eq_top_iff, ← CFSG.LieType.Universal.Spin.plusDatum_iSup_eq_top 4 K three_le_rank_D4]
  refine iSup₂_le fun γ hγ g hg => ?_
  obtain ⟨c, rfl⟩ := ((SpinPlus.isParametrization (K := K) three_le_rank_D4 γ hγ).1 g).1 hg
  exact subset_closure ⟨γ, hγ, c, rfl⟩

theorem conj_comp_spinEquivD4_symm {G : Type} [Group G] {ΦY : spinGroup (quadPlus 4 K) →* G}
    {t : G}
    (hc : ∀ γ ∈ roots (isFiniteType_cartanD 4) ∅, ∀ c : K,
      t * ΦY (SpinPlus.x 4 K three_le_rank_D4 γ c) * t⁻¹ =
        ΦY (SpinPlus.x 4 K three_le_rank_D4 (d4Swap γ) c))
    (x y : e6ScLevi K e6D4Nodes)
    (hxy : (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x) :
    t * ΦY.comp (spinEquivD4 K).symm.toMonoidHom x * t⁻¹ =
      ΦY.comp (spinEquivD4 K).symm.toMonoidHom y := by
  set τ : spinGroup (quadPlus 4 K) →* spinGroup (quadPlus 4 K) :=
    (spinEquivD4 K).symm.toMonoidHom.comp ((sigmaScLevi (K := K) rhoPerm_mem_e6D4Nodes').comp
      (spinEquivD4 K).toMonoidHom) with hτ
  have hτx : ∀ γ ∈ roots (isFiniteType_cartanD 4) ∅, ∀ c : K,
      τ (SpinPlus.x 4 K three_le_rank_D4 γ c) = SpinPlus.x 4 K three_le_rank_D4 (d4Swap γ) c := by
    intro γ hγ c
    rw [hτ, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_eq]
    refine Subtype.ext ?_
    rw [coe_sigmaScLevi, coe_spinEquivD4, coe_spinEquivD4, sigma_spinToE6Sc_x hγ]
  have hconj : (MulAut.conj t).toMonoidHom.comp ΦY = ΦY.comp τ := by
    refine MonoidHom.eq_of_eqOn_dense closure_spinX_four_eq_top ?_
    rintro _ ⟨γ, hγ, c, rfl⟩
    change t * ΦY (SpinPlus.x 4 K three_le_rank_D4 γ c) * t⁻¹ =
      ΦY (τ (SpinPlus.x 4 K three_le_rank_D4 γ c))
    rw [hτx γ hγ c, hc γ hγ c]
  have hy : (spinEquivD4 K).symm y = τ ((spinEquivD4 K).symm x) := by
    rw [hτ, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    congr 1
    refine Subtype.ext ?_
    rw [coe_sigmaScLevi, hxy]
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [hy]
  exact DFunLike.congr_fun hconj _

end Graph

end CFSG.SeitzReduction.F4Pilot
