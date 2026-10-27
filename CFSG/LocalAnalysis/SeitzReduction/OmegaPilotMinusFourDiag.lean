module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusFourFork
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverHR8Model

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup Matrix
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus StatedSp)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus
  minusIndexEquiv)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (leviEmbedSL)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.SeitzReduction.SymplecticPilot (siegelBlock liftParam diagSpEntry)
open CFSG.SeitzReduction.LinearPilot (consecutiveBlock)
open scoped MatrixGroups

section Model

variable {F : Type} [Field F]

theorem exists_siegelBlockGL_not_commute {s : Fin (2 + 1) → Fˣ} (hs : s 1 ≠ s 2) :
    ∃ y ∈ siegelBlockGL F (consecutiveBlock (2 + 1) (2 - 1) 2),
      diagOmega F (2 + 1) s * y ≠ y * diagOmega F (2 + 1) s := by
  have h12 : (1 : Fin (2 + 1)) ≠ 2 := by decide
  have h1 : (1 : Fin (2 + 1)) ∈ consecutiveBlock (2 + 1) (2 - 1) 2 := by decide
  have h2 : (2 : Fin (2 + 1)) ∈ consecutiveBlock (2 + 1) (2 - 1) 2 := by decide
  set C := SpecialLinearGroup.transvection h12 (1 : F) with hC
  have hCmem := LinearPilot.transvection_mem_blockSpecialLinear (K := F) h12 h1 h2 1
  refine ⟨((leviEmbedSL F (2 + 1) C : StatedSp (2 + 1) F) : GL (Fin (2 + 1) ⊕ Fin (2 + 1)) F),
    ⟨leviEmbedSL F (2 + 1) C, ⟨C, hCmem, rfl⟩, rfl⟩, fun h => hs ?_⟩
  have hentry := congrArg (fun g : GL (Fin (2 + 1) ⊕ Fin (2 + 1)) F =>
    (g : Matrix (Fin (2 + 1) ⊕ Fin (2 + 1)) (Fin (2 + 1) ⊕ Fin (2 + 1)) F)
      (Sum.inl 1) (Sum.inl 2)) h
  simp only [Units.val_mul, diagOmega_coe] at hentry
  rw [diagonal_mul, mul_diagonal] at hentry
  have hY : ((((leviEmbedSL F (2 + 1) C : StatedSp (2 + 1) F) :
      GL (Fin (2 + 1) ⊕ Fin (2 + 1)) F) : Matrix (Fin (2 + 1) ⊕ Fin (2 + 1))
        (Fin (2 + 1) ⊕ Fin (2 + 1)) F) (Sum.inl 1) (Sum.inl 2)) = 1 := by
    have := SymplecticPilot.mat_leviEmbedSL_inl_inl C 1 2
    change ((((leviEmbedSL F (2 + 1) C : StatedSp (2 + 1) F) :
      GL (Fin (2 + 1) ⊕ Fin (2 + 1)) F) : Matrix (Fin (2 + 1) ⊕ Fin (2 + 1))
        (Fin (2 + 1) ⊕ Fin (2 + 1)) F) (Sum.inl 1) (Sum.inl 2)) = _ at this
    rw [this, hC, SpecialLinearGroup.transvection_coe]
    simp [Matrix.add_apply, h12]
  rw [hY, SymplecticPilot.diagSpEntry_inl, SymplecticPilot.diagSpEntry_inl, mul_one,
    one_mul] at hentry
  exact Units.ext hentry

theorem exists_forkBlock_not_commute {s : Fin (2 + 1) → Fˣ} (hs1 : s 1 ≠ 1) (hs2 : s 2 = 1)
    {P : Finset (Fin (2 + 1))} (hP : P ⊆ {Fin.last 2}) :
    ∃ y ∈ forkBlock F 2 P, diagOmega F (2 + 1) s * y ≠ y * diagOmega F (2 + 1) s := by
  set s' := flipParam F P s with hs'
  have h1 : s' 1 ≠ s' 2 := by
    have hP1 : (1 : Fin (2 + 1)) ∉ P := fun h => by
      have := hP h
      simp [Fin.ext_iff] at this
    rw [hs', flipParam_apply, flipParam_apply, ite_eq_right_iff.2 (fun h => absurd h hP1), hs2]
    split_ifs <;> simpa using hs1
  obtain ⟨y, hy, hne⟩ := exists_siegelBlockGL_not_commute h1
  refine ⟨flipGL F P * y * (flipGL F P)⁻¹, ⟨y, hy, rfl⟩, fun h => hne ?_⟩
  have hd : diagOmega F (2 + 1) s' = flipGL F P * diagOmega F (2 + 1) s * (flipGL F P)⁻¹ :=
    (flipGL_mul_diagOmega_mul_inv P s).symm
  have hinv : (flipGL F P)⁻¹ = flipGL F P := flipGL_inv P
  have h' : (flipGL F P)⁻¹ * diagOmega F (2 + 1) s * flipGL F P * y =
      y * ((flipGL F P)⁻¹ * diagOmega F (2 + 1) s * flipGL F P) := by
    calc (flipGL F P)⁻¹ * diagOmega F (2 + 1) s * flipGL F P * y =
          (flipGL F P)⁻¹ * (diagOmega F (2 + 1) s * (flipGL F P * y * (flipGL F P)⁻¹)) *
            flipGL F P := by group
      _ = (flipGL F P)⁻¹ * ((flipGL F P * y * (flipGL F P)⁻¹) * diagOmega F (2 + 1) s) *
            flipGL F P := by rw [h]
      _ = y * ((flipGL F P)⁻¹ * diagOmega F (2 + 1) s * flipGL F P) := by group
  have hsym : (flipGL F P)⁻¹ * diagOmega F (2 + 1) s * flipGL F P =
      flipGL F P * diagOmega F (2 + 1) s * (flipGL F P)⁻¹ := by rw [hinv]
  rw [hd, ← hsym]
  exact h'

end Model

section Torus

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2] {hn : 1 ≤ 2 + 2} {b c : K}
  {e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (2 + 2) K hn b c)} {ι : K →+* F}

omit [CharP F 2] in
theorem not_mem_forkNode_of_torus (C₀ : MinusFieldCover e ι 0) (hF : 4 ≤ Nat.card F) {l : Kˣ}
    (hl : l ≠ 1) {P P' : Finset (Fin (2 + 1))} (hP' : P' ⊆ {Fin.last 2})
    (hcomm : C₀.lift (forkBlock F 2 P) ≤ centralizer (C₀.lift (forkBlock F 2 P') : Set G)) :
    ((e.symm ((isHypFrame_minus K hn b c).frameHom (Pi.mulSingle (Fin.last 2) l)) : L) : G) ∉
      C₀.lift (forkBlock F 2 P) := by
  intro hh
  set h := ((e.symm ((isHypFrame_minus K hn b c).frameHom (Pi.mulSingle (Fin.last 2) l)) : L) : G)
    with hhdef
  set E := minusNeighbourCore e (0 : Fin (2 + 1)) with hE
  set s := snocOneParam F 2 (liftParam ι (restrictParam 0 (Pi.mulSingle (Fin.last 2) l))) with hs
  have hs1 : s 1 ≠ 1 := by
    have h1 : s 1 = Units.map (ι : K →* F) l := by
      rw [hs, show (1 : Fin (2 + 1)) = (1 : Fin 2).castSucc from rfl, snocOneParam_castSucc]
      simp [liftParam, restrictParam_apply]
    rw [h1]
    intro h0
    apply hl
    apply Units.ext
    apply ι.injective
    have := congrArg Units.val h0
    simpa using this
  have hs2 : s 2 = 1 := by
    rw [hs, show (2 : Fin (2 + 1)) = Fin.last 2 from rfl, snocOneParam_last]
  have hN : h ∈ normalizer (E : Set G) := by
    have hx : (isHypFrame_minus K hn b c).frameHom (Pi.mulSingle (Fin.last 2) l) ∈
        minusFrameTorus hn b c (rootParam (Fin.last 2)) :=
      (isHypFrame_minus K hn b c).frameHom_mem_frameTorusOf (mulSingle_mem_rootParam _ l)
    have hc : (isHypFrame_minus K hn b c).frameHom (Pi.mulSingle (Fin.last 2) l) ∈
        centralizer (minusPairTorus (K := K) hn b c (0 : Fin (2 + 1)) :
          Set (matrixProjectiveDerived (coordinateQuadMinus (2 + 2) K hn b c))) := by
      rw [← minusFrameTorus_rootParam]
      exact (isHypFrame_minus K hn b c).frameTorusOf_le_centralizer _ _ hx
    exact UnitaryPilot.symm_mem_normalizer_centralizerPerfectCore_modelToG e
      (centralizer_le_normalizer _ hc)
  have hfix : ∀ y ∈ forkBlock F 2 P', diagOmega F (2 + 1) s * y = y * diagOmega F (2 + 1) s := by
    intro y hy
    have hy' := hy
    rw [← C₀.map_lift (forkBlock_le_statedOmega hF (by omega) P')
      (commutator_forkBlock hF (by omega) P')] at hy'
    obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hy'
    have hxh : h * (x : G) * h⁻¹ = x := by
      have hc := mem_centralizer_iff.1 (hcomm hh) x (mem_subgroupOf.1 hx)
      rw [← hc, mul_inv_cancel_right]
    have heq := C₀.equivariant (Pi.mulSingle (Fin.last 2) l) hN x
    have hx' : E.normalizerMonoidHom ⟨h, hN⟩ x = x := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      exact hxh
    rw [hx'] at heq
    have heq' := congrArg Subtype.val heq
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at heq'
    change (C₀.π x : GL (Fin (2 + 1) ⊕ Fin (2 + 1)) F) =
      diagOmega F (2 + 1) s * (C₀.π x : GL (Fin (2 + 1) ⊕ Fin (2 + 1)) F) *
        (diagOmega F (2 + 1) s)⁻¹ at heq'
    change diagOmega F (2 + 1) s * (C₀.π x : GL (Fin (2 + 1) ⊕ Fin (2 + 1)) F) =
      (C₀.π x : GL (Fin (2 + 1) ⊕ Fin (2 + 1)) F) * diagOmega F (2 + 1) s
    calc diagOmega F (2 + 1) s * (C₀.π x : GL (Fin (2 + 1) ⊕ Fin (2 + 1)) F) =
          diagOmega F (2 + 1) s * (C₀.π x : GL (Fin (2 + 1) ⊕ Fin (2 + 1)) F) *
            (diagOmega F (2 + 1) s)⁻¹ * diagOmega F (2 + 1) s := by group
      _ = (C₀.π x : GL (Fin (2 + 1) ⊕ Fin (2 + 1)) F) * diagOmega F (2 + 1) s := by rw [← heq']
  obtain ⟨y, hy, hne⟩ := exists_forkBlock_not_commute (F := F) hs1 hs2 hP'
  exact hne (hfix y hy)

omit [Finite G] in
theorem inf_eq_bot_of_isSimpleGroup_of_not_mem {R U V : Subgroup G} [IsSimpleGroup R]
    (hUV : U ≤ centralizer (V : Set G)) (hRM : R ≤ U ⊔ V) {h : G} (hhR : h ∈ R) (hhU : h ∉ U) :
    R ⊓ U = ⊥ := by
  let N : Subgroup R := (R ⊓ U).subgroupOf R
  have hN : N.Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    exact Subgroup.mem_inf.2 ⟨mul_mem (mul_mem g.2 (Subgroup.mem_inf.1 hn).1) (inv_mem g.2),
      conj_mem_of_mem_sup_of_le_centralizer hUV (hRM g.2) (Subgroup.mem_inf.1 hn).2⟩⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hb | ht
  · rw [eq_bot_iff]
    intro x hx
    have hxN : (⟨x, (Subgroup.mem_inf.1 hx).1⟩ : R) ∈ N := hx
    rw [hb, mem_bot] at hxN
    rw [mem_bot]
    exact congrArg Subtype.val hxN
  · exfalso
    have hxN : (⟨h, hhR⟩ : R) ∈ N := ht ▸ mem_top _
    exact hhU (Subgroup.mem_inf.1 (mem_subgroupOf.1 hxN)).2

theorem stabPairsBar_inf_minusNode_eq_bot_four (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (C₀ : MinusFieldCover e ι 0) (hq : 4 ≤ Nat.card K) (hF : 4 ≤ Nat.card F) :
    modelToG e (stabPairsBar (coordinateQuadMinus (2 + 2) K hn b c)
        (minusIndexEquiv (2 + 2) hn (.inl 0)) (minusIndexEquiv (2 + 2) hn (.inr (.inl 0)))
        (minusIndexEquiv (2 + 2) hn (.inl 1))
        (minusIndexEquiv (2 + 2) hn (.inr (.inl 1)))) ⊓ minusNode C₀ 2 = ⊥ ∧
      modelToG e (stabPairsBar (coordinateQuadMinus (2 + 2) K hn b c)
        (minusIndexEquiv (2 + 2) hn (.inl 0)) (minusIndexEquiv (2 + 2) hn (.inr (.inl 0)))
        (minusIndexEquiv (2 + 2) hn (.inl 1))
        (minusIndexEquiv (2 + 2) hn (.inr (.inl 1)))) ⊓ minusNode C₀ 3 = ⊥ := by
  have h2eq : minusNode C₀ 2 = C₀.lift (forkBlock F 2 ∅) := minusNode_of_eq C₀ (j := 2) rfl
  have h3eq : minusNode C₀ 3 = C₀.lift (forkBlock F 2 {Fin.last 2}) :=
    minusNode_of_eq_succ C₀ (j := 3) rfl
  have h23 : C₀.lift (forkBlock F 2 ∅) ≤
      centralizer (C₀.lift (forkBlock F 2 {Fin.last 2}) : Set G) :=
    lift_forkBlock_le_centralizer C₀ (by omega) hF
  have h32 : C₀.lift (forkBlock F 2 {Fin.last 2}) ≤
      centralizer (C₀.lift (forkBlock F 2 ∅) : Set G) := le_centralizer_iff.1 h23
  obtain ⟨hRq, hRZ, -⟩ := minusStabPairsBar_four (K := K) hirr (i := 0) (j := 1) (by decide)
  have hRs0 : IsSimpleGroup (stabPairsBar (coordinateQuadMinus (2 + 2) K hn b c)
      (minusIndexEquiv (2 + 2) hn (.inl 0)) (minusIndexEquiv (2 + 2) hn (.inr (.inl 0)))
      (minusIndexEquiv (2 + 2) hn (.inl 1)) (minusIndexEquiv (2 + 2) hn (.inr (.inl 1)))) := by
    obtain ⟨-, hs, -⟩ := hRq
    exact ((QuotientGroup.quotientMulEquivOfEq hRZ).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup
  have : IsSimpleGroup (modelToG e (stabPairsBar (coordinateQuadMinus (2 + 2) K hn b c)
      (minusIndexEquiv (2 + 2) hn (.inl 0)) (minusIndexEquiv (2 + 2) hn (.inr (.inl 0)))
      (minusIndexEquiv (2 + 2) hn (.inl 1)) (minusIndexEquiv (2 + 2) hn (.inr (.inl 1))))) :=
    (UnitaryPilot.modelToGEquiv e _).symm.isSimpleGroup
  have hRM : modelToG e (stabPairsBar (coordinateQuadMinus (2 + 2) K hn b c)
      (minusIndexEquiv (2 + 2) hn (.inl 0)) (minusIndexEquiv (2 + 2) hn (.inr (.inl 0)))
      (minusIndexEquiv (2 + 2) hn (.inl 1)) (minusIndexEquiv (2 + 2) hn (.inr (.inl 1)))) ≤
      C₀.lift (forkBlock F 2 ∅) ⊔ C₀.lift (forkBlock F 2 {Fin.last 2}) := by
    have h01c : (({0, 1} : Finset (Fin (2 + 2 - 1)))ᶜ) = {Fin.last 2} := by decide
    have hc := modelToG_stabPairsBar_le_minusPieceCore hn e (i := 0) (j := 1) (by decide)
      (Subgroup.isPerfect_iff.mp hRq.1)
    rw [h01c] at hc
    have hc' := hc.trans (minusPieceCore_le_sup_minusNode_four C₀ hq hF)
    rwa [h2eq, h3eq] at hc'
  obtain ⟨l, hl⟩ := exists_units_ne_one (K := K) (by omega : 3 ≤ Nat.card K)
  have hhR : ((e.symm ((isHypFrame_minus K hn b c).frameHom (Pi.mulSingle (Fin.last 2) l)) :
      L) : G) ∈ modelToG e (stabPairsBar (coordinateQuadMinus (2 + 2) K hn b c)
        (minusIndexEquiv (2 + 2) hn (.inl 0)) (minusIndexEquiv (2 + 2) hn (.inr (.inl 0)))
        (minusIndexEquiv (2 + 2) hn (.inl 1)) (minusIndexEquiv (2 + 2) hn (.inr (.inl 1)))) :=
    UnitaryPilot.symm_mem_modelToG e (minusPairTorus_le_stabPairsBar hn b c (j := Fin.last 2)
      (a := 0) (a' := 1) (by decide) (by decide) (frameHom_mulSingle_mem_minusPairTorus _ l))
  refine ⟨?_, ?_⟩
  · rw [h2eq]
    exact inf_eq_bot_of_isSimpleGroup_of_not_mem h23 hRM hhR
      (not_mem_forkNode_of_torus C₀ hF hl le_rfl h23)
  · rw [h3eq]
    exact inf_eq_bot_of_isSimpleGroup_of_not_mem h32 (by rwa [sup_comm]) hhR
      (not_mem_forkNode_of_torus C₀ hF hl (Finset.empty_subset _) h32)

end Torus

section Inputs


theorem omegaMinusFourForkDiagInput_holds : OmegaMinusFourForkDiagInput := by
  intro G _ _ L hset f K _ _ _ b c hirr hKc hf2 e t ht hKt hrow F _ _ _ ι σ hσ hfix C₀
  have hq : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf2
  have hF : Nat.card F = 2 ^ (2 * f) :=
    SymplecticPilot.natCard_eq_two_pow_two_mul_of_fix ι hKc hσ hfix
  have hF4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact stabPairsBar_inf_minusNode_eq_bot_four hirr C₀ hq hF4

theorem omegaMinusFourForkSwapInput_holds : OmegaMinusFourForkSwapInput :=
  omegaMinusFourForkSwapInput_of_diag omegaMinusFourForkDiagInput_holds

theorem omegaMinusFourInput_of_inputs_final (hswap : OmegaMinusFourSwapRowInput)
    (hcov : OmegaMinusFourCoverInput) (hparam : OmegaMinusFourRootParamInput)
    (hedge : OmegaMinusFourEdgeInput) (huniq : OmegaMinusFourUniqueInput)
    (hend : OmegaMinusFourEndInput) : OmegaMinusFourInput :=
  omegaMinusFourInput_of_inputs hswap hcov hparam omegaMinusFourForkSwapInput_holds hedge huniq
    hend

end Inputs

end CFSG.SeitzReduction.OmegaPilot
