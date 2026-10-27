module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightCommField
public import CFSG.LinearAlgebra.UnitaryInvolutionIndex.CentralExtension

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal Matrix
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus StatedSp)
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadMinus minusIndexEquiv regular_coordinateQuadMinus)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore centralizerPerfectCore_le_centralizer
  centralizerPerfectCore_anti normalizer_le_normalizer_centralizerPerfectCore)
open CFSG.SeitzReduction.SymplecticPilot (siegelBlock planeTorusParam)
open CFSG.SeitzReduction.LinearPilot (consecutiveBlock mem_consecutiveBlock)
open CFSG.Timmesfeld (edgeD)
open scoped MatrixGroups

section ForkBlock

variable {F : Type} [Field F]

@[expose] noncomputable def forkBlockEquiv (r : ℕ) (hr : 1 ≤ r) (P : Finset (Fin (r + 1))) :
    SL(2, F) ≃* forkBlock F r P :=
  (LinearPilot.reindexSpecialLinear (finCongr (card_consecutiveBlock_two (by omega)).symm)).trans
    ((SymplecticPilot.siegelBlockEquiv (consecutiveBlock (r + 1) (r - 1) 2)).trans
      (((siegelBlock F (consecutiveBlock (r + 1) (r - 1) 2)).equivMapOfInjective
        (StatedSp (r + 1) F).subtype (StatedSp (r + 1) F).subtype_injective).trans
        ((siegelBlockGL F (consecutiveBlock (r + 1) (r - 1) 2)).equivMapOfInjective
          (MulAut.conj (flipGL F P)).toMonoidHom (MulAut.conj (flipGL F P)).injective)))

end ForkBlock

section Lift

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F] {r : ℕ} {hn : 1 ≤ r + 2} {b c : K}
  {e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (r + 2) K hn b c)} {ι : K →+* F}

theorem nonempty_mulEquiv_lift_forkBlock
    (C₀ : MinusFieldCover e ι 0)
    (hF5 : 5 ≤ Nat.card F) (hF9 : Nat.card F ≠ 9) (hr : 1 ≤ r) (P : Finset (Fin (r + 1))) :
    Nonempty (SL(2, F) ≃* C₀.lift (forkBlock F r P)) := by
  have hF4 : 4 ≤ Nat.card F := by omega
  set U := C₀.lift (forkBlock F r P) with hUdef
  have hUE : U ≤ minusNeighbourCore e (0 : Fin (r + 1)) := C₀.lift_le _
  set ρ₀ : U →* GL (Fin (r + 1) ⊕ Fin (r + 1)) F :=
    (StatedOmega (StatedQuadPlus (r + 1) F)).subtype.comp (C₀.π.comp (Subgroup.inclusion hUE))
    with hρ₀
  have hrange : ρ₀.range = forkBlock F r P := by
    have h := C₀.map_lift (forkBlock_le_statedOmega hF4 hr P) (commutator_forkBlock hF4 hr P)
    rw [hρ₀, MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.inclusion_range]
    exact h
  set ρ₁ : U →* forkBlock F r P := ρ₀.codRestrict _ (fun x => hrange ▸ ⟨x, rfl⟩) with hρ₁
  set ρ : U →* SL(2, F) := (forkBlockEquiv r hr P).symm.toMonoidHom.comp ρ₁ with hρ
  have hρ₁s : Function.Surjective ρ₁ := by
    rintro ⟨y, hy⟩
    rw [← hrange] at hy
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  have hρs : Function.Surjective ρ := (forkBlockEquiv r hr P).symm.surjective.comp hρ₁s
  have hker : ρ.ker ≤ center U := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : ρ₁ x = 1 := by
      have h := congrArg (forkBlockEquiv r hr P) hx
      simpa [hρ] using h
    have h2 : ρ₀ x = 1 := congrArg Subtype.val h1
    have h3 : C₀.π (Subgroup.inclusion hUE x) = 1 := Subtype.ext h2
    have h4 : Subgroup.inclusion hUE x ∈ center (minusNeighbourCore e (0 : Fin (r + 1))) :=
      C₀.ker_le h3
    rw [mem_center_iff] at h4 ⊢
    intro y
    have h5 := congrArg Subtype.val (h4 (Subgroup.inclusion hUE y))
    exact Subtype.ext h5
  obtain ⟨σ, hσ⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SL2Closed.sl2_exists_section_of_central hF5 hF9 hρs hker
  have : Group.IsPerfect U := Subgroup.isPerfect_iff.mpr (C₀.commutator_lift _)
  have hbot := CFSG.LieType.Steinberg.CentralExt.SL2Closed.ker_eq_bot_of_section ρ hker σ hσ
  have hinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).mp hbot
  exact ⟨(MulEquiv.ofBijective ρ ⟨hinj, hρs⟩).symm⟩

end Lift

section Four

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F]

theorem fork_simple_and_torus
    (hset : CFSG.EvenSmallLie.StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (hq : 4 ≤ Nat.card K) {β γ : K}
    (hirr : ∀ s : K, s ^ 2 + β * s + γ ≠ 0)
    {e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (2 + 2) K (by omega) β γ)}
    {ι : K →+* F} (hFK : Nat.card F = Nat.card K ^ 2) (C₀ : MinusFieldCover e ι 0) {t : G}
    (ht : orderOf t = 2) (htC : t ∈ centralizer (L : Set G))
    (htU : (minusNode C₀ 2).map (MulAut.conj t).toMonoidHom = minusNode C₀ 3) :
    (∀ N : Subgroup (minusNode C₀ 2), N.Normal → N = ⊥ ∨ N = ⊤) ∧
      ∃ x ∈ minusNode C₀ 2, x ∈ normalizer (minusNode C₀ 0 : Set G) ∧
        ∃ a₀ ∈ minusNode C₀ 2, x * a₀ ≠ a₀ * x := by
  have hn1 : 1 ≤ 2 + 2 := by omega
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  have hF16 : 16 ≤ Nat.card F := by
    rw [hFK]
    nlinarith
  have hF4 : 4 ≤ Nat.card F := by omega
  have hF9 : Nat.card F ≠ 9 := by
    intro h9
    rw [hFK] at h9
    nlinarith
  set U₂ := minusNode C₀ 2 with hU₂
  set U₃ := minusNode C₀ 3 with hU₃
  have h2eq : U₂ = C₀.lift (forkBlock F 2 ∅) := minusNode_of_eq C₀ (j := 2) rfl
  obtain ⟨ψ⟩ := nonempty_mulEquiv_lift_forkBlock C₀ (by omega) hF9 (by omega : 1 ≤ 2) ∅
  rw [← h2eq] at ψ
  have := LinearPilot.isSimpleGroup_specialLinearGroup_two (K := F) hF4
  have hU2simple : IsSimpleGroup U₂ := ψ.symm.isSimpleGroup
  have hU2perf : Group.IsPerfect U₂ := Subgroup.isPerfect_iff.mpr (commutator_minusNode C₀ 2)
  have hU2s : ∀ N : Subgroup U₂, N.Normal → N = ⊥ ∨ N = ⊤ := fun N hN => by
    have := hN
    exact IsSimpleGroup.eq_bot_or_eq_top_of_normal N
  refine ⟨hU2s, ?_⟩
  have hZ : center U₂ = ⊥ := by
    rcases hU2s (center U₂) inferInstance with h | h
    · exact h
    · exfalso
      have hc : ⁅(⊤ : Subgroup U₂), (⊤ : Subgroup U₂)⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        rw [mem_centralizer_iff]
        intro y _
        have hy : y ∈ center U₂ := h ▸ mem_top y
        exact (mem_center_iff.1 hy x).symm
      rw [← commutator_def, Group.IsPerfect.commutator_eq_top] at hc
      exact top_ne_bot hc
  have hAB := fork_conj_commute C₀ hF4 htU
  have hU23 : ∀ y ∈ U₂, y ∈ U₃ → y = 1 := by
    intro y hy2 hy3
    have hz : (⟨y, hy2⟩ : U₂) ∈ center U₂ := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (hAB g g.2 y (htU ▸ hy3))
    rw [hZ, mem_bot] at hz
    exact congrArg Subtype.val hz
  have ht2 : t * t = 1 := by
    rw [← _root_.sq, ← ht]
    exact pow_orderOf_eq_one t
  obtain ⟨θ, hθ, -⟩ := exists_diag_hom_of_conj_swap ht2 hAB
  have hθinj : Function.Injective θ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker, hθ] at ha
    have h1 : t * (a : G) * t⁻¹ = (a : G)⁻¹ := eq_inv_of_mul_eq_one_right ha
    have h3 : (a : G)⁻¹ ∈ U₃ := by
      rw [← h1, ← htU]
      exact ⟨a, a.2, rfl⟩
    have h4 := hU23 _ (inv_mem a.2) h3
    rw [inv_eq_one] at h4
    rw [mem_bot]
    exact Subtype.ext h4
  set R := modelToG e (stabPairsBar (coordinateQuadMinus (2 + 2) K hn1 β γ)
      (minusIndexEquiv (2 + 2) hn1 (.inl ⟨0, by omega⟩))
      (minusIndexEquiv (2 + 2) hn1 (.inr (.inl ⟨0, by omega⟩)))
      (minusIndexEquiv (2 + 2) hn1 (.inl ⟨1, by omega⟩))
      (minusIndexEquiv (2 + 2) hn1 (.inr (.inl ⟨1, by omega⟩)))) with hRdef
  have hθR : θ.range ≤ R := by
    rintro _ ⟨a, rfl⟩
    rw [hθ]
    exact fork_mul_conj_mem hset hOut hq hirr C₀ hF4 ht htC htU a a.2
  have hθeq : θ.range = R := by
    refine Subgroup.eq_of_le_of_card_ge hθR ?_
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hθinj, Subgroup.card_top,
      ← Nat.card_congr ψ.toEquiv,
      CFSG.UnitaryInvolutionIndex.card_specialLinearGroup_fin_two, hFK, hRdef,
      UnitaryPilot.card_modelToG]
    have h := (minusStabPairsBar_four (K := K) hirr (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
      (by simp)).2.2
    refine le_of_eq ?_
    rw [← pow_mul]
    exact h
  have hfr := isHypFrame_minus K hn1 β γ
  obtain ⟨l, hl⟩ := exists_units_ne_one (K := K) (by omega : 3 ≤ Nat.card K)
  have hX2R : ∀ c : Kˣ, ((e.symm (hfr.frameHom (Pi.mulSingle (Fin.last 2) c)) : L) : G) ∈ R := by
    intro c
    refine UnitaryPilot.symm_mem_modelToG e (minusPairTorus_le_stabPairsBar hn1 β γ
      (j := Fin.last 2) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) ?_)
    rw [← minusFrameTorus_rootParam]
    exact hfr.frameHom_mem_frameTorusOf (mulSingle_mem_rootParam _ c)
  obtain ⟨a, ha⟩ := (show _ ∈ θ.range from hθeq ▸ hX2R l)
  refine ⟨a, a.2, ?_, ?_⟩
  ·
    have hU0 : minusNode C₀ 0 = minusLevelCore e ({⟨0, by omega⟩, ⟨1, by omega⟩} :
        Finset (Fin (2 + 1))) := by
      rw [minusNode_of_le C₀ (j := 0) (by simp), Fin.val_zero, consecutiveBlock_three_zero_two]
    have hM2 : U₂ ≤ minusPieceCore e {Fin.last 2} := by
      rw [h2eq]
      exact lift_forkBlock_le_minusPieceCore C₀ hF4 (by omega) (Finset.empty_subset _)
    have haT : (a : G) ∈ centralizer (modelToG e (minusPlaneTorus hn1 β γ {Fin.last 2}) :
        Set G) := centralizerPerfectCore_le_centralizer _ (hM2 a.2)
    have hc : (a : G) ∈ centralizer (modelToG e (minusLevelTorus hn1 β γ
        ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin (2 + 1)))) : Set G) := by
      rw [mem_centralizer_iff]
      intro h hh
      obtain ⟨y, hy, rfl⟩ := (UnitaryPilot.mem_modelToG e).1 hh
      have hy' : y ∈ frameTorusOf (coordinateQuadMinus (2 + 2) K hn1 β γ) (minusFrameLeft hn1)
          (minusFrameRight hn1) (levelParam ({⟨0, by omega⟩, ⟨1, by omega⟩} :
            Finset (Fin (2 + 1)))) := hy
      rw [hfr.frameTorusOf_eq_map] at hy'
      obtain ⟨s, -, rfl⟩ := hy'
      set s' := s * (Pi.mulSingle (Fin.last 2) (s (Fin.last 2)))⁻¹ with hs'
      have hss : s = s' * Pi.mulSingle (Fin.last 2) (s (Fin.last 2)) := by
        rw [hs', inv_mul_cancel_right]
      rw [hss, map_mul, map_mul, L.coe_mul]
      have h1 : ((e.symm (hfr.frameHom s') : L) : G) ∈
          modelToG e (minusPlaneTorus hn1 β γ {Fin.last 2}) := by
        refine UnitaryPilot.symm_mem_modelToG e (hfr.frameHom_mem_frameTorusOf ?_)
        intro k hk
        rw [Finset.mem_singleton] at hk
        subst hk
        simp [hs']
      have hc1 := mem_centralizer_iff.1 haT _ h1
      obtain ⟨b, hb⟩ := (show _ ∈ θ.range from hθeq ▸ hX2R (s (Fin.last 2)))
      have hab : θ (a * b) = θ (b * a) := by
        rw [map_mul, map_mul, ha, hb]
        have h := congrArg (fun m => ((e.symm (hfr.frameHom m) : L) : G))
          (mul_comm (Pi.mulSingle (Fin.last 2) l) (Pi.mulSingle (Fin.last 2) (s (Fin.last 2))))
        simpa only [map_mul, L.coe_mul] using h
      have hab' : (a : G) * b = b * a := congrArg Subtype.val (hθinj hab)
      have hc2 : ((e.symm (hfr.frameHom (Pi.mulSingle (Fin.last 2) (s (Fin.last 2)))) : L) : G) *
          a = a * ((e.symm (hfr.frameHom (Pi.mulSingle (Fin.last 2) (s (Fin.last 2)))) : L) :
            G) := by
        rw [← hb, hθ]
        have hbt := hAB a a.2 (t * b * t⁻¹) ⟨b, b.2, rfl⟩
        calc (b : G) * (t * b * t⁻¹) * a = b * ((t * b * t⁻¹) * a) := by group
          _ = b * (a * (t * b * t⁻¹)) := by rw [hbt]
          _ = (b * a) * (t * b * t⁻¹) := by group
          _ = (a * b) * (t * b * t⁻¹) := by rw [hab']
          _ = a * (b * (t * b * t⁻¹)) := by group
      rw [mul_assoc, hc2, ← mul_assoc, hc1, mul_assoc]
    rw [hU0]
    exact normalizer_le_normalizer_centralizerPerfectCore _ (centralizer_le_normalizer _ hc)
  ·
    have ha1 : a ≠ 1 := by
      intro h1
      rw [h1, map_one] at ha
      have h2 : e.symm (hfr.frameHom (Pi.mulSingle (Fin.last 2) l)) = e.symm 1 := by
        rw [map_one]
        exact Subtype.ext ha.symm
      have h3 := e.symm.injective h2
      rw [← map_one hfr.frameHom] at h3
      have h4 := congrFun (hfr.frameHom_injective h3) (Fin.last 2)
      rw [Pi.mulSingle_eq_same, Pi.one_apply] at h4
      exact hl h4
    by_contra hcon
    push Not at hcon
    have hz : a ∈ center U₂ := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (hcon g g.2).symm
    rw [hZ, mem_bot] at hz
    exact ha1 hz

theorem minusNode_le_centralizer_four_field_of_swap
    (hset : SeitzSetting G L)
    {f : ℕ} (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) {β γ : K}
    (hirr : ∀ s : K, s ^ 2 + β * s + γ ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (2 + 2) K (by omega) β γ)) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {ι : K →+* F} {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (P : MinusRootFieldParam (n := 2 + 2) le_rfl hirr e t ι σ ⟨0, by omega⟩ ⟨1, by omega⟩)
    (C₀ : MinusFieldCover e ι 0)
    (htU : (minusNode C₀ 2).map (MulAut.conj t).toMonoidHom = minusNode C₀ 3) :
    ∀ i j : Fin (2 + 2), i ≠ j → ¬ edgeD (2 + 2) i j → ¬ edgeD (2 + 2) j i →
      minusNode C₀ i ≤ centralizer (minusNode C₀ j : Set G) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · rw [pow_zero] at hK; omega
    · exact h
  have hOut : Group.IsSolvable (Outer L) := isSolvable_outer_of_mulEquiv_minus le_rfl hf hK hirr e
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq hKt
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  have hFK := LinearPilot.natCard_eq_sq_of_involution ι hσ1 hσσ hfix
  obtain ⟨hU2s, x, hx2, hxU, a₀, ha₀, hxa₀⟩ :=
    fork_simple_and_torus hset.standardSetting hOut hq hirr hFK C₀ ht htC htU
  exact minusNode_le_centralizer_four_field hset hK hq hirr e ht hKt hσ1 hσσ hfix P C₀ htU hU2s
    hx2 hxU ha₀ hxa₀

end Four

end CFSG.SeitzReduction.OmegaPilot
