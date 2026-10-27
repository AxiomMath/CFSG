module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightComm
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverNodes
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapOverlap

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadMinus minusIndexEquiv regular_coordinateQuadMinus)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore centralizerPerfectCore_le_centralizer
  centralizerPerfectCore_anti)
open CFSG.Quasithin (perfectCore le_perfectCore_of_perfect)
open CFSG.SeitzReduction.LinearPilot (consecutiveBlock mem_consecutiveBlock)
open CFSG.Timmesfeld (edgeD)

section Generic

variable {G : Type*} [Group G]

theorem le_centralizer_of_conj_swap {t : G} {A U R : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ A.map (MulAut.conj t).toMonoidHom, a * b = b * a)
    (hAs : ∀ N : Subgroup A, N.Normal → N = ⊥ ∨ N = ⊤) (hRU : R ≤ centralizer (U : Set G))
    (hdiag : ∀ a ∈ A, a * (t * a * t⁻¹) ∈ R) {x : G} (hxA : x ∈ A)
    (hxU : x ∈ normalizer (U : Set G)) {a₀ : G} (ha₀ : a₀ ∈ A) (hxa₀ : x * a₀ ≠ a₀ * x) :
    A ≤ centralizer (U : Set G) ∧ A.map (MulAut.conj t).toMonoidHom ≤ centralizer (U : Set G) :=
  le_centralizer_of_subdirect hAB hAs hRU
    (fun a ha => ⟨t * a * t⁻¹, ⟨a, ha, rfl⟩, hdiag a ha⟩)
    (fun b hb => by
      obtain ⟨a, ha, rfl⟩ := hb
      exact ⟨a, ha, hdiag a ha⟩)
    hxA hxU ha₀ hxa₀

theorem exists_diag_hom_of_conj_swap {t : G} (ht2 : t * t = 1) {A : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ A.map (MulAut.conj t).toMonoidHom, a * b = b * a) :
    ∃ θ : A →* G, (∀ a : A, θ a = a * (t * a * t⁻¹)) ∧ θ.range ≤ centralizer ({t} : Set G) := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hcomm : ∀ a b : A, (b : G) * (t * a * t⁻¹) = (t * a * t⁻¹) * b := fun a b =>
    hAB b b.2 _ ⟨a, a.2, rfl⟩
  refine ⟨{ toFun := fun a => a * (t * a * t⁻¹), map_one' := by simp, map_mul' := ?_ },
    fun a => rfl, ?_⟩
  · intro a b
    simp only [coe_mul]
    calc (a : G) * b * (t * (a * b) * t⁻¹) = a * (b * (t * a * t⁻¹)) * (t * b * t⁻¹) := by group
      _ = a * ((t * a * t⁻¹) * b) * (t * b * t⁻¹) := by rw [hcomm a b]
      _ = a * (t * a * t⁻¹) * (b * (t * b * t⁻¹)) := by group
  · rintro _ ⟨a, rfl⟩
    rw [mem_centralizer_singleton_iff]
    change (a : G) * (t * a * t⁻¹) * t = t * (a * (t * a * t⁻¹))
    have h := hcomm a a
    calc (a : G) * (t * a * t⁻¹) * t = a * (t * a) := by group
      _ = t * (t * a * t⁻¹) * a := by
          rw [htinv]
          simp only [← mul_assoc, ht2, one_mul]
      _ = t * ((t * a * t⁻¹) * a) := by group
      _ = t * (a * (t * a * t⁻¹)) := by rw [h]

end Generic

section Model

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

omit [Finite G] in
theorem perfect_le_modelToG_pairPerpOf (hq : 4 ≤ Nat.card K) {a b : Fin d}
    (hab : IsHypCoord Q a b) (e : L ≃* matrixProjectiveDerived Q) {H : Subgroup G}
    (hH : ⁅H, H⁆ = H) (hHL : H ≤ L)
    (hHX : H ≤ centralizer (modelToG e (pairTorusOf Q a b) : Set G)) :
    H ≤ modelToG e (pairPerpOf Q a b) := by
  have hle : H ≤ L ⊓ centralizer (modelToG e (pairTorusOf Q a b) : Set G) := le_inf hHL hHX
  rw [UnitaryPilot.inf_centralizer_modelToG, hab.centralizer_pairTorusOf hq,
    UnitaryPilot.modelToG_sup] at hle
  have hXX : modelToG e (pairTorusOf Q a b) ≤
      centralizer (modelToG e (pairTorusOf Q a b) : Set G) :=
    UnitaryPilot.modelToG_le_centralizer e
      (F4Pilot.le_centralizer_self_of_isCyclic hab.isCyclic_pairTorusOf)
  have hXD : modelToG e (pairTorusOf Q a b) ≤
      centralizer (modelToG e (pairPerpOf Q a b) : Set G) :=
    UnitaryPilot.modelToG_le_centralizer e hab.pairTorusOf_le_centralizer_pairPerpOf
  have habel : ∀ x ∈ modelToG e (pairTorusOf Q a b), ∀ y ∈ modelToG e (pairTorusOf Q a b),
      x * y = y * x := fun x hx y hy => mem_centralizer_iff.1 (hXX hy) x hx
  rw [← hH]
  exact (Subgroup.commutator_mono hle hle).trans
    (F4Pilot.commutator_sup_le_of_comm_of_le_normalizer habel
      (hXD.trans (centralizer_le_normalizer _)))

theorem perfect_le_modelToG_stabPairsBar (hq : 4 ≤ Nat.card K) {a a' b b' : Fin d}
    (ha : IsHypCoord Q a a') (hb : IsHypCoord Q b b') (e : L ≃* matrixProjectiveDerived Q)
    (hperf : ⁅stabPairsBar Q a a' b b', stabPairsBar Q a a' b b'⁆ = stabPairsBar Q a a' b b')
    {H : Subgroup G} (hH : ⁅H, H⁆ = H) (hHL : H ≤ L)
    (hHa : H ≤ centralizer (modelToG e (pairTorusOf Q a a') : Set G))
    (hHb : H ≤ centralizer (modelToG e (pairTorusOf Q b b') : Set G)) :
    H ≤ modelToG e (stabPairsBar Q a a' b b') := by
  have hD := perfect_le_modelToG_pairPerpOf hq ha e hH hHL hHa
  rw [← perfectCore_pairPerpOf_inf_centralizer_pairTorusOf hq ha hb hperf,
    ← perfectCore_modelToG_inf_centralizer]
  exact le_perfectCore_of_perfect (le_inf hD hHb) hH

end Model

section Four

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F]

theorem consecutiveBlock_three_zero_two :
    consecutiveBlock (2 + 1) 0 2 = ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin (2 + 1))) := by
  decide

theorem minusNode_le_centralizer_four {β γ : K} {hn : 1 ≤ 2 + 2}
    {e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (2 + 2) K hn β γ)} {ι : K →+* F}
    (C₀ : MinusFieldCover e ι 0) (hF : 4 ≤ Nat.card F)
    (h02 : minusNode C₀ 0 ≤ centralizer (minusNode C₀ 2 : Set G))
    (h03 : minusNode C₀ 0 ≤ centralizer (minusNode C₀ 3 : Set G)) :
    ∀ i j : Fin (2 + 2), i ≠ j → ¬ edgeD (2 + 2) i j → ¬ edgeD (2 + 2) j i →
      minusNode C₀ i ≤ centralizer (minusNode C₀ j : Set G) := by
  have h23 : minusNode C₀ 2 ≤ centralizer (minusNode C₀ 3 : Set G) := by
    rw [minusNode_of_eq C₀ (j := 2) rfl, minusNode_of_eq_succ C₀ (j := 3) rfl]
    exact lift_forkBlock_le_centralizer C₀ le_rfl hF
  intro i j hij h1 h2
  fin_cases i <;> fin_cases j <;> simp_all [edgeD] <;>
    first
    | exact le_centralizer_iff.mp h02
    | exact le_centralizer_iff.mp h03
    | exact le_centralizer_iff.mp h23

theorem fork_conj_commute {β γ : K} {hn : 1 ≤ 2 + 2}
    {e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (2 + 2) K hn β γ)} {ι : K →+* F}
    (C₀ : MinusFieldCover e ι 0) (hF : 4 ≤ Nat.card F) {t : G}
    (htU : (minusNode C₀ 2).map (MulAut.conj t).toMonoidHom = minusNode C₀ 3) :
    ∀ a ∈ minusNode C₀ 2, ∀ b ∈ (minusNode C₀ 2).map (MulAut.conj t).toMonoidHom,
      a * b = b * a := by
  have h23 : minusNode C₀ 2 ≤ centralizer (minusNode C₀ 3 : Set G) := by
    rw [minusNode_of_eq C₀ (j := 2) rfl, minusNode_of_eq_succ C₀ (j := 3) rfl]
    exact lift_forkBlock_le_centralizer C₀ le_rfl hF
  intro a ha b hb
  rw [htU] at hb
  exact (mem_centralizer_iff.1 (h23 ha) b hb).symm

theorem fork_mul_conj_mem (hset : CFSG.EvenSmallLie.StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (hq : 4 ≤ Nat.card K) {β γ : K}
    (hirr : ∀ s : K, s ^ 2 + β * s + γ ≠ 0)
    {e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (2 + 2) K (by omega) β γ)}
    {ι : K →+* F} (C₀ : MinusFieldCover e ι 0) (hF : 4 ≤ Nat.card F) {t : G}
    (ht : orderOf t = 2) (htC : t ∈ centralizer (L : Set G))
    (htU : (minusNode C₀ 2).map (MulAut.conj t).toMonoidHom = minusNode C₀ 3) :
    ∀ a ∈ minusNode C₀ 2, a * (t * a * t⁻¹) ∈ modelToG e (stabPairsBar
      (coordinateQuadMinus (2 + 2) K (by omega) β γ)
      (minusIndexEquiv (2 + 2) (by omega) (.inl ⟨0, by omega⟩))
      (minusIndexEquiv (2 + 2) (by omega) (.inr (.inl ⟨0, by omega⟩)))
      (minusIndexEquiv (2 + 2) (by omega) (.inl ⟨1, by omega⟩))
      (minusIndexEquiv (2 + 2) (by omega) (.inr (.inl ⟨1, by omega⟩)))) := by
  have hn1 : 1 ≤ 2 + 2 := by omega
  set U₂ := minusNode C₀ 2 with hU₂
  set U₃ := minusNode C₀ 3 with hU₃
  have ht2 : t * t = 1 := by
    rw [← _root_.sq, ← ht]
    exact pow_orderOf_eq_one t
  have hAB := fork_conj_commute C₀ hF htU
  have hM2 : U₂ ≤ minusPieceCore e {Fin.last 2} := by
    rw [hU₂, minusNode_of_eq C₀ (j := 2) rfl]
    exact lift_forkBlock_le_minusPieceCore C₀ hF (by omega) (Finset.empty_subset _)
  have hM3 : U₃ ≤ minusPieceCore e {Fin.last 2} := by
    rw [hU₃, minusNode_of_eq_succ C₀ (j := 3) rfl]
    exact lift_forkBlock_le_minusPieceCore C₀ hF (by omega) le_rfl
  obtain ⟨θ, hθ, hθt⟩ := exists_diag_hom_of_conj_swap ht2 hAB
  have : Group.IsPerfect U₂ := Subgroup.isPerfect_iff.mpr (commutator_minusNode C₀ 2)
  have hθperf : ⁅θ.range, θ.range⁆ = θ.range := LinearPilot.commutator_range_eq_self_of_isPerfect θ
  have hθL : θ.range ≤ L := CFSG.SeitzReduction.std_perfect_le hset hOut htC ht hθperf hθt
  have hθM : θ.range ≤ minusPieceCore e {Fin.last 2} := by
    rintro _ ⟨a, rfl⟩
    rw [hθ]
    exact mul_mem (hM2 a.2) (hM3 (htU ▸ ⟨a, a.2, rfl⟩))
  have hX : ∀ k : Fin (2 + 1), k ≠ Fin.last 2 →
      θ.range ≤ centralizer (modelToG e (minusPairTorus hn1 β γ k) : Set G) := by
    intro k hk
    refine hθM.trans ((centralizerPerfectCore_anti (UnitaryPilot.modelToG_mono e
      (minusPairTorus_le_minusPlaneTorus ?_))).trans (centralizerPerfectCore_le_centralizer _))
    simpa using hk
  have hBq := isQuasisimple_minusStabPairsBar_of_four_le (n := 2 + 2) le_rfl hirr
    (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (by simp)
  have hR := perfect_le_modelToG_stabPairsBar hq (isHypCoord_coordinateQuadMinus hn1 β γ _)
    (isHypCoord_coordinateQuadMinus hn1 β γ _) e (Subgroup.isPerfect_iff.mp hBq.1.1) hθperf hθL
    (hX ⟨0, by omega⟩ (by simp [Fin.ext_iff])) (hX ⟨1, by omega⟩ (by simp [Fin.ext_iff]))
  intro a ha
  have h := hR ⟨⟨a, ha⟩, rfl⟩
  rwa [hθ] at h

theorem minusNode_zero_le_centralizer_fork (hset : CFSG.EvenSmallLie.StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) (hq : 4 ≤ Nat.card K) {β γ : K}
    (hirr : ∀ s : K, s ^ 2 + β * s + γ ≠ 0)
    {e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (2 + 2) K (by omega) β γ)}
    {ι : K →+* F} (C₀ : MinusFieldCover e ι 0) (hF : 4 ≤ Nat.card F) {t : G}
    (ht : orderOf t = 2) (htC : t ∈ centralizer (L : Set G))
    (hU0R : minusNode C₀ 0 ≤ centralizer (modelToG e (stabPairsBar
      (coordinateQuadMinus (2 + 2) K (by omega) β γ)
      (minusIndexEquiv (2 + 2) (by omega) (.inl ⟨0, by omega⟩))
      (minusIndexEquiv (2 + 2) (by omega) (.inr (.inl ⟨0, by omega⟩)))
      (minusIndexEquiv (2 + 2) (by omega) (.inl ⟨1, by omega⟩))
      (minusIndexEquiv (2 + 2) (by omega) (.inr (.inl ⟨1, by omega⟩)))) : Set G))
    (htU : (minusNode C₀ 2).map (MulAut.conj t).toMonoidHom = minusNode C₀ 3)
    (hU2s : ∀ N : Subgroup (minusNode C₀ 2), N.Normal → N = ⊥ ∨ N = ⊤) {x : G}
    (hx2 : x ∈ minusNode C₀ 2) (hxU : x ∈ normalizer (minusNode C₀ 0 : Set G)) {a₀ : G}
    (ha₀ : a₀ ∈ minusNode C₀ 2) (hxa₀ : x * a₀ ≠ a₀ * x) :
    minusNode C₀ 0 ≤ centralizer (minusNode C₀ 2 : Set G) ∧
      minusNode C₀ 0 ≤ centralizer (minusNode C₀ 3 : Set G) := by
  have hmain := le_centralizer_of_conj_swap (fork_conj_commute C₀ hF htU) hU2s
    (le_centralizer_iff.mp hU0R) (fork_mul_conj_mem hset hOut hq hirr C₀ hF ht htC htU) hx2 hxU
    ha₀ hxa₀
  rw [htU] at hmain
  exact ⟨le_centralizer_iff.mp hmain.1, le_centralizer_iff.mp hmain.2⟩

theorem minusNode_le_centralizer_four_field (hset : SeitzSetting G L) {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) {β γ : K}
    (hirr : ∀ s : K, s ^ 2 + β * s + γ ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (2 + 2) K (by omega) β γ)) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {ι : K →+* F} {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (P : MinusRootFieldParam (n := 2 + 2) le_rfl hirr e t ι σ ⟨0, by omega⟩ ⟨1, by omega⟩)
    (C₀ : MinusFieldCover e ι 0)
    (htU : (minusNode C₀ 2).map (MulAut.conj t).toMonoidHom = minusNode C₀ 3)
    (hU2s : ∀ N : Subgroup (minusNode C₀ 2), N.Normal → N = ⊥ ∨ N = ⊤) {x : G}
    (hx2 : x ∈ minusNode C₀ 2) (hxU : x ∈ normalizer (minusNode C₀ 0 : Set G)) {a₀ : G}
    (ha₀ : a₀ ∈ minusNode C₀ 2) (hxa₀ : x * a₀ ≠ a₀ * x) :
    ∀ i j : Fin (2 + 2), i ≠ j → ¬ edgeD (2 + 2) i j → ¬ edgeD (2 + 2) j i →
      minusNode C₀ i ≤ centralizer (minusNode C₀ j : Set G) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · rw [pow_zero] at hK; omega
    · exact h
  have hOut : Group.IsSolvable (Outer L) := isSolvable_outer_of_mulEquiv_minus le_rfl hf hK hirr e
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq hKt
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  have hF : 4 ≤ Nat.card F := (LinearPilot.natCard_eq_sq_of_involution ι hσ1 hσσ hfix) ▸
    hq.trans (Nat.le_self_pow two_ne_zero _)
  have hA := minusLevelCore_le_centralizer_field hset le_rfl hK hq hirr e ht hKt
    (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (by simp) hσ1 hσσ hfix P
  have hU0 : minusNode C₀ 0 = minusLevelCore e ({⟨0, by omega⟩, ⟨1, by omega⟩} :
      Finset (Fin (2 + 1))) := by
    rw [minusNode_of_le C₀ (j := 0) (by simp), Fin.val_zero, consecutiveBlock_three_zero_two]
  have hU0R : minusNode C₀ 0 ≤ centralizer (modelToG e (stabPairsBar
      (coordinateQuadMinus (2 + 2) K (by omega) β γ)
      (minusIndexEquiv (2 + 2) (by omega) (.inl ⟨0, by omega⟩))
      (minusIndexEquiv (2 + 2) (by omega) (.inr (.inl ⟨0, by omega⟩)))
      (minusIndexEquiv (2 + 2) (by omega) (.inl ⟨1, by omega⟩))
      (minusIndexEquiv (2 + 2) (by omega) (.inr (.inl ⟨1, by omega⟩)))) : Set G) := by
    rw [hU0]
    exact hA
  obtain ⟨h02, h03⟩ := minusNode_zero_le_centralizer_fork hset.standardSetting hOut hq hirr C₀ hF
    ht htC hU0R htU hU2s hx2 hxU ha₀ hxa₀
  exact minusNode_le_centralizer_four C₀ hF h02 h03

end Four

end CFSG.SeitzReduction.OmegaPilot
