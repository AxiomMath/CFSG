module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightParamLevi
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusEightInputsCover

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup Matrix QuadraticMap
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus
  minusIndexEquiv regular_coordinateQuadMinus)
open CFSG.SeitzReduction.UnitaryPilot (modelToG modelToGEquiv symm_mem_modelToG)
open CFSG.SeitzReduction.SymplecticPilot (liftParam)
open scoped MatrixGroups

section Perp

variable {K : Type} [Field K] {n : ℕ}

theorem frameRootElt_mem_stabSub_minus (hn : 1 ≤ n) (β γ : K) {k p q : Fin (n - 1)}
    (hpq : p ≠ q) (hkp : k ≠ p) (hkq : k ≠ q) (x : K) :
    frameRootElt (coordinateQuadMinus n K hn β γ) (minusFrameLeft hn) (minusFrameRight hn) p q x ∈
      stabSub (minusIndexEquiv n hn (.inl k)) (minusIndexEquiv n hn (.inr (.inl k))) := by
  have h := isHypFrame_minus K hn β γ
  refine ⟨?_, ?_⟩
  · rw [h.frameRootElt_apply hpq]
    have h1 : (Pi.single (minusIndexEquiv n hn (.inl k)) (1 : K) : Fin (2 * n) → K)
        (minusFrameRight hn p) = 0 := Pi.single_eq_of_ne (h.left_ne_right k p).symm _
    have h2 : (Pi.single (minusIndexEquiv n hn (.inl k)) (1 : K) : Fin (2 * n) → K)
        (minusFrameLeft hn q) = 0 := Pi.single_eq_of_ne (fun e => hkq (h.left_injective e).symm) _
    simp [h1, h2]
  · rw [h.frameRootElt_apply hpq]
    have h1 : (Pi.single (minusIndexEquiv n hn (.inr (.inl k))) (1 : K) : Fin (2 * n) → K)
        (minusFrameRight hn p) = 0 :=
      Pi.single_eq_of_ne (fun e => hkp (h.right_injective e).symm) _
    have h2 : (Pi.single (minusIndexEquiv n hn (.inr (.inl k))) (1 : K) : Fin (2 * n) → K)
        (minusFrameLeft hn q) = 0 := Pi.single_eq_of_ne (h.left_ne_right q k) _
    simp [h1, h2]

variable [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem minusRootElt_mem_minusPairPerp (hn : 4 ≤ n) {β γ : K}
    (hirr : ∀ s : K, s ^ 2 + β * s + γ ≠ 0) {k p q : Fin (n - 1)} (hpq : p ≠ q) (hkp : k ≠ p)
    (hkq : k ≠ q) (x : K) :
    minusRootElt hn hirr p q x ∈ minusPairPerp (by omega) β γ k :=
  ⟨_, mem_subgroupOf.2 (frameRootElt_mem_stabSub_minus (by omega) β γ hpq hkp hkq x), rfl⟩

theorem minusPairPerpEquivOfLe_minusRootElt (hn : 4 ≤ n) {β γ : K}
    (hirr : ∀ s : K, s ^ 2 + β * s + γ ≠ 0) (k : Fin (n - 1)) {p' q' : Fin (n - 1 - 1)}
    (hpq' : p' ≠ q') (x : K) :
    ((minusPairPerpEquivOfLe hn hirr k
        ⟨minusRootElt hn hirr (avoid (by omega) k p') (avoid (by omega) k q') x,
          minusRootElt_mem_minusPairPerp hn hirr
            (fun e => hpq' (avoid_injective (by omega) k e)) (avoid_ne (by omega) k p').symm
            (avoid_ne (by omega) k q').symm x⟩ :
        orthDerived (coordinateQuadMinus (n - 1) K (by omega) β γ)) :
        (Fin (2 * (n - 1)) → K) ≃ₗ[K] (Fin (2 * (n - 1)) → K)) =
      frameRootElt (coordinateQuadMinus (n - 1) K (by omega) β γ)
        (minusFrameLeft (n := n - 1) (by omega)) (minusFrameRight (n := n - 1) (by omega)) p' q'
        x := by
  have hn1 : 1 ≤ n := by omega
  have h4 := isHypFrame_minus K hn1 β γ
  have h3 := isHypFrame_minus K (n := n - 1) (by omega) β γ
  have hpq : avoid (by omega) k p' ≠ avoid (M := n - 1 - 1) (by omega) k q' :=
    fun e => hpq' (avoid_injective (by omega) k e)
  refine LinearEquiv.ext fun w => funext fun y => ?_
  rw [minusPairPerpEquivOfLe_apply hn hirr k _
    ⟨frameRootElt (coordinateQuadMinus n K hn1 β γ) (minusFrameLeft hn1) (minusFrameRight hn1)
      (avoid (by omega) k p') (avoid (by omega) k q') x,
      eichler_mem_orthDerived (regular_coordinateQuadMinus n K β γ hn hirr).1
        (regular_coordinateQuadMinus n K β γ hn hirr).2 _ _⟩
    (frameRootElt_mem_stabSub_minus hn1 β γ hpq (avoid_ne (by omega) k p').symm
      (avoid_ne (by omega) k q').symm x) rfl w y]
  change frameRootElt _ _ _ _ _ x _ _ = frameRootElt _ _ _ p' q' x w y
  rw [h4.frameRootElt_apply_coord hpq, h3.frameRootElt_apply_coord hpq']
  have ha : ∀ l : Fin (n - 1 - 1), minusFrameLeft hn1 (avoid (by omega) k l) =
      minusPerpCoord (by omega) k (minusFrameLeft (n := n - 1) (by omega) l) :=
    fun l => (minusPerpCoord_inl (by omega) rfl).symm
  have hb : ∀ l : Fin (n - 1 - 1), minusFrameRight hn1 (avoid (by omega) k l) =
      minusPerpCoord (by omega) k (minusFrameRight (n := n - 1) (by omega) l) :=
    fun l => (minusPerpCoord_inr (by omega) rfl).symm
  rw [ha p', ha q', hb q', hb p']
  simp only [(minusPerpCoord_injective (by omega) k).eq_iff,
    (minusPerpCoord_injective (by omega) k).extend_apply]

end Perp

section Field

theorem map_transvection_eq {R S : Type*} [Field R] [Field S] (f : R →+* S) {ι : Type*}
    [Fintype ι] [DecidableEq ι] {i j : ι} (hij : i ≠ j) (x : R) :
    Matrix.SpecialLinearGroup.map f (Matrix.SpecialLinearGroup.transvection hij x) =
      Matrix.SpecialLinearGroup.transvection hij (f x) := by
  ext a a'
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.map_apply, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply]
  rw [map_add]
  split_ifs <;> simp

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {b c : K}

theorem minusPairPerpFieldEquivOfLe_minusRootElt (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (2 + 2) K (by omega) b c))
    (k : Fin (2 + 1)) {k₀ : Type} [Field k₀] [Finite k₀] [CharP k₀ 2] (φ : K ≃+* k₀)
    (hK : commutator (SpecialLinearGroup (Fin 2) K) = ⊤)
    (hk : commutator (SpecialLinearGroup (Fin 2) k₀) = ⊤) {p' q' : Fin 2} (hpq' : p' ≠ q')
    (x : K)
    (hmem : ((e.symm (minusRootElt (n := 2 + 2) le_rfl hirr (avoid (by omega) k p')
        (avoid (by omega) k q') x) : L) : G) ∈
      ((minusPairPerp (K := K) (n := 2 + 2) (by omega) b c k).map e.symm.toMonoidHom).map
        L.subtype) :
    minusPairPerpFieldEquivOfLe (r := 2) le_rfl hirr e k φ ⟨_, hmem⟩ =
      minusLeviProj (n := 2 + 1) (by omega) (φ b) (φ c) hk
        (Matrix.SpecialLinearGroup.transvection hpq' (-(φ x))) := by
  have hm : minusRootElt (n := 2 + 2) le_rfl hirr (avoid (M := 2) (N := 2 + 1) (by omega) k p')
      (avoid (M := 2) (N := 2 + 1) (by omega) k q') x ∈
        minusPairPerp (K := K) (n := 2 + 2) _ b c k :=
    minusRootElt_mem_minusPairPerp (n := 2 + 2) le_rfl hirr
      (fun e => hpq' (avoid_injective (M := 2) (N := 2 + 1) (by omega) k e))
      (avoid_ne (M := 2) (N := 2 + 1) (by omega) k p').symm
      (avoid_ne (M := 2) (N := 2 + 1) (by omega) k q').symm x
  have h1 : (modelToGEquiv e (minusPairPerp (K := K) (n := 2 + 2) _ b c k)).symm
      ⟨_, hmem⟩ = ⟨_, hm⟩ := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  have hG : frameRootElt (coordinateQuadMinus (2 + 1) K (by omega) b c)
      (minusFrameLeft (n := 2 + 1) (by omega)) (minusFrameRight (n := 2 + 1) (by omega)) p' q' x ∈
        orthDerived (coordinateQuadMinus (2 + 1) K (by omega) b c) := by
    rw [← minusPairPerpEquivOfLe_minusRootElt (n := 2 + 2) le_rfl hirr k hpq' x]
    exact (minusPairPerpEquivOfLe (n := 2 + 2) le_rfl hirr k _).2
  have h2 : minusPairPerpModelEquivOfLe (n := 2 + 2) le_rfl hirr k ⟨_, hm⟩ =
      projHom _ ⟨_, hG⟩ := by
    change projHom _ (minusPairPerpEquivOfLe (n := 2 + 2) le_rfl hirr k ⟨_, hm⟩) = _
    congr 1
    exact Subtype.ext (minusPairPerpEquivOfLe_minusRootElt (n := 2 + 2) le_rfl hirr k hpq' x)
  calc minusPairPerpFieldEquivOfLe (r := 2) le_rfl hirr e k φ ⟨_, hmem⟩
      = minusCongr φ (n := 2 + 1) _ b c (minusPairPerpModelEquivOfLe (n := 2 + 2) le_rfl
          hirr k ((modelToGEquiv e (minusPairPerp (K := K) (n := 2 + 2) _ b c k)).symm
            ⟨_, hmem⟩)) := rfl
    _ = minusCongr φ (n := 2 + 1) _ b c (minusLeviProj (n := 2 + 1) _ b c hK
          (Matrix.SpecialLinearGroup.transvection hpq' (-x))) := by
        rw [h1, h2, projHom_frameRootElt_eq_minusLeviProj]
    _ = _ := by
        rw [minusCongr_minusLeviProj (n := 2 + 1) (by omega) φ b c hK hk, map_transvection_eq,
          RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_neg]

end Field

section Conj

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {r : ℕ} {hn : 1 ≤ r + 2} {b c : K}

theorem conj_of_normalized_minus {M : Type*} [Group M]
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (r + 2) K hn b c)) (k : Fin (r + 1))
    (π : minusNeighbourCore e k →* M)
    (hD : modelToG e (minusPairPerp hn b c k) ≤ minusNeighbourCore e k)
    (δ : (Fin (r + 1) → Kˣ) → M) (hδ : ∀ t, δ (t * (Pi.mulSingle k (t k))⁻¹) = δ t)
    (hnorm : ∀ t : Fin (r + 1) → Kˣ, t k = 1 →
      ∀ hmem : ((e.symm ((isHypFrame_minus K hn b c).frameHom t) : L) : G) ∈
        minusNeighbourCore e k, π ⟨_, hmem⟩ = δ t)
    (t : Fin (r + 1) → Kˣ)
    (hN : ((e.symm ((isHypFrame_minus K hn b c).frameHom t) : L) : G) ∈
      normalizer (minusNeighbourCore e k : Set G)) (x : minusNeighbourCore e k) :
    π ((minusNeighbourCore e k).normalizerMonoidHom ⟨_, hN⟩ x) = δ t * π x * (δ t)⁻¹ := by
  set h := isHypFrame_minus K hn b c
  set c' : Fin (r + 1) → Kˣ := Pi.mulSingle k (t k) with hc'
  set t' : Fin (r + 1) → Kˣ := t * c'⁻¹ with ht'
  have ht'k : t' k = 1 := mul_mulSingle_inv_apply_self k t
  have htt : t = t' * c' := by rw [ht', inv_mul_cancel_right]
  set g' : G := ((e.symm (h.frameHom t') : L) : G) with hg'
  set gc : G := ((e.symm (h.frameHom c') : L) : G) with hgc
  have hgt : ((e.symm (h.frameHom t) : L) : G) = g' * gc := by
    rw [hg', hgc, ← Subgroup.coe_mul, ← map_mul, ← map_mul, ← htt]
  have hgcX : gc ∈ modelToG e (minusPairTorus hn b c k) :=
    symm_mem_modelToG e (frameHom_mulSingle_mem_minusPairTorus (n := r + 2) k (t k))
  have hcomm : ∀ y : minusNeighbourCore e k, (y : G) * gc = gc * y := fun y =>
    (mem_centralizer_iff.1 (F4Pilot.centralizerPerfectCore_le_centralizer _ y.2) gc hgcX).symm
  have hmem : g' ∈ minusNeighbourCore e k :=
    hD (symm_mem_modelToG e (frameHom_mem_minusPairPerp (n := r + 2) ht'k))
  have hval := hnorm t' ht'k hmem
  rw [hδ] at hval
  set y : minusNeighbourCore e k := ⟨g', hmem⟩
  have hconj : (minusNeighbourCore e k).normalizerMonoidHom ⟨_, hN⟩ x = y * x * y⁻¹ := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    change ((e.symm (h.frameHom t) : L) : G) * x * ((e.symm (h.frameHom t) : L) : G)⁻¹ =
      g' * x * g'⁻¹
    rw [hgt, _root_.mul_inv_rev]
    calc g' * gc * ↑x * (gc⁻¹ * g'⁻¹) = g' * (gc * ↑x) * gc⁻¹ * g'⁻¹ := by group
      _ = g' * (↑x * gc) * gc⁻¹ * g'⁻¹ := by rw [hcomm x]
      _ = g' * ↑x * g'⁻¹ := by group
  rw [hconj, map_mul, map_mul, map_inv]
  change π ⟨g', hmem⟩ * π x * (π ⟨g', hmem⟩)⁻¹ = _
  rw [hval]

end Conj

end CFSG.SeitzReduction.OmegaPilot
