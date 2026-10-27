module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2SwapGen
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2SwapFrame

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Module
open CFSG.ClassicalGroups.Orthogonal
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)

section Overlap

variable {Y : Type*} [Group Y] [Finite Y]

theorem perfectCore_inf_sup_eq {A Xb Db : Subgroup Y} (hXab : ∀ x ∈ Xb, ∀ y ∈ Xb, x * y = y * x)
    (hXN : Xb ≤ normalizer (Db : Set Y)) (hperf : ⁅A ⊓ Db, A ⊓ Db⁆ = A ⊓ Db) :
    perfectCore (A ⊓ (Xb ⊔ Db)) = A ⊓ Db := by
  apply le_antisymm
  · set H := A ⊓ (Xb ⊔ Db) with hH
    have hcomm : ⁅H, H⁆ ≤ A ⊓ Db := by
      refine le_inf ((Subgroup.commutator_mono inf_le_left inf_le_left).trans
        (Subgroup.commutator_le.2 fun x hx y hy => mul_mem (mul_mem (mul_mem hx hy)
          (inv_mem hx)) (inv_mem hy))) ?_
      exact (Subgroup.commutator_mono inf_le_right inf_le_right).trans
        (F4Pilot.commutator_sup_le_of_comm_of_le_normalizer hXab hXN)
    have hpc := CFSG.Quasithin.perfectCore_perfect H
    rw [← hpc]
    exact (Subgroup.commutator_mono (perfectCore_le H) (perfectCore_le H)).trans hcomm
  · exact CFSG.Quasithin.le_perfectCore_of_perfect (inf_le_inf_left _ le_sup_right) hperf

end Overlap

section Frame

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

structure AnisoTriangleData (Q : QuadraticForm K (Fin d → K)) (u u' : Fin d) (c : K)
    (p p' r r' : Fin d → K) : Prop where
  perp_p : p ∈ perpSub K u u'
  perp_p' : p' ∈ perpSub K u u'
  perp_r : r ∈ perpSub K u u'
  perp_r' : r' ∈ perpSub K u u'
  map_p : Q p = 1
  map_p' : Q p' = c
  map_r : Q r = 1
  map_r' : Q r' = c
  polar_pp : polar Q p p' = 1
  polar_rr : polar Q r r' = 1
  pr : polar Q p r = 0
  pr' : polar Q p r' = 0
  p'r : polar Q p' r = 0
  p'r' : polar Q p' r' = 0

@[expose] def triVec (p p' r r' eu eu' : Fin d → K) : Fin 3 → Bool → Fin d → K :=
  fun i s => cond s (![p, r, eu] i) (![p', r', eu'] i)

@[simp] theorem triVec_zero_true (p p' r r' eu eu' : Fin d → K) :
    triVec p p' r r' eu eu' 0 true = p := rfl
@[simp] theorem triVec_zero_false (p p' r r' eu eu' : Fin d → K) :
    triVec p p' r r' eu eu' 0 false = p' := rfl
@[simp] theorem triVec_one_true (p p' r r' eu eu' : Fin d → K) :
    triVec p p' r r' eu eu' 1 true = r := rfl
@[simp] theorem triVec_one_false (p p' r r' eu eu' : Fin d → K) :
    triVec p p' r r' eu eu' 1 false = r' := rfl
@[simp] theorem triVec_two_true (p p' r r' eu eu' : Fin d → K) :
    triVec p p' r r' eu eu' 2 true = eu := rfl
@[simp] theorem triVec_two_false (p p' r r' eu eu' : Fin d → K) :
    triVec p p' r r' eu eu' 2 false = eu' := rfl

theorem IsAnisoCoord.polar_of_mem_perpSub {u u' : Fin d} {c : K} (hW : IsAnisoCoord Q u u' 1 c)
    {x : Fin d → K} (hx : x ∈ perpSub K u u') :
    polar Q x (Pi.single u 1) = 0 ∧ polar Q x (Pi.single u' 1) = 0 := by
  rw [polar_comm, hW.polar_left, polar_comm, hW.polar_right, hx.1, hx.2, mul_zero]
  exact ⟨rfl, rfl⟩

theorem IsAnisoCoord.polar_single_single {u u' : Fin d} {c : K} (hW : IsAnisoCoord Q u u' 1 c) :
    polar Q (Pi.single u 1) (Pi.single u' 1) = 1 := by
  rw [hW.polar_left, Pi.single_eq_same, mul_one]

theorem AnisoTriangleData.orthPairTriple {u u' : Fin d} {c : K} (hW : IsAnisoCoord Q u u' 1 c)
    {p p' r r' : Fin d → K} (hA : AnisoTriangleData Q u u' c p p' r r') :
    OrthPairTriple Q (triVec p p' r r' (Pi.single u 1) (Pi.single u' 1)) := by
  obtain ⟨hpu, hpu'⟩ := hW.polar_of_mem_perpSub hA.perp_p
  obtain ⟨hp'u, hp'u'⟩ := hW.polar_of_mem_perpSub hA.perp_p'
  obtain ⟨hru, hru'⟩ := hW.polar_of_mem_perpSub hA.perp_r
  obtain ⟨hr'u, hr'u'⟩ := hW.polar_of_mem_perpSub hA.perp_r'
  have c1 := polar_comm Q p r
  have c2 := polar_comm Q p r'
  have c3 := polar_comm Q p' r
  have c4 := polar_comm Q p' r'
  have c5 := polar_comm Q p (Pi.single u 1)
  have c6 := polar_comm Q p (Pi.single u' 1)
  have c7 := polar_comm Q p' (Pi.single u 1)
  have c8 := polar_comm Q p' (Pi.single u' 1)
  have c9 := polar_comm Q r (Pi.single u 1)
  have c10 := polar_comm Q r (Pi.single u' 1)
  have c11 := polar_comm Q r' (Pi.single u 1)
  have c12 := polar_comm Q r' (Pi.single u' 1)
  refine ⟨fun i => ?_, fun i j hij s t => ?_⟩
  · fin_cases i
    · exact hA.polar_pp
    · exact hA.polar_rr
    · exact hW.polar_single_single
  · fin_cases i <;> fin_cases j <;> cases s <;> cases t <;>
      simp_all [triVec, hA.pr, hA.pr', hA.p'r, hA.p'r']

theorem swapTriangleFrame_of_planes (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {u u' : Fin d} {c : K} (hW : IsAnisoCoord Q u u' 1 c) {p p' r r' : Fin d → K}
    (hA : AnisoTriangleData Q u u' c p p' r r') (P : HypPair Q)
    (hPe : ∀ i s, polar Q (triVec p p' r r' (Pi.single u 1) (Pi.single u' 1) i s) P.e = 0)
    (hPf : ∀ i s, polar Q (triVec p p' r r' (Pi.single u 1) (Pi.single u' 1) i s) P.f = 0)
    {w : Fin d → K} (hw0 : w ≠ 0)
    (hwv : ∀ i s, polar Q (triVec p p' r r' (Pi.single u 1) (Pi.single u' 1) i s) w = 0)
    (hwe : polar Q P.e w = 0) (hwf : polar Q P.f w = 0)
    (hq : CFSG.IsQuasisimple (fixVecBar Q {p, p', r, r'}) ∧
      center (fixVecBar Q {p, p', r, r'}) = ⊥) :
    SwapTriangleFrame (anisoTorusOf Q hW.ne 1 c) (pairPerpOf Q u u') := by
  have : Finite (matrixProjectiveDerived Q) := by
    have : Finite (GL (Fin d) K) := inferInstance
    infer_instance
  set eu : Fin d → K := Pi.single u 1 with heu
  set eu' : Fin d → K := Pi.single u' 1 with heu'
  set v := triVec p p' r r' eu eu' with hv
  have hO : OrthPairTriple Q v := hA.orthPairTriple hW
  have hinjρ := projHom_injective (Q := Q) hW.exists_ne_zero
  obtain ⟨hpu, hpu'⟩ := hW.polar_of_mem_perpSub hA.perp_p
  obtain ⟨hp'u, hp'u'⟩ := hW.polar_of_mem_perpSub hA.perp_p'
  obtain ⟨hru, hru'⟩ := hW.polar_of_mem_perpSub hA.perp_r
  obtain ⟨hr'u, hr'u'⟩ := hW.polar_of_mem_perpSub hA.perp_r'
  have hS₀ : PlaneSwapData Q eu eu' p p' :=
    ⟨by rw [hW.map_left, hA.map_p], by rw [hW.map_right, hA.map_p'], hW.polar_single_single,
      hA.polar_pp, by rw [polar_comm, hpu], by rw [polar_comm, hp'u], by rw [polar_comm, hpu'],
      by rw [polar_comm, hp'u']⟩
  have hS₁ : PlaneSwapData Q eu eu' r r' :=
    ⟨by rw [hW.map_left, hA.map_r], by rw [hW.map_right, hA.map_r'], hW.polar_single_single,
      hA.polar_rr, by rw [polar_comm, hru], by rw [polar_comm, hr'u], by rw [polar_comm, hru'],
      by rw [polar_comm, hr'u']⟩
  set E₀ : orthDerived Q := ⟨eichler Q (eu + p) (eu' + p'), eichler_mem_orthDerived hQ hT _ _⟩
    with hE₀
  set E₁ : orthDerived Q := ⟨eichler Q (eu + r) (eu' + r'), eichler_mem_orthDerived hQ hT _ _⟩
    with hE₁
  have a₀u : (E₀ : (Fin d → K) ≃ₗ[K] (Fin d → K)) eu = p := hS₀.eichler_left
  have a₀u' : (E₀ : (Fin d → K) ≃ₗ[K] (Fin d → K)) eu' = p' := hS₀.eichler_left'
  have a₀p : (E₀ : (Fin d → K) ≃ₗ[K] (Fin d → K)) p = eu := hS₀.eichler_right
  have a₀p' : (E₀ : (Fin d → K) ≃ₗ[K] (Fin d → K)) p' = eu' := hS₀.eichler_right'
  have a₀r : (E₀ : (Fin d → K) ≃ₗ[K] (Fin d → K)) r = r :=
    PlaneSwapData.eichler_of_perp hru hru' (by rw [polar_comm]; exact hA.pr)
      (by rw [polar_comm]; exact hA.p'r)
  have a₀r' : (E₀ : (Fin d → K) ≃ₗ[K] (Fin d → K)) r' = r' :=
    PlaneSwapData.eichler_of_perp hr'u hr'u' (by rw [polar_comm]; exact hA.pr')
      (by rw [polar_comm]; exact hA.p'r')
  have a₁u : (E₁ : (Fin d → K) ≃ₗ[K] (Fin d → K)) eu = r := hS₁.eichler_left
  have a₁u' : (E₁ : (Fin d → K) ≃ₗ[K] (Fin d → K)) eu' = r' := hS₁.eichler_left'
  have a₁r : (E₁ : (Fin d → K) ≃ₗ[K] (Fin d → K)) r = eu := hS₁.eichler_right
  have a₁r' : (E₁ : (Fin d → K) ≃ₗ[K] (Fin d → K)) r' = eu' := hS₁.eichler_right'
  have a₁p : (E₁ : (Fin d → K) ≃ₗ[K] (Fin d → K)) p = p :=
    PlaneSwapData.eichler_of_perp hpu hpu' hA.pr hA.pr'
  have a₁p' : (E₁ : (Fin d → K) ≃ₗ[K] (Fin d → K)) p' = p' :=
    PlaneSwapData.eichler_of_perp hp'u hp'u' hA.p'r hA.p'r'
  set Eo : Fin 3 → orthDerived Q := ![E₀, E₁, 1] with hEo
  set g : Fin 3 → matrixProjectiveDerived Q := fun a => projHom Q (Eo a) with hg
  set X := anisoTorusOf Q hW.ne 1 c with hXdef
  set D := pairPerpOf Q u u' with hDdef
  have himg : ∀ a, (Eo a : (Fin d → K) ≃ₗ[K] (Fin d → K)) '' {eu, eu'} = pairSet v a := by
    intro a
    fin_cases a
    · change (E₀ : (Fin d → K) ≃ₗ[K] (Fin d → K)) '' {eu, eu'} = {p, p'}
      rw [Set.image_pair, a₀u, a₀u']
    · change (E₁ : (Fin d → K) ≃ₗ[K] (Fin d → K)) '' {eu, eu'} = {r, r'}
      rw [Set.image_pair, a₁u, a₁u']
    · change ((1 : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) '' {eu, eu'} = {eu, eu'}
      rw [Set.image_pair]
      rfl
  have hD : ∀ a, D.map (MulAut.conj (g a)).toMonoidHom = fixVecBar Q (pairSet v a) := by
    intro a
    rw [hDdef, pairPerpOf_eq_fixVecBar, map_conj_fixVecBar, himg]
  have hX : ∀ a, X.map (MulAut.conj (g a)).toMonoidHom ≤
      fixVecBar Q ((Eo a : (Fin d → K) ≃ₗ[K] (Fin d → K)) ''
        (perpSub K u u' : Set (Fin d → K))) := by
    intro a
    rw [← map_conj_fixVecBar]
    exact map_mono (anisoTorusOf_le_fixVecBar hW.ne 1 c)
  have hsub : ∀ a b, a ≠ b → pairSet v a ⊆
      (Eo b : (Fin d → K) ≃ₗ[K] (Fin d → K)) '' (perpSub K u u' : Set (Fin d → K)) := by
    intro a b hab
    fin_cases a <;> fin_cases b
    · exact absurd rfl hab
    · rintro x (rfl | rfl)
      exacts [⟨_, hA.perp_p, a₁p⟩, ⟨_, hA.perp_p', a₁p'⟩]
    · rintro x (rfl | rfl)
      exacts [⟨_, hA.perp_p, rfl⟩, ⟨_, hA.perp_p', rfl⟩]
    · rintro x (rfl | rfl)
      exacts [⟨_, hA.perp_r, a₀r⟩, ⟨_, hA.perp_r', a₀r'⟩]
    · exact absurd rfl hab
    · rintro x (rfl | rfl)
      exacts [⟨_, hA.perp_r, rfl⟩, ⟨_, hA.perp_r', rfl⟩]
    · rintro x (rfl | rfl)
      exacts [⟨_, hA.perp_p, a₀p⟩, ⟨_, hA.perp_p', a₀p'⟩]
    · rintro x (rfl | rfl)
      exacts [⟨_, hA.perp_r, a₁r⟩, ⟨_, hA.perp_r', a₁r'⟩]
    · exact absurd rfl hab
  have hXD : ∀ a b : Fin 3, a ≠ b →
      X.map (MulAut.conj (g b)).toMonoidHom ≤ D.map (MulAut.conj (g a)).toMonoidHom :=
    fun a b hab => (hX b).trans (by rw [hD a]; exact fixVecBar_anti (hsub a b hab))
  have hC : ∀ b, centralizer (X.map (MulAut.conj (g b)).toMonoidHom : Set _) =
      X.map (MulAut.conj (g b)).toMonoidHom ⊔ D.map (MulAut.conj (g b)).toMonoidHom := by
    intro b
    rw [← F4Pilot.map_centralizer_mulEquiv, hXdef, hW.centralizer_anisoTorusOf hQ hT,
      Subgroup.map_sup]
  have hcommX : ∀ b, ∀ x ∈ X.map (MulAut.conj (g b)).toMonoidHom,
      ∀ y ∈ X.map (MulAut.conj (g b)).toMonoidHom, x * y = y * x := by
    intro b x hx y hy
    have hle : X.map (MulAut.conj (g b)).toMonoidHom ≤
        centralizer (X.map (MulAut.conj (g b)).toMonoidHom : Set _) := by
      rw [← F4Pilot.map_centralizer_mulEquiv]
      exact map_mono hW.anisoTorusOf_le_centralizer_self
    exact mem_centralizer_iff.1 (hle hy) x hx
  have hNX : ∀ b, X.map (MulAut.conj (g b)).toMonoidHom ≤
      normalizer (D.map (MulAut.conj (g b)).toMonoidHom : Set _) := by
    intro b
    refine le_trans ?_ (centralizer_le_normalizer _)
    rw [← F4Pilot.map_centralizer_mulEquiv]
    exact map_mono hW.anisoTorusOf_le_centralizer_pairPerpOf
  have hP0 : pairSet v 0 = {p, p'} := rfl
  have hP1 : pairSet v 1 = {r, r'} := rfl
  have hP2 : pairSet v 2 = {eu, eu'} := rfl
  have himg02 : (E₁ : (Fin d → K) ≃ₗ[K] (Fin d → K)) '' (pairSet v 0 ∪ pairSet v 1) =
      pairSet v 0 ∪ pairSet v 2 := by
    rw [hP0, hP1, hP2, Set.image_union, Set.image_pair, Set.image_pair, a₁p, a₁p', a₁r, a₁r']
  have himg12 : (E₀ : (Fin d → K) ≃ₗ[K] (Fin d → K)) '' (pairSet v 0 ∪ pairSet v 1) =
      pairSet v 1 ∪ pairSet v 2 := by
    rw [hP0, hP1, hP2, Set.image_union, Set.image_pair, Set.image_pair, a₀p, a₀p', a₀r, a₀r',
      Set.union_comm]
  have hconjq : ∀ (x : matrixProjectiveDerived Q) (H : Subgroup (matrixProjectiveDerived Q)),
      CFSG.IsQuasisimple H ∧ center H = ⊥ →
        CFSG.IsQuasisimple (H.map (MulAut.conj x).toMonoidHom) ∧
          center (H.map (MulAut.conj x).toMonoidHom) = ⊥ := by
    intro x H h
    have e := H.equivMapOfInjective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective
    exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e h.1, F4Pilot.center_eq_bot_congr e h.2⟩
  have hq01 : CFSG.IsQuasisimple (fixVecBar Q (pairSet v 0 ∪ pairSet v 1)) ∧
      center (fixVecBar Q (pairSet v 0 ∪ pairSet v 1)) = ⊥ := by
    rw [hP0, hP1, Set.insert_union, Set.singleton_union]
    exact hq
  have hqs : ∀ a b : Fin 3, a < b →
      CFSG.IsQuasisimple (fixVecBar Q (pairSet v a ∪ pairSet v b)) ∧
        center (fixVecBar Q (pairSet v a ∪ pairSet v b)) = ⊥ := by
    intro a b hab
    fin_cases a <;> fin_cases b
    · exact absurd hab (by decide)
    · exact hq01
    · have h := hconjq (projHom Q E₁) _ hq01
      rwa [map_conj_fixVecBar, himg02] at h
    · exact absurd hab (by decide)
    · exact absurd hab (by decide)
    · have h := hconjq (projHom Q E₀) _ hq01
      rwa [map_conj_fixVecBar, himg12] at h
    · exact absurd hab (by decide)
    · exact absurd hab (by decide)
    · exact absurd hab (by decide)
  have hov : ∀ a b : Fin 3, a < b →
      triOverlap X D (g a) (g b) = fixVecBar Q (pairSet v a ∪ pairSet v b) := by
    intro a b hab
    have hDD : D.map (MulAut.conj (g a)).toMonoidHom ⊓ D.map (MulAut.conj (g b)).toMonoidHom =
        fixVecBar Q (pairSet v a ∪ pairSet v b) := by
      rw [hD a, hD b, fixVecBar_inf hW.exists_ne_zero]
    rw [triOverlap, hC b, perfectCore_inf_sup_eq (hcommX b) (hNX b)
      (by rw [hDD]; exact Subgroup.isPerfect_iff.mp (hqs a b hab).1.1), hDD]
  set E₂ : orthDerived Q := ⟨eichler Q P.e w, eichler_mem_orthDerived hQ hT _ _⟩ with hE₂
  have hE₂fix : ∀ a b, (E₂ : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈
      fixVecSub (pairSet v a ∪ pairSet v b) := by
    intro a b
    refine eichler_mem_fixVecSub ?_ ?_
    · rintro y ((rfl | rfl) | (rfl | rfl)) <;> exact hPe _ _
    · rintro y ((rfl | rfl) | (rfl | rfl)) <;> exact hwv _ _
  have hE₂ne : E₂ ≠ 1 := by
    intro h1
    have hf : (E₂ : (Fin d → K) ≃ₗ[K] (Fin d → K)) P.f = P.f := by rw [h1]; rfl
    change eichler Q P.e w P.f = P.f at hf
    rw [eichler_apply P.Q_e hwe, P.polar_fe, hwf, one_smul, zero_add, mul_one] at hf
    have h2 : w - Q w • P.e = 0 := by
      have h3 : P.f + (w - Q w • P.e) = P.f + 0 := by
        rw [add_zero, ← add_sub_assoc]
        exact hf
      exact add_left_cancel h3
    have h3 : w = Q w • P.e := sub_eq_zero.1 h2
    have h4 : Q w = 0 := by
      have h5 := hwf
      rw [h3, polar_smul_right, P.polar_fe, smul_eq_mul, mul_one] at h5
      exact h5
    exact hw0 (by rw [h3, h4, zero_smul])
  have hq1 : projHom Q E₂ ≠ 1 := fun h => hE₂ne (hinjρ (h.trans (map_one _).symm))
  have hgen := hO.fixVecBar_sup_eq_top hQ hT P hPe hPf
  refine ⟨g, hXD, fun a b hab => ?_, ⟨projHom Q E₂, hq1, fun a b hab => ?_⟩, ?_⟩
  · rw [hov a b hab]
    exact ⟨isSimpleGroup_of_isQuasisimple_of_center_eq_bot (hqs a b hab).1 (hqs a b hab).2,
      (hqs a b hab).2⟩
  · rw [hov a b hab]
    exact ⟨E₂, mem_subgroupOf.2 (hE₂fix a b), rfl⟩
  · rw [hov 0 1 (by decide), hov 0 2 (by decide), hov 1 2 (by decide)]
    exact hgen

end Frame

end CFSG.SeitzReduction.OmegaPilot
