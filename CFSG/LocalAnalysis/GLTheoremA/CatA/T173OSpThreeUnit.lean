module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ODefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpThreeLin
public import CFSG.LieType.SeitzGeneration.SpFourMix
public import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeGLCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA
open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.LieType.SeitzGeneration
open Polynomial Module
open scoped commutatorElement

variable {F : Type} [Field F] [Finite F] {ℓ : ℕ}

theorem three_ne_zero_of_charP_two [CharP F 2] : (3 : F) ≠ 0 := by
  intro h
  have h2 : (2 : ℕ) ∣ 3 := (CharP.cast_eq_zero_iff F 2 3).mp h
  norm_num at h2

private theorem add_smul_add_smul_add_smul [CharP F 2] {V : Type} [AddCommGroup V]
    [Module F V] (v x y : V) (a b : F) :
    v + a • x + b • y + (a + b) • (x + y) = v + a • y + b • x := by
  have hss : ∀ (c : F) (z : V), c • z + c • z = 0 := by
    intro c z
    have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    calc c • z + c • z = (2 : F) • (c • z) := (two_smul F (c • z)).symm
      _ = 0 := by rw [h2, zero_smul]
  rw [smul_add, add_smul, add_smul]
  have h : v + a • x + b • y + (a • x + b • x + (a • y + b • y))
      = v + (a • x + a • x) + (b • y + b • y) + (b • x + a • y) := by abel
  rw [h, hss a x, hss b y]
  abel

theorem primaryComponent_sub_one_eq_fixSub {d : ↥(StatedSp ℓ F)} :
    primaryComponent (spEnd d) (X - 1) = CFSG.LieType.SeitzGeneration.fixSub d := by
  rw [primaryComponent, CFSG.LieType.SeitzGeneration.fixSub]
  congr 1
  simp [map_sub, map_one, aeval_X]

theorem primaryComponent_quad_eq_normKer {d : ↥(StatedSp ℓ F)} :
    primaryComponent (spEnd d) (X ^ 2 + X + 1) = CFSG.LieType.SeitzGeneration.normKer d := by
  rw [primaryComponent, CFSG.LieType.SeitzGeneration.normKer]
  congr 1
  simp only [map_add, map_mul, map_pow, map_one, aeval_X, aeval_C, pow_two]
  abel

theorem spEnd_sq_apply_of_mem_primary [CharP F 2] {d : ↥(StatedSp ℓ F)}
    {u : Fin ℓ ⊕ Fin ℓ → F} (hu : u ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1)) :
    spEnd d (spEnd d u) = u + spEnd d u := by
  have hu' : u ∈ CFSG.LieType.SeitzGeneration.normKer d := by
    rwa [← primaryComponent_quad_eq_normKer]
  rw [CFSG.LieType.SeitzGeneration.mem_normKer] at hu'
  have h : spEnd d (spEnd d u) + (u + spEnd d u) = 0 := by
    simpa [add_comm, add_left_comm, add_assoc] using hu'
  have hself : ∀ x : Fin ℓ ⊕ Fin ℓ → F, x + x = 0 := by
    intro x
    have h2F : (2 : F) = 0 := CharP.cast_eq_zero F 2
    calc x + x = (2 : F) • x := (two_smul F x).symm
      _ = 0 := by rw [h2F, zero_smul]
  have hx : -(u + spEnd d u) = u + spEnd d u :=
    neg_eq_of_add_eq_zero_left (hself (u + spEnd d u))
  rw [← hx]
  exact (neg_eq_of_add_eq_zero_left h).symm

theorem spEnd_mem_normKer {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1)
    {u : Fin ℓ ⊕ Fin ℓ → F} (hu : u ∈ CFSG.LieType.SeitzGeneration.normKer d) :
    spEnd d u ∈ CFSG.LieType.SeitzGeneration.normKer d := by
  rw [CFSG.LieType.SeitzGeneration.mem_normKer] at hu ⊢
  rw [spEnd_cube_apply hd3 u]
  have h := congrArg (spEnd d) hu
  simp only [map_add, map_zero] at h
  rw [spEnd_cube_apply hd3 u] at h
  simpa [add_comm, add_left_comm, add_assoc] using h

private theorem aeval_primary_identities [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
    (T : Module.End F V) (hT3 : T ^ 3 = 1) :
    aeval T (X ^ 2 + X + 1 : F[X]) * aeval T (X ^ 2 + X + 1 : F[X]) =
        aeval T (X ^ 2 + X + 1 : F[X]) ∧
      aeval T (X : F[X]) * aeval T (X ^ 2 + X + 1 : F[X]) = aeval T (X ^ 2 + X + 1 : F[X]) ∧
      aeval T (X ^ 2 + X + 1 : F[X]) + aeval T (X ^ 2 + X : F[X]) = 1 ∧
      aeval T (X ^ 2 + X + 1 : F[X]) * aeval T (X ^ 2 + X : F[X]) = 0 := by
  have h2poly : (2 : F[X]) = 0 := by
    have h2F : (2 : F) = 0 := CharP.cast_eq_zero F 2
    calc (2 : F[X]) = algebraMap F F[X] (2 : F) := (map_ofNat _ 2).symm
      _ = 0 := by rw [h2F, map_zero]
  have hp1 : (X ^ 2 + X + 1 : F[X]) * (X ^ 2 + X + 1) =
      (X ^ 2 + X + 1) + (X ^ 3 - 1) * X := by
    have h : (X ^ 2 + X + 1 : F[X]) * (X ^ 2 + X + 1) =
        (X ^ 2 + X + 1) + (X ^ 3 - 1) * X + 2 * (X ^ 3 + X ^ 2 + X) := by ring
    rw [h, h2poly, zero_mul, add_zero]
  have hp2 : (X ^ 2 + X + 1 : F[X]) + (X ^ 2 + X) = 1 := by
    have h : (X ^ 2 + X + 1 : F[X]) + (X ^ 2 + X) = 1 + 2 * (X ^ 2 + X) := by ring
    rw [h, h2poly, zero_mul, add_zero]
  have hp3 : (X ^ 2 + X + 1 : F[X]) * (X ^ 2 + X) = (X ^ 3 - 1) * X := by
    have h : (X ^ 2 + X + 1 : F[X]) * (X ^ 2 + X) =
        (X ^ 3 - 1) * X + 2 * (X ^ 3 + X ^ 2 + X) := by ring
    rw [h, h2poly, zero_mul, add_zero]
  have hp4 : (X : F[X]) * (X ^ 2 + X + 1) = (X ^ 2 + X + 1) + (X ^ 3 - 1) := by ring
  have hzero : aeval T (X ^ 3 - 1 : F[X]) = 0 := by
    simp [map_sub, map_pow, map_one, aeval_X, hT3]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← map_mul, hp1, map_add, map_mul, hzero, zero_mul, add_zero]
  · rw [← map_mul, hp4, map_add, hzero, add_zero]
  · rw [← map_add, hp2, map_one]
  · rw [← map_mul, hp3, map_mul, hzero, zero_mul]

theorem split_primary [CharP F 2] {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1)
    (v : Fin ℓ ⊕ Fin ℓ → F) :
    ((spEnd d) ^ 2 + spEnd d + 1 : Module.End F (Fin ℓ ⊕ Fin ℓ → F)) v ∈
        primaryComponent (spEnd d) (X - 1) ∧
    ((spEnd d) ^ 2 + spEnd d : Module.End F (Fin ℓ ⊕ Fin ℓ → F)) v ∈
        primaryComponent (spEnd d) (X ^ 2 + X + 1) ∧
    v = ((spEnd d) ^ 2 + spEnd d + 1 : Module.End F (Fin ℓ ⊕ Fin ℓ → F)) v +
        ((spEnd d) ^ 2 + spEnd d : Module.End F (Fin ℓ ⊕ Fin ℓ → F)) v := by
  set T := spEnd d
  have hT3 : T ^ 3 = 1 := spEnd_pow hd3
  obtain ⟨he1', hTe1', hsum', hprod'⟩ := aeval_primary_identities T hT3
  have he1eq : aeval T (X ^ 2 + X + 1 : F[X]) = T ^ 2 + T + 1 := by
    simp only [map_add, map_mul, map_pow, map_one, aeval_X, aeval_C, pow_two]
  have he3eq : aeval T (X ^ 2 + X : F[X]) = T ^ 2 + T := by
    simp only [map_add, map_mul, map_pow, map_one, aeval_X, aeval_C, pow_two]
  have he1 : (T ^ 2 + T + 1) * (T ^ 2 + T + 1) = T ^ 2 + T + 1 := by
    rw [← he1eq]
    exact he1'
  have hX : aeval T (X : F[X]) = T := by simp
  have hTe1 : T * (T ^ 2 + T + 1) = T ^ 2 + T + 1 := by
    have h1 : T * (T ^ 2 + T + 1) =
        aeval T (X : F[X]) * aeval T ((X : F[X]) ^ 2 + X + 1) := by
      rw [hX, he1eq]
    rw [h1, hTe1', he1eq]
  have hsum : (T ^ 2 + T + 1) + (T ^ 2 + T) = 1 := by
    rw [← he1eq, ← he3eq]
    exact hsum'
  have hprod : (T ^ 2 + T + 1) * (T ^ 2 + T) = 0 := by
    rw [← he1eq, ← he3eq]
    exact hprod'
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_primaryComponent]
    rw [show aeval T (X - 1 : F[X]) = T - 1 from by simp [map_sub, map_one, aeval_X]]
    change (T - 1 : Module.End F (Fin ℓ ⊕ Fin ℓ → F))
      ((T ^ 2 + T + 1 : Module.End F (Fin ℓ ⊕ Fin ℓ → F)) v) = 0
    rw [LinearMap.sub_apply, ← Module.End.mul_apply, hTe1, Module.End.one_apply, sub_self]
  · rw [mem_primaryComponent]
    rw [show aeval T (X ^ 2 + X + 1 : F[X]) = T ^ 2 + T + 1 from he1eq]
    change (T ^ 2 + T + 1 : Module.End F (Fin ℓ ⊕ Fin ℓ → F))
      ((T ^ 2 + T : Module.End F (Fin ℓ ⊕ Fin ℓ → F)) v) = 0
    rw [← Module.End.mul_apply, hprod, LinearMap.zero_apply]
  · rw [← LinearMap.add_apply, hsum, Module.End.one_apply]

private theorem nondegenerate_primary [CharP F 2] {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1)
    {f : F[X]} (hf : f = X - 1 ∨ f = X ^ 2 + X + 1) :
    ((spForm ℓ F).restrict (primaryComponent (spEnd d) f)).Nondegenerate := by
  rcases hf with rfl | rfl
  · rw [primaryComponent_sub_one_eq_fixSub]
    exact nondegenerate_fixSub (three_ne_zero_of_charP_two) hd3
  · rw [primaryComponent_quad_eq_normKer]
    exact nondegenerate_normKer (three_ne_zero_of_charP_two) hd3

theorem exists_spForm_eq_one_of_mem_primary [CharP F 2] (hF : Nat.card F = 2)
    {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1) {f : F[X]}
    (hf : f = X - 1 ∨ f = X ^ 2 + X + 1) {r : Fin ℓ ⊕ Fin ℓ → F}
    (hr : r ∈ primaryComponent (spEnd d) f) (hr0 : r ≠ 0) :
    ∃ x ∈ primaryComponent (spEnd d) f, spForm ℓ F r x = 1 := by
  have hnd := nondegenerate_primary hd3 hf
  have hex : ∃ x ∈ primaryComponent (spEnd d) f, spForm ℓ F r x ≠ 0 := by
    by_contra h
    push Not at h
    exact hr0 (congrArg Subtype.val (hnd.1 ⟨r, hr⟩ fun x => h x x.2))
  obtain ⟨x, hx, hx0⟩ := hex
  refine ⟨(spForm ℓ F r x)⁻¹ • x, (primaryComponent (spEnd d) f).smul_mem _ hx, ?_⟩
  rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hx0]

@[expose] noncomputable def unitTransv (d : ↥(StatedSp ℓ F))
    (u : Fin ℓ ⊕ Fin ℓ → F) : ↥(StatedSp ℓ F) :=
  spTransvection u (1 : F) * spTransvection (spEnd d u) (1 : F) *
    spTransvection (u + spEnd d u) (1 : F)

private theorem unitTransv_eq_mixElt [CharP F 2] {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1)
    {u : Fin ℓ ⊕ Fin ℓ → F} (hu : u ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1)) :
    unitTransv d u = mixElt d u 1 := by
  unfold unitTransv mixElt
  rw [spEnd_sq_apply_of_mem_primary hu]

theorem spEnd_unitTransv [CharP F 2] {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1)
    {u : Fin ℓ ⊕ Fin ℓ → F} (hu : u ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1))
    (hQ : spForm ℓ F u (spEnd d u) = 0) (v : Fin ℓ ⊕ Fin ℓ → F) :
    spEnd (unitTransv d u) v =
      v + spForm ℓ F v u • spEnd d u + spForm ℓ F v (spEnd d u) • u := by
  rw [unitTransv_eq_mixElt hd3 hu, spEnd_mixElt hd3 hQ 1 v,
    spEnd_sq_apply_of_mem_primary hu, map_add]
  simpa only [one_mul] using
    (add_smul_add_smul_add_smul (V := Fin ℓ ⊕ Fin ℓ → F) v u (spEnd d u)
      (spForm ℓ F v u) (spForm ℓ F v (spEnd d u)))

private theorem unitTransv_sq [CharP F 2] {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1)
    {u : Fin ℓ ⊕ Fin ℓ → F} (hu : u ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1))
    (hQ : spForm ℓ F u (spEnd d u) = 0) : unitTransv d u ^ 2 = 1 := by
  rw [unitTransv_eq_mixElt hd3 hu]
  obtain ⟨h13, h23⟩ := mixElt_orth hd3 hQ
  have k12 : Commute (spTransvection u (1 : F)) (spTransvection (spEnd d u) (1 : F)) :=
    spTransvection_comm_of_form_eq_zero hQ 1 1
  have k13 : Commute (spTransvection u (1 : F))
      (spTransvection (spEnd d (spEnd d u)) (1 : F)) :=
    spTransvection_comm_of_form_eq_zero h13 1 1
  have k23 : Commute (spTransvection (spEnd d u) (1 : F))
      (spTransvection (spEnd d (spEnd d u)) (1 : F)) :=
    spTransvection_comm_of_form_eq_zero h23 1 1
  have hT : ∀ w : Fin ℓ ⊕ Fin ℓ → F,
      spTransvection w (1 : F) ^ 2 = 1 := by
    intro w
    rw [sq]
    apply spLin_injective
    rw [map_mul, map_one, spLin_spTransvection,
      CFSG.ClassicalGroups.Alternating.symplecticTransvection_mul]
    have h2 : (1 : F) + 1 = 0 := by
      have h2F : (2 : F) = 0 := CharP.cast_eq_zero F 2
      calc (1 : F) + 1 = 2 := by norm_num
        _ = 0 := h2F
    rw [h2]
    exact CFSG.ClassicalGroups.Alternating.symplecticTransvection_zero
      (B := spForm ℓ F) spForm_isAlt w
  unfold mixElt
  rw [(k13.mul_left k23).mul_pow, k12.mul_pow, hT, hT, hT, one_mul, one_mul]

private lemma unitTransv_mem_aux [CharP F 2] (hF : Nat.card F = 2) {d : ↥(StatedSp ℓ F)}
    (hd3 : d ^ 3 = 1) {u : Fin ℓ ⊕ Fin ℓ → F}
    (hu : u ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1))
    (hQ : spForm ℓ F u (spEnd d u) = 0) :
    unitTransv d u ∈ spSupported d {X ^ 2 + X + 1} := by
  have hcomm : unitTransv d u * d = d * unitTransv d u := by
    rw [unitTransv_eq_mixElt hd3 hu]
    exact mixElt_comm hd3 hQ 1
  have hfix : ∀ k ∈ primaryFactors (spEnd d), k ∉ ({X ^ 2 + X + 1} : Set F[X]) →
      ∀ v ∈ primaryComponent (spEnd d) k, spEnd (unitTransv d u) v = v := by
    intro k hk hkO v hv
    have hmin : minpoly F (spEnd d) ∣ (X ^ 3 - C 1 : F[X]) := by
      refine minpoly.dvd F (spEnd d) ?_
      simp [map_sub, map_pow, aeval_X, spEnd_pow hd3]
    obtain ⟨hkirr, hkmon, hkdvd⟩ := mem_primaryFactors.mp hk
    have hcases :=
      CFSG.HardMathSupport.Curtis.Coordinator.eq_X_sub_one_or_eq_quad_of_dvd hF hkirr hkmon
        (hkdvd.trans hmin)
    have hk1 : k = X - 1 := by
      rcases hcases with h | h
      · simpa using h
      · exact absurd h hkO
    have hv1 : v ∈ CFSG.LieType.SeitzGeneration.fixSub d := by
      rw [← primaryComponent_sub_one_eq_fixSub, ← hk1]
      exact hv
    have hu3 : u ∈ CFSG.LieType.SeitzGeneration.normKer d := by
      rwa [← primaryComponent_quad_eq_normKer]
    have hdu3 : spEnd d u ∈ CFSG.LieType.SeitzGeneration.normKer d := spEnd_mem_normKer hd3 hu3
    have hvu : spForm ℓ F v u = 0 := spForm_fixSub_normKer (three_ne_zero_of_charP_two) d hv1 hu3
    have hvd : spForm ℓ F v (spEnd d u) = 0 :=
      spForm_fixSub_normKer (three_ne_zero_of_charP_two) d hv1 hdu3
    rw [spEnd_unitTransv hd3 hu hQ v, hvu, hvd, zero_smul, zero_smul, add_zero, add_zero]
  rw [mem_spSupported]
  exact ⟨hcomm, hfix⟩

private lemma unitTransv_ratio_of_eq_one [CharP F 2] (hF : Nat.card F = 2)
    {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1) {u : Fin ℓ ⊕ Fin ℓ → F}
    (hu : u ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1))
    (hQ : spForm ℓ F u (spEnd d u) = 0) (hu0 : u ≠ 0)
    (h1 : unitTransv d u = 1) :
    ∃ c : F, spEnd d u = c • u ∧ c ^ 2 + c + 1 = 0 := by
  have hrel : ∀ v, spForm ℓ F v u • spEnd d u + spForm ℓ F v (spEnd d u) • u = 0 := by
    intro v
    have hv := spEnd_unitTransv hd3 hu hQ v
    rw [h1, spEnd_one, Module.End.one_apply] at hv
    have hva : v + (spForm ℓ F v u • spEnd d u +
        spForm ℓ F v (spEnd d u) • u) = v + 0 := by
      rw [add_zero]
      calc v + (spForm ℓ F v u • spEnd d u + spForm ℓ F v (spEnd d u) • u)
          = (v + spForm ℓ F v u • spEnd d u) + spForm ℓ F v (spEnd d u) • u := by abel
        _ = v := hv.symm
    exact add_left_cancel hva
  obtain ⟨v, hv⟩ : ∃ v, spForm ℓ F v u ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (spForm_nondegenerate.2 u fun v => h v)
  have hvu : spForm ℓ F v u = 1 := by
    rcases CFSG.HardMathSupport.Curtis.Coordinator.eq_zero_or_eq_one_of_card_eq_two hF
      (spForm ℓ F v u) with h0 | h0
    · exact absurd h0 hv
    · exact h0
  set c := spForm ℓ F v (spEnd d u) with hc
  have hrelv := hrel v
  rw [hvu, one_smul] at hrelv
  have hdu : spEnd d u = c • u := by
    have h2 : c • u + c • u = 0 := by
      have h2F : (2 : F) = 0 := CharP.cast_eq_zero F 2
      calc c • u + c • u = (2 : F) • (c • u) := (two_smul F (c • u)).symm
        _ = 0 := by rw [h2F, zero_smul]
    calc spEnd d u = spEnd d u + (c • u + c • u) := by rw [h2, add_zero]
      _ = (spEnd d u + c • u) + c • u := by abel
      _ = c • u := by rw [hrelv]; simp
  have hc0 : c ^ 2 + c + 1 = 0 := by
    have hu' : u ∈ CFSG.LieType.SeitzGeneration.normKer d := by
      rwa [← primaryComponent_quad_eq_normKer]
    rw [CFSG.LieType.SeitzGeneration.mem_normKer] at hu'
    have hdu2 : spEnd d (spEnd d u) = c ^ 2 • u := by
      rw [hdu, map_smul, hdu, smul_smul, pow_two]
    rw [hdu2, hdu] at hu'
    have hzero : (c ^ 2 + c + 1) • u = 0 := by
      linear_combination (norm := module) hu'
    exact (smul_eq_zero.mp hzero).resolve_right hu0
  exact ⟨c, hdu, hc0⟩

private lemma unitTransv_ne_one [CharP F 2] (hF : Nat.card F = 2) {d : ↥(StatedSp ℓ F)}
    (hd3 : d ^ 3 = 1) {u : Fin ℓ ⊕ Fin ℓ → F}
    (hu : u ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1))
    (hQ : spForm ℓ F u (spEnd d u) = 0) (hu0 : u ≠ 0) : unitTransv d u ≠ 1 := by
  intro h1
  obtain ⟨c, hdu, hc0⟩ := unitTransv_ratio_of_eq_one hF hd3 hu hQ hu0 h1
  rcases CFSG.HardMathSupport.Curtis.Coordinator.eq_zero_or_eq_one_of_card_eq_two hF c with
    hc0' | hc0'
  · rw [hc0'] at hc0
    norm_num at hc0
  · rw [hc0'] at hc0
    norm_num at hc0
    exact three_ne_zero_of_charP_two hc0

theorem unitTransv_mem [CharP F 2] (hF : Nat.card F = 2) {d : ↥(StatedSp ℓ F)}
    (hd3 : d ^ 3 = 1) {u : Fin ℓ ⊕ Fin ℓ → F}
    (hu : u ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1))
    (hQ : spForm ℓ F u (spEnd d u) = 0) :
    unitTransv d u ∈ spSupported d {X ^ 2 + X + 1} ∧ unitTransv d u ^ 2 = 1 ∧
      (u ≠ 0 → unitTransv d u ≠ 1) :=
  ⟨unitTransv_mem_aux hF hd3 hu hQ, unitTransv_sq hd3 hu hQ,
    fun hu0 => unitTransv_ne_one hF hd3 hu hQ hu0⟩

private theorem spEnd_mem_primary_and_isotropic [CharP F 2] {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1)
    {u : Fin ℓ ⊕ Fin ℓ → F} (hu : u ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1))
    (hQ : spForm ℓ F u (spEnd d u) = 0) :
    spEnd d u ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1) ∧
      spForm ℓ F (spEnd d u) (spEnd d (spEnd d u)) = 0 := by
  refine ⟨apply_mem_primaryComponent (Commute.refl (spEnd d)) hu, ?_⟩
  rw [spEnd_sq_apply_of_mem_primary hu, map_add, spForm_isAlt.self_eq_zero, add_zero,
    ← spForm_isAlt.neg_eq u, hQ, neg_zero]

private theorem unitTransv_shift [CharP F 2] {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1)
    {u : Fin ℓ ⊕ Fin ℓ → F} (hu : u ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1))
    (hQ : spForm ℓ F u (spEnd d u) = 0) :
    unitTransv d (spEnd d u) = unitTransv d u := by
  obtain ⟨hdu3, hQdu⟩ := spEnd_mem_primary_and_isotropic hd3 hu hQ
  have hss : spEnd d u + spEnd d u = 0 := by
    have h2F : (2 : F) = 0 := CharP.cast_eq_zero F 2
    calc spEnd d u + spEnd d u = (2 : F) • spEnd d u := (two_smul F (spEnd d u)).symm
      _ = 0 := by rw [h2F, zero_smul]
  have hsum : spEnd d u + (u + spEnd d u) = u := by
    rw [show spEnd d u + (u + spEnd d u) = (spEnd d u + spEnd d u) + u by abel, hss, zero_add]
  unfold unitTransv
  rw [spEnd_sq_apply_of_mem_primary hu, hsum]
  have k12 : Commute (spTransvection (spEnd d u) (1 : F)) (spTransvection u (1 : F)) :=
    spTransvection_comm_of_form_eq_zero
      (by rw [← spForm_isAlt.neg_eq u, hQ, neg_zero]) 1 1
  have k13 : Commute (spTransvection (spEnd d u) (1 : F))
      (spTransvection (u + spEnd d u) (1 : F)) :=
    spTransvection_comm_of_form_eq_zero
      (by rw [map_add, ← spForm_isAlt.neg_eq u, hQ, neg_zero, spForm_isAlt.self_eq_zero,
        zero_add]) 1 1
  have k12u : Commute (spTransvection u (1 : F))
      (spTransvection (spEnd d u) (1 : F)) :=
    spTransvection_comm_of_form_eq_zero hQ 1 1
  have k13u : Commute (spTransvection u (1 : F))
      (spTransvection (u + spEnd d u) (1 : F)) :=
    spTransvection_comm_of_form_eq_zero
      (by rw [map_add, spForm_isAlt.self_eq_zero, hQ, add_zero]) 1 1
  have hc : Commute (spTransvection u (1 : F))
      (spTransvection (spEnd d u) (1 : F) * spTransvection (u + spEnd d u) (1 : F)) :=
    k12u.mul_right k13u
  simpa only [mul_assoc] using hc.eq.symm

private theorem conj_unitTransv {x d : ↥(StatedSp ℓ F)} (hxd : x * d = d * x)
    (u : Fin ℓ ⊕ Fin ℓ → F) :
    x * unitTransv d u * x⁻¹ = unitTransv d (spEnd x u) := by
  have hcomm : spEnd x * spEnd d = spEnd d * spEnd x := by
    have h := congrArg spEnd hxd
    rwa [spEnd_mul, spEnd_mul] at h
  have hxdu : spEnd x (spEnd d u) = spEnd d (spEnd x u) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, hcomm]
  unfold unitTransv
  calc x * (spTransvection u (1 : F) * spTransvection (spEnd d u) (1 : F) *
        spTransvection (u + spEnd d u) (1 : F)) * x⁻¹
      = (x * spTransvection u (1 : F) * x⁻¹) * (x * spTransvection (spEnd d u) (1 : F) * x⁻¹) *
        (x * spTransvection (u + spEnd d u) (1 : F) * x⁻¹) := by group
    _ = spTransvection (spEnd x u) (1 : F) * spTransvection (spEnd x (spEnd d u)) (1 : F) *
        spTransvection (spEnd x (u + spEnd d u)) (1 : F) := by
        rw [CFSG.RankThree.PartOne.CTP.spTransvection_conj,
          CFSG.RankThree.PartOne.CTP.spTransvection_conj,
          CFSG.RankThree.PartOne.CTP.spTransvection_conj]
    _ = spTransvection (spEnd x u) (1 : F) * spTransvection (spEnd d (spEnd x u)) (1 : F) *
        spTransvection (spEnd x u + spEnd d (spEnd x u)) (1 : F) := by
        rw [map_add, hxdu]

theorem commute_unitTransv [CharP F 2] {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1)
    {u : Fin ℓ ⊕ Fin ℓ → F} (hu : u ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1))
    (hQ : spForm ℓ F u (spEnd d u) = 0) {x : ↥(StatedSp ℓ F)} (hxd : x * d = d * x)
    {j : ℕ} (hxu : spEnd x u = spEnd (d ^ j) u) :
    x * unitTransv d u = unitTransv d u * x := by
  have hconj : x * unitTransv d u * x⁻¹ = unitTransv d u := by
    rw [conj_unitTransv hxd u, hxu, pow_eq_pow_mod j hd3]
    have h3 : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases h3 with h | h | h
    · rw [h, pow_zero, spEnd_one, Module.End.one_apply]
    · rw [h, pow_one]
      exact unitTransv_shift hd3 hu hQ
    · rw [h, show (2 : ℕ) = 1 + 1 by norm_num, pow_add, pow_one, spEnd_mul,
        Module.End.mul_apply]
      exact (unitTransv_shift hd3 (spEnd_mem_primary_and_isotropic hd3 hu hQ).1
        (spEnd_mem_primary_and_isotropic hd3 hu hQ).2).trans (unitTransv_shift hd3 hu hQ)
  exact mul_inv_eq_iff_eq_mul.mp hconj

private theorem eq_of_spEnd_eq_of_apply {g h : ↥(StatedSp ℓ F)}
    (hgh : ∀ v, spEnd g v = spEnd h v) : g = h :=
  spLin_injective (Units.ext (LinearMap.ext hgh))

private theorem char_two_rotation_vector [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
    (a b : F) (z w dw : V) :
    z + a • dw + (a + b) • (w + dw) = z + (a + b) • w + b • dw := by
  have hss : a + a = 0 := by
    have h2F : (2 : F) = 0 := CharP.cast_eq_zero F 2
    calc a + a = (2 : F) * a := by ring
      _ = 0 := by rw [h2F, zero_mul]
  have hcoef : a + (a + b) = b := by
    calc a + (a + b) = (a + a) + b := by abel
      _ = b := by rw [hss, zero_add]
  calc z + a • dw + (a + b) • (w + dw)
      = z + a • dw + ((a + b) • w + (a + b) • dw) := by rw [smul_add]
    _ = z + (a + b) • w + (a • dw + (a + b) • dw) := by abel
    _ = z + (a + b) • w + (a + (a + b)) • dw := by rw [← add_smul]
    _ = z + (a + b) • w + b • dw := by rw [hcoef]

private lemma rotation_comm_d [CharP F 2] {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1)
    {w : Fin ℓ ⊕ Fin ℓ → F} (hw : w ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1))
    (hQ : spForm ℓ F w (spEnd d w) = 1) :
    (⁅spTransvection w (1 : F), spTransvection (spEnd d w) (1 : F)⁆ : ↥(StatedSp ℓ F)) * d =
      d * ⁅spTransvection w (1 : F), spTransvection (spEnd d w) (1 : F)⁆ := by
  set y : ↥(StatedSp ℓ F) := ⁅spTransvection w (1 : F), spTransvection (spEnd d w) (1 : F)⁆
  have hy : ∀ z, spEnd y z = z + spForm ℓ F z w • w +
      (spForm ℓ F z w + spForm ℓ F z (spEnd d w)) • spEnd d w :=
    fun z => spEnd_commutator_transvection hQ z
  have hcomm : y * d = d * y := by
    apply eq_of_spEnd_eq_of_apply
    intro z
    rw [spEnd_mul, spEnd_mul, Module.End.mul_apply, Module.End.mul_apply, hy, hy,
      map_add, map_add, map_smul, map_smul, spEnd_sq_apply_of_mem_primary hw]
    have hd2 : spEnd (d ^ 2) (spEnd d z) = z := by
      rw [pow_two, spEnd_mul, Module.End.mul_apply, spEnd_cube_apply hd3 z]
    have hB1 : spForm ℓ F (spEnd d z) w =
        spForm ℓ F z w + spForm ℓ F z (spEnd d w) := by
      have hd2w : spEnd (d ^ 2) w = w + spEnd d w := by
        rw [pow_two, spEnd_mul, Module.End.mul_apply, spEnd_sq_apply_of_mem_primary hw]
      have h := CFSG.RankThree.PartOne.CTP.spEnd_isometry (d ^ 2) (spEnd d z) w
      rw [hd2, hd2w, map_add] at h
      exact h.symm
    have hB2 : spForm ℓ F (spEnd d z) (spEnd d w) = spForm ℓ F z w :=
      CFSG.RankThree.PartOne.CTP.spEnd_isometry d z w
    have hb : (spForm ℓ F z w + spForm ℓ F z (spEnd d w)) + spForm ℓ F z w =
        spForm ℓ F z (spEnd d w) := by
      have hss : spForm ℓ F z w + spForm ℓ F z w = 0 := by
        have h2F : (2 : F) = 0 := CharP.cast_eq_zero F 2
        calc spForm ℓ F z w + spForm ℓ F z w = (2 : F) • spForm ℓ F z w :=
              (two_smul F (spForm ℓ F z w)).symm
          _ = 0 := by rw [h2F, zero_smul]
      calc (spForm ℓ F z w + spForm ℓ F z (spEnd d w)) + spForm ℓ F z w
          = (spForm ℓ F z w + spForm ℓ F z w) + spForm ℓ F z (spEnd d w) := by abel
        _ = spForm ℓ F z (spEnd d w) := by rw [hss, zero_add]
    rw [hB1, hB2, hb]
    exact (char_two_rotation_vector (spForm ℓ F z w) (spForm ℓ F z (spEnd d w))
      (spEnd d z) w (spEnd d w)).symm

  exact hcomm

private lemma rotation_fix_other [CharP F 2] (hF : Nat.card F = 2) {d : ↥(StatedSp ℓ F)}
    (hd3 : d ^ 3 = 1) {w : Fin ℓ ⊕ Fin ℓ → F}
    (hw : w ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1))
    (hQ : spForm ℓ F w (spEnd d w) = 1) :
    ∀ k ∈ primaryFactors (spEnd d), k ∉ ({X ^ 2 + X + 1} : Set F[X]) →
      ∀ v ∈ primaryComponent (spEnd d) k,
        spEnd (⁅spTransvection w (1 : F), spTransvection (spEnd d w) (1 : F)⁆) v = v := by
  set y : ↥(StatedSp ℓ F) := ⁅spTransvection w (1 : F), spTransvection (spEnd d w) (1 : F)⁆
  have hy : ∀ z, spEnd y z = z + spForm ℓ F z w • w +
      (spForm ℓ F z w + spForm ℓ F z (spEnd d w)) • spEnd d w :=
    fun z => spEnd_commutator_transvection hQ z
  have hfix : ∀ k ∈ primaryFactors (spEnd d), k ∉ ({X ^ 2 + X + 1} : Set F[X]) →
      ∀ v ∈ primaryComponent (spEnd d) k, spEnd y v = v := by
    intro k hk hkO v hv
    have hmin : minpoly F (spEnd d) ∣ (X ^ 3 - C 1 : F[X]) := by
      refine minpoly.dvd F (spEnd d) ?_
      simp [map_sub, map_pow, aeval_X, spEnd_pow hd3]
    obtain ⟨hkirr, hkmon, hkdvd⟩ := mem_primaryFactors.mp hk
    have hcases :=
      CFSG.HardMathSupport.Curtis.Coordinator.eq_X_sub_one_or_eq_quad_of_dvd hF hkirr hkmon
        (hkdvd.trans hmin)
    have hk1 : k = X - 1 := by
      rcases hcases with h | h
      · simpa using h
      · exact absurd h hkO
    have hv1 : v ∈ CFSG.LieType.SeitzGeneration.fixSub d := by
      rw [← primaryComponent_sub_one_eq_fixSub, ← hk1]
      exact hv
    have hw3 : w ∈ CFSG.LieType.SeitzGeneration.normKer d := by
      rwa [← primaryComponent_quad_eq_normKer]
    have hdw3 : spEnd d w ∈ CFSG.LieType.SeitzGeneration.normKer d :=
      spEnd_mem_normKer hd3 hw3
    have hvw : spForm ℓ F v w = 0 :=
      spForm_fixSub_normKer (three_ne_zero_of_charP_two) d hv1 hw3
    have hvdw : spForm ℓ F v (spEnd d w) = 0 :=
      spForm_fixSub_normKer (three_ne_zero_of_charP_two) d hv1 hdw3
    rw [hy v, hvw, hvdw]
    simp

  exact hfix

theorem rotation_mem_spSupported_unitary [CharP F 2] (hF : Nat.card F = 2)
    {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1) {w : Fin ℓ ⊕ Fin ℓ → F}
    (hw : w ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1))
    (hQ : spForm ℓ F w (spEnd d w) = 1) :
    ⁅spTransvection w (1 : F), spTransvection (spEnd d w) (1 : F)⁆ ∈
      spSupported d {X ^ 2 + X + 1} := by
  rw [mem_spSupported]
  exact ⟨rotation_comm_d hd3 hw hQ, rotation_fix_other hF hd3 hw hQ⟩

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
