module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpThreeUnit
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpThreeLin

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA
open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.LieType.SeitzGeneration
open Polynomial Module
open scoped commutatorElement

variable {F : Type} [Field F] [Finite F] {ℓ : ℕ}

theorem spForm_add_add_self [CharP F 2] {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1)
    {u v : Fin ℓ ⊕ Fin ℓ → F}
    (hu : u ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1))
    (hv : v ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1)) :
    spForm ℓ F (u + v) (spEnd d (u + v)) =
      spForm ℓ F u (spEnd d u) + spForm ℓ F v (spEnd d v) + spForm ℓ F u v := by
  have hvu : spForm ℓ F v (spEnd d u) =
      spForm ℓ F u v + spForm ℓ F u (spEnd d v) := by
    have hd2u : spEnd (d ^ 2) (spEnd d u) = u := by
      have h : spEnd (d ^ 2) = spEnd d * spEnd d := by rw [pow_two, spEnd_mul]
      rw [h, Module.End.mul_apply, spEnd_cube_apply hd3 u]
    have hd2v : spEnd (d ^ 2) v = spEnd d (spEnd d v) := by
      rw [pow_two, spEnd_mul, Module.End.mul_apply]
    have h := CFSG.RankThree.PartOne.CTP.spEnd_isometry (d ^ 2) v (spEnd d u)
    rw [hd2u, hd2v, spEnd_sq_apply_of_mem_primary hv] at h
    rw [map_add, LinearMap.add_apply, ← spForm_isAlt.neg_eq u v,
      ← spForm_isAlt.neg_eq u (spEnd d v), CharTwo.neg_eq,
      CharTwo.neg_eq] at h
    exact h.symm
  have hself : spForm ℓ F u (spEnd d v) + spForm ℓ F u (spEnd d v) = 0 := by
    have h2F : (2 : F) = 0 := CharP.cast_eq_zero F 2
    calc spForm ℓ F u (spEnd d v) + spForm ℓ F u (spEnd d v)
        = (2 : F) * spForm ℓ F u (spEnd d v) := by ring
      _ = 0 := by rw [h2F, zero_mul]
  simp only [map_add, LinearMap.add_apply, hvu]
  linear_combination (norm := abel) hself

private lemma three_independent_vectors_of_three_le [CharP F 2]
    {Y : Submodule F (Fin ℓ ⊕ Fin ℓ → F)} (h3 : 3 ≤ finrank F Y) :
    ∃ v : Fin 3 → Fin ℓ ⊕ Fin ℓ → F,
      (∀ i, v i ∈ Y) ∧ LinearIndependent F v ∧
      (∀ i, v i ∈ Submodule.span F (Set.range v)) := by
  classical
  let b : Basis (Fin (finrank F Y)) F Y := Module.finBasis F Y
  have hliY : LinearIndependent F b := b.linearIndependent
  have hliV : LinearIndependent F (fun i => ((b i : Y) : Fin ℓ ⊕ Fin ℓ → F)) :=
    hliY.map' (Submodule.subtype Y) (by
      rw [Submodule.eq_bot_iff]
      intro x hx
      exact Subtype.ext (by simpa using hx))
  let e : Fin 3 → Fin (finrank F Y) := Fin.castLE h3
  have he : Function.Injective e := fun a c hac => by
    apply Fin.ext
    simpa [e] using congrArg Fin.val hac
  let v : Fin 3 → Fin ℓ ⊕ Fin ℓ → F := fun i => ((b (e i) : Y) : Fin ℓ ⊕ Fin ℓ → F)
  have hli3 : LinearIndependent F v := hliV.comp e he
  have hvY : ∀ i, v i ∈ Y := fun i => (b (e i)).2
  have hmem : ∀ i, v i ∈ Submodule.span F (Set.range v) := fun i =>
    Submodule.subset_span ⟨i, rfl⟩
  exact ⟨v, hvY, hli3, hmem⟩

private lemma partial_sums_ne_zero [CharP F 2] {v : Fin 3 → Fin ℓ ⊕ Fin ℓ → F}
    (hli : LinearIndependent F v) :
    v 0 + v 1 ≠ 0 ∧ v 0 + v 2 ≠ 0 ∧ v 1 + v 2 ≠ 0 ∧ v 0 + (v 1 + v 2) ≠ 0 := by
  have hneg : ∀ x : Fin ℓ ⊕ Fin ℓ → F, -x = x := by
    intro x
    have h2F : (2 : F) = 0 := CharP.cast_eq_zero F 2
    have h : x + x = 0 := by
      calc x + x = (2 : F) • x := (two_smul F x).symm
        _ = 0 := by rw [h2F, zero_smul]
    exact neg_eq_of_add_eq_zero_left h
  have h01ne : v 0 + v 1 ≠ 0 := by
    intro h
    have h' := eq_neg_of_add_eq_zero_left h
    rw [hneg] at h'
    exact (by decide : (0 : Fin 3) ≠ 1) (hli.injective h')
  have h02ne : v 0 + v 2 ≠ 0 := by
    intro h
    have h' := eq_neg_of_add_eq_zero_left h
    rw [hneg] at h'
    exact (by decide : (0 : Fin 3) ≠ 2) (hli.injective h')
  have h12ne : v 1 + v 2 ≠ 0 := by
    intro h
    have h' := eq_neg_of_add_eq_zero_left h
    rw [hneg] at h'
    exact (by decide : (1 : Fin 3) ≠ 2) (hli.injective h')
  have h03ne : v 0 + (v 1 + v 2) ≠ 0 := by
    intro h
    have h' : (∑ i : Fin 3, (1 : F) • v i) = 0 := by
      simpa [Fin.sum_univ_three, add_assoc] using h
    have hc := (Fintype.linearIndependent_iff.mp hli) (fun _ => (1 : F)) h' 0
    exact one_ne_zero hc
  exact ⟨h01ne, h02ne, h12ne, h03ne⟩

private lemma isotropic_pairings_eq_one [CharP F 2] {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1)
    {v : Fin 3 → Fin ℓ ⊕ Fin ℓ → F}
    (hvY : ∀ i, v i ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1))
    (hli : LinearIndependent F v)
    (hmem : ∀ i, v i ∈ Submodule.span F (Set.range v))
    (hQeq : ∀ u ∈ Submodule.span F (Set.range v), u ≠ 0 →
      spForm ℓ F u (spEnd d u) = 1)
    (h01ne : v 0 + v 1 ≠ 0) (h02ne : v 0 + v 2 ≠ 0) (h12ne : v 1 + v 2 ≠ 0) :
    spForm ℓ F (v 0) (v 1) = 1 ∧ spForm ℓ F (v 0) (v 2) = 1 ∧
      spForm ℓ F (v 1) (v 2) = 1 ∧
      spForm ℓ F (v 1 + v 2) (spEnd d (v 1 + v 2)) = 1 + 1 + 1 := by
  have h2F : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h11 : (1 : F) + 1 = 0 := by
    calc (1 : F) + 1 = 2 := by norm_num
      _ = 0 := h2F
  have hv0 : spForm ℓ F (v 0) (spEnd d (v 0)) = 1 := hQeq _ (hmem 0) (hli.ne_zero 0)
  have hv1 : spForm ℓ F (v 1) (spEnd d (v 1)) = 1 := hQeq _ (hmem 1) (hli.ne_zero 1)
  have hv2 : spForm ℓ F (v 2) (spEnd d (v 2)) = 1 := hQeq _ (hmem 2) (hli.ne_zero 2)
  have h01 : spForm ℓ F (v 0) (v 1) = 1 := by
    have hQsum := spForm_add_add_self hd3 (hvY 0) (hvY 1)
    rw [hv0, hv1] at hQsum
    have hq := hQeq _ (Submodule.add_mem _ (hmem 0) (hmem 1)) h01ne
    rw [hq, h11, zero_add] at hQsum
    exact hQsum.symm
  have h02 : spForm ℓ F (v 0) (v 2) = 1 := by
    have hQsum := spForm_add_add_self hd3 (hvY 0) (hvY 2)
    rw [hv0, hv2] at hQsum
    have hq := hQeq _ (Submodule.add_mem _ (hmem 0) (hmem 2)) h02ne
    rw [hq, h11, zero_add] at hQsum
    exact hQsum.symm
  have h12 : spForm ℓ F (v 1) (v 2) = 1 := by
    have hQsum := spForm_add_add_self hd3 (hvY 1) (hvY 2)
    rw [hv1, hv2] at hQsum
    have hq := hQeq _ (Submodule.add_mem _ (hmem 1) (hmem 2)) h12ne
    rw [hq, h11, zero_add] at hQsum
    exact hQsum.symm
  have hQ12 : spForm ℓ F (v 1 + v 2) (spEnd d (v 1 + v 2)) = 1 + 1 + 1 := by
    have hQsum := spForm_add_add_self hd3 (hvY 1) (hvY 2)
    rw [hv1, hv2, h12] at hQsum
    exact hQsum
  exact ⟨h01, h02, h12, hQ12⟩

private lemma isotropic_contradiction [CharP F 2] (hF : Nat.card F = 2)
    {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1) {v : Fin 3 → Fin ℓ ⊕ Fin ℓ → F}
    (hvY : ∀ i, v i ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1))
    (hY : Submodule.span F (Set.range v) ≤ primaryComponent (spEnd d) (X ^ 2 + X + 1))
    (hmem : ∀ i, v i ∈ Submodule.span F (Set.range v))
    (hQeq : ∀ u ∈ Submodule.span F (Set.range v), u ≠ 0 →
      spForm ℓ F u (spEnd d u) = 1)
    (h03ne : v 0 + (v 1 + v 2) ≠ 0)
    (hv0 : spForm ℓ F (v 0) (spEnd d (v 0)) = 1)
    (h01 : spForm ℓ F (v 0) (v 1) = 1) (h02 : spForm ℓ F (v 0) (v 2) = 1)
    (hQ12 : spForm ℓ F (v 1 + v 2) (spEnd d (v 1 + v 2)) = 1 + 1 + 1) : False := by
  have hsum12 : v 1 + v 2 ∈ Submodule.span F (Set.range v) :=
    Submodule.add_mem _ (hmem 1) (hmem 2)
  have hQ3 := spForm_add_add_self hd3 (hvY 0) (hY hsum12)
  rw [hQ12] at hQ3
  conv_rhs at hQ3 => rw [map_add]
  rw [h01, h02] at hQ3
  have hq := hQeq (v 0 + (v 1 + v 2))
    (Submodule.add_mem _ (hmem 0) hsum12) h03ne
  rw [hQ3] at hq
  have h2F : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h11 : (1 : F) + 1 = 0 := by
    calc (1 : F) + 1 = 2 := by norm_num
      _ = 0 := h2F
  have h111 : (1 : F) + 1 + 1 = 1 := by rw [h11, zero_add]
  simp [h11, h111] at hq
  rw [hq] at hv0
  exact one_ne_zero hv0.symm


theorem exists_isotropic_of_three_le [CharP F 2] (hF : Nat.card F = 2)
    {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1)
    {Y : Submodule F (Fin ℓ ⊕ Fin ℓ → F)}
    (hY : Y ≤ primaryComponent (spEnd d) (X ^ 2 + X + 1)) (h3 : 3 ≤ finrank F Y) :
    ∃ u ∈ Y, u ≠ 0 ∧ spForm ℓ F u (spEnd d u) = 0 := by
  obtain ⟨v, hvY, hli, hmem⟩ := three_independent_vectors_of_three_le h3
  obtain ⟨h01ne, h02ne, h12ne, h03ne⟩ := partial_sums_ne_zero hli
  let Z : Submodule F (Fin ℓ ⊕ Fin ℓ → F) := Submodule.span F (Set.range v)
  have hZle : Z ≤ Y := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact hvY i
  by_contra hcon
  push Not at hcon
  have hQ : ∀ u ∈ Z, u ≠ 0 → spForm ℓ F u (spEnd d u) ≠ 0 :=
    fun u hu hu0 => hcon u (hZle hu) hu0
  have hQeq : ∀ u ∈ Z, u ≠ 0 → spForm ℓ F u (spEnd d u) = 1 := by
    intro u hu hu0
    rcases CFSG.HardMathSupport.Curtis.Coordinator.eq_zero_or_eq_one_of_card_eq_two hF
      (spForm ℓ F u (spEnd d u)) with h | h
    · exact absurd h (hQ u hu hu0)
    · exact h
  have hv0 : spForm ℓ F (v 0) (spEnd d (v 0)) = 1 := hQeq _ (hmem 0) (hli.ne_zero 0)
  obtain ⟨h01, h02, h12, hQ12⟩ :=
    isotropic_pairings_eq_one hd3 (fun i => hY (hvY i)) hli hmem hQeq h01ne h02ne h12ne
  exact isotropic_contradiction hF hd3 (fun i => hY (hvY i))
    (fun z hz => hY (hZle hz)) hmem hQeq h03ne hv0 h01 h02 hQ12

theorem exists_isotropic_partner [CharP F 2] {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1)
    {r : Fin ℓ ⊕ Fin ℓ → F} (hr : r ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1))
    (hr0 : r ≠ 0) (hQ : spForm ℓ F r (spEnd d r) = 0) :
    ∃ r' ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1),
      spForm ℓ F r r' = 1 ∧ spForm ℓ F r' (spEnd d r') = 0 := by
  have hnd : ((spForm ℓ F).restrict (CFSG.LieType.SeitzGeneration.normKer d)).Nondegenerate :=
    nondegenerate_normKer (three_ne_zero_of_charP_two) hd3
  have hr3 : r ∈ CFSG.LieType.SeitzGeneration.normKer d := by
    rwa [← primaryComponent_quad_eq_normKer]
  have hex : ∃ x ∈ CFSG.LieType.SeitzGeneration.normKer d, spForm ℓ F r x ≠ 0 := by
    by_contra h
    push Not at h
    exact hr0 (congrArg Subtype.val (hnd.1 ⟨r, hr3⟩ fun x => h x x.2))
  obtain ⟨x, hx, hx0⟩ := hex
  set x' : Fin ℓ ⊕ Fin ℓ → F := (spForm ℓ F r x)⁻¹ • x with hx'def
  have hxpc : x ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1) := by
    rwa [primaryComponent_quad_eq_normKer]
  have hx'mem : x' ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1) :=
    (primaryComponent (spEnd d) (X ^ 2 + X + 1)).smul_mem _ hxpc
  have hBx' : spForm ℓ F r x' = 1 := by
    rw [hx'def, map_smul, smul_eq_mul, inv_mul_cancel₀ hx0]
  have hBx'r : spForm ℓ F x' r = 1 := by
    rw [← spForm_isAlt.neg_eq r x', hBx']
    exact CharTwo.neg_eq 1
  set c : F := spForm ℓ F x' (spEnd d x') with hc
  have hcr_mem : c • r ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1) :=
    (primaryComponent (spEnd d) (X ^ 2 + X + 1)).smul_mem _ hr
  refine ⟨x' + c • r, ?_, ?_, ?_⟩
  · exact (primaryComponent (spEnd d) (X ^ 2 + X + 1)).add_mem hx'mem hcr_mem
  · rw [map_add, hBx', map_smul, spForm_isAlt.self_eq_zero, smul_eq_mul, mul_zero, add_zero]
  · have h := spForm_add_add_self hd3 hx'mem hcr_mem
    have hQcr : spForm ℓ F (c • r) (spEnd d (c • r)) = 0 := by
      calc spForm ℓ F (c • r) (spEnd d (c • r))
          = c * c * spForm ℓ F r (spEnd d r) := by
            simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
            ring
        _ = 0 := by rw [hQ, mul_zero]
    have hBxcr : spForm ℓ F x' (c • r) = c := by
      rw [map_smul, smul_eq_mul, hBx'r, mul_one]
    rw [hQcr, hBxcr, hc] at h
    have hss : spForm ℓ F x' (spEnd d x') + spForm ℓ F x' (spEnd d x') = 0 := by
      have h2F : (2 : F) = 0 := CharP.cast_eq_zero F 2
      calc spForm ℓ F x' (spEnd d x') + spForm ℓ F x' (spEnd d x')
          = (2 : F) * spForm ℓ F x' (spEnd d x') := by ring
        _ = 0 := by rw [h2F, zero_mul]
    rw [add_zero, hss] at h
    exact h

theorem exists_spForm_self_eq_one [CharP F 2] (hF : Nat.card F = 2)
    {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1)
    (hne : primaryComponent (spEnd d) (X ^ 2 + X + 1) ≠ ⊥) :
    ∃ w ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1),
      spForm ℓ F w (spEnd d w) = 1 := by
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  by_cases hQr : spForm ℓ F r (spEnd d r) = 1
  · exact ⟨r, hr, hQr⟩
  · have hQr0 : spForm ℓ F r (spEnd d r) = 0 := by
      rcases CFSG.HardMathSupport.Curtis.Coordinator.eq_zero_or_eq_one_of_card_eq_two hF
        (spForm ℓ F r (spEnd d r)) with h | h
      · exact h
      · exact absurd h hQr
    obtain ⟨r', hr', hBr', hQ'⟩ := exists_isotropic_partner hd3 hr hr0 hQr0
    refine ⟨r + r', (primaryComponent (spEnd d) (X ^ 2 + X + 1)).add_mem hr hr', ?_⟩
    have h := spForm_add_add_self hd3 hr hr'
    rw [hQr0, hQ', hBr'] at h
    rw [h]
    norm_num [hF]

theorem mem_of_unitTransv_stable [CharP F 2] (hF : Nat.card F = 2)
    {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1) {W : Submodule F (Fin ℓ ⊕ Fin ℓ → F)}
    (hWd : ∀ w ∈ W, spEnd d w ∈ W) {r r' : Fin ℓ ⊕ Fin ℓ → F}
    (hr' : r' ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1))
    (hQ' : spForm ℓ F r' (spEnd d r') = 0) (hrW : r ∈ W) (hrr' : spForm ℓ F r r' = 1)
    (hWt : ∀ w ∈ W, spEnd (unitTransv d r') w ∈ W) : r' ∈ W := by
  set c : F := spForm ℓ F r (spEnd d r') with hc
  have hw : spEnd d r' + c • r' ∈ W := by
    have h := hWt r hrW
    rw [spEnd_unitTransv hd3 hr' hQ' r, hrr', one_smul] at h
    have h' : spEnd d r' + c • r' = (r + spEnd d r' + c • r') - r := by abel
    rw [h']
    exact W.sub_mem h hrW
  have hcases := CFSG.HardMathSupport.Curtis.Coordinator.eq_zero_or_eq_one_of_card_eq_two hF c
  rcases hcases with hc0 | hc1
  · rw [hc0, zero_smul, add_zero] at hw
    have h1 : spEnd d (spEnd d r') ∈ W := hWd _ hw
    have h2 : spEnd d (spEnd d (spEnd d r')) ∈ W := hWd _ h1
    rwa [spEnd_cube_apply hd3 r'] at h2
  · rw [hc1, one_smul] at hw
    have h1 : spEnd d (spEnd d r' + r') ∈ W := hWd _ hw
    rw [map_add, spEnd_sq_apply_of_mem_primary hr'] at h1
    have hss : spEnd d r' + spEnd d r' = 0 := by
      have h2F : (2 : F) = 0 := CharP.cast_eq_zero F 2
      calc spEnd d r' + spEnd d r' = (2 : F) • spEnd d r' := (two_smul F _).symm
        _ = 0 := by rw [h2F, zero_smul]
    rw [add_assoc, hss, add_zero] at h1
    exact h1


private lemma proj_zero_kill {V : Type} [AddCommGroup V] [Module F V]
    (A : Module.End F V) (hA3 : A ^ 3 = 1) :
    (A - 1) * (1 + A + A ^ 2) = 0 := by
  rw [show (A - 1) * (1 + A + A ^ 2) = A ^ 3 - 1 by noncomm_ring, hA3, sub_self]

private lemma proj_one_kill {V : Type} [AddCommGroup V] [Module F V]
    (A T : Module.End F V) (hAT : A * T = T * A) (hA3 : A ^ 3 = 1) (hT3 : T ^ 3 = 1) :
    (A - T) * (1 + T ^ 2 * A + T * A ^ 2) = 0 := by
  have hA2 : A * T ^ 2 = T ^ 2 * A := by
    calc A * T ^ 2 = (A * T) * T := by rw [pow_two, mul_assoc]
      _ = (T * A) * T := by rw [hAT]
      _ = T * (A * T) := by rw [mul_assoc]
      _ = T * (T * A) := by rw [hAT]
      _ = T ^ 2 * A := by rw [pow_two, mul_assoc]
  have h1 : A * (T ^ 2 * A) = T ^ 2 * A ^ 2 := by
    rw [← mul_assoc, hA2, mul_assoc]
    rw [show A * A = A ^ 2 by noncomm_ring]
  have h2 : T * (T ^ 2 * A) = A := by
    rw [← mul_assoc]
    rw [show T * T ^ 2 = T ^ 3 by noncomm_ring, hT3, one_mul]
  have h3 : A * (T * A ^ 2) = T := by
    rw [← mul_assoc, hAT, mul_assoc]
    rw [show A * A ^ 2 = A ^ 3 by noncomm_ring, hA3, mul_one]
  have h4 : T * (T * A ^ 2) = T ^ 2 * A ^ 2 := by
    rw [← mul_assoc]
    rw [show T * T = T ^ 2 by noncomm_ring]
  calc (A - T) * (1 + T ^ 2 * A + T * A ^ 2)
      = A + A * (T ^ 2 * A) + A * (T * A ^ 2) -
          (T * 1 + T * (T ^ 2 * A) + T * (T * A ^ 2)) := by
        rw [sub_mul, mul_add, mul_add, mul_one, mul_add, mul_add]
    _ = A + T ^ 2 * A ^ 2 + T - (T + A + T ^ 2 * A ^ 2) := by
        rw [h1, h2, h3, h4, mul_one]
    _ = 0 := by abel

private lemma proj_two_kill {V : Type} [AddCommGroup V] [Module F V]
    (A T : Module.End F V) (hAT : A * T = T * A) (hA3 : A ^ 3 = 1) (hT3 : T ^ 3 = 1) :
    (A - T ^ 2) * (1 + T * A + T ^ 2 * A ^ 2) = 0 := by
  have hA2 : A * T ^ 2 = T ^ 2 * A := by
    calc A * T ^ 2 = (A * T) * T := by rw [pow_two, mul_assoc]
      _ = (T * A) * T := by rw [hAT]
      _ = T * (A * T) := by rw [mul_assoc]
      _ = T * (T * A) := by rw [hAT]
      _ = T ^ 2 * A := by rw [pow_two, mul_assoc]
  have hT4 : T ^ 4 = T := by
    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, hT3, one_mul, pow_one]
  have h1 : A * (T * A) = T * A ^ 2 := by
    rw [← mul_assoc, hAT, mul_assoc]
    rw [show A * A = A ^ 2 by noncomm_ring]
  have h2 : A * (T ^ 2 * A ^ 2) = T ^ 2 := by
    rw [← mul_assoc, hA2, mul_assoc]
    rw [show A * A ^ 2 = A ^ 3 by noncomm_ring, hA3, mul_one]
  have h3 : T ^ 2 * (T * A) = A := by
    rw [← mul_assoc]
    rw [show T ^ 2 * T = T ^ 3 by noncomm_ring, hT3, one_mul]
  have h4 : T ^ 2 * (T ^ 2 * A ^ 2) = T * A ^ 2 := by
    rw [← mul_assoc]
    rw [show T ^ 2 * T ^ 2 = T ^ 4 by noncomm_ring, hT4]
  calc (A - T ^ 2) * (1 + T * A + T ^ 2 * A ^ 2)
      = A + A * (T * A) + A * (T ^ 2 * A ^ 2) -
          (T ^ 2 * 1 + T ^ 2 * (T * A) + T ^ 2 * (T ^ 2 * A ^ 2)) := by
        rw [sub_mul, mul_add, mul_add, mul_one, mul_add, mul_add]
    _ = A + T * A ^ 2 + T ^ 2 - (T ^ 2 + A + T * A ^ 2) := by
        rw [h1, h2, h3, h4, mul_one]
    _ = 0 := by abel

private lemma proj_sum {V : Type} [AddCommGroup V] [Module F V] (A T : Module.End F V) :
    (1 + A + A ^ 2) + (1 + T ^ 2 * A + T * A ^ 2) + (1 + T * A + T ^ 2 * A ^ 2) =
      (3 : ℕ) • (1 : Module.End F V) + (1 + T + T ^ 2) * A + (1 + T + T ^ 2) * A ^ 2 := by
  noncomm_ring


private lemma eigen_projection_mem {V : Type} [AddCommGroup V] [Module F V]
    (A T : Module.End F V) (W : Submodule F V)
    (hAW : ∀ z ∈ W, A z ∈ W) (hTW : ∀ z ∈ W, T z ∈ W) :
    (∀ z ∈ W, ((1 + A + A ^ 2 : Module.End F V)) z ∈ W) ∧
      (∀ z ∈ W, ((1 + T ^ 2 * A + T * A ^ 2 : Module.End F V)) z ∈ W) ∧
      (∀ z ∈ W, ((1 + T * A + T ^ 2 * A ^ 2 : Module.End F V)) z ∈ W) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    have hAz : A z ∈ W := hAW z hz
    have hA2z : A (A z) ∈ W := hAW _ hAz
    have hz' : ((1 + A + A ^ 2 : Module.End F V)) z = z + A z + A (A z) := by
      simp [pow_two, LinearMap.add_apply, Module.End.one_apply]
    rw [hz']
    exact W.add_mem (W.add_mem hz hAz) hA2z
  · intro z hz
    have hAz : A z ∈ W := hAW z hz
    have hA2z : A (A z) ∈ W := hAW _ hAz
    have hT1 : T (A z) ∈ W := hTW _ hAz
    have hT2 : T (T (A z)) ∈ W := hTW _ hT1
    have hS1 : T (A (A z)) ∈ W := hTW _ hA2z
    have hz' : ((1 + T ^ 2 * A + T * A ^ 2 : Module.End F V)) z =
        z + T (T (A z)) + T (A (A z)) := by
      simp [pow_two, LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply]
    rw [hz']
    exact W.add_mem (W.add_mem hz hT2) hS1
  · intro z hz
    have hAz : A z ∈ W := hAW z hz
    have hA2z : A (A z) ∈ W := hAW _ hAz
    have hT1 : T (A z) ∈ W := hTW _ hAz
    have hT2 : T (T (A z)) ∈ W := hTW _ hT1
    have hS1 : T (A (A z)) ∈ W := hTW _ hA2z
    have hz' : ((1 + T * A + T ^ 2 * A ^ 2 : Module.End F V)) z =
        z + T (A z) + T (T (A (A z))) := by
      simp [pow_two, LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply]
    rw [hz']
    exact W.add_mem (W.add_mem hz hT1) (hTW _ (hTW _ hA2z))

private lemma eigen_projection_sum [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
    (A T : Module.End F V) (W : Submodule F V) (hAW : ∀ z ∈ W, A z ∈ W)
    (hnormop : ∀ z ∈ W, ((1 + T + T ^ 2 : Module.End F V)) z = 0) :
    ∀ z ∈ W, ((1 + A + A ^ 2 : Module.End F V)) z +
      ((1 + T ^ 2 * A + T * A ^ 2 : Module.End F V)) z +
      ((1 + T * A + T ^ 2 * A ^ 2 : Module.End F V)) z = z := by
  intro z hz
  have hzA : A z ∈ W := hAW z hz
  have hzA2 : A (A z) ∈ W := hAW _ hzA
  have h1 : A z + T (A z) + (T ^ 2) (A z) = 0 := by
    have h := hnormop (A z) hzA
    simpa [LinearMap.add_apply, Module.End.one_apply] using h
  have h2 : (A ^ 2) z + T ((A ^ 2) z) + (T ^ 2) ((A ^ 2) z) = 0 := by
    have hz2 : (A ^ 2) z ∈ W := by simpa [pow_two] using hzA2
    have h := hnormop ((A ^ 2) z) hz2
    simpa [LinearMap.add_apply, Module.End.one_apply] using h
  have h3op : (3 : Module.End F V) = 1 := by
    have h2 : (2 : Module.End F V) = 0 := by
      have h2F : (2 : F) = 0 := CharP.cast_eq_zero F 2
      calc (2 : Module.End F V) = algebraMap F (Module.End F V) (2 : F) := (map_ofNat _ 2).symm
        _ = 0 := by rw [h2F, map_zero]
    rw [show (3 : Module.End F V) = 2 + 1 by norm_num, h2, zero_add]
  have h3 : ((3 : ℕ) • (1 : Module.End F V)) z = z := by
    rw [show ((3 : ℕ) • (1 : Module.End F V)) = (3 : Module.End F V) by simp]
    rw [h3op, Module.End.one_apply]
  have h := congrArg (fun f : Module.End F V => f z) (proj_sum A T)
  simp only [LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply] at h
  rw [h1, h2, h3] at h
  simpa only [add_zero, LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply] using h

private lemma eigen_projection_kernel {V : Type} [AddCommGroup V] [Module F V]
    (A T : Module.End F V) (W : Submodule F V)
    (hP0W : ∀ z ∈ W, ((1 + A + A ^ 2 : Module.End F V)) z ∈ W)
    (hP1W : ∀ z ∈ W, ((1 + T ^ 2 * A + T * A ^ 2 : Module.End F V)) z ∈ W)
    (hP2W : ∀ z ∈ W, ((1 + T * A + T ^ 2 * A ^ 2 : Module.End F V)) z ∈ W)
    (hk0 : (A - 1) * (1 + A + A ^ 2) = 0)
    (hk1 : (A - T) * (1 + T ^ 2 * A + T * A ^ 2) = 0)
    (hk2 : (A - T ^ 2) * (1 + T * A + T ^ 2 * A ^ 2) = 0) :
    (∀ z ∈ W, ((1 + A + A ^ 2 : Module.End F V)) z ∈ W ⊓ LinearMap.ker (A - 1)) ∧
      (∀ z ∈ W, ((1 + T ^ 2 * A + T * A ^ 2 : Module.End F V)) z ∈
        W ⊓ LinearMap.ker (A - T)) ∧
      (∀ z ∈ W, ((1 + T * A + T ^ 2 * A ^ 2 : Module.End F V)) z ∈
        W ⊓ LinearMap.ker (A - T ^ 2)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    refine ⟨hP0W z hz, ?_⟩
    change (A - 1) (((1 + A + A ^ 2 : Module.End F V)) z) = 0
    have h := congrArg (fun f : Module.End F V => f z) hk0
    simpa [Module.End.mul_apply, LinearMap.sub_apply] using h
  · intro z hz
    refine ⟨hP1W z hz, ?_⟩
    change (A - T) (((1 + T ^ 2 * A + T * A ^ 2 : Module.End F V)) z) = 0
    have h := congrArg (fun f : Module.End F V => f z) hk1
    simpa [Module.End.mul_apply, LinearMap.sub_apply] using h
  · intro z hz
    refine ⟨hP2W z hz, ?_⟩
    change (A - T ^ 2) (((1 + T * A + T ^ 2 * A ^ 2 : Module.End F V)) z) = 0
    have h := congrArg (fun f : Module.End F V => f z) hk2
    simpa [Module.End.mul_apply, LinearMap.sub_apply] using h

private lemma eigen_primary_le_sup_abstract [CharP F 2] {V : Type} [AddCommGroup V]
    [Module F V] (A T : Module.End F V) (W : Submodule F V)
    (hA3 : A ^ 3 = 1) (hT3 : T ^ 3 = 1) (hcomm : A * T = T * A)
    (hAW : ∀ z ∈ W, A z ∈ W) (hTW : ∀ z ∈ W, T z ∈ W)
    (hnormop : ∀ z ∈ W, ((1 + T + T ^ 2 : Module.End F V)) z = 0) :
    W ≤ (W ⊓ LinearMap.ker (A - 1)) ⊔ (W ⊓ LinearMap.ker (A - T)) ⊔
      (W ⊓ LinearMap.ker (A - T ^ 2)) := by
  obtain ⟨hP0W, hP1W, hP2W⟩ := eigen_projection_mem A T W hAW hTW
  have hsum := eigen_projection_sum A T W hAW hnormop
  have hk0 : (A - 1) * (1 + A + A ^ 2) = 0 := proj_zero_kill A hA3
  have hk1 : (A - T) * (1 + T ^ 2 * A + T * A ^ 2) = 0 :=
    proj_one_kill A T hcomm hA3 hT3
  have hk2 : (A - T ^ 2) * (1 + T * A + T ^ 2 * A ^ 2) = 0 :=
    proj_two_kill A T hcomm hA3 hT3
  obtain ⟨hm0, hm1, hm2⟩ :=
    eigen_projection_kernel A T W hP0W hP1W hP2W hk0 hk1 hk2
  intro z hz
  have hzsum := hsum z hz
  rw [← hzsum]
  refine Submodule.mem_sup.mpr ⟨((1 + A + A ^ 2 : Module.End F V)) z +
    ((1 + T ^ 2 * A + T * A ^ 2 : Module.End F V)) z, ?_,
    ((1 + T * A + T ^ 2 * A ^ 2 : Module.End F V)) z, hm2 z hz, rfl⟩
  exact Submodule.mem_sup.mpr ⟨((1 + A + A ^ 2 : Module.End F V)) z, hm0 z hz,
    ((1 + T ^ 2 * A + T * A ^ 2 : Module.End F V)) z, hm1 z hz, rfl⟩

private lemma eigen_primary_le_sup [CharP F 2] {d x : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1)
    (hx3 : x ^ 3 = 1) (hxd : x * d = d * x) :
    primaryComponent (spEnd d) (X ^ 2 + X + 1) ≤
      (primaryComponent (spEnd d) (X ^ 2 + X + 1) ⊓
        LinearMap.ker (spEnd x - spEnd (d ^ 0))) ⊔
      (primaryComponent (spEnd d) (X ^ 2 + X + 1) ⊓
        LinearMap.ker (spEnd x - spEnd (d ^ 1))) ⊔
      (primaryComponent (spEnd d) (X ^ 2 + X + 1) ⊓
        LinearMap.ker (spEnd x - spEnd (d ^ 2))) := by
  let T := spEnd d
  let A := spEnd x
  let W : Submodule F (Fin ℓ ⊕ Fin ℓ → F) := primaryComponent T (X ^ 2 + X + 1)
  have hT3 : T ^ 3 = 1 := spEnd_pow hd3
  have hA3 : A ^ 3 = 1 := spEnd_pow hx3
  have hcomm : A * T = T * A := by
    have h := congrArg spEnd hxd
    rwa [spEnd_mul, spEnd_mul] at h
  have hTW : ∀ z ∈ W, T z ∈ W := fun z hz => apply_mem_primaryComponent (Commute.refl T) hz
  have hAW : ∀ z ∈ W, A z ∈ W :=
    fun z hz => apply_mem_primaryComponent (show Commute A T from hcomm) hz
  have hnormop : ∀ z ∈ W, ((1 + T + T ^ 2 : Module.End F (Fin ℓ ⊕ Fin ℓ → F))) z = 0 := by
    intro z hz
    have hz' : z ∈ primaryComponent (spEnd d) (X ^ 2 + X + 1) := by simpa [W] using hz
    rw [primaryComponent_quad_eq_normKer] at hz'
    rw [mem_normKer] at hz'
    simpa [W, pow_two, LinearMap.add_apply, Module.End.one_apply] using hz'
  have h := eigen_primary_le_sup_abstract A T W hA3 hT3 hcomm hAW hTW hnormop
  have hT2 : spEnd (d ^ 2) = T ^ 2 := by rw [pow_two, spEnd_mul]; rfl
  simpa [W, T, A, pow_zero, pow_one, spEnd_one, hT2] using h

private lemma eigen_finrank_bound [CharP F 2] {d x : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1)
    (hx3 : x ^ 3 = 1) (hxd : x * d = d * x)
    (h7 : 7 ≤ finrank F (primaryComponent (spEnd d) (X ^ 2 + X + 1))) :
    ∃ j : ℕ, j < 3 ∧ 3 ≤ finrank F ↥(primaryComponent (spEnd d) (X ^ 2 + X + 1) ⊓
      LinearMap.ker (spEnd x - spEnd (d ^ j))) := by
  let W : Submodule F (Fin ℓ ⊕ Fin ℓ → F) := primaryComponent (spEnd d) (X ^ 2 + X + 1)
  let K0 : Submodule F (Fin ℓ ⊕ Fin ℓ → F) := W ⊓ LinearMap.ker (spEnd x - spEnd (d ^ 0))
  let K1 : Submodule F (Fin ℓ ⊕ Fin ℓ → F) := W ⊓ LinearMap.ker (spEnd x - spEnd (d ^ 1))
  let K2 : Submodule F (Fin ℓ ⊕ Fin ℓ → F) := W ⊓ LinearMap.ker (spEnd x - spEnd (d ^ 2))
  have hWle : W ≤ K0 ⊔ K1 ⊔ K2 := by
    simpa [W, K0, K1, K2] using eigen_primary_le_sup hd3 hx3 hxd
  haveI : Module.Finite F (Fin ℓ ⊕ Fin ℓ → F) := inferInstance
  haveI : Module.Finite F ↥W :=
    Module.Finite.of_injective (Submodule.subtype W) Subtype.val_injective
  haveI : Module.Finite F ↥K0 :=
    Module.Finite.of_injective (Submodule.subtype K0) Subtype.val_injective
  haveI : Module.Finite F ↥K1 :=
    Module.Finite.of_injective (Submodule.subtype K1) Subtype.val_injective
  haveI : Module.Finite F ↥K2 :=
    Module.Finite.of_injective (Submodule.subtype K2) Subtype.val_injective
  haveI : Module.Finite F ↥(K0 ⊔ K1 ⊔ K2) :=
    Module.Finite.of_injective (Submodule.subtype (K0 ⊔ K1 ⊔ K2)) Subtype.val_injective
  have hdim : finrank F W ≤ finrank F K0 + finrank F K1 + finrank F K2 := by
    have hmono : finrank F W ≤ finrank F ↥(K0 ⊔ K1 ⊔ K2) :=
      Submodule.finrank_mono (R := F) (M := Fin ℓ ⊕ Fin ℓ → F)
        (s := W) (t := K0 ⊔ K1 ⊔ K2) hWle
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq K0 K1
    have h3 := Submodule.finrank_sup_add_finrank_inf_eq (K0 ⊔ K1) K2
    omega
  have h7W : 7 ≤ finrank F W := by simpa [W] using h7
  have hsome : 3 ≤ finrank F K0 ∨ 3 ≤ finrank F K1 ∨ 3 ≤ finrank F K2 := by
    by_contra h
    push Not at h
    omega
  rcases hsome with h | h | h
  · exact ⟨0, by norm_num, by simpa [K0] using h⟩
  · exact ⟨1, by norm_num, by simpa [K1] using h⟩
  · exact ⟨2, by norm_num, by simpa [K2] using h⟩

theorem exists_three_le_finrank_eigen [CharP F 2] {d x : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1)
    (hx3 : x ^ 3 = 1) (hxd : x * d = d * x)
    (h7 : 7 ≤ finrank F (primaryComponent (spEnd d) (X ^ 2 + X + 1))) :
    ∃ j : ℕ, j < 3 ∧ 3 ≤ finrank F ↥(primaryComponent (spEnd d) (X ^ 2 + X + 1) ⊓
      LinearMap.ker (spEnd x - spEnd (d ^ j))) :=
  eigen_finrank_bound hd3 hx3 hxd h7

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
