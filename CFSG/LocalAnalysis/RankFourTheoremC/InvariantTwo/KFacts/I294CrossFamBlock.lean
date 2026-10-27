module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamOrder
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open Polynomial

section Degree

variable {K : Type*} [Field K] [Finite K]

theorem natDegree_le_of_dvd_X_pow_sub_one {p e : ℕ} (he : 0 < e) (hpe : p ∣ Nat.card K ^ e - 1)
    {f : K[X]} (hf : Irreducible f) (hdvd : f ∣ X ^ p - 1) : f.natDegree ≤ e := by
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  obtain ⟨t, ht⟩ := hpe
  have hqe : Nat.card K ^ e = p * t + 1 := by
    have := Nat.one_le_pow e (Nat.card K) (by omega)
    omega
  have h1 : (X ^ p - 1 : K[X]) ∣ X ^ (Nat.card K ^ e) - X := by
    have : (X ^ (Nat.card K ^ e) - X : K[X]) = X * ((X ^ p) ^ t - 1 ^ t) := by
      rw [hqe, pow_succ, pow_mul, one_pow]
      ring
    rw [this]
    exact Dvd.dvd.mul_left (sub_dvd_pow_sub_pow _ _ _) _
  exact Nat.le_of_dvd he (hf.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X (hdvd.trans h1))

end Degree

section Invariant

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {y : Module.End K V}

theorem pow_apply_mem {Z : Submodule K V} (hZ : ∀ x ∈ Z, y x ∈ Z) (n : ℕ) {x : V}
    (hx : x ∈ Z) : (y ^ n) x ∈ Z := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact hZ _ ih

theorem aeval_apply_mem {Z : Submodule K V} (hZ : ∀ x ∈ Z, y x ∈ Z) (q : K[X]) {x : V}
    (hx : x ∈ Z) : aeval y q x ∈ Z := by
  have hpow : ∀ n : ℕ, (y ^ n) x ∈ Z := fun n => pow_apply_mem hZ n hx
  induction q using Polynomial.induction_on' with
  | add f g hf hg =>
    rw [map_add, LinearMap.add_apply]
    exact Z.add_mem hf hg
  | monomial n c =>
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact Z.smul_mem c (hpow n)

theorem exists_irreducible_ker {p : ℕ} (hy : y ^ p = 1) (hp0 : 0 < p) {Z : Submodule K V}
    (hZ : ∀ x ∈ Z, y x ∈ Z) (hZ0 : Z ≠ ⊥) :
    ∃ f : K[X], Irreducible f ∧ f ∣ X ^ p - 1 ∧ ∃ z ∈ Z, z ≠ 0 ∧ aeval y f z = 0 := by
  have hP0 : (X ^ p - 1 : K[X]) ≠ 0 := by
    simpa using X_pow_sub_C_ne_zero hp0 (1 : K)
  have hPy : aeval y (X ^ p - 1 : K[X]) = 0 := by simp [hy]
  have key : ∀ (d : ℕ) (g : K[X]), g.natDegree = d → g ∣ X ^ p - 1 → g ≠ 0 →
      (∃ z ∈ Z, z ≠ 0 ∧ aeval y g z = 0) →
      ∃ f : K[X], Irreducible f ∧ f ∣ X ^ p - 1 ∧ ∃ z ∈ Z, z ≠ 0 ∧ aeval y f z = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro g hgd hgP hg0 ⟨z, hzZ, hz0, hgz⟩
      by_cases hirr : Irreducible g
      · exact ⟨g, hirr, hgP, z, hzZ, hz0, hgz⟩
      · have hnu : ¬ IsUnit g := by
          intro hu
          obtain ⟨c, hc, rfl⟩ := Polynomial.isUnit_iff.1 hu
          rw [aeval_C, Module.algebraMap_end_apply] at hgz
          exact hz0 ((smul_eq_zero.1 hgz).resolve_left hc.ne_zero)
        obtain ⟨a, b, hab, ha, hb⟩ : ∃ a b : K[X], g = a * b ∧ ¬ IsUnit a ∧ ¬ IsUnit b := by
          by_contra hcon
          refine hirr ⟨hnu, fun a b hab => ?_⟩
          by_contra h
          exact hcon ⟨a, b, hab, fun h' => h (Or.inl h'), fun h' => h (Or.inr h')⟩
        have ha0 : a ≠ 0 := left_ne_zero_of_mul (hab ▸ hg0)
        have hb0 : b ≠ 0 := right_ne_zero_of_mul (hab ▸ hg0)
        have hdeg : ∀ q : K[X], q ≠ 0 → ¬ IsUnit q → 0 < q.natDegree := by
          intro q hq0 hqu
          refine Nat.pos_of_ne_zero fun h => hqu ?_
          obtain ⟨x, hx⟩ := Polynomial.natDegree_eq_zero.1 h
          rw [← hx] at hq0 ⊢
          exact Polynomial.isUnit_C.2 (isUnit_iff_ne_zero.2 fun h0 => hq0 (by rw [h0, C_0]))
        have hda := hdeg a ha0 ha
        have hdb := hdeg b hb0 hb
        have hsum : g.natDegree = a.natDegree + b.natDegree := by
          rw [hab, natDegree_mul ha0 hb0]
        have hmem : aeval y b z ∈ Z := aeval_apply_mem hZ b hzZ
        have hcomp : aeval y a (aeval y b z) = 0 := by
          rw [← Module.End.mul_apply, ← map_mul, ← hab, hgz]
        by_cases hz' : aeval y b z = 0
        · exact ih b.natDegree (by omega) b rfl ((hab ▸ dvd_mul_left b a).trans hgP) hb0
            ⟨z, hzZ, hz0, hz'⟩
        · exact ih a.natDegree (by omega) a rfl ((hab ▸ dvd_mul_right a b).trans hgP) ha0
            ⟨_, hmem, hz', hcomp⟩
  obtain ⟨z, hzZ, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hZ0
  exact key _ (X ^ p - 1) rfl dvd_rfl hP0 ⟨z, hzZ, hz0, by simp [hPy]⟩

theorem exists_invt_le {p e : ℕ} (hy : y ^ p = 1) (hp0 : 0 < p)
    (hdeg : ∀ f : K[X], Irreducible f → f ∣ X ^ p - 1 → f.natDegree ≤ e)
    {Z : Submodule K V} (hZ : ∀ x ∈ Z, y x ∈ Z) (hZ0 : Z ≠ ⊥) :
    ∃ U : Submodule K V, (∀ x ∈ U, y x ∈ U) ∧ U ≤ Z ∧ U ≠ ⊥ ∧ Module.finrank K U ≤ e := by
  obtain ⟨f, hf, hfP, z, hzZ, hz0, hfz⟩ := exists_irreducible_ker hy hp0 hZ hZ0
  set d := f.natDegree with hd
  have hdpos : 0 < d := hf.natDegree_pos
  have hf0 : f ≠ 0 := hf.ne_zero
  let g : Fin d → V := fun i => (y ^ (i : ℕ)) z
  let U := Submodule.span K (Set.range g)
  have hgU : ∀ i : Fin d, g i ∈ U := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hlead : f.coeff d ≠ 0 := leadingCoeff_ne_zero.2 hf0
  have hrec : (y ^ d) z ∈ U := by
    have hsum : ∑ i ∈ Finset.range (d + 1), f.coeff i • (y ^ i) z = 0 := by
      have h := hfz
      rw [aeval_eq_sum_range, LinearMap.sum_apply] at h
      simpa [LinearMap.smul_apply] using h
    rw [Finset.sum_range_succ] at hsum
    have h2 : f.coeff d • (y ^ d) z = -∑ i ∈ Finset.range d, f.coeff i • (y ^ i) z :=
      eq_neg_of_add_eq_zero_right hsum
    have h3 : (y ^ d) z = (-(f.coeff d)⁻¹) • ∑ i ∈ Finset.range d, f.coeff i • (y ^ i) z := by
      rw [neg_smul, ← smul_neg, ← h2, smul_smul, inv_mul_cancel₀ hlead, one_smul]
    rw [h3]
    refine U.smul_mem _ (U.sum_mem fun i hi => U.smul_mem _ ?_)
    exact hgU ⟨i, Finset.mem_range.1 hi⟩
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      have hyi : y (g i) = (y ^ ((i : ℕ) + 1)) z := by
        simp only [g]
        rw [pow_succ', Module.End.mul_apply]
      rw [hyi]
      by_cases hi : (i : ℕ) + 1 < d
      · exact hgU ⟨(i : ℕ) + 1, hi⟩
      · have : (i : ℕ) + 1 = d := by omega
        rw [this]
        exact hrec
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact U.add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact U.smul_mem a hx
  · exact Submodule.span_le.2 (by
      rintro _ ⟨i, rfl⟩
      exact pow_apply_mem hZ i hzZ)
  · intro h
    have hzU : z ∈ U := by simpa [g] using hgU ⟨0, hdpos⟩
    exact hz0 ((Submodule.mem_bot K).1 (h ▸ hzU))
  · calc Module.finrank K U ≤ d := by
          simpa [Set.finrank] using finrank_range_le_card (R := K) g
      _ ≤ e := hdeg f hf hfP

variable [Module.Finite K V]

theorem isSemisimple_of_pow_eq_one {p : ℕ} (hy : y ^ p = 1) (hp0 : (p : K) ≠ 0) :
    y.IsSemisimple := by
  have hsep : (X ^ p - C (1 : K) : K[X]).Separable := separable_X_pow_sub_C 1 hp0 one_ne_zero
  rw [C_1] at hsep
  exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree (by simp [hy])

theorem exists_window {p e c : ℕ} (hy : y ^ p = 1) (hp0 : (p : K) ≠ 0) (hp : 0 < p)
    (he : 0 < e) (hdeg : ∀ f : K[X], Irreducible f → f ∣ X ^ p - 1 → f.natDegree ≤ e)
    (hc : c * e ≤ Module.finrank K V) :
    ∃ W C : Submodule K V, (∀ x ∈ W, y x ∈ W) ∧ (∀ x ∈ C, y x ∈ C) ∧ IsCompl W C ∧
      c * e ≤ Module.finrank K W ∧ Module.finrank K W < (c + 1) * e := by
  have hsemi := isSemisimple_of_pow_eq_one hy hp0
  have hcompl : ∀ W : Submodule K V, (∀ x ∈ W, y x ∈ W) →
      ∃ C : Submodule K V, (∀ x ∈ C, y x ∈ C) ∧ IsCompl W C := by
    intro W hW
    obtain ⟨C, hC, hWC⟩ := Module.End.isSemisimple_iff.1 hsemi W
      ((Module.End.mem_invtSubmodule y).2 fun x hx => hW x hx)
    exact ⟨C, fun x hx => ((Module.End.mem_invtSubmodule y).1 hC) hx, hWC⟩
  let S : Set ℕ := {m | ∃ W : Submodule K V, (∀ x ∈ W, y x ∈ W) ∧
    Module.finrank K W = m ∧ m < (c + 1) * e}
  have hS0 : S.Nonempty :=
    ⟨0, ⊥, fun x hx => by simp [(Submodule.mem_bot K).1 hx], by simp, by positivity⟩
  have hSb : BddAbove S := ⟨(c + 1) * e, fun m ⟨_, _, _, hm⟩ => hm.le⟩
  obtain ⟨W, hW, hWm, hWlt⟩ := Nat.sSup_mem hS0 hSb
  have hge : c * e ≤ Module.finrank K W := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨C, hC, hWC⟩ := hcompl W hW
    have hsum := Submodule.finrank_add_eq_of_isCompl hWC
    have hC0 : C ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hsum
      omega
    obtain ⟨U, hU, hUC, hU0, hUe⟩ := exists_invt_le hy hp hdeg hC hC0
    have hdisj : Disjoint W U := hWC.disjoint.mono_right hUC
    have hfin : Module.finrank K ↥(W ⊔ U) = Module.finrank K W + Module.finrank K U := by
      have := Submodule.finrank_sup_add_finrank_inf_eq W U
      rw [disjoint_iff.1 hdisj, finrank_bot] at this
      omega
    have hU1 : 1 ≤ Module.finrank K U := Submodule.one_le_finrank_iff.2 hU0
    have hinv : ∀ x ∈ W ⊔ U, y x ∈ W ⊔ U := by
      intro x hx
      obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.1 hx
      rw [map_add]
      exact (W ⊔ U).add_mem (Submodule.mem_sup_left (hW w hw))
        (Submodule.mem_sup_right (hU u hu))
    have hce : (c + 1) * e = c * e + e := by ring
    have hmemS : Module.finrank K ↥(W ⊔ U) ∈ S := ⟨W ⊔ U, hinv, rfl, by omega⟩
    have hle := le_csSup hSb hmemS
    omega
  obtain ⟨C, hC, hWC⟩ := hcompl W hW
  exact ⟨W, C, hW, hC, hWC, hge, by omega⟩

end Invariant

end CFSG.LocalAnalysis.RankFourTheoremC
