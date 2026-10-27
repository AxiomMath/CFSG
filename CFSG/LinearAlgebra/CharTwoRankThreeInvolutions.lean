module

public import CFSG.LinearAlgebra.ElationInvariantSubspace

public section

namespace CFSG.LinearAlgebra

open Matrix Module
open scoped Pointwise

variable {K : Type*} [Field K] [CharP K 2]

private abbrev V3 := Fin 3 → K

private abbrev shift (t : GL (Fin 3) K) : Module.End K (V3 (K := K)) :=
  shiftEnd t

private lemma mat_sq_sub_one (t : GL (Fin 3) K) (ht : t * t = 1) :
    ((t : Matrix (Fin 3) (Fin 3) K) - 1) * ((t : Matrix (Fin 3) (Fin 3) K) - 1) = 0 := by
  have ht' : (t : Matrix (Fin 3) (Fin 3) K) * t = 1 := by
    simpa using congrArg (fun u : GL (Fin 3) K => (u : Matrix (Fin 3) (Fin 3) K)) ht
  rw [sub_mul, mul_sub, mul_sub, ht']
  simp only [mul_one, one_mul]
  rw [show (1 - (t : Matrix (Fin 3) (Fin 3) K)) - ((t : Matrix (Fin 3) (Fin 3) K) - 1) =
    2 • (1 : Matrix (Fin 3) (Fin 3) K) - 2 • (t : Matrix (Fin 3) (Fin 3) K) by abel]
  have h1 : 2 • (1 : Matrix (Fin 3) (Fin 3) K) = 0 := by
    rw [two_nsmul]
    ext i j
    exact CharTwo.add_self_eq_zero _
  have h2 : 2 • (t : Matrix (Fin 3) (Fin 3) K) = 0 := by
    rw [two_nsmul]
    ext i j
    exact CharTwo.add_self_eq_zero _
  rw [h1, h2, sub_zero]

private lemma shift_mul_self (t : GL (Fin 3) K) (ht : t * t = 1) :
    shift t * shift t = 0 := by
  change (Matrix.toLin' ((t : Matrix (Fin 3) (Fin 3) K) - 1)) *
      (Matrix.toLin' ((t : Matrix (Fin 3) (Fin 3) K) - 1)) = 0
  rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, mat_sq_sub_one t ht, map_zero]

private lemma finrank_range_le_one {a : Module.End K (V3 (K := K))} (ha : a * a = 0) :
    finrank K (LinearMap.range a) ≤ 1 := by
  have hle : LinearMap.range a ≤ LinearMap.ker a := by
    rintro y ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    exact congrArg (fun f : Module.End K (V3 (K := K)) => f x) ha
  have h1 : finrank K (LinearMap.range a) ≤ finrank K (LinearMap.ker a) :=
    Submodule.finrank_mono hle
  have h2 := LinearMap.finrank_range_add_finrank_ker a
  have h3 : finrank K (V3 (K := K)) = 3 := Module.finrank_fin_fun (R := K) (n := 3)
  omega


private lemma finrank_ker_eq_two_of_finrank_range_eq_one {a : Module.End K (V3 (K := K))}
    (hda : finrank K (LinearMap.range a) = 1) : finrank K (LinearMap.ker a) = 2 := by
  have h := LinearMap.finrank_range_add_finrank_ker a
  have h3 : finrank K (V3 (K := K)) = 3 := Module.finrank_fin_fun (R := K) (n := 3)
  omega

private lemma ker_eq_of_commute_of_mul_eq_zero {a b : Module.End K (V3 (K := K))}
    (ha : a * a = 0) (hb : b * b = 0) (hab : a * b = b * a)
    (hda : finrank K (LinearMap.range a) = 1)
    (hdb : finrank K (LinearMap.range b) = 1)
    (hrange : LinearMap.range a ≠ LinearMap.range b) (hab0 : a * b = 0) :
    LinearMap.ker a = LinearMap.ker b := by
  have ha_range : LinearMap.range a ≤ LinearMap.ker a := by
    rintro y ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    exact congrArg (fun f : Module.End K (V3 (K := K)) => f x) ha
  have hb_range : LinearMap.range b ≤ LinearMap.ker b := by
    rintro y ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    exact congrArg (fun f : Module.End K (V3 (K := K)) => f x) hb
  have hker_a : finrank K (LinearMap.ker a) = 2 :=
    finrank_ker_eq_two_of_finrank_range_eq_one hda
  have hker_b : finrank K (LinearMap.ker b) = 2 :=
    finrank_ker_eq_two_of_finrank_range_eq_one hdb
  have hbker : LinearMap.range b ≤ LinearMap.ker a := by
    rintro y ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    exact congrArg (fun f : Module.End K (V3 (K := K)) => f x) hab0
  have hab0' : b * a = 0 := by
    rwa [hab] at hab0
  have haker : LinearMap.range a ≤ LinearMap.ker b := by
    rintro y ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    exact congrArg (fun f : Module.End K (V3 (K := K)) => f x) hab0'
  have hlt : LinearMap.range a < LinearMap.range a ⊔ LinearMap.range b := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro h
    apply hrange
    have hb_le : LinearMap.range b ≤ LinearMap.range a := h ▸ le_sup_right
    exact (Submodule.eq_of_le_of_finrank_eq hb_le (by rw [hdb, hda])).symm
  have hfin_sup : 2 ≤ finrank K (LinearMap.range a ⊔ LinearMap.range b :
      Submodule K (V3 (K := K))) := by
    have h := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  have hsup_a : LinearMap.range a ⊔ LinearMap.range b ≤ LinearMap.ker a :=
    sup_le ha_range hbker
  have hsup_b : LinearMap.range a ⊔ LinearMap.range b ≤ LinearMap.ker b :=
    sup_le haker hb_range
  have hfin_sup_a : finrank K (LinearMap.range a ⊔ LinearMap.range b :
      Submodule K (V3 (K := K))) ≤ 2 := by
    calc finrank K (LinearMap.range a ⊔ LinearMap.range b :
          Submodule K (V3 (K := K))) ≤ finrank K (LinearMap.ker a) :=
          Submodule.finrank_mono hsup_a
      _ = 2 := hker_a
  have hAa : LinearMap.range a ⊔ LinearMap.range b = LinearMap.ker a :=
    Submodule.eq_of_le_of_finrank_eq hsup_a (by omega)
  have hBb : LinearMap.range a ⊔ LinearMap.range b = LinearMap.ker b :=
    Submodule.eq_of_le_of_finrank_eq hsup_b (by omega)
  rw [← hAa, ← hBb]

private lemma range_eq_of_commute_of_mul_ne_zero {a b : Module.End K (V3 (K := K))}
    (hab : a * b = b * a) (hda : finrank K (LinearMap.range a) = 1)
    (hdb : finrank K (LinearMap.range b) = 1) (hab0 : a * b ≠ 0) :
    LinearMap.range a = LinearMap.range b := by
  have hle_a : LinearMap.range (a * b) ≤ LinearMap.range a := by
    rintro y ⟨x, rfl⟩
    exact ⟨b x, rfl⟩
  have hle_b : LinearMap.range (a * b) ≤ LinearMap.range b := by
    rintro y ⟨x, rfl⟩
    refine ⟨a x, ?_⟩
    rw [hab]
    rfl
  have hne_bot : LinearMap.range (a * b) ≠ ⊥ := by
    rwa [Ne, LinearMap.range_eq_bot]
  have hpos : 0 < finrank K (LinearMap.range (a * b)) := by
    by_contra h
    have h0 : finrank K (LinearMap.range (a * b)) = 0 := by omega
    exact hne_bot ((Submodule.finrank_eq_zero).mp h0)
  have hfin_a : finrank K (LinearMap.range (a * b)) ≤ 1 := by
    calc finrank K (LinearMap.range (a * b)) ≤ finrank K (LinearMap.range a) :=
          Submodule.finrank_mono hle_a
      _ = 1 := hda
  have hfin_b : finrank K (LinearMap.range (a * b)) ≤ 1 := by
    calc finrank K (LinearMap.range (a * b)) ≤ finrank K (LinearMap.range b) :=
          Submodule.finrank_mono hle_b
      _ = 1 := hdb
  have hEqA : LinearMap.range (a * b) = LinearMap.range a :=
    Submodule.eq_of_le_of_finrank_eq hle_a (by omega)
  have hEqB : LinearMap.range (a * b) = LinearMap.range b :=
    Submodule.eq_of_le_of_finrank_eq hle_b (by omega)
  rw [← hEqA, ← hEqB]

private lemma range_eq_or_ker_eq_of_commute {a b : Module.End K (V3 (K := K))}
    (ha : a * a = 0) (hb : b * b = 0) (hab : a * b = b * a)
    (hda : finrank K (LinearMap.range a) = 1)
    (hdb : finrank K (LinearMap.range b) = 1) :
    LinearMap.range a = LinearMap.range b ∨ LinearMap.ker a = LinearMap.ker b := by
  by_cases hrange : LinearMap.range a = LinearMap.range b
  · exact Or.inl hrange
  · right
    by_cases hab0 : a * b = 0
    · exact ker_eq_of_commute_of_mul_eq_zero ha hb hab hda hdb hrange hab0
    · exact absurd (range_eq_of_commute_of_mul_ne_zero hab hda hdb hab0) hrange

private lemma finrank_range_shift_eq_one (t : GL (Fin 3) K) (ht : t * t = 1)
    (h0 : shift t ≠ 0) : finrank K (LinearMap.range (shift t)) = 1 := by
  have hle : finrank K (LinearMap.range (shift t)) ≤ 1 :=
    finrank_range_le_one (shift_mul_self t ht)
  have hne : LinearMap.range (shift t) ≠ ⊥ := by
    rwa [Ne, LinearMap.range_eq_bot]
  have hpos : 0 < finrank K (LinearMap.range (shift t)) := by
    by_contra h
    have hzero : finrank K (LinearMap.range (shift t)) = 0 := by omega
    exact hne ((Submodule.finrank_eq_zero).mp hzero)
  omega

private lemma finrank_ker_shift_eq_two (t : GL (Fin 3) K) (ht : t * t = 1)
    (h0 : shift t ≠ 0) : finrank K (LinearMap.ker (shift t)) = 2 :=
  finrank_ker_eq_two_of_finrank_range_eq_one (finrank_range_shift_eq_one t ht h0)


private lemma shift_comm {s t : GL (Fin 3) K} (h : s * t = t * s) :
    shift s * shift t = shift t * shift s := by
  have hmat : (s : Matrix (Fin 3) (Fin 3) K) * t = (t : Matrix (Fin 3) (Fin 3) K) * s := by
    simpa using congrArg (fun u : GL (Fin 3) K => (u : Matrix (Fin 3) (Fin 3) K)) h
  have hsub : ((s : Matrix (Fin 3) (Fin 3) K) - 1) * ((t : Matrix (Fin 3) (Fin 3) K) - 1) =
      ((t : Matrix (Fin 3) (Fin 3) K) - 1) * ((s : Matrix (Fin 3) (Fin 3) K) - 1) := by
    calc ((s : Matrix (Fin 3) (Fin 3) K) - 1) * ((t : Matrix (Fin 3) (Fin 3) K) - 1) =
        (s : Matrix (Fin 3) (Fin 3) K) * t - s - t + 1 := by noncomm_ring
      _ = (t : Matrix (Fin 3) (Fin 3) K) * s - t - s + 1 := by rw [hmat]; abel
      _ = ((t : Matrix (Fin 3) (Fin 3) K) - 1) * ((s : Matrix (Fin 3) (Fin 3) K) - 1) := by
        noncomm_ring
  change Matrix.toLin' ((s : Matrix (Fin 3) (Fin 3) K) - 1) *
      Matrix.toLin' ((t : Matrix (Fin 3) (Fin 3) K) - 1) =
    Matrix.toLin' ((t : Matrix (Fin 3) (Fin 3) K) - 1) *
      Matrix.toLin' ((s : Matrix (Fin 3) (Fin 3) K) - 1)
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp,
    ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hsub]

private lemma exists_common_centre_or_axis
    (T : Subgroup (GL (Fin 3) K))
    (hT2 : ∀ t ∈ T, t * t = 1)
    (hTc : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s) :
    (∃ p : Submodule K (V3 (K := K)), finrank K p = 1 ∧
      ∀ t ∈ T, LinearMap.range (shift t) ≤ p) ∨
    (∃ l : Submodule K (V3 (K := K)), finrank K l = 2 ∧
      ∀ t ∈ T, l ≤ LinearMap.ker (shift t)) := by
  by_cases htriv : ∀ t ∈ T, shift t = 0
  · left
    refine ⟨Submodule.span K {(Pi.single 0 (1 : K) : V3 (K := K))}, ?_, ?_⟩
    · rw [finrank_span_singleton]
      exact Pi.single_ne_zero_iff.mpr one_ne_zero
    · intro t ht
      simp [htriv t ht]
  · push Not at htriv
    obtain ⟨s, hsT, hs0⟩ := htriv
    have hsrange : finrank K (LinearMap.range (shift s)) = 1 :=
      finrank_range_shift_eq_one s (hT2 s hsT) hs0
    by_cases hall : ∀ t ∈ T, shift t = 0 ∨
        LinearMap.range (shift t) = LinearMap.range (shift s)
    · left
      refine ⟨LinearMap.range (shift s), hsrange, fun t ht => ?_⟩
      rcases hall t ht with h0 | h
      · simp [h0]
      · exact le_of_eq h
    · push Not at hall
      obtain ⟨u, huT, hu0, hurange⟩ := hall
      have hurange' : finrank K (LinearMap.range (shift u)) = 1 :=
        finrank_range_shift_eq_one u (hT2 u huT) hu0
      have hs_u : LinearMap.ker (shift s) = LinearMap.ker (shift u) := by
        rcases range_eq_or_ker_eq_of_commute (shift_mul_self s (hT2 s hsT))
          (shift_mul_self u (hT2 u huT)) (shift_comm (hTc s hsT u huT)) hsrange hurange'
          with h | h
        · exact absurd h.symm hurange
        · exact h
      right
      refine ⟨LinearMap.ker (shift s), finrank_ker_shift_eq_two s (hT2 s hsT) hs0, ?_⟩
      intro t ht
      by_cases ht0 : shift t = 0
      · simp [ht0]
      · have ht_range : finrank K (LinearMap.range (shift t)) = 1 :=
          finrank_range_shift_eq_one t (hT2 t ht) ht0
        by_cases htp : LinearMap.range (shift t) = LinearMap.range (shift s)
        · have h := range_eq_or_ker_eq_of_commute (shift_mul_self t (hT2 t ht))
            (shift_mul_self u (hT2 u huT)) (shift_comm (hTc t ht u huT)) ht_range hurange'
          rcases h with h | h
          · exfalso
            exact hurange (h.symm.trans htp)
          · rw [hs_u.trans h.symm]
        · have h := range_eq_or_ker_eq_of_commute (shift_mul_self t (hT2 t ht))
            (shift_mul_self s (hT2 s hsT)) (shift_comm (hTc t ht s hsT)) ht_range hsrange
          rcases h with h | h
          · exact absurd h htp
          · rw [h]


def submoduleStabilizer (U : Submodule K (Fin 3 → K)) : Subgroup (GL (Fin 3) K) :=
  glStabilizer (n := 3) U

theorem mem_submoduleStabilizer_iff {U : Submodule K (Fin 3 → K)} {x : GL (Fin 3) K} :
    x ∈ submoduleStabilizer U ↔
      Submodule.map (Matrix.toLin' (x : Matrix (Fin 3) (Fin 3) K)) U = U :=
  mem_glStabilizer_iff

theorem mem_submoduleStabilizer_of_map_le {U : Submodule K (Fin 3 → K)} {x : GL (Fin 3) K}
    (h : Submodule.map (Matrix.toLin' (x : Matrix (Fin 3) (Fin 3) K)) U ≤ U) :
    x ∈ submoduleStabilizer U :=
  mem_glStabilizer_of_map_le h

theorem exists_proper_invariant_subspace (T : Subgroup (GL (Fin 3) K))
    (hT2 : ∀ t ∈ T, t * t = 1)
    (hTc : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s) (g : GL (Fin 3) K) :
    ∃ U : Submodule K (Fin 3 → K), U ≠ ⊥ ∧ U ≠ ⊤ ∧
      ∀ x ∈ T ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup g T, ∀ u ∈ U,
        (x : Matrix (Fin 3) (Fin 3) K) *ᵥ u ∈ U := by
  rcases exists_common_centre_or_axis T hT2 hTc with ⟨p, hp, hcent⟩ | ⟨l, hl, haxis⟩
  · exact exists_invariant_of_common_centre (by norm_num) T g hp hcent
  · exact exists_invariant_of_common_axis (by norm_num) T g hl haxis

end CFSG.LinearAlgebra

end
