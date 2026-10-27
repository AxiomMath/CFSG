module

public import Certificates.Data.Kernel.PermCent.SylowListC
public import CFSG.Certificates.Kernel.PermCent.SylowReps
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.Certificates.Kernel.PkCV.SylL

open Subgroup

variable {n : Nat} [Small n]

theorem ev_wordC_mem (gs : List (CV n)) (w : List Nat) :
    ev (wordC gs w) ∈ closure {σ | σ ∈ gs.map ev} := by
  induction w with
  | nil =>
    rw [wordC, ev_one]
    exact one_mem _
  | cons k w ih =>
    rw [wordC, ev_mul]
    refine mul_mem ?_ ih
    rw [List.getD_eq_getElem?_getD]
    cases hk : gs[k]? with
    | none =>
      rw [Option.getD_none, ev_one]
      exact one_mem _
    | some g =>
      rw [Option.getD_some]
      exact subset_closure (List.mem_map_of_mem (List.mem_of_getElem? hk))

theorem mem_of_words (gs : List (CV n)) (W : List (List Nat)) :
    ∀ x ∈ W.map (wordC gs), ev x ∈ closure {σ | σ ∈ gs.map ev} := by
  intro x hx
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
  exact ev_wordC_mem gs w

theorem closure_words_le (gs : List (CV n)) (W : List (List Nat)) :
    closure {σ | σ ∈ (W.map (wordC gs)).map ev} ≤ closure {σ | σ ∈ gs.map ev} := by
  rw [closure_le]
  intro σ hσ
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hσ
  exact mem_of_words gs W x hx

@[expose] noncomputable def evAt (L : List (CV n)) (i : Nat) : Equiv.Perm (Fin n) :=
  if h : i < L.length then ev L[i] else 1

theorem image_evAt (G : List (CV n)) : evAt G '' {k | k < G.length} = {σ | σ ∈ G.map ev} := by
  ext σ
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk' : k < G.length := hk
    rw [Set.mem_setOf_eq, evAt, dif_pos hk']
    exact List.mem_map_of_mem (List.getElem_mem hk')
  · intro hσ
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hσ
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hg
    exact ⟨k, hk, by rw [evAt, dif_pos hk]⟩

theorem nodup_of_distinctC : ∀ {L : List (CV n)}, distinctC L = true → L.Nodup
  | [], _ => List.nodup_nil
  | x :: L, h => by
    rw [distinctC, Bool.and_eq_true, List.all_eq_true] at h
    refine List.nodup_cons.2 ⟨fun hx => ?_, nodup_of_distinctC h.2⟩
    have h1 := h.1 x hx
    simp at h1

theorem idx_inj {α : Type*} : ∀ {L : List α}, L.Nodup → ∀ {i j : Nat} (hi : i < L.length)
    (hj : j < L.length), L[i] = L[j] → i = j
  | [], _, _, _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | x :: L, h, i, j, hi, hj, e => by
    rw [List.nodup_cons] at h
    match i, j, hi, hj, e with
    | 0, 0, _, _, _ => rfl
    | 0, j + 1, _, hj, e =>
      rw [List.getElem_cons_zero, List.getElem_cons_succ] at e
      exact absurd (e ▸ List.getElem_mem _) h.1
    | i + 1, 0, hi, _, e =>
      rw [List.getElem_cons_zero, List.getElem_cons_succ] at e
      exact absurd (e.symm ▸ List.getElem_mem _) h.1
    | i + 1, j + 1, hi, hj, e =>
      rw [List.getElem_cons_succ, List.getElem_cons_succ] at e
      rw [idx_inj h.2 (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj) e]

theorem closedC_sound (G L : List (CV n)) (hmem : ∀ x ∈ L, ev x ∈ closure {σ | σ ∈ G.map ev})
    (h : closedC G L = true) :
    Nat.card (closure {σ | σ ∈ G.map ev}) = L.length ∧
      ∀ y ∈ closure {σ | σ ∈ G.map ev}, ∃ x ∈ L, ev x = y := by
  simp only [closedC, Bool.and_eq_true, List.any_eq_true, List.all_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨x1, hx1, e1⟩, hd⟩, hc⟩ := h
  have hnd := nodup_of_distinctC hd
  have himg : (fun k => (MonoidHom.id (Equiv.Perm (Fin n))) (evAt G k)) '' {k | k < G.length} =
      {σ | σ ∈ G.map ev} := image_evAt G
  have h0 : ∃ i < L.length, evAt L i = 1 := by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx1
    exact ⟨i, hi, by rw [evAt, dif_pos hi, e1, ev_one]⟩
  have hm : ∀ i < L.length, evAt L i ∈
      closure ((fun k => (MonoidHom.id (Equiv.Perm (Fin n))) (evAt G k)) '' {k | k < G.length}) := by
    intro i hi
    rw [himg, evAt, dif_pos hi]
    exact hmem _ (List.getElem_mem hi)
  have hcl : ∀ i < L.length, ∀ k < G.length, ∃ j < L.length,
      (MonoidHom.id (Equiv.Perm (Fin n))) (evAt G k) * evAt L i = evAt L j := by
    intro i hi k hk
    obtain ⟨y, hy, e⟩ := hc G[k] (List.getElem_mem hk) L[i] (List.getElem_mem hi)
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hy
    refine ⟨j, hj, ?_⟩
    rw [MonoidHom.id_apply, evAt, dif_pos hk, evAt, dif_pos hi, evAt, dif_pos hj, ← ev_mul, e]
  have hinj : ∀ i < L.length, ∀ j < L.length, evAt L i = evAt L j → i = j := by
    intro i hi j hj e
    rw [evAt, dif_pos hi, evAt, dif_pos hj] at e
    exact idx_inj hnd hi hj (ev_injective e)
  obtain ⟨hcard, hall⟩ := CFSG.KC.OrbGroup.group_of_reps (MonoidHom.id (Equiv.Perm (Fin n)))
    Function.injective_id (evAt G) (evAt L) h0 hm hcl hinj
  rw [image_evAt] at hcard hall
  refine ⟨hcard, fun y hy => ?_⟩
  obtain ⟨i, hi, e⟩ := hall y hy
  refine ⟨L[i], List.getElem_mem hi, ?_⟩
  rw [evAt, dif_pos hi] at e
  exact e

theorem coverAtC_sound {gA R : List (CV n)} {x : CV n} {c : Option (Nat × List Nat)}
    (h : coverAtC gA R x c = true) :
    (x * x = 1 → x = 1) ∨ ∃ ρ ∈ R, ∃ w, wordC gA w * x = ρ * wordC gA w := by
  cases c with
  | none =>
    refine Or.inl fun hx => ?_
    by_contra hne
    simp [coverAtC, hx, hne] at h
  | some p =>
    obtain ⟨r, w⟩ := p
    cases hr : R[r]? with
    | none => simp [coverAtC, hr] at h
    | some ρ =>
      simp only [coverAtC, hr, decide_eq_true_eq] at h
      exact Or.inr ⟨ρ, List.mem_of_getElem? hr, w, h⟩

theorem coverC_sound (gA R : List (CV n)) : ∀ (L : List (CV n)) (cs : List (Option (Nat × List Nat))),
    coverC gA R L cs = true →
      ∀ x ∈ L, (x * x = 1 → x = 1) ∨ ∃ ρ ∈ R, ∃ w, wordC gA w * x = ρ * wordC gA w
  | [], _, _, x, hx => absurd hx List.not_mem_nil
  | x :: L, c :: cs, h, y, hy => by
    rw [coverC, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hy with rfl | hy
    · exact coverAtC_sound h.1
    · exact coverC_sound gA R L cs h.2 y hy
  | _ :: _, [], h, _, _ => by
    rw [coverC] at h
    exact absurd h Bool.false_ne_true

theorem cover_sound (gA R L : List (CV n)) (cs : List (Option (Nat × List Nat)))
    (h : coverC gA R L cs = true) :
    ∀ x ∈ L, ev x ^ 2 = 1 → ev x ≠ 1 →
      ∃ ρ ∈ R, ∃ g ∈ closure {σ | σ ∈ gA.map ev}, g * ev x = ev ρ * g := by
  intro x hx h2 h1
  rcases coverC_sound gA R L cs h x hx with h3 | ⟨ρ, hρ, w, e⟩
  · refine absurd ?_ h1
    rw [h3 (ev_injective (by rw [ev_mul, ← sq, h2, ev_one])), ev_one]
  · exact ⟨ρ, hρ, _, ev_wordC_mem gA w, by rw [← ev_mul, e, ev_mul]⟩

theorem forall_invol_of_checks (A : Subgroup (Equiv.Perm (Fin n))) (gA G R L : List (CV n))
    (cs : List (Option (Nat × List Nat))) (hgA : closure {σ | σ ∈ gA.map ev} ≤ A)
    (hGA : closure {σ | σ ∈ G.map ev} ≤ A) (hL : ∀ x ∈ L, ev x ∈ closure {σ | σ ∈ G.map ev})
    (hcl : closedC G L = true) (hcov : coverC gA R L cs = true) {k m : Nat} (hk : 0 < k)
    (hT : L.length = 2 ^ k) (hA : Nat.card A = 2 ^ k * m) (hm : ¬ 2 ∣ m)
    (Φ : Equiv.Perm (Fin n) → Prop) (hΦ : ∀ g ∈ A, ∀ x ∈ A, Φ (g * x * g⁻¹) → Φ x)
    (hR : ∀ ρ ∈ R, Φ (ev ρ)) : ∀ x ∈ A, x ^ 2 = 1 → x ≠ 1 → Φ x := by
  obtain ⟨hcard, hall⟩ := closedC_sound G L hL hcl
  let Ψ : Equiv.Perm (Fin n) → Prop := fun x => x ^ 2 = 1 → x ≠ 1 → Φ x
  have hinv : ∀ g ∈ A, ∀ x ∈ A, Ψ (g * x * g⁻¹) → Ψ x := by
    intro g hg x hx h h2 h1
    refine hΦ g hg x hx (h (by rw [conj_pow, h2, mul_one, mul_inv_cancel]) fun e => h1 ?_)
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [e, mul_one, inv_mul_cancel]
  have hLT : ∀ x ∈ closure {σ | σ ∈ G.map ev}, x ∈ L.map ev := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hall x hx
    exact List.mem_map_of_mem hy
  have hRΨ : ∀ r ∈ R.map ev, Ψ r := by
    intro r hr _ _
    obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.1 hr
    exact hR ρ hρ
  have hcov' : ∀ x ∈ L.map ev, Ψ x ∨ ∃ r ∈ R.map ev, ∃ g ∈ A, g * x = r * g := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    by_cases h2 : ev y ^ 2 = 1
    · by_cases h1 : ev y = 1
      · exact Or.inl fun _ h1' => absurd h1 h1'
      · obtain ⟨ρ, hρ, g, hg, e⟩ := cover_sound gA R L cs hcov y hy h2 h1
        exact Or.inr ⟨ev ρ, List.mem_map_of_mem hρ, g, hgA hg, e⟩
    · exact Or.inl fun h2' => absurd h2' h2
  have key := CFSG.KC.SylowReps.forall_of_sylow_reps A (closure {σ | σ ∈ G.map ev})
    Nat.prime_two hGA (hcard.trans hT) hA hm Ψ hinv (L.map ev) (R.map ev) hLT hRΨ hcov'
  intro x hx h2 h1
  have e : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  exact key x hx (by rw [e, pow_mul, h2, one_pow]) h2 h1

end CFSG.Certificates.Kernel.PkCV.SylL

end
