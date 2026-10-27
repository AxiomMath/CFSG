module

public import CFSG.LocalAnalysis.OddStandard.Solomon75AhatDataPerm
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4GenInputs
public import Mathlib.GroupTheory.GroupAction.Jordan

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup MulAction

theorem alt_le_closure_of_two_transitive {n : ℕ} {S : Set (Perm (Fin n))} {p q : Fin n}
    (hpq : p ≠ q)
    (hpairs : ∀ x y : Fin n, x ≠ y → ∃ h ∈ Subgroup.closure S, h p = x ∧ h q = y)
    (hc : ∃ c ∈ Subgroup.closure S, c.IsThreeCycle) :
    alternatingGroup (Fin n) ≤ Subgroup.closure S := by
  obtain ⟨c, hcmem, hc3⟩ := hc
  have h2 : IsMultiplyPretransitive (Subgroup.closure S) (Fin n) 2 := by
    refine (isPretransitive_iff_base (Function.Embedding.embFinTwo hpq)).2 fun e => ?_
    obtain ⟨h, hh, hp, hq⟩ := hpairs (e 0) (e 1) (e.injective.ne (by decide))
    refine ⟨⟨h, hh⟩, ?_⟩
    refine Function.Embedding.ext fun i => ?_
    fin_cases i
    · exact hp
    · exact hq
  exact alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem
    (isPreprimitive_of_is_two_pretransitive h2) hc3 hcmem

namespace AhatData

variable {n : ℕ}

theorem exists_eightSub' {xa xb xc : Array ℕ} {a b c : Perm (Fin n)} (ha : Rep n xa a)
    (hb : Rep n xb b) (hc : Rep n xc c) {Q : Subgroup (Perm (Fin n))} (haQ : a ∈ Q) (hbQ : b ∈ Q)
    (hcQ : c ∈ Q) (hia : IsoI a) (hib : IsoI b) (hic : IsoI c) (hiab : IsoI (a * b))
    (hiac : IsoI (a * c)) (hibc : IsoI (b * c)) (hiabc : IsoI (a * b * c))
    (h : eightSubOK n xa xb xc = true) :
    ∃ E : Subgroup (Perm (Fin n)), E ≤ Q ∧ Nat.card E = 8 ∧ (∀ e ∈ E, e = 1 ∨ IsoI e) ∧
      a ∈ E ∧ b ∈ E ∧ c ∈ E := by
  set Ei : Fin 8 → Perm (Fin n) := ![1, a, b, a * b, c, a * c, b * c, a * b * c] with hEi
  have hsz : (eightArr n xa xb xc).size = 8 := rfl
  have hrep : ∀ i : Fin 8, Rep n (eightArr n xa xb xc)[(i : ℕ)]! (Ei i) := by
    intro i
    fin_cases i
    · exact rep_idA
    · exact ha
    · exact hb
    · exact rep_mulA ha hb
    · exact hc
    · exact rep_mulA ha hc
    · exact rep_mulA hb hc
    · exact rep_mulA (rep_mulA ha hb) hc
  have hsq : ∀ i : Fin 8, Ei i * Ei i = 1 := by
    intro i
    fin_cases i
    · exact mul_one 1
    · exact hia.1
    · exact hib.1
    · exact hiab.1
    · exact hic.1
    · exact hiac.1
    · exact hibc.1
    · exact hiabc.1
  have hiso : ∀ i : Fin 8, Ei i = 1 ∨ IsoI (Ei i) := by
    intro i
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr hia
    · exact Or.inr hib
    · exact Or.inr hiab
    · exact Or.inr hic
    · exact Or.inr hiac
    · exact Or.inr hibc
    · exact Or.inr hiabc
  have hmemQ : ∀ i : Fin 8, Ei i ∈ Q := by
    intro i
    fin_cases i
    · exact Q.one_mem
    · exact haQ
    · exact hbQ
    · exact mul_mem haQ hbQ
    · exact hcQ
    · exact mul_mem haQ hcQ
    · exact mul_mem hbQ hcQ
    · exact mul_mem (mul_mem haQ hbQ) hcQ
  simp only [eightSubOK, Bool.and_eq_true] at h
  obtain ⟨hcl, hdist⟩ := h
  rw [nat_all_iff] at hcl hdist
  have hclosed : ∀ i j : Fin 8, ∃ k : Fin 8, Ei i * Ei j = Ei k := by
    intro i j
    have h1 := hcl i i.2
    rw [nat_all_iff] at h1
    have h2 := h1 j j.2
    rw [Array.any_eq_true'] at h2
    obtain ⟨z, hz, hzeq⟩ := h2
    obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 hz
    have hk8 : k < 8 := by simpa [hsz] using hk
    refine ⟨⟨k, hk8⟩, ?_⟩
    have e2 := rep_of_eqA_left (rep_mulA (hrep i) (hrep j)) hzeq
    have e3 := hrep ⟨k, hk8⟩
    rw [getElem!_pos _ k hk] at e3
    exact Rep.unique e2 e3
  have hdist' : ∀ i j : Fin 8, (j : ℕ) < i → Ei i ≠ Ei j := by
    intro i j hji heq
    have h1 := hdist i i.2
    rw [nat_all_iff] at h1
    have h2 := h1 j hji
    rw [Bool.not_eq_true'] at h2
    have h3 : eqA n (eightArr n xa xb xc)[(i : ℕ)]! (eightArr n xa xb xc)[(j : ℕ)]! = true :=
      (eqA_iff (hrep i) (hrep j)).2 heq
    rw [h3] at h2
    exact absurd h2 (by simp)
  have hinj : Function.Injective Ei := by
    intro i j heq
    by_contra hne
    rcases Nat.lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hlt
    · exact hdist' j i hlt heq.symm
    · exact hdist' i j hlt heq
  let T : Subgroup (Perm (Fin n)) :=
    { carrier := {σ | ∃ i : Fin 8, σ = Ei i}
      mul_mem' := by
        rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
        obtain ⟨k, hk⟩ := hclosed i j
        exact ⟨k, hk⟩
      one_mem' := ⟨0, rfl⟩
      inv_mem' := by
        rintro _ ⟨i, rfl⟩
        exact ⟨i, inv_eq_of_mul_eq_one_right (hsq i)⟩ }
  refine ⟨T, ?_, ?_, ?_, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨4, rfl⟩⟩
  · rintro _ ⟨i, rfl⟩
    exact hmemQ i
  · have hbij : Function.Bijective (fun i : Fin 8 => (⟨Ei i, i, rfl⟩ : T)) := by
      constructor
      · intro i j heq
        exact hinj (congrArg Subtype.val heq)
      · rintro ⟨_, i, rfl⟩
        exact ⟨i, rfl⟩
    rw [← Nat.card_eq_of_bijective _ hbij]
    simp
  · rintro _ ⟨i, rfl⟩
    exact hiso i

structure GenGood (n : ℕ) (Q : Subgroup (Perm (Fin n))) (jmode : Bool) : Prop where
  ex : ∃ l : List (Perm (Fin n) × Perm (Fin n)),
    (∀ p ∈ l, p.1 ∈ Q ∧ IsoI p.1 ∧ p.2 ∈ alternatingGroup (Fin n) ∧ p.2 * p.1 = p.1 * p.2 ∧
      (jmode = true → ∃ E : Subgroup (Perm (Fin n)), E ≤ Q ∧ Nat.card E = 8 ∧
        (∀ e ∈ E, e = 1 ∨ IsoI e) ∧ p.1 ∈ E)) ∧
    alternatingGroup (Fin n) ≤ Subgroup.closure {g | ∃ p ∈ l, p.2 = g}

theorem GenGood.conj {Q : Subgroup (Perm (Fin n))} {jmode : Bool} (h : GenGood n Q jmode)
    (g : Perm (Fin n)) : GenGood n (conjSub g Q) jmode := by
  obtain ⟨l, hl, hgen⟩ := h.ex
  refine ⟨l.map (fun p => (g * p.1 * g⁻¹, g * p.2 * g⁻¹)), ?_, ?_⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    obtain ⟨h1, h2, h3, h4, h5⟩ := hl q hq
    refine ⟨conj_mem_conjSub h1, isoI_conj.2 h2, ?_, ?_, fun hj => ?_⟩
    · rw [Perm.mem_alternatingGroup] at h3 ⊢
      simp [Perm.sign_mul, h3]
    · exact conj_comm_iff.2 h4.symm |>.symm
    · obtain ⟨E, hEQ, hE8, hEi, haE⟩ := h5 hj
      refine ⟨conjSub g E, ?_, ?_, ?_, conj_mem_conjSub haE⟩
      · rintro _ ⟨x, hx, rfl⟩
        exact conj_mem_conjSub (hEQ hx)
      · rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj g).injective, hE8]
      · intro e he
        obtain ⟨x, hx, rfl⟩ := exists_conj_mem.1 he
        rcases hEi x hx with h1 | h1
        · left
          rw [h1]
          group
        · right
          exact isoI_conj.2 h1
  · intro x hx
    have hx' : g⁻¹ * x * g ∈ alternatingGroup (Fin n) := by
      rw [Perm.mem_alternatingGroup] at hx ⊢
      simp [Perm.sign_mul, hx]
    have h1 := hgen hx'
    have h2 : g * (g⁻¹ * x * g) * g⁻¹ ∈
        (Subgroup.closure {g | ∃ p ∈ l, p.2 = g}).map (MulAut.conj g).toMonoidHom :=
      ⟨_, h1, by simp [MulAut.conj_apply]⟩
    rw [MonoidHom.map_closure] at h2
    have h3 : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [h3] at h2
    refine Subgroup.closure_mono ?_ h2
    rintro _ ⟨y, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨(g * p.1 * g⁻¹, g * p.2 * g⁻¹), List.mem_map.2 ⟨p, hp, rfl⟩,
      by simp [MulAut.conj_apply]⟩

section Sound

variable [NeZero n]

omit [NeZero n] in
theorem swOK_spec {sw : List (ℕ × ℕ)} {ev : Bool} (h : swOK n sw ev = true) :
    (∀ p ∈ sw, p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2) ∧ (ev = true → Even sw.length) := by
  unfold swOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun p hp => ?_, fun hev => ?_⟩
  · have := h1 p hp
    exact ⟨this.1.1, this.1.2, this.2⟩
  · rcases h2 with h2 | h2
    · rw [h2] at hev
      exact absurd hev (by simp)
    · exact Nat.even_iff.2 h2

end Sound

end AhatData

end CFSG.OddStandard.Solomon75
