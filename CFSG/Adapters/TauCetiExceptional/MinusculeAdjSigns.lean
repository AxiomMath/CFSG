module

public import CFSG.LieType.Steinberg.Minuscule.RootOps

public noncomputable section

namespace CFSG.TauCetiBridge.Minuscule

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule MinData

structure AdjSigns (τ : Tag) where
  eps : List Bool
  sgn : List Bool

namespace AdjSigns

variable {τ : Tag} (S : AdjSigns τ)

@[expose] def epsZ (i : Fin τ.rank) : ℤ := if S.eps.getD i false then -1 else 1

@[expose] def sgnZ (k : ℕ) : ℤ := if S.sgn.getD k false then -1 else 1

open Classical in
@[expose] def sRoot (γ : Fin τ.rank → ℤ) : ℤ :=
  if h : ∃ k, k < τ.rootCertificate.roots.length ∧ τ.rootCertificate.root k = γ then
    S.sgnZ (Nat.find h) else 1

@[expose] def check (D : MinData τ) : Bool :=
  ((List.finRange τ.rank).all fun i => (List.finRange τ.rank).all fun j =>
    decide (i = j) || decide (τ.cartan i j = 0) ||
      (decide (τ.cartan i j = -1) && (S.eps.getD i false != S.eps.getD j false))) &&
  ((List.finRange τ.rank).all fun i => (S.sgn.getD i false == !S.eps.getD i false) &&
    (S.sgn.getD (τ.rootCertificate.image i i) false == S.eps.getD i false)) &&
  ((List.range τ.rootCertificate.roots.length).all fun l => (List.finRange τ.rank).all fun j =>
    (List.range τ.rootCertificate.roots.length).all fun m =>
      !(List.ofFn (τ.rootCertificate.root m) ==
          List.ofFn (Pi.single j 1 + τ.rootCertificate.root l)) ||
        (union D.d (comp D.d (D.op j) (D.op l)) (neg D.d (comp D.d (D.op l) (D.op j))) ==
          if S.sgn.getD m false == S.sgn.getD l false then D.op m else neg D.d (D.op m)))

theorem epsZ_mul_self (i : Fin τ.rank) : S.epsZ i * S.epsZ i = 1 := by
  unfold epsZ
  split_ifs <;> norm_num

theorem sgnZ_mul_self (k : ℕ) : S.sgnZ k * S.sgnZ k = 1 := by
  unfold sgnZ
  split_ifs <;> norm_num

theorem sRoot_mul_self (γ : Fin τ.rank → ℤ) : S.sRoot γ * S.sRoot γ = 1 := by
  unfold sRoot
  split_ifs
  · exact S.sgnZ_mul_self _
  · norm_num

theorem sRoot_root
    {k : ℕ} (hk : k < τ.rootCertificate.roots.length) :
    S.sRoot (τ.rootCertificate.root k) = S.sgnZ k := by
  classical
  have h : ∃ k', k' < τ.rootCertificate.roots.length ∧
      τ.rootCertificate.root k' = τ.rootCertificate.root k := ⟨k, hk, rfl⟩
  rw [sRoot, dite_eq_left h]
  congr 1
  exact root_injOn (Nat.find_spec h).1 hk (Nat.find_spec h).2

variable {S}

section Check

variable {D : MinData τ} (hS : S.check D = true)
include hS

private theorem check_and :
    (∀ i j : Fin τ.rank, i = j ∨ τ.cartan i j = 0 ∨
      (τ.cartan i j = -1 ∧ S.eps.getD i false ≠ S.eps.getD j false)) ∧
    (∀ i : Fin τ.rank, S.sgn.getD i false = !S.eps.getD i false ∧
      S.sgn.getD (τ.rootCertificate.image i i) false = S.eps.getD i false) ∧
    ∀ l < τ.rootCertificate.roots.length, ∀ j : Fin τ.rank,
      ∀ m < τ.rootCertificate.roots.length,
        τ.rootCertificate.root m = Pi.single j 1 + τ.rootCertificate.root l →
          union D.d (comp D.d (D.op j) (D.op l)) (neg D.d (comp D.d (D.op l) (D.op j))) =
            if S.sgn.getD m false = S.sgn.getD l false then D.op m else neg D.d (D.op m) := by
  have h := hS
  simp only [check, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, List.mem_range,
    true_implies, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq,
    Bool.not_eq_true'] at h
  refine ⟨fun i j => ?_, fun i => ⟨(h.1.2 i).1, (h.1.2 i).2⟩, fun l hl j m hm e => ?_⟩
  · rcases h.1.1 i j with (h1 | h1) | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
  · rcases h.2 l hl j m hm with h1 | h1
    · rw [beq_eq_false_iff_ne] at h1
      exact absurd (congrArg List.ofFn e) h1
    · exact h1

theorem cartan_cases (i j : Fin τ.rank) :
    i = j ∨ τ.cartan i j = 0 ∨ (τ.cartan i j = -1 ∧ S.epsZ j = -S.epsZ i) := by
  rcases (check_and hS).1 i j with h | h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨h1, ?_⟩)
    unfold epsZ
    revert h2
    cases S.eps.getD i false <;> cases S.eps.getD j false <;> simp

theorem sRoot_single
    (i : Fin τ.rank) : S.sRoot (Pi.single i 1) = -S.epsZ i := by
  rw [← root_basis i, S.sRoot_root (lt_of_lt_of_le i.2 rank_le_length), sgnZ, epsZ,
    (check_and hS).2.1 i |>.1]
  cases S.eps.getD i false <;> simp

theorem sRoot_neg_single
    (i : Fin τ.rank) : S.sRoot (-Pi.single i 1) = S.epsZ i := by
  rw [← root_image_self i, S.sRoot_root (image_lt (lt_of_lt_of_le i.2 rank_le_length) i), sgnZ,
    epsZ, (check_and hS).2.1 i |>.2]

variable (hV : D.Valid) (R : Type*) [CommRing R]
include hV

theorem rootOp_single_comm
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (j : Fin τ.rank)
    (hr : IsRoot τ (Pi.single j 1 + γ)) :
    D.rootOp R (Pi.single j 1) * D.rootOp R γ - D.rootOp R γ * D.rootOp R (Pi.single j 1) =
      ((S.sRoot (Pi.single j 1 + γ) * S.sRoot γ : ℤ) : R) •
        D.rootOp R (Pi.single j 1 + γ) := by
  obtain ⟨l, hl, rfl⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hγ
  have hj : (j : ℕ) < τ.rootCertificate.roots.length := lt_of_lt_of_le j.2 rank_le_length
  have hEj : D.rootOp R (Pi.single j 1) = D.E R j := by rw [← root_basis j, rootOp_root hj]
  rcases hV.pairs hl j with h | ⟨hnr, -⟩ | ⟨m, hm, hroot, hdisj, -, -, -⟩
  · exact absurd (by rw [h, add_neg_cancel]) hr.ne_zero
  · exact absurd hr hnr
  · have hu := (check_and hS).2.2 l hl j m hm hroot
    have htu := toEnd_union_neg (R := R) hdisj
    rw [toEnd_comp (hV.wf_op l), toEnd_comp (hV.wf_op j)] at htu
    rw [hEj, rootOp_root hl, ← hroot, rootOp_root hm, S.sRoot_root hm, S.sRoot_root hl]
    change toEnd R D.d (D.op j) * toEnd R D.d (D.op l) -
      toEnd R D.d (D.op l) * toEnd R D.d (D.op j) = _
    rw [← htu, hu]
    unfold sgnZ
    split_ifs with h1 h2 h3 h3 <;> simp_all [MinData.E, toEnd_neg]

end Check

end AdjSigns

end CFSG.TauCetiBridge.Minuscule
