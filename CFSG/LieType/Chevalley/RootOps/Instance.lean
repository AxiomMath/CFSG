module

public import CFSG.LieType.Chevalley.RootOps.Finger
public import CFSG.LieType.Chevalley.RootOps.Family
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley.RootOps

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.RootWalk

variable {τ : Tag}

theorem exists_rootPos (α : Root τ) :
    ∃ a, a < τ.rootCertificate.roots.length ∧ τ.rootCertificate.root a = α.1 :=
  RootCertificate.exists_root_eq τ.rootCertificate_check α.2

open _root_.Classical in
@[expose] noncomputable def rootPos (α : Root τ) : ℕ :=
  Nat.find (exists_rootPos α)

theorem rootPos_lt (α : Root τ) : rootPos α < τ.rootCertificate.roots.length := by
  classical
  exact (Nat.find_spec (exists_rootPos α)).1

theorem root_rootPos (α : Root τ) : τ.rootCertificate.root (rootPos α) = α.1 := by
  classical
  exact (Nat.find_spec (exists_rootPos α)).2

theorem rootPos_eq {α : Root τ} {a : ℕ} (ha : a < τ.rootCertificate.roots.length)
    (h : τ.rootCertificate.root a = α.1) : rootPos α = a :=
  rootCertificate_root_injOn (rootPos_lt α) ha ((root_rootPos α).trans h.symm)

theorem rootPos_simpleRoot (j : Fin τ.rank) : rootPos (simpleRoot τ j) = j := by
  obtain ⟨hr, hb, -⟩ := rootCertificate_basis_table (τ := τ)
  exact rootPos_eq (lt_of_lt_of_le j.2 hr) (hb j)

theorem rootPos_neg_simpleRoot (j : Fin τ.rank) :
    rootPos (-simpleRoot τ j) = τ.rootCertificate.image j j := by
  obtain ⟨hr, hb, -⟩ := rootCertificate_basis_table (τ := τ)
  have hj : (j : ℕ) < τ.rootCertificate.roots.length := lt_of_lt_of_le j.2 hr
  refine rootPos_eq (rootCertificate_image_lt hj j) ?_
  rw [rootCertificate_root_image hj, hb j, reflect_single_self]
  rfl

theorem rootPos_smul (i : Fin τ.rank) (α : Root τ) :
    rootPos (simple τ i • α) = τ.rootCertificate.image (rootPos α) i := by
  refine rootPos_eq (rootCertificate_image_lt (rootPos_lt α) i) ?_
  rw [rootCertificate_root_image (rootPos_lt α), root_rootPos, coe_smul_root, simple_smul]

@[expose] def allValid (τ : Tag) : Bool :=
  (List.range τ.rootCertificate.roots.length).all fun a =>
    [1, 2, 3].all fun k => validB τ (entries τ a k)

@[expose] def conjRange (τ : Tag) (lo hi : ℕ) : Bool :=
  (List.range' lo (hi - lo)).all fun a => (List.finRange τ.rank).all fun i =>
    [1, 2, 3].all fun k => fingerCheck τ a i k

theorem conjRange_spec {lo hi : ℕ} (h : conjRange τ lo hi = true) {a : ℕ} (ha : lo ≤ a)
    (ha' : a < hi) (i : Fin τ.rank) {k : ℕ} (hk : k ∈ [1, 2, 3]) : fingerCheck τ a i k = true := by
  simp only [conjRange, List.all_eq_true, List.mem_range', List.mem_finRange, true_implies] at h
  exact h a ⟨a - lo, by omega, by omega⟩ i k hk

structure DataChecks (τ : Tag) : Prop where
  tab : tabCheck τ = true
  valid : allValid τ = true
  conj : ∀ a < τ.rootCertificate.roots.length, ∀ (i : Fin τ.rank), ∀ k ∈ [1, 2, 3],
    fingerCheck τ a i k = true
  simple : ∀ (R : Type) [CommRing R] (j : Fin τ.rank) (k : ℕ), 1 ≤ k → k ≤ 3 →
    entriesOp τ R (entries τ j k) = xCoeff τ R j k
  negSimple : ∀ (R : Type) [CommRing R] (j : Fin τ.rank) (k : ℕ), 1 ≤ k → k ≤ 3 →
    entriesOp τ R (entries τ (τ.rootCertificate.image j j) k) = yCoeff τ R j k

theorem mem_one_two_three {k : ℕ} (h1 : 1 ≤ k) (h3 : k ≤ 3) : k ∈ [1, 2, 3] := by
  interval_cases k <;> simp

theorem validB_of_allValid (h : allValid τ = true) {a : ℕ}
    (ha : a < τ.rootCertificate.roots.length) {k : ℕ} (hk : k ∈ [1, 2, 3]) :
    validB τ (entries τ a k) = true := by
  simp only [allValid, List.all_eq_true, List.mem_range] at h
  exact h a ha k hk

@[expose] noncomputable def dataD (τ : Tag) (R : Type) [CommRing R] (α : Root τ) (k : ℕ) :
    Module.End R (RootModule τ R) :=
  if k = 0 then 1 else if k ≤ 3 then entriesOp τ R (entries τ (rootPos α) k) else 0

@[expose] noncomputable def DataChecks.family (h : DataChecks τ) : RootOperatorFamily τ where
  D := dataD τ
  D_zero R _ α := by simp [dataD]
  D_eq_zero R _ α k hk := by
    unfold dataD
    simp only [show k ≠ 0 by omega, show ¬k ≤ 3 by omega, ↓reduceIte]
  D_simple R _ j k := by
    unfold dataD
    rw [rootPos_simpleRoot]
    split_ifs with h0 h3
    · subst h0
      exact (xCoeff_zero j).symm
    · exact h.simple R j k (by omega) h3
    · exact (xCoeff_eq_zero j (by omega)).symm
  D_neg_simple R _ j k := by
    unfold dataD
    rw [rootPos_neg_simpleRoot]
    split_ifs with h0 h3
    · subst h0
      exact (yCoeff_zero j).symm
    · exact h.negSimple R j k (by omega) h3
    · exact (yCoeff_eq_zero j (by omega)).symm
  sign i α := signOf τ (rootPos α) i
  sign_eq i α := signOf_eq τ (rootPos α) i
  conj R _ i α k := by
    unfold dataD
    split_ifs with h0 h3
    · subst h0
      simp
    · have hk : k ∈ [1, 2, 3] := mem_one_two_three (by omega) h3
      rw [rootPos_smul]
      exact conj_of_fingerCheck h.tab (validB_of_allValid h.valid (rootPos_lt α) hk)
        (h.conj (rootPos α) (rootPos_lt α) i k hk)
    · simp

end CFSG.LieType.Chevalley.RootOps
