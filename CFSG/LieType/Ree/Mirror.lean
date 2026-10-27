module

public import CFSG.Blueprint.ChevalleyInfinitesimals
public import Certificates.Certificate113
public import Certificates.Certificate114

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint.Chevalley

variable {τ : Tag} (C : RootCertificate τ) (S : StringData τ)

abbrev Idx : Type := Fin τ.rank ⊕ Fin C.roots.length

abbrev Col : Type := Option (Idx C × ℤ)

@[expose] def vecBEq (u v : Fin τ.rank → ℤ) : Bool :=
  List.ofFn u == List.ofFn v

theorem vecBEq_iff {u v : Fin τ.rank → ℤ} : vecBEq u v = true ↔ u = v := by
  rw [vecBEq, beq_iff_eq, List.ofFn_inj]

@[expose] def findRoot (v : Fin τ.rank → ℤ) : Option (Fin C.roots.length) :=
  match (S.bucket v).find? fun n => vecBEq (C.root n) v with
  | some n => if h : n < C.roots.length then some ⟨n, h⟩ else none
  | none => none

@[expose] def rootCol (v : Fin τ.rank → ℤ) : Col C :=
  (findRoot C S v).map fun n => (.inr n, 1)

@[expose] def scaleCol (c : ℤ) (u : Col C) : Col C :=
  u.map fun a => (a.1, c * a.2)

@[expose] def bindCol (f : Idx C → Col C) (u : Col C) : Col C :=
  u.bind fun a => scaleCol C a.2 (f a.1)

@[expose] def normCol (p : ℕ) (u : Col C) : Col C :=
  u.bind fun a => if a.2 % (p : ℤ) = 0 then none else some (a.1, a.2 % (p : ℤ))

@[expose] def opEq (p : ℕ) (f g : Idx C → Col C) : Bool :=
  (List.finRange τ.rank).all (fun j => normCol C p (f (.inl j)) == normCol C p (g (.inl j))) &&
    (List.finRange C.roots.length).all fun m =>
      normCol C p (f (.inr m)) == normCol C p (g (.inr m))

@[expose] def xCol (i : Fin τ.rank) (k : ℕ) : Idx C → Col C
  | .inl j =>
    if k = 0 then some (.inl j, 1)
    else if k = 1 then scaleCol C (τ.cartan j i).natAbs (rootCol C S (Pi.single i 1)) else none
  | .inr m =>
    if vecBEq (C.root m) (Pi.single i 1) then (if k = 0 then some (.inr m, 1) else none)
    else if vecBEq (C.root m) (-Pi.single i 1) then
      (if k = 0 then some (.inr m, 1) else if k = 1 then some (.inl i, 1)
      else if k = 2 then rootCol C S (Pi.single i 1) else none)
    else
      scaleCol C ((S.down m i + k).choose k) (rootCol C S (C.root m + (k : ℤ) • Pi.single i 1))

@[expose] def yCol (i : Fin τ.rank) (k : ℕ) : Idx C → Col C
  | .inl j =>
    if k = 0 then some (.inl j, 1)
    else if k = 1 then scaleCol C (τ.cartan j i).natAbs (rootCol C S (-Pi.single i 1)) else none
  | .inr m =>
    if vecBEq (C.root m) (-Pi.single i 1) then (if k = 0 then some (.inr m, 1) else none)
    else if vecBEq (C.root m) (Pi.single i 1) then
      (if k = 0 then some (.inr m, 1) else if k = 1 then some (.inl i, 1)
      else if k = 2 then rootCol C S (-Pi.single i 1) else none)
    else
      scaleCol C ((S.up m i + k).choose k) (rootCol C S (C.root m - (k : ℤ) • Pi.single i 1))

variable {C} (hC : C.check = true)

@[expose] def toLabel : Idx C → Label τ
  | .inl j => .inl j
  | .inr m => .inr ⟨C.root m, RootCertificate.isRoot_root hC m m.2⟩

variable (R : Type*) [CommRing R]

@[expose] def toVec : Col C → RootModule τ R
  | none => 0
  | some a => (a.2 : R) • Finsupp.single (toLabel hC a.1) 1

@[simp] theorem toVec_none : toVec hC R none = 0 :=
  rfl

@[simp] theorem toVec_some (a : Idx C) (c : ℤ) :
    toVec hC R (some (a, c)) = (c : R) • Finsupp.single (toLabel hC a) 1 :=
  rfl

theorem rootVec_eq_single {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    rootVec τ R β = Finsupp.single (Sum.inr ⟨β, hβ⟩) 1 :=
  dite_eq_left hβ

theorem rootVec_eq_zero {β : Fin τ.rank → ℤ} (hβ : ¬IsRoot τ β) : rootVec τ R β = 0 :=
  dite_eq_right hβ

theorem single_toLabel_inr (m : Fin C.roots.length) :
    Finsupp.single (toLabel hC (.inr m)) (1 : R) = rootVec τ R (C.root m) :=
  (rootVec_eq_single R _).symm

theorem single_toLabel_inl (j : Fin τ.rank) :
    Finsupp.single (toLabel hC (.inl j : Idx C)) (1 : R) = hVec τ R j :=
  rfl

theorem surjective_toLabel : Function.Surjective (toLabel hC) := by
  rintro (j | ⟨α, hα⟩)
  · exact ⟨.inl j, rfl⟩
  · obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq hC hα
    exact ⟨.inr ⟨k, hk⟩, rfl⟩

variable {S}

theorem findRoot_eq_some {v : Fin τ.rank → ℤ} {n : Fin C.roots.length}
    (h : findRoot C S v = some n) : C.root n = v := by
  unfold findRoot at h
  split at h
  · rename_i n' hn'
    split at h
    · cases h
      have := List.find?_some hn'
      exact vecBEq_iff.1 this
    · cases h
  · cases h

theorem lt_of_mem_bucket (hS : S.check C = true) {v : Fin τ.rank → ℤ} {n : ℕ}
    (hn : n ∈ S.bucket v) : n < C.roots.length := by
  simp only [StringData.check, Bool.and_eq_true] at hS
  obtain ⟨⟨⟨-, hbb⟩, -⟩, -⟩ := hS
  simp only [StringData.checkBucketBounds, List.all_eq_true, decide_eq_true_eq] at hbb
  simp only [StringData.bucket] at hn
  split_ifs at hn
  · obtain ⟨x, hx, hnx⟩ := StringData.mem_of_mem_getD hn
    exact hbb x hx n hnx
  · simp at hn

theorem mem_bucket_root (hS : S.check C = true) {k : ℕ} (hk : k < C.roots.length) :
    k ∈ S.bucket (C.root k) := by
  simp only [StringData.check, Bool.and_eq_true] at hS
  obtain ⟨⟨⟨hb, -⟩, -⟩, -⟩ := hS
  simp only [StringData.checkBuckets, List.all_eq_true, List.mem_range,
    List.contains_iff_mem] at hb
  exact hb k hk

include hC in
theorem findRoot_eq_none (hS : S.check C = true) {v : Fin τ.rank → ℤ}
    (h : findRoot C S v = none) : ¬IsRoot τ v := by
  intro hv
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq hC hv
  unfold findRoot at h
  split at h
  · rename_i n hn
    split at h
    · cases h
    · rename_i hlt
      exact hlt (lt_of_mem_bucket hS (List.mem_of_find?_eq_some hn))
  · rename_i hn
    rw [List.find?_eq_none] at hn
    exact hn k (mem_bucket_root hS hk) (vecBEq_iff.2 rfl)

theorem toVec_rootCol (hS : S.check C = true) (v : Fin τ.rank → ℤ) :
    toVec hC R (rootCol C S v) = rootVec τ R v := by
  unfold rootCol
  cases h : findRoot C S v with
  | none => rw [Option.map_none, toVec_none, rootVec_eq_zero R (findRoot_eq_none hC hS h)]
  | some n =>
    have hv := findRoot_eq_some h
    subst hv
    rw [Option.map_some, toVec_some, Int.cast_one, one_smul, single_toLabel_inr]

theorem toVec_scaleCol (c : ℤ) (u : Col C) :
    toVec hC R (scaleCol C c u) = (c : R) • toVec hC R u := by
  rcases u with _ | ⟨a, d⟩
  · simp [scaleCol]
  · simp [scaleCol, mul_smul]

theorem map_toVec {Op : Module.End R (RootModule τ R)} {f : Idx C → Col C}
    (hOp : ∀ a, Op (Finsupp.single (toLabel hC a) 1) = toVec hC R (f a)) (u : Col C) :
    Op (toVec hC R u) = toVec hC R (bindCol C f u) := by
  rcases u with _ | ⟨a, c⟩
  · simp [bindCol]
  · simp only [bindCol, Option.bind_some, toVec_some, map_smul, hOp, toVec_scaleCol]

theorem toVec_normCol {p : ℕ} (hp : (p : R) = 0) (u : Col C) :
    toVec hC R (normCol C p u) = toVec hC R u := by
  rcases u with _ | ⟨a, c⟩
  · rfl
  · have hc : (c : R) = ((c % p : ℤ) : R) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv c p]
      push_cast [hp]
      ring
    simp only [normCol, Option.bind_some]
    split_ifs with h
    · rw [toVec_none, toVec_some, hc, h, Int.cast_zero, zero_smul]
    · rw [toVec_some, toVec_some, hc]

theorem ext_of_opEq {p : ℕ} (hp : (p : R) = 0) {f g : Idx C → Col C}
    {Op₁ Op₂ : Module.End R (RootModule τ R)}
    (h₁ : ∀ a, Op₁ (Finsupp.single (toLabel hC a) 1) = toVec hC R (f a))
    (h₂ : ∀ a, Op₂ (Finsupp.single (toLabel hC a) 1) = toVec hC R (g a))
    (h : opEq C p f g = true) : Op₁ = Op₂ := by
  have key : ∀ a, normCol C p (f a) = normCol C p (g a) := by
    simp only [opEq, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
      beq_iff_eq] at h
    rintro (j | m)
    · exact h.1 j
    · exact h.2 m
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  obtain ⟨a, rfl⟩ := surjective_toLabel hC b
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [h₁, h₂, ← toVec_normCol hC R hp, key, toVec_normCol hC R hp]

include hC in
theorem stringDown_root (hS : S.check C = true) {m : ℕ} (hm : m < C.roots.length)
    (i : Fin τ.rank) (h₁ : C.root m ≠ Pi.single i 1) (h₂ : C.root m ≠ -Pi.single i 1) :
    stringDown τ i (C.root m) = S.down m i ∧ stringUp τ i (C.root m) = S.up m i := by
  have hα := RootCertificate.isRoot_root hC m hm
  obtain ⟨-, ha⟩ := isRoot_add_smul_single_iff hα i h₁ h₂
  obtain ⟨-, hb⟩ := StringData.isRoot_root_add_iff hC hS hm i h₁ h₂
  have key : ∀ x : ℤ, (-(stringDown τ i (C.root m) : ℤ) ≤ x ∧ x ≤ stringUp τ i (C.root m)) ↔
      (-(S.down m i : ℤ) ≤ x ∧ x ≤ S.up m i) := fun x => (ha x).symm.trans (hb x)
  have k1 := (key (-(stringDown τ i (C.root m) : ℤ))).1 ⟨le_rfl, by omega⟩
  have k2 := (key (-(S.down m i : ℤ))).2 ⟨le_rfl, by omega⟩
  have k3 := (key (stringUp τ i (C.root m) : ℤ)).1 ⟨by omega, le_rfl⟩
  have k4 := (key (S.up m i : ℤ)).2 ⟨by omega, le_rfl⟩
  omega

theorem xCoeff_toLabel (hS : S.check C = true) (i : Fin τ.rank) (k : ℕ) (b : Idx C) :
    xCoeff τ R i k (Finsupp.single (toLabel hC b) 1) = toVec hC R (xCol C S i k b) := by
  rcases b with j | m
  · rw [single_toLabel_inl, xCoeff_hVec]
    simp only [xCol]
    split_ifs
    · rw [toVec_some, Int.cast_one, one_smul, single_toLabel_inl]
    · rw [toVec_scaleCol, toVec_rootCol hC R hS, Int.cast_natCast]
    · rfl
  · rw [single_toLabel_inr]
    simp only [xCol]
    by_cases h₁ : C.root m = Pi.single i 1
    · rw [ite_eq_left (vecBEq_iff.2 h₁), h₁, xCoeff_rootVec_single]
      split_ifs
      · rw [toVec_some, Int.cast_one, one_smul, single_toLabel_inr, h₁]
      · rfl
    rw [ite_eq_right (mt vecBEq_iff.1 h₁)]
    by_cases h₂ : C.root m = -Pi.single i 1
    · rw [ite_eq_left (vecBEq_iff.2 h₂), h₂, xCoeff_rootVec_neg_single]
      split_ifs
      · rw [toVec_some, Int.cast_one, one_smul, single_toLabel_inr, h₂]
      · rw [toVec_some, Int.cast_one, one_smul, single_toLabel_inl]
      · rw [toVec_rootCol hC R hS]
      · rfl
    rw [ite_eq_right (mt vecBEq_iff.1 h₂),
      xCoeff_rootVec_of_ne i k (RootCertificate.isRoot_root hC m m.2) h₁ h₂, toVec_scaleCol,
      toVec_rootCol hC R hS, (stringDown_root hC hS m.2 i h₁ h₂).1, Int.cast_natCast]

theorem yCoeff_toLabel (hS : S.check C = true) (i : Fin τ.rank) (k : ℕ) (b : Idx C) :
    yCoeff τ R i k (Finsupp.single (toLabel hC b) 1) = toVec hC R (yCol C S i k b) := by
  rcases b with j | m
  · rw [single_toLabel_inl, yCoeff_hVec]
    simp only [yCol]
    split_ifs
    · rw [toVec_some, Int.cast_one, one_smul, single_toLabel_inl]
    · rw [toVec_scaleCol, toVec_rootCol hC R hS, Int.cast_natCast]
    · rfl
  · rw [single_toLabel_inr]
    simp only [yCol]
    by_cases h₂ : C.root m = -Pi.single i 1
    · rw [ite_eq_left (vecBEq_iff.2 h₂), h₂, yCoeff_rootVec_neg_single]
      split_ifs
      · rw [toVec_some, Int.cast_one, one_smul, single_toLabel_inr, h₂]
      · rfl
    rw [ite_eq_right (mt vecBEq_iff.1 h₂)]
    by_cases h₁ : C.root m = Pi.single i 1
    · rw [ite_eq_left (vecBEq_iff.2 h₁), h₁, yCoeff_rootVec_single]
      split_ifs
      · rw [toVec_some, Int.cast_one, one_smul, single_toLabel_inr, h₁]
      · rw [toVec_some, Int.cast_one, one_smul, single_toLabel_inl]
      · rw [toVec_rootCol hC R hS]
      · rfl
    rw [ite_eq_right (mt vecBEq_iff.1 h₁),
      yCoeff_rootVec_of_ne i k (RootCertificate.isRoot_root hC m m.2) h₁ h₂, toVec_scaleCol,
      toVec_rootCol hC R hS, (stringDown_root hC hS m.2 i h₁ h₂).2, Int.cast_natCast]

end CFSG.LieType.Ree
