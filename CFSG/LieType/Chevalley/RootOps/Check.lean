module

public import CFSG.LieType.Chevalley.RootOps.Sparse
public import CFSG.LieType.Chevalley.RootOps.Data.G2
public import CFSG.LieType.Chevalley.RootOps.Data.F4
public import CFSG.LieType.Chevalley.RootOps.Data.D4
public import CFSG.LieType.Chevalley.RootOps.Data.E6
public import CFSG.LieType.Chevalley.RootOps.Data.E7
public import CFSG.LieType.Chevalley.RootOps.Data.E8
public import CFSG.LieType.Ree.Mirror
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley.RootOps

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.RootWalk

@[expose] def codes : Tag → ℕ → List ℕ
  | .G2, 1 => g2Codes1
  | .G2, 2 => g2Codes2
  | .G2, 3 => g2Codes3
  | .F4, 1 => f4Codes1
  | .F4, 2 => f4Codes2
  | .F4, 3 => f4Codes3
  | .D4, 1 => d4Codes1
  | .D4, 2 => d4Codes2
  | .D4, 3 => d4Codes3
  | .E6, 1 => e6Codes1
  | .E6, 2 => e6Codes2
  | .E6, 3 => e6Codes3
  | .E7, 1 => e7Codes1
  | .E7, 2 => e7Codes2
  | .E7, 3 => e7Codes3
  | .E8, 1 => e8Codes1
  | .E8, 2 => e8Codes2
  | .E8, 3 => e8Codes3
  | _, _ => []

@[expose] def signCodes : Tag → List ℕ
  | .G2 => g2Signs
  | .F4 => f4Signs
  | .D4 => d4Signs
  | .E6 => e6Signs
  | .E7 => e7Signs
  | .E8 => e8Signs

@[expose] def entries (τ : Tag) (a k : ℕ) : List Entry :=
  decodeEntries 128 ((codes τ k).getD a 0)

@[expose] def signOf (τ : Tag) (a : ℕ) (i : Fin τ.rank) : ℤ :=
  if (signCodes τ).getD a 0 / 2 ^ (i : ℕ) % 2 = 1 then -1 else 1

theorem signOf_eq (τ : Tag) (a : ℕ) (i : Fin τ.rank) : signOf τ a i = 1 ∨ signOf τ a i = -1 := by
  unfold signOf
  split_ifs
  · exact .inr rfl
  · exact .inl rfl

@[expose] def validB (τ : Tag) (L : List Entry) : Bool :=
  L.all fun e => decide (e.1 < dim τ) && decide (e.2.1 < dim τ)

theorem validEntries_of_validB {τ : Tag} {L : List Entry} (h : validB τ L = true) :
    ValidEntries τ L := by
  intro e he
  simp only [validB, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h e he

@[expose] def colCheck (τ : Tag) (i : Fin τ.rank) (L L' : List Entry) (s : ℤ) (c : ℕ) : Bool :=
  normalize (nVecL τ i (colOf L c)) ==
    normalize ((applyL L' (nPos τ i c)).map fun x => (x.1, s * x.2))

@[expose] def conjCheckAux (τ : Tag) (i : Fin τ.rank) (L L' : List Entry) (s : ℤ) : Bool :=
  validB τ L &&
    ((List.range τ.rank).all fun c => colCheck τ i L L' s c) &&
    (L.all fun e => decide (e.1 < τ.rank) || colCheck τ i L L' s e.1) &&
    (L'.all fun e => decide (e.1 < τ.rank) ||
      L.any fun f => f.1 == τ.rank + τ.rootCertificate.image (e.1 - τ.rank) i)

@[expose] def conjCheck (τ : Tag) (a : ℕ) (i : Fin τ.rank) (k : ℕ) : Bool :=
  conjCheckAux τ i (entries τ a k) (entries τ (τ.rootCertificate.image a i) k) (signOf τ a i ^ k)

@[expose] def idxPos {τ : Tag} : CFSG.LieType.Ree.Idx τ.rootCertificate → ℕ
  | .inl j => j
  | .inr m => τ.rank + m

@[expose] def colOfMirror {τ : Tag} : CFSG.LieType.Ree.Col τ.rootCertificate → List (ℕ × ℤ)
  | none => []
  | some (b, z) => [(idxPos b, z)]

@[expose] def allIdx (τ : Tag) : List (CFSG.LieType.Ree.Idx τ.rootCertificate) :=
  (List.finRange τ.rank).map .inl ++ (List.finRange τ.rootCertificate.roots.length).map .inr

@[expose] def simpleCheck (τ : Tag) (j : Fin τ.rank) (k : ℕ) : Bool :=
  (allIdx τ).all fun b => normalize (colOf (entries τ j k) (idxPos b)) ==
    normalize (colOfMirror (CFSG.LieType.Ree.xCol τ.rootCertificate τ.stringData j k b))

@[expose] def negSimpleCheck (τ : Tag) (j : Fin τ.rank) (k : ℕ) : Bool :=
  (allIdx τ).all fun b =>
    normalize (colOf (entries τ (τ.rootCertificate.image j j) k) (idxPos b)) ==
      normalize (colOfMirror (CFSG.LieType.Ree.yCol τ.rootCertificate τ.stringData j k b))

@[expose] def checkAll (τ : Tag) : Bool :=
  ((List.range τ.rootCertificate.roots.length).all fun a => (List.finRange τ.rank).all fun i =>
      [1, 2, 3].all fun k => conjCheck τ a i k) &&
    (List.finRange τ.rank).all fun j =>
      [1, 2, 3].all fun k => simpleCheck τ j k && negSimpleCheck τ j k

variable {τ : Tag} {R : Type*} [CommRing R]

theorem image_image {m : ℕ} (hm : m < τ.rootCertificate.roots.length) (i : Fin τ.rank) :
    τ.rootCertificate.image (τ.rootCertificate.image m i) i = m := by
  have h1 := rootCertificate_image_lt hm i
  have h2 := rootCertificate_image_lt h1 i
  refine rootCertificate_root_injOn h2 hm ?_
  rw [rootCertificate_root_image h1, rootCertificate_root_image hm, reflect_reflect]

theorem colCheck_spec {i : Fin τ.rank} {L L' : List Entry} {s : ℤ} {c : ℕ} (hL : ValidEntries τ L)
    (hc : c < dim τ) (h : colCheck τ i L L' s c = true) :
    (weylElt τ R i 1 : Module.End R (RootModule τ R)) (entriesOp τ R L (posVec τ R c)) =
      (s : R) • entriesOp τ R L' ((weylElt τ R i 1 : Module.End R (RootModule τ R))
        (posVec τ R c)) := by
  rw [entriesOp_posVec L hc, weylElt_vecOf i (hL.colOf c), weylElt_posVec i hc,
    entriesOp_vecOf L' (validVec_nPos i hc), ← vecOf_map_mul]
  exact vecOf_eq_of_normalize_eq (beq_iff_eq.1 h)

theorem conj_of_conjCheckAux {i : Fin τ.rank} {L L' : List Entry} {s : ℤ}
    (h : conjCheckAux τ i L L' s = true) :
    (weylElt τ R i 1 : Module.End R (RootModule τ R)) * entriesOp τ R L =
      (s : R) • (entriesOp τ R L' * (weylElt τ R i 1 : Module.End R (RootModule τ R))) := by
  simp only [conjCheckAux, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hv, hh⟩, hcols⟩, hsupp⟩ := h
  have hL := validEntries_of_validB hv
  refine ext_posVec fun c hc => ?_
  rw [Module.End.mul_apply, LinearMap.smul_apply, Module.End.mul_apply]
  by_cases hcr : c < τ.rank
  · exact colCheck_spec hL hc (hh c hcr)
  by_cases hmem : ∃ e ∈ L, e.1 = c
  · obtain ⟨e, he, rfl⟩ := hmem
    exact colCheck_spec hL hc ((hcols e he).resolve_left hcr)
  push Not at hmem
  have hcolL : colOf L c = [] := by
    simp only [colOf, List.map_eq_nil_iff, List.filter_eq_nil_iff, beq_iff_eq]
    exact hmem
  have hm : c - τ.rank < τ.rootCertificate.roots.length := by simp only [dim] at hc; omega
  have hcolL' : colOf L' (τ.rank + τ.rootCertificate.image (c - τ.rank) i) = [] := by
    simp only [colOf, List.map_eq_nil_iff, List.filter_eq_nil_iff, beq_iff_eq]
    intro e he hec
    rcases hsupp e he with hlt | ⟨f, hf, hfc⟩
    · omega
    · refine hmem f hf ?_
      rw [hfc, hec, Nat.add_sub_cancel_left, image_image hm]
      omega
  rw [entriesOp_posVec L hc, hcolL, vecOf_nil, map_zero, weylElt_posVec i hc]
  simp only [nPos, hcr, ↓reduceDIte]
  rw [vecOf_cons, vecOf_nil, add_zero, map_smul, entriesOp_posVec L', hcolL',
    vecOf_nil, smul_zero, smul_zero]
  have := rootCertificate_image_lt hm i
  simp only [dim]
  omega

theorem conj_of_conjCheck {a : ℕ} {i : Fin τ.rank} {k : ℕ} (h : conjCheck τ a i k = true) :
    (weylElt τ R i 1 : Module.End R (RootModule τ R)) * entriesOp τ R (entries τ a k) =
      ((signOf τ a i ^ k : ℤ) : R) • (entriesOp τ R (entries τ (τ.rootCertificate.image a i) k) *
        (weylElt τ R i 1 : Module.End R (RootModule τ R))) :=
  conj_of_conjCheckAux h

theorem idxPos_lt (b : CFSG.LieType.Ree.Idx τ.rootCertificate) : idxPos b < dim τ := by
  rcases b with j | m
  · simp only [idxPos, dim]
    omega
  · simp only [idxPos, dim]
    omega

theorem posVec_idxPos (b : CFSG.LieType.Ree.Idx τ.rootCertificate) :
    posVec τ R (idxPos b) =
      Finsupp.single (CFSG.LieType.Ree.toLabel τ.rootCertificate_check b) 1 := by
  rw [posVec_eq_single (idxPos_lt b)]
  congr 1
  rcases b with j | m
  · simp [posLabel, idxPos, CFSG.LieType.Ree.toLabel]
  · simp [posLabel, idxPos, CFSG.LieType.Ree.toLabel]

theorem vecOf_colOfMirror (u : CFSG.LieType.Ree.Col τ.rootCertificate) :
    vecOf τ R (colOfMirror u) = CFSG.LieType.Ree.toVec τ.rootCertificate_check R u := by
  rcases u with _ | ⟨b, z⟩
  · rfl
  · simp [colOfMirror, posVec_idxPos]

theorem mem_allIdx (b : CFSG.LieType.Ree.Idx τ.rootCertificate) : b ∈ allIdx τ := by
  rcases b with j | m <;> simp [allIdx]

theorem exists_idxPos {c : ℕ} (hc : c < dim τ) :
    ∃ b : CFSG.LieType.Ree.Idx τ.rootCertificate, idxPos b = c := by
  by_cases h : c < τ.rank
  · exact ⟨.inl ⟨c, h⟩, rfl⟩
  · simp only [dim] at hc
    exact ⟨.inr ⟨c - τ.rank, by omega⟩, by simp only [idxPos]; omega⟩

theorem entriesOp_eq_xCoeff {j : Fin τ.rank} {k : ℕ} (h : simpleCheck τ j k = true) :
    entriesOp τ R (entries τ j k) = xCoeff τ R j k := by
  simp only [simpleCheck, List.all_eq_true, beq_iff_eq] at h
  refine ext_posVec fun c hc => ?_
  obtain ⟨b, rfl⟩ := exists_idxPos hc
  rw [entriesOp_posVec _ hc, vecOf_eq_of_normalize_eq (h b (mem_allIdx b)), vecOf_colOfMirror,
    posVec_idxPos, CFSG.LieType.Ree.xCoeff_toLabel τ.rootCertificate_check R τ.stringData_check]

theorem entriesOp_eq_yCoeff {j : Fin τ.rank} {k : ℕ} (h : negSimpleCheck τ j k = true) :
    entriesOp τ R (entries τ (τ.rootCertificate.image j j) k) = yCoeff τ R j k := by
  simp only [negSimpleCheck, List.all_eq_true, beq_iff_eq] at h
  refine ext_posVec fun c hc => ?_
  obtain ⟨b, rfl⟩ := exists_idxPos hc
  rw [entriesOp_posVec _ hc, vecOf_eq_of_normalize_eq (h b (mem_allIdx b)), vecOf_colOfMirror,
    posVec_idxPos, CFSG.LieType.Ree.yCoeff_toLabel τ.rootCertificate_check R τ.stringData_check]

theorem checkAll_spec (h : checkAll τ = true) :
    (∀ a < τ.rootCertificate.roots.length, ∀ (i : Fin τ.rank), ∀ k ∈ [1, 2, 3],
      conjCheck τ a i k = true) ∧
      ∀ (j : Fin τ.rank), ∀ k ∈ [1, 2, 3], simpleCheck τ j k = true ∧ negSimpleCheck τ j k = true := by
  simp only [checkAll, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.mem_finRange,
    true_implies] at h
  exact ⟨fun a ha i k hk => h.1 a ha i k hk, fun j k hk => h.2 j k hk⟩

end CFSG.LieType.Chevalley.RootOps
