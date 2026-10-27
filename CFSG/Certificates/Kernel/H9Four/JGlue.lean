module

public import Certificates.Data.Kernel.H9Four.J
public import CFSG.Certificates.Kernel.H9Four.Sound

public section

namespace CFSG.KC.H9Four.JGlue

open CFSG.Quasithin.H13.H9Four CFSG.KC.H9Four CFSG.KC.H9Four.J CFSG.KC.H9Four.Codes
  CFSG.KC.H9Four.Masks CFSG.KC.H9Four.Sound

theorem eqE_iff (s t : ℕ) : eqE s t = true ↔ decE s = decE t := by
  have key : ∀ a < 2, ∀ b < 2, Nat.beq a 1 = Nat.beq b 1 → a = b := by decide
  unfold eqE decE
  simp only [Bool.and_eq_true, Nat.beq_eq, Elt.mk.injEq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    rw [h1, h2, h3]
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨ofCode_injective (fa_lt s) (fa_lt t) h1, ofCode_injective (fai_lt s) (fai_lt t) h2⟩,
      key _ (fb_lt s) _ (fb_lt t) h3⟩

theorem beq_decE (s t : ℕ) : (decE s == decE t) = eqE s t := by
  rw [Bool.eq_iff_iff, beq_iff_eq, eqE_iff]

theorem bne_decE (s t : ℕ) : (decE s != decE t) = !eqE s t := by
  rw [bne, beq_decE]

theorem contains_decE (t : ℕ) (L : List ℕ) : (L.map decE).contains (decE t) = memE t L := by
  unfold memE
  induction L with
  | nil => rfl
  | cons a L ih => rw [List.map_cons, List.contains_cons, List.any_cons, ih, beq_decE]

theorem nodup_decE (L : List ℕ) : decide (L.map decE).Nodup = nodupE L := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    have e : nodupE (a :: L) = (!(memE a L) && nodupE L) := rfl
    rw [e, ← ih, ← contains_decE, List.map_cons]
    cases h : (L.map decE).contains (decE a) <;>
      simp_all [List.nodup_cons, List.contains_iff_mem]

theorem valid_decE (t : ℕ) : (decE t).valid = validE t := (validE_iff t).symm

theorem b_decE (t : ℕ) : (decE t).b = Nat.beq (fb t) 1 := rfl

theorem mul_decE (s t : ℕ) : (decE s).mul (decE t) = decE (mulE s t) := (decE_mulE s t).symm

theorem inv_decE (t : ℕ) : (decE t).inv = decE (invE t) := (decE_invE t).symm

theorem one_decE : Elt.one = decE oneE := decE_oneE.symm

theorem gensK_nil : gensK [] = [] := rfl

theorem ofCodes_decE (p : ℕ × ℕ × Bool) (h : canonK [p] = true) :
    Elt.ofCodes p = decE (codeK p) := by
  have h1 := (gensK_spec [p] h).1
  simp only [gensK_cons, gensK_nil, List.map_cons, List.map_nil, List.cons.injEq, and_true] at h1
  exact h1.symm

theorem elems_decE (G : List ℕ) : elems (G.map decE) = (elemsK G).map decE := (elemsK_spec G).1.symm

theorem anyFix_decE (G : List ℕ) (y : ℕ) :
    (fixPts (G.map decE)).any (fun w => (decE y).act w != w) = anyFixK G y := by
  unfold anyFixK
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨p, hp, hne⟩
    obtain ⟨w, hw, rfl⟩ := exists_code_pt p
    refine ⟨w, List.mem_range.2 hw, ?_⟩
    rw [Bool.and_eq_true, ← mem_fixPts hw]
    refine ⟨hp, ?_⟩
    rw [bne_iff_ne, ne_eq, fixed_iff_actK y hw] at hne
    simpa using hne
  · rintro ⟨w, hw, h⟩
    rw [List.mem_range] at hw
    rw [Bool.and_eq_true, ← mem_fixPts hw] at h
    refine ⟨ptOfCode w, h.1, ?_⟩
    rw [bne_iff_ne, ne_eq, fixed_iff_actK y hw]
    simpa using h.2

theorem pow3_decE (y : ℕ) : pow3 (decE y) = (pow3K y).map decE := by
  simp only [pow3, pow3K, List.map_cons, List.map_nil, one_decE, mul_decE]

section Lists

variable (hc : canonDataK = true)
include hc

theorem canon_parts : canonK u0Codes = true ∧ canonK [s0Code] = true ∧ canonK j0Codes = true ∧
    canonK [y1Code] = true ∧ canonK [y2Code] = true ∧
    ∀ p ∈ lineCodes, canonK [p.1] = true ∧ canonK [p.2] = true := by
  simp only [canonDataK, Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem u0Gens_eq : u0Gens = u0K.map decE := (gensK_spec _ (canon_parts hc).1).1.symm

theorem s0Elt_eq : s0Elt = decE s0K := ofCodes_decE _ (canon_parts hc).2.1

theorem j0Gens_eq : j0Gens = j0GensK.map decE := (gensK_spec _ (canon_parts hc).2.2.1).1.symm

theorem y1Elt_eq : y1Elt = decE y1K := ofCodes_decE _ (canon_parts hc).2.2.2.1

theorem y2Elt_eq : y2Elt = decE y2K := ofCodes_decE _ (canon_parts hc).2.2.2.2.1

theorem s0Gens_eq : s0Gens = s0GensK.map decE := by
  rw [s0Gens, u0Gens_eq hc, s0Elt_eq hc, s0GensK, List.map_append]
  rfl

theorem s0List_eq : s0List = s0ListK.map decE := by
  simp only [s0List, u0Gens_eq hc, elems_decE, s0Elt_eq hc, s0ListK, List.map_append, List.map_map,
    Function.comp_def, mul_decE]

theorem j0List_eq : j0List = j0ListK.map decE := by
  rw [j0List, j0Gens_eq hc, elems_decE]
  rfl

theorem x0Gens_eq : x0Gens = x0GensK.map decE := by
  rw [x0Gens, j0Gens_eq hc, y1Elt_eq hc, y2Elt_eq hc, x0GensK, List.map_append]
  rfl

theorem x0List_eq : x0List = x0ListK.map decE := by
  simp only [x0List, x0ListK, j0List_eq hc, y1Elt_eq hc, y2Elt_eq hc, pow3_decE, List.flatMap_map,
    List.map_flatMap, List.map_map, Function.comp_def, mul_decE]

theorem e9Gens_eq : e9Gens = e9GensK.map decE := by
  rw [e9Gens, y1Elt_eq hc, y2Elt_eq hc]
  rfl

theorem e9List_eq : e9List = e9ListK.map decE := by
  simp only [e9List, e9ListK, y1Elt_eq hc, y2Elt_eq hc, pow3_decE, List.flatMap_map,
    List.map_flatMap, List.map_map, Function.comp_def, mul_decE]

theorem lines_eq : lines = linesK.map fun q => (decE q.1, decE q.2) := by
  rw [lines, linesK, List.map_map]
  refine List.map_congr_left fun p hp => ?_
  have h := (canon_parts hc).2.2.2.2.2 p hp
  simp only [Function.comp_apply, ofCodes_decE _ h.1, ofCodes_decE _ h.2]

theorem lineList_decE (y : ℕ) : lineList (decE y) = (lineListK y).map decE := by
  simp only [lineList, lineListK, j0List_eq hc, List.map_append, List.map_map, Function.comp_def,
    mul_decE]

theorem lineLists_eq : lineLists = lineListsK.map (List.map decE) := by
  simp only [lineLists, lineListsK, lines_eq hc, List.map_map, Function.comp_def, lineList_decE hc]

end Lists

section Checks

variable (hc : canonDataK = true)
include hc

theorem s0Check_of (h : s0CheckK = true) : s0Check = true := by
  unfold s0CheckK closedK at h
  rw [s0Check, s0Gens_eq hc, s0List_eq hc]
  simp only [closedRCheck, List.all_map, List.length_map, Function.comp_def, valid_decE, mul_decE,
    inv_decE, contains_decE, nodup_decE]
  exact h

theorem j0Check_of (h : j0CheckK = true) : j0Check = true := by
  unfold j0CheckK at h
  rw [j0Check, j0Gens_eq hc, j0List_eq hc, s0List_eq hc]
  simp only [commutes, List.all_map, Function.comp_def, valid_decE, b_decE, mul_decE, one_decE,
    beq_decE, bne_decE, contains_decE, nodup_decE]
  exact h

theorem x0Check_of (h : x0CheckK = true) : x0Check = true := by
  unfold x0CheckK closedK conjK at h
  rw [x0Check, x0Gens_eq hc, x0List_eq hc, j0Gens_eq hc, j0List_eq hc, s0Gens_eq hc]
  simp only [closedRCheck, conjE, List.all_map, List.length_map, Function.comp_def, valid_decE,
    b_decE, mul_decE, inv_decE, one_decE, contains_decE, nodup_decE]
  exact h

theorem oddGenCheck_of (h : oddGenCheckK = true) : oddGenCheck = true := by
  unfold oddGenCheckK at h
  rw [oddGenCheck, x0List_eq hc]
  simp only [List.all_map, List.any_map, Function.comp_def, mul_decE, inv_decE, one_decE,
    beq_decE]
  exact h

theorem lineCheck_of (h : lineCheckK = true) : lineCheck = true := by
  unfold lineCheckK conjK at h
  rw [lineCheck, lines_eq hc, lineLists_eq hc, x0List_eq hc, s0List_eq hc, j0List_eq hc]
  simp only [conjE, List.all_map, List.any_map, Function.comp_def, lineList_decE hc, mul_decE,
    inv_decE, one_decE, beq_decE, contains_decE, nodup_decE]
  exact h

theorem fixCheck_of (h : fixCheckK = true) : fixCheck = true := by
  unfold fixCheckK at h
  rw [fixCheck, x0Gens_eq hc, fixPts_length]
  exact h

theorem kerCheck_of (h : kerCheckK = true) : kerCheck = true := by
  unfold kerCheckK conjK at h
  rw [kerCheck, s0List_eq hc, j0List_eq hc, x0Gens_eq hc]
  simp only [conjE, List.all_map, List.any_map, Function.comp_def, mul_decE, inv_decE,
    contains_decE]
  exact h

theorem e9Check_of (h : e9CheckK = true) : e9Check = true := by
  unfold e9CheckK closedK at h
  rw [e9Check, e9List_eq hc, e9Gens_eq hc, j0Gens_eq hc, y1Elt_eq hc, anyFix_decE, fixPts_length]
  simp only [closedRCheck, List.all_map, List.length_map, Function.comp_def, mul_decE, inv_decE,
    one_decE, contains_decE, nodup_decE]
  exact h

theorem ffRepCheck_of (h : ffRepCheckK = true) : ffRepCheck = true := by
  unfold ffRepCheckK at h
  unfold ffRepCheck reps
  rw [List.all_eq_true] at h ⊢
  intro gs' hgs'
  obtain ⟨gs, hgs, rfl⟩ := List.mem_map.1 hgs'
  have hg := h gs hgs
  rw [Bool.and_eq_true] at hg
  rw [← (gensK_spec gs hg.1).1, List.isEmpty_map, elems_length, List.length_map, fixPts_length]
  exact hg.2

theorem u0Check_of (h : u0CheckK = true) : u0Check = true := by
  unfold u0CheckK at h
  rw [u0Check, s0List_eq hc, j0List_eq hc]
  simp only [commutes, List.all_map, List.filter_map, List.length_map, Function.comp_def, b_decE,
    mul_decE, one_decE, beq_decE, bne_decE, contains_decE]
  exact h

end Checks

end CFSG.KC.H9Four.JGlue

end
