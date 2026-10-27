module

public import CFSG.Certificates.Kernel.Mat8PSound

public section

namespace CFSG.KC.Mat8P

open CFSG.Quasithin.H13.Mat8Cert

@[expose] def closedP (gp L : List ℕ) : Bool :=
  L.all fun x => gp.all fun g => memP (ofListP L) (mulP g x)

theorem code64R_unpackM {X : ℕ} (hX : X < 2 ^ 64) : code64R (unpackM X) = X := by
  rw [code64R_eq, unpackM_eq, code64_unpackS, Nat.mod_eq_of_lt hX]

theorem code64R_lt (y : List ℕ) (hy : validB y = true) : code64R y < 2 ^ 64 := by
  rw [← unpackM_code64R y hy, code64R_eq, unpackM_eq, code64_unpackS]
  exact Nat.mod_lt _ (by norm_num)

theorem contains_map (L : List ℕ) (hL : ∀ p ∈ L, p < 2 ^ 64) (y : List ℕ) :
    (L.map unpackM).contains y = (validB y && L.contains (code64R y)) := by
  by_cases hy : validB y = true
  · rw [hy, Bool.true_and]
    have hyl := code64R_lt y hy
    rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, List.mem_map]
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [code64R_unpackM (hL p hp)]
      exact hp
    · intro h
      exact ⟨_, h, unpackM_code64R y hy⟩
  · rw [Bool.eq_false_iff.mpr hy, Bool.false_and, Bool.eq_false_iff]
    intro h
    rw [List.contains_iff_mem, List.mem_map] at h
    obtain ⟨p, _, rfl⟩ := h
    exact hy (validB_unpackM p)

theorem hs_contains_map (L : List ℕ) (hL : ∀ p ∈ L, p < 2 ^ 64) (y : List ℕ) :
    (Std.HashSet.ofList (L.map unpackM)).contains y =
      (validB y && memP (ofListP L) (code64R y)) := by
  rw [Std.HashSet.contains_ofList, contains_map L hL, memP_ofListP]

theorem closedB_map (gp L : List ℕ) (hL : ∀ p ∈ L, p < 2 ^ 64) :
    closedB (gp.map unpackM) (L.map unpackM) = closedP gp L := by
  rw [closedB, closedP]
  simp only [List.all_map]
  congr 1
  funext x
  simp only [Function.comp_def]
  congr 1
  funext g
  rw [hs_contains_map L hL, mul8_unpackM, validB_unpackM, Bool.true_and,
    code64R_unpackM (mulP_lt g x), memP_ofListP]

theorem nodupB_map (L : List ℕ) (hL : ∀ p ∈ L, p < 2 ^ 64) :
    nodupB (L.map unpackM) = nodupP L := by
  rw [nodupB_toP, List.map_map]
  congr 1
  conv_rhs => rw [← List.map_id L]
  exact List.map_congr_left (fun p hp => code64R_unpackM (hL p hp))

theorem all_validB_map (L : List ℕ) : (L.map unpackM).all validB = true := by
  rw [List.all_map, List.all_eq_true]
  intro p _
  exact validB_unpackM p

theorem unpack_code64R_map (G : List (List ℕ)) (h : G.all validB = true) :
    G = (G.map code64R).map unpackM := by
  rw [List.map_map]
  conv_lhs => rw [← List.map_id G]
  apply List.map_congr_left
  intro x hx
  rw [List.all_eq_true] at h
  exact (unpackM_code64R x (h x hx)).symm

end CFSG.KC.Mat8P

end
