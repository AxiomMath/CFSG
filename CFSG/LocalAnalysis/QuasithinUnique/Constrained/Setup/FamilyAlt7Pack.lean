module

public import CFSG.Quasithin.H13.L32AC50aPack

public section

namespace CFSG.QuasithinUnique.Setup.FamilyAlt7Pack

open Equiv CFSG.Permutation.FinPack CFSG.Quasithin.H13.L32A.C.Alt7Pack

@[expose] def e7Codes : List ℕ :=
  [106181136, 105186081, 105197586, 106172466, 106168611, 106177281, 105193731, 105189936]

theorem e7_closed_of (a b : Perm (Fin 7)) (ha : a = swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5)
    (hb : b = swap 0 2 * swap 4 5) :
    (1 : Perm (Fin 7)) ∈ [1, a, b, a * a, a * b, b * a, a * a * a, b * a * a] ∧
      (∀ x ∈ [1, a, b, a * a, a * b, b * a, a * a * a, b * a * a],
        ∀ y ∈ [1, a, b, a * a, a * b, b * a, a * a * a, b * a * a],
          x * y ∈ [1, a, b, a * a, a * b, b * a, a * a * a, b * a * a]) ∧
      ∀ x ∈ [1, a, b, a * a, a * b, b * a, a * a * a, b * a * a],
        x⁻¹ ∈ [1, a, b, a * a, a * b, b * a, a * a * a, b * a * a] := by
  subst ha hb
  exact closed_of_K (by norm_num) _ e7Codes one7 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem fix_of_K {n : ℕ} (hn : n ≤ 16) (L : List (Perm (Fin n))) (C : List ℕ)
    (hC : (L.map enc == C) = true) (i : Fin n)
    (h : allK (fun c => Nat.beq (rd c i) i) C = true) : ∀ u ∈ L, u i = i := by
  rw [beq_iff_eq] at hC
  subst hC
  intro u hu
  have h1 := allK_iff.1 h _ (List.mem_map.2 ⟨u, hu, rfl⟩)
  rw [Nat.beq_eq, rd_enc hn] at h1
  exact Fin.ext h1

theorem e7_fix6_of (a b : Perm (Fin 7)) (ha : a = swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5)
    (hb : b = swap 0 2 * swap 4 5) :
    ∀ u ∈ [1, a, b, a * a, a * b, b * a, a * a * a, b * a * a], u 6 = 6 := by
  subst ha hb
  exact fix_of_K (by norm_num) _ e7Codes (by decide +kernel) 6 (by decide +kernel)

end CFSG.QuasithinUnique.Setup.FamilyAlt7Pack
