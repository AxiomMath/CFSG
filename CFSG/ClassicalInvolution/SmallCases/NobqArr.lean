module

public import CFSG.Monster.B.Co2.PermArr

public section

namespace CFSG.ClassicalInvolution.Nobq

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

variable {n : ℕ}

@[expose] def closureA (n : ℕ) (gens : List (Array ℕ)) (fuel : ℕ) : List (Array ℕ) :=
  (List.range fuel).foldl
    (fun L _ => (L ++ L.flatMap fun x => gens.map fun g => compA n x g).eraseDups) [idA n]

theorem closureA_rep (K : Subgroup (Equiv.Perm (Fin n))) (gens : List (Array ℕ))
    (hgens : ∀ g ∈ gens, ∃ G ∈ K, Rep n g G) (fuel : ℕ) :
    ∀ x ∈ closureA n gens fuel, ∃ X ∈ K, Rep n x X := by
  induction fuel with
  | zero =>
    intro x hx
    simp only [closureA, List.range_zero, List.foldl_nil, List.mem_singleton] at hx
    subst hx
    exact ⟨1, K.one_mem, rep_idA⟩
  | succ k ih =>
    intro x hx
    simp only [closureA, List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil] at hx
    rw [List.mem_eraseDups, List.mem_append] at hx
    rcases hx with hx | hx
    · exact ih x hx
    · obtain ⟨y, hy, hxy⟩ := List.mem_flatMap.1 hx
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hxy
      obtain ⟨Y, hYK, hY⟩ := ih y hy
      obtain ⟨G, hGK, hG⟩ := hgens g hg
      exact ⟨Y * G, K.mul_mem hYK hGK, rep_compA hY hG⟩

@[expose] def conjArr (n : ℕ) (w c : Array ℕ) : Array ℕ := compA n w (compA n c (invCand n w))

@[expose] def cqTestA (n : ℕ) (r : Array ℕ) (ws : List (Array ℕ)) (c : Array ℕ) : Bool :=
  !(eqA n (compA n c c) r) || ws.any fun w =>
    isInvA n w (invCand n w) &&
      (eqA n (compA n (compA n c (conjArr n w c)) (compA n c (conjArr n w c))) (idA n) &&
        !(eqA n (compA n c (conjArr n w c)) (idA n)) && !(eqA n (compA n c (conjArr n w c)) r))

theorem cqTestA_sound {K : Subgroup (Equiv.Perm (Fin n))} {r c : Array ℕ}
    {R C : Equiv.Perm (Fin n)} (hr : Rep n r R) (hc : Rep n c C) {ws : List (Array ℕ)}
    (hws : ∀ w ∈ ws, ∃ W ∈ K, Rep n w W) (h : cqTestA n r ws c = true) (hCC : C * C = R) :
    ∃ G ∈ K, (C * (G * C * G⁻¹)) * (C * (G * C * G⁻¹)) = 1 ∧ C * (G * C * G⁻¹) ≠ 1 ∧
      C * (G * C * G⁻¹) ≠ R := by
  simp only [cqTestA, Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true,
    Bool.and_eq_true] at h
  rcases h with h | ⟨w, hw, hv, ⟨hx1, hx2⟩, hx3⟩
  · exfalso
    rw [(eqA_iff (rep_compA hc hc) hr).2 hCC] at h
    exact Bool.noConfusion h
  · obtain ⟨W, hWK, hW⟩ := hws w hw
    obtain ⟨hw1, hw2⟩ := rep_permOfArr hv
    have hWe : W = permOfArr n w := hW.unique hw1
    have hWi : Rep n (invCand n w) W⁻¹ := by rw [hWe]; exact hw2
    have hconj : Rep n (conjArr n w c) (W * (C * W⁻¹)) := rep_compA hW (rep_compA hc hWi)
    have hx := rep_compA hc hconj
    have e : C * (W * C * W⁻¹) = C * (W * (C * W⁻¹)) := by rw [mul_assoc W C W⁻¹]
    refine ⟨W, hWK, ?_, fun h1 => ?_, fun h1 => ?_⟩
    · rw [e]
      exact (eqA_iff (rep_compA hx hx) rep_idA).1 hx1
    · rw [e] at h1
      rw [(eqA_iff hx rep_idA).2 h1] at hx2
      exact Bool.noConfusion hx2
    · rw [e] at h1
      rw [(eqA_iff hx hr).2 h1] at hx3
      exact Bool.noConfusion hx3

end CFSG.ClassicalInvolution.Nobq
