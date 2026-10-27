module

public import CFSG.Certificates.Kernel.SporLatDcSound
public import CFSG.Certificates.Kernel.SporLatDcGood

public section

namespace CFSG.KC.SLDc

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.E64F

variable {Γ : Type} [Group Γ]

private theorem getD_sl (a b : Γ) (sg : List Γ) {j : ℕ} (hj : j < sg.length) :
    (a :: b :: (sg ++ sg.map (·⁻¹))).getD (2 + j) 1 = (a :: b :: sg).getD (2 + j) 1 := by
  rw [Nat.add_comm 2 j, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ,
    List.getD_cons_succ, List.getD_append _ _ _ _ hj]

private theorem getD_sl_inv (a b : Γ) (sg : List Γ) {i : ℕ} (hi : i < sg.length) :
    (a :: b :: (sg ++ sg.map (·⁻¹))).getD (2 + sg.length + i) 1 =
      ((a :: b :: sg).getD (2 + i) 1)⁻¹ := by
  have e : 2 + sg.length + i = sg.length + i + 1 + 1 := by omega
  rw [e, List.getD_cons_succ, List.getD_cons_succ, Nat.add_comm 2 i, List.getD_cons_succ,
    List.getD_cons_succ, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

theorem dcCheckS_sound_inv [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)] (C : DcCtx) (hn : C.n = n)
    (D : DcData) (s : ℕ) (a b : Γ) (gen : Subgroup.closure ({a, b} : Set Γ) = ⊤) (sg : List Γ)
    (hng : C.ng = sg.length) (hns : C.ns = 2 * sg.length)
    (hL : ∀ l < 2 + sg.length, Good n (tab n ((a :: b :: sg).getD l 1)).toArray (C.L l))
    (hinv : ∀ i < sg.length, ∀ p < n, C.L (2 + sg.length + i) (C.L (2 + i) p) = p)
    (hk : Nat.card (Subgroup.closure {x | x ∈ sg}) = s) (hN : Nat.card Γ = C.N * s)
    (hsep : ∀ g : Γ, (∀ p ∈ D.sep, act n g p = p) → g = 1)
    (hΔ : PtValid n C.Δ) (h : dcCheckS C D s = true) :
    (∀ g : Γ, lab n ptLab C.Δ g = C.Δ ↔ g ∈ Subgroup.closure {x | x ∈ sg}) ∧
    ∀ Z : Subgroup Γ, Subgroup.closure {x | x ∈ sg} ≤ Z → ∃ j ≤ D.mw.length,
      Z = memberOrTop D.mw.length
        (fun j => Subgroup.closure {x | x ∈ sg ++ (D.mw.getD j []).map (wordElt a b)}) j := by
  have htake : (sg ++ sg.map (·⁻¹)).take C.ng = sg := by
    rw [hng, List.take_left' rfl]
  have hL' : ∀ l < 2 + C.ns,
      Good n (tab n ((a :: b :: (sg ++ sg.map (·⁻¹))).getD l 1)).toArray (C.L l) := by
    intro l hl
    rcases Nat.lt_or_ge l (2 + sg.length) with h1 | h1
    · rcases Nat.lt_or_ge l 2 with h2 | h2
      · interval_cases l
        · exact hL 0 (by omega)
        · exact hL 1 (by omega)
      · obtain ⟨j, rfl⟩ : ∃ j, l = 2 + j := ⟨l - 2, by omega⟩
        rw [getD_sl a b sg (by omega)]
        exact hL _ h1
    · obtain ⟨i, rfl⟩ : ∃ i, l = 2 + sg.length + i := ⟨l - (2 + sg.length), by omega⟩
      rw [getD_sl_inv a b sg (by omega)]
      exact good_inv (hL (2 + i) (by omega)) (hinv i (by omega))
  have hS : ∀ x ∈ sg ++ sg.map (·⁻¹),
      x ∈ Subgroup.closure {x | x ∈ (sg ++ sg.map (·⁻¹)).take C.ng} := by
    intro x hx
    rw [htake]
    rcases List.mem_append.1 hx with h | h
    · exact Subgroup.subset_closure h
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h
      exact Subgroup.inv_mem _ (Subgroup.subset_closure hy)
  have h0 := dcCheckS_sound C hn D s a b gen (sg ++ sg.map (·⁻¹))
    (by rw [List.length_append, List.length_map, hns]; omega) hL' hS (by rw [htake]; exact hk) hN
    hsep hΔ h
  rw [htake] at h0
  exact h0

end CFSG.KC.SLDc

end
