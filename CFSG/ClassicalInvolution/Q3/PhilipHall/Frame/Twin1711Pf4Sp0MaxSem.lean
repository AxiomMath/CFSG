module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf4Sp0MaxData

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Sp0K

section Sem

variable {GB : ℕ → Equiv.Perm (Fin 36)} (hB : ∀ l, PRep (baseGl.getD l oneP) (GB l))
  (hc : invChk = true)

include hB hc in
theorem omRecChk_sound {r : List ℕ} (h : omRecChk r = true) :
    (∀ l ∈ r.drop 2, 4 ≤ l ∧ l ≤ 15) ∧ r.getD 1 0 < 4 ∧
      PRep (r.getD 0 0) (permW (LG GB) (r.drop 2) * LG GB (16 + r.getD 1 0) *
        permW (LG GB) [12, 12] * (LG GB (16 + r.getD 1 0))⁻¹ * (permW (LG GB) (r.drop 2))⁻¹) := by
  have hI : ∀ l, LG GB (invL l) = (LG GB l)⁻¹ := LG_inv hB hc
  simp only [omRecChk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun l hl => by simpa [tLetter] using h1 l hl, h2, ?_⟩
  have hi : invL (16 + r.getD 1 0) = 20 + r.getD 1 0 := by
    have := h2
    generalize r.getD 1 0 = i at this ⊢
    have h4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h4 with rfl | rfl | rfl | rfl <;> rfl
  have hm := prep_LG hB (16 + r.getD 1 0)
  have e : LG GB (20 + r.getD 1 0) = (LG GB (16 + r.getD 1 0))⁻¹ := by rw [← hi, hI]
  have hmi : PRep (GL.getD (20 + r.getD 1 0) oneP) (LG GB (16 + r.getD 1 0))⁻¹ := by
    rw [← e]
    exact prep_LG hB _
  have hc' := prep_permW hB (r.drop 2)
  have hci := prep_permW hB (invW (r.drop 2))
  rw [permW_invW hI] at hci
  have hr2 : PRep r2p (permW (LG GB) [12, 12]) := prep_permW hB [12, 12]
  rw [← h3]
  exact ((((hc'.comp hm).comp hr2).comp hmi).comp hci)

include hB hc in
theorem omClosed_sound (h : omClosed = true) {s : Equiv.Perm (Fin 36)}
    (hs : ∃ p ∈ omP, PRep p s) (l : ℕ) (hl : l < 4) :
    ∃ p ∈ omP, PRep p (LG GB l * s * (LG GB l)⁻¹) := by
  have hI : ∀ l, LG GB (invL l) = (LG GB l)⁻¹ := LG_inv hB hc
  obtain ⟨p, hp, hps⟩ := hs
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 h p hp |> fun h' => h') l (List.mem_range.2 hl)
  refine ⟨_, List.mem_of_elem_eq_true h1, ?_⟩
  have := ((prep_LG hB l).comp hps).comp (prep_LG hB (invL l))
  rwa [hI] at this

end Sem

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Sp0K
