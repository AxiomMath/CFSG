module

public import CFSG.LieType.Chevalley.KernelComponentRoots

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag}

private theorem iform_zero_right (x : Fin τ.rank → ℤ) : iform x 0 = 0 := by
  simp [iform]

theorem iform_list_sum_right (x : Fin τ.rank → ℤ) (l : List (Fin τ.rank → ℤ)) :
    iform x l.sum = (l.map (iform x)).sum := by
  induction l with
  | nil => simp [iform_zero_right]
  | cons a l ih => rw [List.sum_cons, iform_add_right, ih, List.map_cons, List.sum_cons]

theorem two_mul_length_le_iform_sum (l : List (Fin τ.rank → ℤ))
    (hnorm : ∀ x ∈ l, iform x x = 2)
    (hpair : ∀ a b rest, l.Perm (a :: b :: rest) → 0 ≤ iform a b) :
    2 * (l.length : ℤ) ≤ iform l.sum l.sum := by
  induction l with
  | nil => simp [iform_zero_right]
  | cons c l ih =>
    have hpair' : ∀ a b rest, l.Perm (a :: b :: rest) → 0 ≤ iform a b := fun a b rest h =>
      hpair a b (c :: rest) ((h.cons c).trans
        ((List.Perm.swap a c (b :: rest)).trans ((List.Perm.swap b c rest).cons a)))
    have hc : ∀ x ∈ l, 0 ≤ iform c x := fun x hx =>
      hpair c x (l.erase x) ((List.perm_cons_erase hx).cons c)
    have hsum : 0 ≤ iform c l.sum := by
      rw [iform_list_sum_right]
      exact List.sum_nonneg fun y hy => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
        exact hc x hx
    have hcc := hnorm c (List.mem_cons_self ..)
    have ihl := ih (fun x hx => hnorm x (List.mem_cons_of_mem c hx)) hpair'
    have hsym : iform l.sum c = iform c l.sum := iform_comm _ _
    rw [List.sum_cons, iform_add_left, iform_add_right, iform_add_right, hsym, hcc,
      List.length_cons]
    push_cast
    linarith

theorem mem_of_isRoot_mem_addClosure (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {Ψ : Set (Fin τ.rank → ℤ)} (hroot : ∀ α ∈ Ψ, IsRoot τ α) (hneg : ∀ α ∈ Ψ, -α ∈ Ψ)
    (hadd : ∀ α ∈ Ψ, ∀ β ∈ Ψ, IsRoot τ (α + β) → α + β ∈ Ψ) {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (hmem : β ∈ AddSubgroup.closure Ψ) : β ∈ Ψ := by
  classical
  have hnorm : ∀ {x : Fin τ.rank → ℤ}, IsRoot τ x → iform x x = 2 := fun hx => by
    rw [← dotProduct_mulVec_eq_iform]
    exact rootForm_self hτ hx
  have hmon : β ∈ AddSubmonoid.closure Ψ := by
    have h : β ∈ (AddSubgroup.closure Ψ).toAddSubmonoid := hmem
    rw [AddSubgroup.closure_toAddSubmonoid] at h
    refine (AddSubmonoid.closure_le.2 ?_) h
    rintro x (hx | hx)
    · exact AddSubmonoid.subset_closure hx
    · exact AddSubmonoid.subset_closure (by simpa using hneg _ hx)
  have hex : ∃ n, ∃ l : List (Fin τ.rank → ℤ), l.length = n ∧ (∀ x ∈ l, x ∈ Ψ) ∧ l.sum = β := by
    obtain ⟨l, hl, hs⟩ := AddSubmonoid.exists_list_of_mem_closure hmon
    exact ⟨l.length, l, rfl, hl, hs⟩
  obtain ⟨l, hlen, hl, hs⟩ := Nat.find_spec hex
  have hmin : ∀ l' : List (Fin τ.rank → ℤ), (∀ x ∈ l', x ∈ Ψ) → l'.sum = β →
      Nat.find hex ≤ l'.length := fun l' hl' hs' => Nat.find_min' hex ⟨l', rfl, hl', hs'⟩
  have hpair : ∀ a b rest, l.Perm (a :: b :: rest) → 0 ≤ iform a b := by
    intro a b rest hp
    by_contra hneg'
    push Not at hneg'
    have ha : a ∈ Ψ := hl a (hp.symm.subset (List.mem_cons_self ..))
    have hb : b ∈ Ψ := hl b (hp.symm.subset (List.mem_cons_of_mem a (List.mem_cons_self ..)))
    have hrest : ∀ x ∈ rest, x ∈ Ψ := fun x hx =>
      hl x (hp.symm.subset (List.mem_cons_of_mem a (List.mem_cons_of_mem b hx)))
    have hsum : a + (b + rest.sum) = β := by
      rw [← hs, hp.sum_eq, List.sum_cons, List.sum_cons]
    have hlen' : l.length = rest.length + 2 := by
      rw [hp.length_eq]
      simp
    by_cases hab : a = -b
    · have h1 := hmin rest hrest (by rw [← hsum, hab, neg_add_cancel_left])
      omega
    · have hr := isRoot_add_of_iform_neg (hroot a ha) (hroot b hb) hab hneg'
      have h1 := hmin ((a + b) :: rest)
        (fun x hx => (List.mem_cons.1 hx).elim (fun h => h ▸ hadd a ha b hb hr) (hrest x))
        (by rw [List.sum_cons, add_assoc, hsum])
      simp only [List.length_cons] at h1
      omega
  have hineq := two_mul_length_le_iform_sum l (fun x hx => hnorm (hroot x (hl x hx))) hpair
  rw [hs, hnorm hβ] at hineq
  match l, hl, hs, hineq with
  | [], _, hs, _ =>
    have h0 : β = 0 := hs.symm
    have hp := iform_self_pos_of_isRoot hβ
    rw [h0, iform_zero_right] at hp
    exact absurd hp (lt_irrefl 0)
  | [x], hl, hs, _ =>
    have : β = x := by simpa using hs.symm
    exact this ▸ hl x (List.mem_singleton_self x)
  | _ :: _ :: _, _, _, hineq =>
    simp only [List.length_cons] at hineq
    push_cast at hineq
    linarith

end CFSG.LieType.Chevalley
