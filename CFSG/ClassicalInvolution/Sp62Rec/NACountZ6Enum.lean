module

public import CFSG.ClassicalInvolution.Solomon73.YamakiEnum

public section

namespace CFSG.ClassicalInvolution.Sp62Rec.Z6NA

open CFSG.ClassicalInvolution.Solomon73.Yamaki

structure IsArrCode {H : Type*} [Group H] (cd : H → Array ℕ) : Prop where
  mul : ∀ x y, cd (x * y) = compA (cd x) (cd y)
  one : cd 1 = idA ()
  injective : Function.Injective cd

variable {H : Type*} [Group H] {cd : H → Array ℕ} {E : Enum} {gs : Array (Array ℕ)}
  {s : ℕ → H}

theorem inv_eq_pow_orderOf_sub_one [Finite H] (x : H) : x⁻¹ = x ^ (orderOf x - 1) := by
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  rw [pow_sub_one_mul (orderOf_pos x).ne', pow_orderOf_eq_one]

theorem exists_mem_closure_of_treeOK (hc : IsArrCode cd) (hgs : ∀ j < gs.size, gs[j]! = cd (s j))
    (h : treeOK E gs = true) :
    ∀ i < E.elems.size, ∃ x ∈ Subgroup.closure (s '' Set.Iio gs.size), cd x = E.elems[i]! := by
  simp only [treeOK, Bool.and_eq_true, decide_eq_true_eq, allLt_iff, Bool.or_eq_true] at h
  obtain ⟨h0, hall⟩ := h
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases hall i hi with rfl | ⟨⟨hp, hg⟩, he⟩
    · exact ⟨1, one_mem _, by rw [hc.one, getElem!_eq_of_getElem? h0]⟩
    · obtain ⟨x, hx, hxe⟩ := ih _ hp (hp.trans hi)
      refine ⟨x * s E.gen[i]!, mul_mem hx (Subgroup.subset_closure ⟨_, hg, rfl⟩), ?_⟩
      rw [hc.mul, hxe, ← hgs _ hg, he]

theorem lookup_isSome_of_mem_closure [Finite H] (hc : IsArrCode cd)
    (hgs : ∀ j < gs.size, gs[j]! = cd (s j)) (h : enumOK E gs = true) {x : H}
    (hx : x ∈ Subgroup.closure (s '' Set.Iio gs.size)) : (E.lookup (cd x)).isSome := by
  simp only [enumOK, Bool.and_eq_true] at h
  obtain ⟨⟨htree, hclosed⟩, hnodup⟩ := h
  have h0 : E.elems[0]? = some (idA ()) := by
    simp only [treeOK, Bool.and_eq_true, decide_eq_true_eq] at htree
    exact htree.1
  have h1 : (E.lookup (cd 1)).isSome := by
    have := (allLt_iff.mp hnodup) 0 (size_pos_of_getElem? h0)
    rw [decide_eq_true_eq, getElem!_eq_of_getElem? h0] at this
    rw [hc.one, this]
    rfl
  have hmul : ∀ y, (E.lookup (cd y)).isSome → ∀ j < gs.size,
      (E.lookup (cd (y * s j))).isSome := by
    intro y hy j hj
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hy
    obtain ⟨hks, hke⟩ := Enum.lookup_spec hk
    have := (allLt_iff.mp ((allLt_iff.mp hclosed) k hks)) j hj
    rwa [hke, hgs j hj, ← hc.mul] at this
  have hpow : ∀ y, (E.lookup (cd y)).isSome → ∀ j < gs.size, ∀ m : ℕ,
      (E.lookup (cd (y * s j ^ m))).isSome := by
    intro y hy j hj m
    induction m with
    | zero => rwa [pow_zero, mul_one]
    | succ m ih =>
      rw [pow_succ, ← mul_assoc]
      exact hmul _ ih j hj
  induction hx using Subgroup.closure_induction_right with
  | one => exact h1
  | mul_right y _ z hz ih =>
    obtain ⟨j, hj, rfl⟩ := hz
    exact hmul y ih j hj
  | mul_inv_cancel y _ z hz ih =>
    obtain ⟨j, hj, rfl⟩ := hz
    rw [inv_eq_pow_orderOf_sub_one]
    exact hpow y ih j hj _

theorem mem_closure_iff_isSome [Finite H] (hc : IsArrCode cd)
    (hgs : ∀ j < gs.size, gs[j]! = cd (s j)) (h : enumOK E gs = true) (x : H) :
    x ∈ Subgroup.closure (s '' Set.Iio gs.size) ↔ (E.lookup (cd x)).isSome := by
  refine ⟨lookup_isSome_of_mem_closure hc hgs h, fun hx => ?_⟩
  have htree : treeOK E gs = true := by
    simp only [enumOK, Bool.and_eq_true] at h
    exact h.1.1
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hx
  obtain ⟨hks, hke⟩ := Enum.lookup_spec hk
  obtain ⟨y, hy, hye⟩ := exists_mem_closure_of_treeOK hc hgs htree k hks
  rwa [hc.injective (hke.symm.trans hye.symm)]

end CFSG.ClassicalInvolution.Sp62Rec.Z6NA
