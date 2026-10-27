module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralWeyl

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag}

structure IsAChain {n : ℕ} (β : Fin n → Fin τ.rank → ℤ) : Prop where
  isRoot : ∀ i, IsRoot τ (β i)
  adj : ∀ i j : Fin n, (j : ℕ) = i + 1 → iform (β i) (β j) = -1
  orth : ∀ i j : Fin n, (i : ℕ) + 2 ≤ j → iform (β i) (β j) = 0

@[expose] def aChainRoots {n : ℕ} (β : Fin n → Fin τ.rank → ℤ) : Set (Fin τ.rank → ℤ) :=
  {x | ∃ i l : Fin n, i ≤ l ∧
    (x = ∑ k ∈ Finset.Icc i l, β k ∨ x = -∑ k ∈ Finset.Icc i l, β k)}

@[expose] def chainRefl {n : ℕ} (β : Fin n → Fin τ.rank → ℤ) : WeylGroup τ :=
  (List.ofFn fun i => rootReflection (β i)).prod

@[expose] def ChainsStrOrth {n : ℕ} (β γ : Fin n → Fin τ.rank → ℤ) : Prop :=
  ∀ x ∈ aChainRoots β, ∀ y ∈ aChainRoots γ, StrOrth x y

section General

theorem IsAChain.iform_sum_succ {n : ℕ} {β : Fin n → Fin τ.rank → ℤ} (h : IsAChain β)
    {i l l' : Fin n} (hil : i ≤ l) (hl' : (l' : ℕ) = l + 1) :
    iform (∑ k ∈ Finset.Icc i l, β k) (β l') = -1 := by
  classical
  rw [iform_finset_sum_left, Finset.sum_eq_single l]
  · exact h.adj l l' hl'
  · intro k hk hkl
    have hk' := (Finset.mem_Icc.1 hk).2
    have : (k : ℕ) < l := lt_of_le_of_ne (Fin.le_iff_val_le_val.1 hk') (fun e => hkl (Fin.ext e))
    exact h.orth k l' (by omega)
  · intro hl
    exact absurd (Finset.mem_Icc.2 ⟨hil, le_rfl⟩) hl

theorem IsAChain.isRoot_sum (hSL : ∀ γ, IsRoot τ γ → iform γ γ = 2) {n : ℕ}
    {β : Fin n → Fin τ.rank → ℤ} (h : IsAChain β) :
    ∀ i l : Fin n, i ≤ l → IsRoot τ (∑ k ∈ Finset.Icc i l, β k) := by
  classical
  intro i l hil
  obtain ⟨d, hd⟩ : ∃ d, (l : ℕ) = i + d := ⟨l - i, by omega⟩
  induction d generalizing l with
  | zero =>
    have : l = i := Fin.ext (by omega)
    subst this
    rw [Finset.Icc_self, Finset.sum_singleton]
    exact h.isRoot l
  | succ d ih =>
    have hl0 : (l : ℕ) ≠ 0 := by omega
    set l₀ : Fin n := ⟨l - 1, by omega⟩ with hl₀
    have hl₀v : (l₀ : ℕ) = l - 1 := rfl
    have hil₀ : i ≤ l₀ := Fin.le_iff_val_le_val.2 (by rw [hl₀v]; omega)
    have hr := ih l₀ hil₀ (by rw [hl₀v]; omega)
    have hsplit : ∑ k ∈ Finset.Icc i l, β k = (∑ k ∈ Finset.Icc i l₀, β k) + β l := by
      have hIcc : Finset.Icc i l = insert l (Finset.Icc i l₀) := by
        ext k
        rw [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Icc, Fin.le_iff_val_le_val,
          Fin.le_iff_val_le_val, Fin.le_iff_val_le_val, Fin.ext_iff, hl₀v]
        omega
      have hnot : l ∉ Finset.Icc i l₀ := by
        rw [Finset.mem_Icc, Fin.le_iff_val_le_val, Fin.le_iff_val_le_val, hl₀v]
        omega
      rw [hIcc, Finset.sum_insert hnot, add_comm]
    have he := h.iform_sum_succ hil₀ (by rw [hl₀v]; omega : (l : ℕ) = l₀ + 1)
    rw [hsplit]
    refine isRoot_add_of_iform_neg hr (h.isRoot l) (fun e => ?_) (by rw [he]; omega)
    rw [e, iform_neg_fst, hSL _ (h.isRoot l)] at he
    omega

theorem mem_aChainRoots_isRoot (hSL : ∀ γ, IsRoot τ γ → iform γ γ = 2) {n : ℕ}
    {β : Fin n → Fin τ.rank → ℤ} (h : IsAChain β) : ∀ x ∈ aChainRoots β, IsRoot τ x := by
  rintro x ⟨i, l, hil, rfl | rfl⟩
  · exact h.isRoot_sum hSL i l hil
  · exact IsRoot.neg (h.isRoot_sum hSL i l hil)

theorem iform_eq_zero_of_mem_aChainRoots {n : ℕ} {β : Fin n → Fin τ.rank → ℤ}
    {x v : Fin τ.rank → ℤ} (hx : x ∈ aChainRoots β) (hv : ∀ k, iform (β k) v = 0) :
    iform x v = 0 := by
  obtain ⟨i, l, -, rfl | rfl⟩ := hx
  · rw [iform_finset_sum_left]
    exact Finset.sum_eq_zero fun k _ => hv k
  · rw [iform_neg_fst, iform_finset_sum_left, Finset.sum_eq_zero fun k _ => hv k, neg_zero]

theorem smul_eq_of_mem_aChainRoots {n : ℕ} {β : Fin n → Fin τ.rank → ℤ} {x : Fin τ.rank → ℤ}
    (hx : x ∈ aChainRoots β) {u : WeylGroup τ} (hu : ∀ k, u • β k = β k) : u • x = x := by
  obtain ⟨i, l, -, rfl | rfl⟩ := hx
  · rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => hu k
  · rw [smul_neg, Finset.smul_sum, Finset.sum_congr rfl fun k _ => hu k]

theorem aChainRoots_subset_kernelRoots (hSL : ∀ γ, IsRoot τ γ → iform γ γ = 2) {M : Type*}
    [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {n : ℕ}
    {β : Fin n → Fin τ.rank → ℤ} (h : IsAChain β) (hβ : ∀ k, β k ∈ kernelRoots χ) :
    aChainRoots β ⊆ kernelRoots χ := by
  intro x hx
  refine ⟨mem_aChainRoots_isRoot hSL h x hx, ?_⟩
  have hsum : ∀ s : Finset (Fin n), χ (Multiplicative.ofAdd (∑ k ∈ s, β k)) = 1 := by
    intro s
    induction s using Finset.cons_induction with
    | empty => rw [Finset.sum_empty, ofAdd_zero, map_one]
    | cons a s ha ih => rw [Finset.sum_cons, ofAdd_add, map_mul, (hβ a).2, ih, one_mul]
  obtain ⟨i, l, -, rfl | rfl⟩ := hx
  · exact hsum _
  · rw [ofAdd_neg, map_inv, hsum, inv_one]

end General

end CFSG.HardMathSupport.Timmesfeld.CrossChar
