module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GroupTheory.PermSylowTwo

open Equiv Equiv.Perm

variable (β γ : Type) [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

@[expose] def pairInv : Perm ((β × Bool) ⊕ γ) :=
  Equiv.sumCongr (Equiv.prodCongr (Equiv.refl β) (Equiv.swap false true)) (Equiv.refl γ)

@[expose] def pairSwap (b : β) : Perm ((β × Bool) ⊕ γ) :=
  Equiv.swap (Sum.inl (b, false)) (Sum.inl (b, true))

@[expose] def pairSwaps : Subgroup (Perm ((β × Bool) ⊕ γ)) :=
  Subgroup.closure (Set.range (pairSwap β γ))

@[expose] def pairCent : Subgroup (Perm ((β × Bool) ⊕ γ)) :=
  Subgroup.centralizer {pairInv β γ}

@[expose] def pairFun (g : Perm ((β × Bool) ⊕ γ)) (b : β) : β :=
  Sum.elim Prod.fst (fun _ => b) (g (Sum.inl (b, false)))

variable {β γ}

theorem pairInv_apply_inl_false (b : β) :
    pairInv β γ (Sum.inl (b, false)) = Sum.inl (b, true) := by
  simp [pairInv]

theorem pairInv_apply_inl_true (b : β) :
    pairInv β γ (Sum.inl (b, true)) = Sum.inl (b, false) := by
  simp [pairInv]

theorem pairInv_apply_inl (b : β) (c : Bool) :
    pairInv β γ (Sum.inl (b, c)) = Sum.inl (b, !c) := by
  cases c
  · simpa using pairInv_apply_inl_false (β := β) (γ := γ) b
  · simpa using pairInv_apply_inl_true (β := β) (γ := γ) b

theorem pairInv_apply_inr (x : γ) : pairInv β γ (Sum.inr x) = Sum.inr x := by
  simp [pairInv]

theorem pairInv_involutive (z : (β × Bool) ⊕ γ) :
    pairInv β γ (pairInv β γ z) = z := by
  rcases z with ⟨b, c⟩ | x
  · cases c <;> simp [pairInv_apply_inl_false, pairInv_apply_inl_true]
  · simp [pairInv_apply_inr]

theorem pairInv_commute_of_mem_pairCent {g : Perm ((β × Bool) ⊕ γ)} (hg : g ∈ pairCent β γ)
    (z : (β × Bool) ⊕ γ) : pairInv β γ (g z) = g (pairInv β γ z) := by
  have h : pairInv β γ * g = g * pairInv β γ :=
    (Subgroup.mem_centralizer_iff.mp hg) (pairInv β γ) (Set.mem_singleton _)
  calc pairInv β γ (g z) = (pairInv β γ * g) z := rfl
    _ = (g * pairInv β γ) z := by rw [h]
    _ = g (pairInv β γ z) := rfl

theorem pairCent_apply_inl_false {g : Perm ((β × Bool) ⊕ γ)} (hg : g ∈ pairCent β γ) (b : β) :
    ∃ (b' : β) (c' : Bool), g (Sum.inl (b, false)) = Sum.inl (b', c') := by
  rcases h : g (Sum.inl (b, false)) with ⟨b', c'⟩ | y
  · exact ⟨b', c', rfl⟩
  · exfalso
    have h2 : pairInv β γ (g (Sum.inl (b, false))) = g (pairInv β γ (Sum.inl (b, false))) :=
      pairInv_commute_of_mem_pairCent hg _
    rw [h, pairInv_apply_inr, pairInv_apply_inl_false] at h2
    have heq : (Sum.inl (b, true) : (β × Bool) ⊕ γ) = Sum.inl (b, false) := by
      apply g.injective
      rw [← h2]
      exact h.symm
    simp at heq

theorem pairCent_apply_inl {g : Perm ((β × Bool) ⊕ γ)} (hg : g ∈ pairCent β γ) (b : β)
    (c : Bool) : ∃ c' : Bool, g (Sum.inl (b, c)) = Sum.inl (pairFun β γ g b, c') := by
  obtain ⟨b', c₀, hb⟩ := pairCent_apply_inl_false hg b
  have hfun : pairFun β γ g b = b' := by
    rw [pairFun, hb]
    rfl
  cases c
  · exact ⟨c₀, by rw [hfun]; exact hb⟩
  · refine ⟨!c₀, ?_⟩
    have hμ : Sum.inl (b, true) = pairInv β γ (Sum.inl (b, false)) := by
      rw [pairInv_apply_inl_false]
    rw [hμ, ← pairInv_commute_of_mem_pairCent hg (Sum.inl (b, false)), hb, pairInv_apply_inl,
      hfun]

theorem pairCent_apply_inr {g : Perm ((β × Bool) ⊕ γ)} (hg : g ∈ pairCent β γ) (x : γ) :
    ∃ y : γ, g (Sum.inr x) = Sum.inr y := by
  rcases h : g (Sum.inr x) with ⟨b, c⟩ | y
  · exfalso
    have h2 : pairInv β γ (g (Sum.inr x)) = g (Sum.inr x) := by
      rw [pairInv_commute_of_mem_pairCent hg, pairInv_apply_inr]
    rw [h] at h2
    cases c <;> simp [pairInv_apply_inl_false, pairInv_apply_inl_true] at h2
  · exact ⟨y, rfl⟩

theorem pairFun_inv_pairFun {g : Perm ((β × Bool) ⊕ γ)} (hg : g ∈ pairCent β γ) (b : β) :
    pairFun β γ g⁻¹ (pairFun β γ g b) = b := by
  obtain ⟨b', c₀, hb⟩ := pairCent_apply_inl_false hg b
  have hfun : pairFun β γ g b = b' := by
    rw [pairFun, hb]
    rfl
  have hb' : g⁻¹ (Sum.inl (b', c₀)) = Sum.inl (b, false) := by
    have h := congrArg (fun z => g⁻¹ z) hb
    simpa using h.symm
  obtain ⟨c₁, hc₁⟩ := pairCent_apply_inl (inv_mem hg) b' c₀
  have hfirst : (b, false) = (pairFun β γ g⁻¹ b', c₁) :=
    Sum.inl.inj (by rw [← hb', hc₁])
  rw [hfun]
  exact (congrArg Prod.fst hfirst).symm

theorem pairFun_mul_pairFun {g h : Perm ((β × Bool) ⊕ γ)} (hg : g ∈ pairCent β γ)
    (hh : h ∈ pairCent β γ) (b : β) :
    pairFun β γ (g * h) b = pairFun β γ g (pairFun β γ h b) := by
  obtain ⟨c₁, hc₁⟩ := pairCent_apply_inl hh b false
  obtain ⟨c₂, hc₂⟩ := pairCent_apply_inl hg (pairFun β γ h b) c₁
  change Sum.elim Prod.fst (fun _ => b) ((g * h) (Sum.inl (b, false))) =
    pairFun β γ g (pairFun β γ h b)
  rw [Perm.mul_apply, hc₁, hc₂]
  rfl

variable (β γ)

theorem sumCongr_prodCongr_apply_inl (σ : Perm β) (b : β) (c : Bool) :
    (Equiv.sumCongr (Equiv.prodCongr σ (Equiv.refl Bool)) (Equiv.refl γ) :
      Perm ((β × Bool) ⊕ γ)) (Sum.inl (b, c)) = Sum.inl (σ b, c) := rfl

theorem sumCongr_prodCongr_apply_inr (σ : Perm β) (x : γ) :
    (Equiv.sumCongr (Equiv.prodCongr σ (Equiv.refl Bool)) (Equiv.refl γ) :
      Perm ((β × Bool) ⊕ γ)) (Sum.inr x) = Sum.inr x := rfl

@[expose] def pairHom : ↥(pairCent β γ) →* Perm β where
  toFun g :=
    { toFun := pairFun β γ g
      invFun := pairFun β γ g⁻¹
      left_inv := fun b => pairFun_inv_pairFun g.2 b
      right_inv := fun b => by
        simpa [inv_inv] using
          pairFun_inv_pairFun (g := (g : Perm ((β × Bool) ⊕ γ))⁻¹) (inv_mem g.2) b }
  map_one' := by
    ext b
    show pairFun β γ (1 : Perm ((β × Bool) ⊕ γ)) b = b
    simp [pairFun]
  map_mul' := by
    intro g h
    ext b
    show pairFun β γ (↑(g * h)) b = pairFun β γ (↑g) (pairFun β γ (↑h) b)
    simpa using pairFun_mul_pairFun g.2 h.2 b

@[expose] def pairLift : Perm β →* ↥(pairCent β γ) where
  toFun σ := ⟨Equiv.sumCongr (Equiv.prodCongr σ (Equiv.refl Bool)) (Equiv.refl γ), by
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro h hh
    have hh' : h = pairInv β γ := by simpa using hh
    subst hh'
    ext z
    rcases z with ⟨b, c⟩ | x
    · change pairInv β γ (Equiv.sumCongr (Equiv.prodCongr σ (Equiv.refl Bool))
          (Equiv.refl γ) (Sum.inl (b, c))) =
        Equiv.sumCongr (Equiv.prodCongr σ (Equiv.refl Bool)) (Equiv.refl γ)
          (pairInv β γ (Sum.inl (b, c)))
      simp only [sumCongr_prodCongr_apply_inl, pairInv_apply_inl]
    · change pairInv β γ (Equiv.sumCongr (Equiv.prodCongr σ (Equiv.refl Bool))
          (Equiv.refl γ) (Sum.inr x)) =
        Equiv.sumCongr (Equiv.prodCongr σ (Equiv.refl Bool)) (Equiv.refl γ)
          (pairInv β γ (Sum.inr x))
      simp only [sumCongr_prodCongr_apply_inr, pairInv_apply_inr]⟩
  map_one' := by
    apply Subtype.ext
    change (Equiv.sumCongr (Equiv.prodCongr (1 : Perm β) (Equiv.refl Bool))
      (Equiv.refl γ) : Perm ((β × Bool) ⊕ γ)) = 1
    ext z
    rcases z with ⟨b, c⟩ | x
    · simp only [sumCongr_prodCongr_apply_inl]
      rfl
    · simp only [sumCongr_prodCongr_apply_inr]
      rfl
  map_mul' := by
    intro σ τ
    apply Subtype.ext
    change (Equiv.sumCongr (Equiv.prodCongr (σ * τ) (Equiv.refl Bool)) (Equiv.refl γ) :
        Perm ((β × Bool) ⊕ γ)) =
      (Equiv.sumCongr (Equiv.prodCongr σ (Equiv.refl Bool)) (Equiv.refl γ) :
        Perm ((β × Bool) ⊕ γ)) *
      (Equiv.sumCongr (Equiv.prodCongr τ (Equiv.refl Bool)) (Equiv.refl γ) :
        Perm ((β × Bool) ⊕ γ))
    ext z
    rcases z with ⟨b, c⟩ | x
    · simp only [sumCongr_prodCongr_apply_inl, Perm.mul_apply]
    · simp only [sumCongr_prodCongr_apply_inr, Perm.mul_apply]

variable {β γ}

theorem pairLift_apply_inl (σ : Perm β) (b : β) (c : Bool) :
    ((pairLift β γ σ : ↥(pairCent β γ)) : Perm ((β × Bool) ⊕ γ)) (Sum.inl (b, c)) =
      Sum.inl (σ b, c) := rfl

theorem pairHom_apply (g : ↥(pairCent β γ)) (b : β) :
    pairHom β γ g b = pairFun β γ (g : Perm ((β × Bool) ⊕ γ)) b :=
  rfl

theorem pairHom_pairLift (σ : Perm β) : pairHom β γ (pairLift β γ σ) = σ := by
  ext b
  rw [pairHom_apply, pairFun, pairLift_apply_inl]
  rfl

theorem pairLift_mem_alternatingGroup (σ : Perm β) :
    ((pairLift β γ σ : ↥(pairCent β γ)) : Perm ((β × Bool) ⊕ γ)) ∈
      alternatingGroup ((β × Bool) ⊕ γ) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  change Equiv.Perm.sign
    (Equiv.sumCongr (Equiv.prodCongr σ (Equiv.refl Bool)) (Equiv.refl γ)) = 1
  rw [Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_refl, mul_one]
  have hprod : Equiv.prodCongr σ (Equiv.refl Bool) =
      Equiv.prodCongrLeft (fun _ : Bool => σ) := by
    apply Equiv.ext
    rintro ⟨b, c⟩
    rfl
  rw [hprod, Equiv.Perm.sign_prodCongrLeft, Fintype.prod_bool, Int.units_mul_self]

theorem sq_eq_one_of_pairHom_eq_one [Subsingleton γ] {g : ↥(pairCent β γ)}
    (hg : pairHom β γ g = 1) : g ^ 2 = 1 := by
  have hb : ∀ b, pairFun β γ (g : Perm ((β × Bool) ⊕ γ)) b = b := by
    intro b
    have h := congrArg (fun σ : Perm β => σ b) hg
    simpa [pairHom_apply] using h
  apply Subtype.ext
  have hgg : (g : Perm ((β × Bool) ⊕ γ)) * (g : Perm ((β × Bool) ⊕ γ)) = 1 := by
    ext z
    rcases z with ⟨b, c⟩ | x
    · obtain ⟨c₁, h₁⟩ := pairCent_apply_inl g.2 b c
      rw [hb b] at h₁
      rw [Perm.mul_apply, h₁]
      by_cases hc : c₁ = c
      · rw [hc] at h₁ ⊢
        exact h₁
      · have hc' : c₁ = !c := Bool.eq_not_iff.mpr hc
        have hcomm := pairInv_commute_of_mem_pairCent g.2 (Sum.inl (b, c))
        rw [pairInv_apply_inl] at hcomm
        rw [hc', ← hcomm, h₁, hc', pairInv_apply_inl]
        simp
    · obtain ⟨y, hy⟩ := pairCent_apply_inr g.2 x
      rw [Perm.mul_apply, hy]
      obtain ⟨y', hy'⟩ := pairCent_apply_inr g.2 y
      rw [hy']
      exact congrArg Sum.inr (Subsingleton.elim y' x)
  simpa [pow_two] using hgg

theorem pairSwap_mem_pairSwaps (b : β) : pairSwap β γ b ∈ pairSwaps β γ :=
  Subgroup.subset_closure (Set.mem_range_self b)

@[expose] def pairPreserve : Subgroup (Perm ((β × Bool) ⊕ γ)) where
  carrier := {g | ∀ z, g z = z ∨ g z = pairInv β γ z}
  mul_mem' := by
    intro a b ha hb z
    rw [Perm.mul_apply]
    rcases hb z with h | h
    · rw [h]; exact ha z
    · rw [h]
      rcases ha (pairInv β γ z) with h' | h'
      · exact Or.inr h'
      · exact Or.inl (h'.trans (pairInv_involutive z))
  one_mem' := fun z => Or.inl rfl
  inv_mem' := by
    intro a ha z
    have h1 : a (a⁻¹ z) = z := by simp
    rcases ha (a⁻¹ z) with h | h
    · exact Or.inl (h.symm.trans h1)
    · have hz : z = pairInv β γ (a⁻¹ z) := h1.symm.trans h
      exact Or.inr ((congrArg (pairInv β γ) hz).trans (pairInv_involutive _)).symm

theorem pairPreserve_mul_self {σ : Perm ((β × Bool) ⊕ γ)}
    (hσ : σ ∈ pairPreserve (β := β) (γ := γ)) :
    σ * σ = 1 := by
  have hσ' : ∀ z, σ z = z ∨ σ z = pairInv β γ z := hσ
  ext z
  rw [Perm.mul_apply, Perm.one_apply]
  rcases hσ' z with h | h
  · rw [h, h]
  · rw [h]
    rcases hσ' (pairInv β γ z) with h' | h'
    · have hz : pairInv β γ z = z := σ.injective (by rw [h']; exact h.symm)
      rw [h', hz]
    · rw [h', pairInv_involutive]

theorem pairSwap_mem_pairPreserve (b : β) : pairSwap β γ b ∈ pairPreserve (β := β) (γ := γ) := by
  intro z
  by_cases h₁ : z = Sum.inl (b, false)
  · rw [h₁]
    exact Or.inr (by rw [pairSwap, Equiv.swap_apply_left, pairInv_apply_inl_false])
  · by_cases h₂ : z = Sum.inl (b, true)
    · rw [h₂]
      exact Or.inr (by rw [pairSwap, Equiv.swap_apply_right, pairInv_apply_inl_true])
    · exact Or.inl (by rw [pairSwap]; exact Equiv.swap_apply_of_ne_of_ne h₁ h₂)

theorem pairSwaps_le_pairPreserve : pairSwaps β γ ≤ pairPreserve (β := β) (γ := γ) := by
  change Subgroup.closure (Set.range (pairSwap β γ)) ≤ pairPreserve (β := β) (γ := γ)
  rw [Subgroup.closure_le]
  rintro _ ⟨b, rfl⟩
  exact pairSwap_mem_pairPreserve b

theorem isPGroup_two_pairSwaps : IsPGroup 2 ↥(pairSwaps β γ) := by
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  have hg : (g : Perm ((β × Bool) ⊕ γ)) * (g : Perm ((β × Bool) ⊕ γ)) = 1 :=
    pairPreserve_mul_self (pairSwaps_le_pairPreserve g.2)
  simpa [pow_two] using hg

theorem pairLift_conj_pairSwap (σ : Perm β) (b : β) :
    (pairLift β γ σ : Perm ((β × Bool) ⊕ γ)) * pairSwap β γ b *
      (pairLift β γ σ : Perm ((β × Bool) ⊕ γ))⁻¹ = pairSwap β γ (σ b) := by
  rw [pairSwap, ← Equiv.swap_apply_apply (pairLift β γ σ : Perm ((β × Bool) ⊕ γ))
    (Sum.inl (b, false)) (Sum.inl (b, true)), pairLift_apply_inl, pairLift_apply_inl]
  rfl

theorem pairLift_conj_mem_pairSwaps (σ : Perm β) {n : Perm ((β × Bool) ⊕ γ)}
    (hn : n ∈ pairSwaps β γ) :
    (pairLift β γ σ : Perm ((β × Bool) ⊕ γ)) * n * (pairLift β γ σ : Perm _)⁻¹ ∈
      pairSwaps β γ := by
  have hle : Subgroup.map ((MulAut.conj (pairLift β γ σ : Perm _)).toMonoidHom)
      (pairSwaps β γ) ≤ pairSwaps β γ := by
    simp only [pairSwaps, MonoidHom.map_closure]
    rw [Subgroup.closure_le]
    rintro _ ⟨x, ⟨b, rfl⟩, rfl⟩
    change (MulAut.conj (pairLift β γ σ : Perm _)) (pairSwap β γ b) ∈ pairSwaps β γ
    rw [MulAut.conj_apply, pairLift_conj_pairSwap]
    exact pairSwap_mem_pairSwaps (σ b)
  have hmem : (MulAut.conj (pairLift β γ σ : Perm _)) n ∈ pairSwaps β γ :=
    hle (Subgroup.mem_map_of_mem _ hn)
  simpa [MulAut.conj_apply] using hmem

theorem pairLift_mem_normalizer_pairSwaps (σ : Perm β) :
    ((pairLift β γ σ : ↥(pairCent β γ)) : Perm ((β × Bool) ⊕ γ)) ∈
      Subgroup.normalizer (pairSwaps β γ : Set (Perm ((β × Bool) ⊕ γ))) := by
  have hinv : (pairLift β γ σ : ↥(pairCent β γ))⁻¹ = pairLift β γ σ⁻¹ := by
    have h : (pairLift β γ σ : ↥(pairCent β γ)) * pairLift β γ σ⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    exact inv_eq_of_mul_eq_one_right h
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · exact pairLift_conj_mem_pairSwaps σ
  · intro hn
    have hconj := pairLift_conj_mem_pairSwaps (σ := σ⁻¹)
      (n := (pairLift β γ σ : Perm _) * n * (pairLift β γ σ : Perm _)⁻¹) hn
    have hval : ((pairLift β γ σ⁻¹ : ↥(pairCent β γ)) : Perm ((β × Bool) ⊕ γ)) =
        (pairLift β γ σ : Perm ((β × Bool) ⊕ γ))⁻¹ := by
      have h := congrArg (fun x : ↥(pairCent β γ) => (x : Perm ((β × Bool) ⊕ γ))) hinv
      simpa using h.symm
    rw [hval, inv_inv] at hconj
    have heq : (pairLift β γ σ : Perm _)⁻¹ *
        ((pairLift β γ σ : Perm _) * n * (pairLift β γ σ : Perm _)⁻¹) *
        (pairLift β γ σ : Perm _) = n := by group
    rw [heq] at hconj
    exact hconj

theorem three_dvd_orderOf_mul {α : Type*} {x y : Perm α} {a b e : α} (hab : a ≠ b)
    (hae : a ≠ e) (hbe : b ≠ e) (hxa : x a = b) (hxb : x b = a) (hxe : x e = e) (hya : y a = e)
    (hye : y e = a) (hyb : y b = b) : 3 ∣ orderOf (x * y) := by
  obtain ⟨z, hz⟩ : ∃ z : Perm α, x * y = z := ⟨x * y, rfl⟩
  rw [hz]
  have hza : z a = e := by rw [← hz, Perm.mul_apply, hya, hxe]
  have hze : z e = b := by rw [← hz, Perm.mul_apply, hye, hxa]
  have hzb : z b = a := by rw [← hz, Perm.mul_apply, hyb, hxb]
  have h3 : (z ^ 3) a = a := by
    rw [pow_succ, pow_succ, pow_succ, pow_zero, one_mul, Perm.mul_apply, Perm.mul_apply,
      hza, hze, hzb]
  have hfix : ∀ m : ℕ, (z ^ (3 * m)) a = a := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        have h3m : 3 * (m + 1) = 3 * m + 3 := by ring
        rw [h3m, pow_add, Perm.mul_apply, h3, ih]
  have hmod : ∀ k : ℕ, (z ^ k) a = (z ^ (k % 3)) a := by
    intro k
    conv_lhs => rw [← Nat.mod_add_div k 3]
    rw [pow_add, Perm.mul_apply, hfix]
  have key : ∀ k : ℕ, (z ^ k) a = a ↔ 3 ∣ k := by
    intro k
    constructor
    · intro hk
      have hk' : (z ^ (k % 3)) a = a := (hmod k).symm.trans hk
      have hlt : k % 3 < 3 := Nat.mod_lt k (by norm_num)
      interval_cases h : k % 3
      · exact Nat.dvd_of_mod_eq_zero h
      · rw [pow_one, hza] at hk'
        exact absurd hk'.symm hae
      · have h2 : (z ^ 2) a = b := by rw [pow_two, Perm.mul_apply, hza, hze]
        rw [h2] at hk'
        exact absurd hk'.symm hab
    · rintro ⟨m, rfl⟩
      exact hfix m
  exact (key (orderOf z)).mp (by rw [pow_orderOf_eq_one]; rfl)

end CFSG.GroupTheory.PermSylowTwo
