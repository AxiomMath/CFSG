module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Algebra.Group.Subgroup.Ker

public section


namespace CFSG.HardMathSupport.Solomon.Coordinator

open Equiv Equiv.Perm

section Star

variable {γ : Type} [DecidableEq γ]

theorem i28_14_symAut_pair_of_mem {D : Finset γ} {b : γ} (hD : D.card = 2) (hb : b ∈ D) :
    ∃ c, c ≠ b ∧ D = {b, c} := by
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.1 hD
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl
  · exact ⟨v, huv.symm, rfl⟩
  · exact ⟨u, huv, Finset.pair_comm _ _⟩

theorem i28_14_symAut_star (𝓕 : Finset (Finset γ)) (hcard : ∀ A ∈ 𝓕, A.card = 2)
    (hint : ∀ A ∈ 𝓕, ∀ B ∈ 𝓕, (A ∩ B).Nonempty) (h4 : 4 ≤ 𝓕.card) :
    ∃ p, ∀ A ∈ 𝓕, p ∈ A := by
  by_contra hcon
  push Not at hcon
  have hne : 𝓕.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨A, hA⟩ := hne
  obtain ⟨a, b, hab, hAeq⟩ := Finset.card_eq_two.1 (hcard A hA)
  obtain ⟨B, hB, haB⟩ := hcon a
  obtain ⟨C, hC, hbC⟩ := hcon b
  have hbB : b ∈ B := by
    obtain ⟨x, hx_x⟩ := hint _ hA B hB
    obtain ⟨hx1, hx2⟩ := Finset.mem_inter.1 hx_x
    rw [hAeq] at hx1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx1
    rcases hx1 with rfl | rfl
    · exact absurd hx2 haB
    · exact hx2
  have haC : a ∈ C := by
    obtain ⟨x, hx_x⟩ := hint _ hA C hC
    obtain ⟨hx1, hx2⟩ := Finset.mem_inter.1 hx_x
    rw [hAeq] at hx1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx1
    rcases hx1 with rfl | rfl
    · exact hx2
    · exact absurd hx2 hbC
  obtain ⟨c, hcb, hBeq⟩ := i28_14_symAut_pair_of_mem (hcard B hB) hbB
  obtain ⟨d, hda, hCeq⟩ := i28_14_symAut_pair_of_mem (hcard C hC) haC
  have hac : a ≠ c := by
    rintro rfl
    exact haB (hBeq ▸ by simp)
  have hdc : d = c := by
    obtain ⟨x, hx⟩ := hint _ hB _ hC
    obtain ⟨hxB, hxC⟩ := Finset.mem_inter.1 hx
    have hxB' := hxB
    have hxC' := hxC
    rw [hBeq] at hxB'
    rw [hCeq] at hxC'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxB' hxC'
    rcases hxB' with h | h
    · exact absurd (h ▸ hxC) hbC
    · rcases hxC' with h' | h'
      · exact absurd (h' ▸ hxB) haB
      · exact h'.symm.trans h
  subst hdc
  have hsub : 𝓕 ⊆ {A, B, C} := by
    intro D hD
    obtain ⟨u, v, huv, hDeq⟩ := Finset.card_eq_two.1 (hcard D hD)
    obtain ⟨y1, hy1⟩ := hint _ hD A hA
    obtain ⟨y2, hy2⟩ := hint _ hD B hB
    obtain ⟨y3, hy3⟩ := hint _ hD C hC
    rw [Finset.mem_inter, hDeq, hAeq] at hy1
    rw [Finset.mem_inter, hDeq, hBeq] at hy2
    rw [Finset.mem_inter, hDeq, hCeq] at hy3
    rw [hDeq]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy1 hy2 hy3 ⊢
    rw [hAeq, hBeq, hCeq]
    clear hDeq hA hB hC hD hint hcard hcon hAeq hBeq hCeq h4
    rcases hy1 with ⟨h1 | h1, h1' | h1'⟩ <;> rcases hy2 with ⟨h2 | h2, h2' | h2'⟩ <;>
      rcases hy3 with ⟨h3 | h3, h3' | h3'⟩ <;> subst_vars <;> simp_all [Finset.pair_comm]
  have := Finset.card_le_card hsub
  have h3 := Finset.card_le_three (a := A) (b := B) (c := C)
  omega

end Star

section Swaps

variable {m : ℕ}

theorem i28_14_symAut_not_commute_aux {a b d : Fin m} (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    ¬ Commute (swap a b) (swap a d) := by
  intro h
  have := congrArg (fun f : Perm (Fin m) => f b) h.eq
  simp [swap_apply_def, hab.symm, hbd, had] at this

theorem i28_14_symAut_swap_through {a b x : Fin m} (hab : a ≠ b) (hx : x ∈ ({a, b} : Finset (Fin m))) :
    ∃ y, x ≠ y ∧ swap a b = swap x y := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact ⟨b, hab, rfl⟩
  · exact ⟨a, hab.symm, swap_comm _ _⟩

theorem i28_14_symAut_not_commute {s t : Perm (Fin m)} (hs : s.IsSwap) (ht : t.IsSwap)
    (hst : s ≠ t) (hd : ¬ _root_.Disjoint s.support t.support) : ¬ Commute s t := by
  obtain ⟨a, b, hab, rfl⟩ := hs
  obtain ⟨c, d, hcd, rfl⟩ := ht
  rw [support_swap hab, support_swap hcd, Finset.not_disjoint_iff] at hd
  obtain ⟨x, hx1, hx2⟩ := hd
  obtain ⟨y, hxy, h1⟩ := i28_14_symAut_swap_through hab hx1
  obtain ⟨z, hxz, h2⟩ := i28_14_symAut_swap_through hcd hx2
  rw [h1, h2] at hst ⊢
  have hyz : y ≠ z := fun h => hst (by rw [h])
  exact i28_14_symAut_not_commute_aux hxy hxz hyz

theorem i28_14_symAut_support_inj {s t : Perm (Fin m)} (hs : s.IsSwap) (ht : t.IsSwap)
    (h : s.support = t.support) : s = t := by
  obtain ⟨a, b, hab, rfl⟩ := hs
  obtain ⟨c, d, hcd, rfl⟩ := ht
  rw [support_swap hab, support_swap hcd] at h
  have ha : a ∈ ({c, d} : Finset (Fin m)) := h ▸ (by simp)
  have hb : b ∈ ({c, d} : Finset (Fin m)) := h ▸ (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact absurd rfl hab
  · rfl
  · exact swap_comm _ _
  · exact absurd rfl hab

theorem i28_14_symAut_commute_of_disjoint {s t : Perm (Fin m)}
    (h : _root_.Disjoint s.support t.support) : Commute s t :=
  (disjoint_iff_disjoint_support.2 h).commute

variable (α : MulAut (Perm (Fin m)))

theorem i28_14_symAut_inter {i j k : Fin m} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ _root_.Disjoint (α (swap i j)).support (α (swap i k)).support := by
  intro hd
  have hc := i28_14_symAut_commute_of_disjoint hd
  have hc' : Commute (swap i j) (swap i k) := by
    apply α.injective
    rw [map_mul, map_mul]
    exact hc.eq
  exact i28_14_symAut_not_commute_aux hij hik hjk hc'

theorem i28_14_symAut_common_point (hm : 5 ≤ m)
    (hα : ∀ i j : Fin m, i ≠ j → ∃ a b : Fin m, a ≠ b ∧ α (swap i j) = swap a b) (i : Fin m) :
    ∃ p, ∀ j, j ≠ i → p ∈ (α (swap i j)).support := by
  have hsw : ∀ j, j ≠ i → (α (swap i j)).IsSwap := fun j hj => by
    obtain ⟨a, b, hab, h⟩ := hα i j hj.symm
    exact ⟨a, b, hab, h⟩
  classical
  let f : Fin m → Finset (Fin m) := fun j => (α (swap i j)).support
  have hinj : Set.InjOn f (Finset.univ.erase i : Finset (Fin m)) := by
    intro j hj k hk hjk
    have hj' := Finset.ne_of_mem_erase hj
    have hk' := Finset.ne_of_mem_erase hk
    have h1 := i28_14_symAut_support_inj (hsw j hj') (hsw k hk') hjk
    have h2 : swap i j = swap i k := α.injective h1
    have := congrArg (fun g : Perm (Fin m) => g i) h2
    simpa using this
  have hcard : ((Finset.univ.erase i).image f).card = m - 1 := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp
  obtain ⟨p, hp⟩ := i28_14_symAut_star ((Finset.univ.erase i).image f) (by
      intro A hA
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hA
      exact Equiv.Perm.card_support_eq_two.2 (hsw j (Finset.ne_of_mem_erase hj))) (by
      intro A hA B hB
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hA
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hB
      have hj' := Finset.ne_of_mem_erase hj
      have hk' := Finset.ne_of_mem_erase hk
      by_cases hjk : j = k
      · subst hjk
        have : 0 < (f j).card := by
          rw [Equiv.Perm.card_support_eq_two.2 (hsw j hj')]; omega
        simpa using Finset.card_pos.1 this
      · exact Finset.not_disjoint_iff_nonempty_inter.1
          (i28_14_symAut_inter α hj'.symm hk'.symm hjk)) (by omega)
  exact ⟨p, fun j hj => hp _ (Finset.mem_image_of_mem f (by simp [hj]))⟩

theorem i28_14_symAut_point_injective (hm : 5 ≤ m)
    (hα : ∀ i j : Fin m, i ≠ j → ∃ a b : Fin m, a ≠ b ∧ α (swap i j) = swap a b)
    (π : Fin m → Fin m) (hπ : ∀ i j, j ≠ i → π i ∈ (α (swap i j)).support) :
    Function.Injective π := by
  intro i j hij
  by_contra hne
  classical
  have hcard : 1 < (((Finset.univ : Finset (Fin m)).erase i).erase j).card := by
    rw [Finset.card_erase_of_mem, Finset.card_erase_of_mem (Finset.mem_univ _)]
    · simp; omega
    · simp [Ne.symm hne]
  obtain ⟨k, hk, l, hl, hkl⟩ := Finset.one_lt_card.1 hcard
  simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hk hl
  have hsw : ∀ a b : Fin m, a ≠ b → (α (swap a b)).IsSwap := fun a b hab => by
    obtain ⟨c, d, hcd, h⟩ := hα a b hab
    exact ⟨c, d, hcd, h⟩
  have hk1 : k ≠ i := hk.2
  have hl1 : l ≠ i := hl.2
  have hk2 : k ≠ j := hk.1
  have hl2 : l ≠ j := hl.1
  have hne' : α (swap i k) ≠ α (swap j l) := by
    intro h
    have h2 : swap i k = swap j l := α.injective h
    have := congrArg (fun g : Perm (Fin m) => g i) h2
    simp [swap_apply_def, hne, hl1.symm] at this
    exact hk1 this
  have hdisj : Commute (swap i k) (swap j l) := by
    apply i28_14_symAut_commute_of_disjoint
    rw [support_swap hk1.symm, support_swap hl2.symm, Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hx'
    rcases hx with h | h <;> rcases hx' with h' | h' <;> grind
  have hc : Commute (α (swap i k)) (α (swap j l)) := by
    unfold Commute SemiconjBy
    rw [← map_mul, ← map_mul, hdisj.eq]
  exact i28_14_symAut_not_commute (hsw i k hk1.symm) (hsw j l hl2.symm) hne'
    (by
      rw [Finset.not_disjoint_iff]
      exact ⟨π i, hπ i k hk1, hij ▸ hπ j l hl2⟩) hc

end Swaps

theorem perm_aut_preserving_swaps_inner {m : ℕ} (hm : 5 ≤ m) (α : MulAut (Equiv.Perm (Fin m)))
    (hα : ∀ i j : Fin m, i ≠ j → ∃ a b : Fin m, a ≠ b ∧ α (Equiv.swap i j) = Equiv.swap a b) :
    ∃ π : Equiv.Perm (Fin m), α = MulAut.conj π := by
  choose π hπ using i28_14_symAut_common_point α hm hα
  have hinj : Function.Injective π := i28_14_symAut_point_injective α hm hα π hπ
  let σ : Perm (Fin m) := Equiv.ofBijective π (Finite.injective_iff_bijective.1 hinj)
  have hσ : ∀ i, σ i = π i := fun i => rfl
  have hswap : ∀ i j : Fin m, i ≠ j → α (swap i j) = swap (σ i) (σ j) := by
    intro i j hij
    obtain ⟨a, b, hab, h⟩ := hα i j hij
    have h1 : π i ∈ (swap a b).support := h ▸ hπ i j hij.symm
    have h2 : π j ∈ (swap a b).support := by
      rw [← h, swap_comm]
      exact hπ j i hij
    rw [support_swap hab] at h1 h2
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    have hne : π i ≠ π j := fun e => hij (hinj e)
    rw [h, hσ, hσ]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · rw [h1, h2]
    · rw [h1, h2, swap_comm]
    · exact absurd (h1.trans h2.symm) hne
  refine ⟨σ, ?_⟩
  have hhom : (α : Perm (Fin m) →* Perm (Fin m)) = (MulAut.conj σ : Perm (Fin m) →* Perm (Fin m)) := by
    refine MonoidHom.eq_of_eqOn_dense closure_isSwap ?_
    intro s hs
    obtain ⟨i, j, hij, rfl⟩ := hs
    change α (swap i j) = σ * swap i j * σ⁻¹
    rw [hswap i j hij, swap_apply_apply]
  exact MulEquiv.ext fun x => DFunLike.congr_fun hhom x

end CFSG.HardMathSupport.Solomon.Coordinator
