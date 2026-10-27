module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.MaximalSubgroups

public section

namespace CFSG.CGT.PushingUpLit.SolK

open Equiv Equiv.Perm MulAction
open scoped Pointwise

variable {d : ℕ}

theorem swap_stab {A : Finset (Fin d)} {p q : Fin d} (h : p ∈ A ↔ q ∈ A) :
    ∀ z, swap p q z ∈ A ↔ z ∈ A := by
  intro z
  by_cases hp : z = p
  · subst hp
    rw [swap_apply_left]
    exact h.symm
  · by_cases hq : z = q
    · subst hq
      rw [swap_apply_right]
      exact h
    · rw [swap_apply_of_ne_of_ne hp hq]

theorem mem_stabilizer_alt_iff (I : Finset (Fin d)) (σ : ↥(alternatingGroup (Fin d))) :
    σ ∈ stabilizer (alternatingGroup (Fin d)) (I : Set (Fin d)) ↔
      ∀ x, (σ : Perm (Fin d)) x ∈ I ↔ x ∈ I := by
  have hact : ∀ (τ : ↥(alternatingGroup (Fin d))) (x : Fin d), τ • x = (τ : Perm (Fin d)) x :=
    fun τ x => rfl
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h x
    have h1 : σ • x ∈ σ • (I : Set (Fin d)) ↔ x ∈ (I : Set (Fin d)) := Set.smul_mem_smul_set_iff
    rw [h, hact] at h1
    simpa using h1
  · intro h
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem, hact]
    have := h (((σ⁻¹ : ↥(alternatingGroup (Fin d))) : Perm (Fin d)) x)
    have e : (σ : Perm (Fin d)) (((σ⁻¹ : ↥(alternatingGroup (Fin d))) : Perm (Fin d)) x) = x := by
      simp
    rw [e] at this
    simpa using this.symm

theorem swap_mul_swap_mem_alt' {a b c e : Fin d} (hab : a ≠ b) (hce : c ≠ e) :
    swap a b * swap c e ∈ alternatingGroup (Fin d) := by
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab,
    Equiv.Perm.sign_swap hce]
  decide

theorem exists_alt_stab_map (hd : 5 ≤ d) {A : Finset (Fin d)} {a b : Fin d} (ha : a ∈ A)
    (hb : b ∈ A) (hab : a ≠ b) :
    ∃ σ : Perm (Fin d), σ ∈ alternatingGroup (Fin d) ∧ (∀ x, σ x ∈ A ↔ x ∈ A) ∧ σ a = b := by
  classical
  have hcard : A.card + Aᶜ.card = d := by
    rw [Finset.card_add_card_compl, Fintype.card_fin]
  obtain ⟨x, y, hxy, hxyA, hxa, hxb, hya, hyb⟩ : ∃ x y : Fin d, x ≠ y ∧ (x ∈ A ↔ y ∈ A) ∧
      x ≠ a ∧ x ≠ b ∧ y ≠ a ∧ y ≠ b := by
    by_cases h2 : 2 ≤ Aᶜ.card
    · obtain ⟨x, y, hx, hy, hxy⟩ := Finset.one_lt_card_iff.1 (by omega : 1 < Aᶜ.card)
      have hx' : x ∉ A := Finset.mem_compl.1 hx
      have hy' : y ∉ A := Finset.mem_compl.1 hy
      exact ⟨x, y, hxy, ⟨fun h => absurd h hx', fun h => absurd h hy'⟩,
        fun h => hx' (h ▸ ha), fun h => hx' (h ▸ hb), fun h => hy' (h ▸ ha),
        fun h => hy' (h ▸ hb)⟩
    · have h1 := Finset.le_card_sdiff ({a, b} : Finset (Fin d)) A
      have h2' : ({a, b} : Finset (Fin d)).card ≤ 2 := Finset.card_le_two
      obtain ⟨x, y, hx, hy, hxy⟩ := Finset.one_lt_card_iff.1 (by omega : 1 < (A \ {a, b}).card)
      rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hx hy
      push Not at hx hy
      exact ⟨x, y, hxy, ⟨fun _ => hy.1, fun _ => hx.1⟩, hx.2.1, hx.2.2, hy.2.1, hy.2.2⟩
  refine ⟨swap a b * swap x y, swap_mul_swap_mem_alt' hab hxy, fun z => ?_, ?_⟩
  · rw [mul_apply]
    exact (swap_stab ⟨fun _ => hb, fun _ => ha⟩ (swap x y z)).trans (swap_stab hxyA z)
  · rw [mul_apply, swap_apply_of_ne_of_ne (Ne.symm hxa) (Ne.symm hya), swap_apply_left]

theorem isCoatom_altStab (hdodd : Odd d) {I : Finset (Fin d)} (hI : I.Nonempty)
    (hIe : Even I.card) :
    IsCoatom (stabilizer (alternatingGroup (Fin d)) (I : Set (Fin d))) := by
  have hIc : Iᶜ.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have h1 := Finset.card_add_card_compl I
    rw [h, Finset.card_empty, Fintype.card_fin] at h1
    obtain ⟨k, hk⟩ := hIe
    obtain ⟨m, hm⟩ := hdodd
    omega
  apply alternatingGroup.isCoatom_stabilizer
  · exact_mod_cast hI
  · rw [← Finset.coe_compl]
    exact_mod_cast hIc
  · rw [Set.ncard_coe_finset, Nat.card_eq_fintype_card, Fintype.card_fin]
    obtain ⟨k, hk⟩ := hIe
    obtain ⟨m, hm⟩ := hdodd
    omega

theorem altStab_ne (hd : 5 ≤ d) (hdodd : Odd d) {I J : Finset (Fin d)} (hIe : Even I.card)
    (hJe : Even J.card) (hJ0 : J.Nonempty) (hne : I ≠ J) :
    stabilizer (alternatingGroup (Fin d)) (I : Set (Fin d)) ≠
      stabilizer (alternatingGroup (Fin d)) (J : Set (Fin d)) := by
  classical
  intro heq
  have hJ : ∀ σ : Perm (Fin d), σ ∈ alternatingGroup (Fin d) → (∀ x, σ x ∈ I ↔ x ∈ I) →
      ∀ x, σ x ∈ J ↔ x ∈ J := by
    intro σ hσ hI x
    have h1 : (⟨σ, hσ⟩ : ↥(alternatingGroup (Fin d))) ∈
        stabilizer (alternatingGroup (Fin d)) (I : Set (Fin d)) :=
      (mem_stabilizer_alt_iff I _).2 hI
    rw [heq] at h1
    exact (mem_stabilizer_alt_iff J _).1 h1 x
  have hI1 : ∀ a ∈ I, ∀ b ∈ I, (a ∈ J ↔ b ∈ J) := by
    intro a ha b hb
    by_cases hab : a = b
    · rw [hab]
    · obtain ⟨σ, hσ, hstab, hσa⟩ := exists_alt_stab_map hd ha hb hab
      have := hJ σ hσ hstab a
      rw [hσa] at this
      exact this.symm
  have hI2 : ∀ a ∈ Iᶜ, ∀ b ∈ Iᶜ, (a ∈ J ↔ b ∈ J) := by
    intro a ha b hb
    by_cases hab : a = b
    · rw [hab]
    · obtain ⟨σ, hσ, hstab, hσa⟩ := exists_alt_stab_map hd ha hb hab
      have hstab' : ∀ x, σ x ∈ I ↔ x ∈ I := fun x => by
        have := hstab x
        rw [Finset.mem_compl, Finset.mem_compl] at this
        exact not_iff_not.1 this
      have := hJ σ hσ hstab' a
      rw [hσa] at this
      exact this.symm
  have hcompl : Iᶜ.card + I.card = d := by
    rw [add_comm, Finset.card_add_card_compl, Fintype.card_fin]
  have hIcodd : ¬ Even Iᶜ.card := by
    obtain ⟨k, hk⟩ := hIe
    obtain ⟨m, hm⟩ := hdodd
    rintro ⟨l, hl⟩
    omega
  have hdJ : J.card ≠ d := by
    obtain ⟨m, hm⟩ := hdodd
    obtain ⟨l, hl⟩ := hJe
    omega
  apply hne
  by_cases hIJ : ∃ y ∈ I, y ∈ J
  · obtain ⟨y, hyI, hyJ⟩ := hIJ
    have hIsub : I ⊆ J := fun a ha => (hI1 a ha y hyI).2 hyJ
    by_cases hcJ : ∃ z ∈ Iᶜ, z ∈ J
    · obtain ⟨z, hzI, hzJ⟩ := hcJ
      have hIcsub : Iᶜ ⊆ J := fun a ha => (hI2 a ha z hzI).2 hzJ
      exfalso
      apply hdJ
      have : J = Finset.univ := by
        refine Finset.eq_univ_iff_forall.2 fun x => ?_
        by_cases hx : x ∈ I
        · exact hIsub hx
        · exact hIcsub (Finset.mem_compl.2 hx)
      rw [this, Finset.card_univ, Fintype.card_fin]
    · push Not at hcJ
      refine Finset.Subset.antisymm hIsub fun x hx => ?_
      by_contra hxI
      exact hcJ x (Finset.mem_compl.2 hxI) hx
  · push Not at hIJ
    exfalso
    obtain ⟨z, hz⟩ := hJ0
    have hzI : z ∈ Iᶜ := Finset.mem_compl.2 fun h => hIJ z h hz
    have hJeq : J = Iᶜ := by
      refine Finset.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
      · exact Finset.mem_compl.2 fun h => hIJ x h hx
      · exact (hI2 x hx z hzI).2 hz
    exact hIcodd (hJeq ▸ hJe)

theorem eq_top_of_stab_le (hd : 5 ≤ d) (hdodd : Odd d) {I J : Finset (Fin d)}
    (hIe : Even I.card) (hJe : Even J.card) (hI0 : I.Nonempty) (hJ0 : J.Nonempty) (hne : I ≠ J)
    {K : Subgroup ↥(alternatingGroup (Fin d))}
    (hIK : stabilizer (alternatingGroup (Fin d)) (I : Set (Fin d)) ≤ K)
    (hJK : stabilizer (alternatingGroup (Fin d)) (J : Set (Fin d)) ≤ K) : K = ⊤ := by
  by_contra hK
  have hcI := isCoatom_altStab hdodd hI0 hIe
  have hcJ := isCoatom_altStab hdodd hJ0 hJe
  have h1 : stabilizer (alternatingGroup (Fin d)) (I : Set (Fin d)) = K := by
    by_contra h
    exact hK (hcI.2 K (lt_of_le_of_ne hIK h))
  have h2 : stabilizer (alternatingGroup (Fin d)) (J : Set (Fin d)) = K := by
    by_contra h
    exact hK (hcJ.2 K (lt_of_le_of_ne hJK h))
  exact altStab_ne hd hdodd hIe hJe hJ0 hne (h1.trans h2.symm)

end CFSG.CGT.PushingUpLit.SolK
