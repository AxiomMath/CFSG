module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15A10GenJ1

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace A10StabS8

open Equiv Equiv.Perm

abbrev Rest (a b : Fin 10) : Type := {z : Fin 10 // z ≠ a ∧ z ≠ b}

theorem card_rest {a b : Fin 10} (hab : a ≠ b) : Fintype.card (Rest a b) = 8 := by
  classical
  rw [Fintype.card_subtype]
  have h : (Finset.univ.filter fun z : Fin 10 => z ≠ a ∧ z ≠ b) = Finset.univ \ {a, b} := by
    ext z
    simp [not_or]
  rw [h, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_pair hab]
  simp

noncomputable def toRest {a b : Fin 10} (hab : a ≠ b) : Fin 8 ≃ Rest a b :=
  (Fintype.equivFinOfCardEq (card_rest hab)).symm

noncomputable def ext8 {a b : Fin 10} (hab : a ≠ b) : Perm (Fin 8) →* Perm (Fin 10) :=
  Equiv.Perm.extendDomainHom (toRest hab)

theorem ext8_apply_a {a b : Fin 10} (hab : a ≠ b) (τ : Perm (Fin 8)) : ext8 hab τ a = a :=
  Equiv.Perm.extendDomain_apply_not_subtype _ _ (fun h => h.1 rfl)

theorem ext8_apply_b {a b : Fin 10} (hab : a ≠ b) (τ : Perm (Fin 8)) : ext8 hab τ b = b :=
  Equiv.Perm.extendDomain_apply_not_subtype _ _ (fun h => h.2 rfl)

theorem ext8_apply_rest {a b : Fin 10} (hab : a ≠ b) (τ : Perm (Fin 8)) (x : Fin 8) :
    ext8 hab τ (toRest hab x) = toRest hab (τ x) :=
  Equiv.Perm.extendDomain_apply_image _ _ _

theorem sign_ext8 {a b : Fin 10} (hab : a ≠ b) (τ : Perm (Fin 8)) :
    Perm.sign (ext8 hab τ) = Perm.sign τ :=
  Equiv.Perm.sign_extendDomain _ _

theorem commute_ext8_swap {a b : Fin 10} (hab : a ≠ b) (τ : Perm (Fin 8)) :
    Commute (ext8 hab τ) (swap a b) := by
  refine Equiv.Perm.Disjoint.commute fun x => ?_
  by_cases hx : x ≠ a ∧ x ≠ b
  · exact Or.inr (swap_apply_of_ne_of_ne hx.1 hx.2)
  · refine Or.inl (Equiv.Perm.extendDomain_apply_not_subtype _ _ hx)

noncomputable def fixer (a b : Fin 10) (τ : Perm (Fin 8)) : Perm (Fin 10) :=
  if Perm.sign τ = 1 then 1 else swap a b

theorem fixer_mul (a b : Fin 10) (τ₁ τ₂ : Perm (Fin 8)) :
    fixer a b (τ₁ * τ₂) = fixer a b τ₁ * fixer a b τ₂ := by
  have hss : swap a b * swap a b = 1 := swap_mul_self a b
  have hne : ¬ ((-1 : ℤˣ) = 1) := by decide
  unfold fixer
  rcases Int.units_eq_one_or (Perm.sign τ₁) with h1 | h1 <;>
    rcases Int.units_eq_one_or (Perm.sign τ₂) with h2 | h2
  · have h12 : Perm.sign (τ₁ * τ₂) = 1 := by rw [map_mul, h1, h2]; rfl
    rw [if_pos h12, if_pos h1, if_pos h2, mul_one]
  · have h12 : ¬ Perm.sign (τ₁ * τ₂) = 1 := by rw [map_mul, h1, h2]; exact hne
    rw [if_neg h12, if_pos h1, if_neg (by rw [h2]; exact hne), one_mul]
  · have h12 : ¬ Perm.sign (τ₁ * τ₂) = 1 := by rw [map_mul, h1, h2]; exact hne
    rw [if_neg h12, if_neg (by rw [h1]; exact hne), if_pos h2, mul_one]
  · have h12 : Perm.sign (τ₁ * τ₂) = 1 := by rw [map_mul, h1, h2]; rfl
    rw [if_pos h12, if_neg (by rw [h1]; exact hne), if_neg (by rw [h2]; exact hne), hss]

theorem commute_ext8_fixer {a b : Fin 10} (hab : a ≠ b) (τ₁ τ₂ : Perm (Fin 8)) :
    Commute (ext8 hab τ₂) (fixer a b τ₁) := by
  unfold fixer
  split_ifs
  · exact Commute.one_right _
  · exact commute_ext8_swap hab τ₂

@[expose] noncomputable def twist {a b : Fin 10} (hab : a ≠ b) : Perm (Fin 8) →* Perm (Fin 10) where
  toFun τ := ext8 hab τ * fixer a b τ
  map_one' := by simp [fixer]
  map_mul' τ₁ τ₂ := by
    have hcomm := (commute_ext8_fixer hab τ₁ τ₂).eq
    show ext8 hab (τ₁ * τ₂) * fixer a b (τ₁ * τ₂) =
      ext8 hab τ₁ * fixer a b τ₁ * (ext8 hab τ₂ * fixer a b τ₂)
    rw [map_mul, fixer_mul]
    calc ext8 hab τ₁ * ext8 hab τ₂ * (fixer a b τ₁ * fixer a b τ₂)
        = ext8 hab τ₁ * (ext8 hab τ₂ * fixer a b τ₁) * fixer a b τ₂ := by simp only [mul_assoc]
      _ = ext8 hab τ₁ * (fixer a b τ₁ * ext8 hab τ₂) * fixer a b τ₂ := by rw [hcomm]
      _ = ext8 hab τ₁ * fixer a b τ₁ * (ext8 hab τ₂ * fixer a b τ₂) := by simp only [mul_assoc]

theorem twist_apply {a b : Fin 10} (hab : a ≠ b) (τ : Perm (Fin 8)) :
    twist hab τ = ext8 hab τ * fixer a b τ := rfl

theorem fixer_apply_rest {a b : Fin 10} (τ : Perm (Fin 8)) {z : Fin 10} (hza : z ≠ a)
    (hzb : z ≠ b) : fixer a b τ z = z := by
  unfold fixer
  split_ifs
  · rfl
  · exact swap_apply_of_ne_of_ne hza hzb

theorem sign_twist {a b : Fin 10} (hab : a ≠ b) (τ : Perm (Fin 8)) :
    Perm.sign (twist hab τ) = 1 := by
  rw [twist_apply, map_mul, sign_ext8]
  unfold fixer
  rcases Int.units_eq_one_or (Perm.sign τ) with h | h
  · simp [h]
  · have h' : ¬ Perm.sign τ = 1 := by rw [h]; decide
    simp [h', h, Perm.sign_swap hab]

theorem twist_injective {a b : Fin 10} (hab : a ≠ b) : Function.Injective (twist hab) := by
  rw [injective_iff_map_eq_one]
  intro τ hτ
  refine Equiv.ext fun x => ?_
  have h1 : twist hab τ (toRest hab x : Fin 10) = (toRest hab x : Fin 10) := by rw [hτ]; rfl
  rw [twist_apply, Perm.mul_apply,
    fixer_apply_rest τ (toRest hab x).2.1 (toRest hab x).2.2, ext8_apply_rest] at h1
  have h2 : toRest hab (τ x) = toRest hab x := Subtype.ext h1
  exact (toRest hab).injective h2

theorem twist_apply_a_of_even {a b : Fin 10} (hab : a ≠ b) {τ : Perm (Fin 8)} (h : Perm.sign τ = 1) :
    twist hab τ a = a := by
  rw [twist_apply, Perm.mul_apply]
  simp [fixer, h, ext8_apply_a]

theorem twist_apply_b_of_even {a b : Fin 10} (hab : a ≠ b) {τ : Perm (Fin 8)} (h : Perm.sign τ = 1) :
    twist hab τ b = b := by
  rw [twist_apply, Perm.mul_apply]
  simp [fixer, h, ext8_apply_b]

theorem sign_eq_one_of_odd_orderOf {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α}
    (h : Odd (orderOf σ)) : Perm.sign σ = 1 := by
  have h1 : Perm.sign σ ^ orderOf σ = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  rcases Int.units_eq_one_or (Perm.sign σ) with h2 | h2
  · exact h2
  · rw [h2, h.neg_one_pow] at h1
    exact absurd h1 (by decide)

end A10StabS8

theorem exists_s8_of_embed (ψ : alternatingGroup (Fin 8) →* Equiv.Perm (Fin 10))
    (hψ : Function.Injective ψ) :
    ∃ P : Subgroup (alternatingGroup (Fin 10)), Nonempty (↥P ≃* Equiv.Perm (Fin 8)) ∧
      ∀ x ∈ P, Odd (orderOf x) → (x : Equiv.Perm (Fin 10)) ∈ ψ.range := by
  obtain ⟨a, b, hab, hstab⟩ := A10GenJ1.embed_contains_stabilizer ψ hψ
  let g : Equiv.Perm (Fin 8) →* alternatingGroup (Fin 10) :=
    (A10StabS8.twist hab).codRestrict _ fun τ =>
      Equiv.Perm.mem_alternatingGroup.2 (A10StabS8.sign_twist hab τ)
  have hg : Function.Injective g := fun τ τ' h =>
    A10StabS8.twist_injective hab (congrArg Subtype.val h)
  refine ⟨g.range, ⟨(MonoidHom.ofInjective hg).symm⟩, ?_⟩
  rintro _ ⟨τ, rfl⟩ hodd
  have hodd' : Odd (orderOf τ) := by rwa [← orderOf_injective g hg τ]
  have hs := A10StabS8.sign_eq_one_of_odd_orderOf hodd'
  exact hstab _ (Equiv.Perm.mem_alternatingGroup.2 (A10StabS8.sign_twist hab τ))
    (A10StabS8.twist_apply_a_of_even hab hs) (A10StabS8.twist_apply_b_of_even hab hs)

end CFSG.LocalAnalysis.RankThreeUC.S15
