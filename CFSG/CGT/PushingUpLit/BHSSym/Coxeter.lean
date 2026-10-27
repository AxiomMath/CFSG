module

public import CFSG.Permutation.SymmetricCoxeter
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

public section

namespace CFSG.CGT.PushingUpLit.BHSSym

open CFSG.Permutation.SymmetricCoxeter Equiv Equiv.Perm

section Relations

variable {H : Type*} [Group H]

theorem braid_of_pow_three {u v : H} (hu : u * u = 1) (hv : v * v = 1) (h : (u * v) ^ 3 = 1) :
    u * v * u = v * u * v := by
  have h6 : (u * v * u) * (v * u * v) = 1 := by
    have h' : (u * v) ^ 3 = (u * v * u) * (v * u * v) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [← h', h]
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  rw [eq_inv_of_mul_eq_one_left h6]
  simp [mul_assoc, hu', hv']

theorem pow_three_of_braid {u v : H} (hu : u * u = 1) (hv : v * v = 1) (h : u * v * u = v * u * v) :
    (u * v) ^ 3 = 1 := by
  calc (u * v) ^ 3 = (u * v * u) * (v * u * v) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = (v * u * v) * (v * u * v) := by rw [h]
    _ = v * u * (v * v) * u * v := by simp only [mul_assoc]
    _ = 1 := by rw [hv]; simp only [mul_one, mul_assoc, hu, hv]

theorem IsCoxeterA.pow_three {n : ℕ} {x : ℕ → H} (hx : IsCoxeterA n x) {i : ℕ} (hi : i + 1 < n) :
    (x i * x (i + 1)) ^ 3 = 1 :=
  pow_three_of_braid (hx.sq i (by omega)) (hx.sq (i + 1) hi) (hx.braid i hi)

theorem isCoxeterA_of_pow_three {n : ℕ} {x : ℕ → H} (hsq : ∀ i, i < n → x i * x i = 1)
    (hadj : ∀ i, i + 1 < n → (x i * x (i + 1)) ^ 3 = 1)
    (hcomm : ∀ i j, i + 2 ≤ j → j < n → x i * x j = x j * x i) : IsCoxeterA n x :=
  ⟨hsq, fun i hi => braid_of_pow_three (hsq i (by omega)) (hsq (i + 1) hi) (hadj i hi), hcomm⟩

end Relations

section Swaps

variable {α : Type*} [DecidableEq α]

theorem swap_eq_swap {a b c d : α} (hab : a ≠ b) (hcd : c ≠ d) (h : swap a b = swap c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have h1 := congrArg (fun f => f a) h
  simp only [swap_apply_left] at h1
  by_cases hac : a = c
  · subst hac
    left
    refine ⟨rfl, ?_⟩
    simpa [swap_apply_left] using h1
  · by_cases had : a = d
    · subst had
      right
      refine ⟨rfl, ?_⟩
      simpa [swap_apply_right] using h1
    · rw [swap_apply_of_ne_of_ne hac had] at h1
      exact absurd h1.symm hab

theorem exists_two_ne [Fintype α] (h3 : 3 ≤ Fintype.card α) (a : α) :
    ∃ b c : α, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  have h : 1 < ((Finset.univ : Finset α).erase a).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]
    omega
  obtain ⟨b, hb, c, hc, hbc⟩ := Finset.one_lt_card.1 h
  exact ⟨b, c, (Finset.ne_of_mem_erase hb).symm, (Finset.ne_of_mem_erase hc).symm, hbc⟩

theorem eq_one_of_forall_swap_conj [Fintype α] (h3 : 3 ≤ Fintype.card α) {σ : Perm α}
    (h : ∀ a b : α, a ≠ b → swap (σ a) (σ b) = swap a b) : σ = 1 := by
  refine Equiv.ext fun a => ?_
  rw [Perm.one_apply]
  obtain ⟨b, c, hab, hac, hbc⟩ := exists_two_ne h3 a
  have hb := swap_eq_swap (σ.injective.ne hab) hab (h a b hab)
  have hc := swap_eq_swap (σ.injective.ne hac) hac (h a c hac)
  rcases hb with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact h1
  · rcases hc with ⟨h2, -⟩ | ⟨h2, -⟩
    · exact h2
    · exact absurd (h1.symm.trans h2) hbc

end Swaps

theorem injective_vec3 {β : Type*} {p q r : β} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    Function.Injective ![p, q, r] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> tauto

theorem injective_vec4 {β : Type*} {p q r s : β} (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) : Function.Injective ![p, q, r, s] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> tauto

section Kernel

variable {H : Type*} [Group H] {n : ℕ}

theorem hom_swap_conj (ψ : Perm (Fin (n + 1)) →* H) (σ : Perm (Fin (n + 1)))
    (a b : Fin (n + 1)) :
    ψ (swap (σ a) (σ b)) = ψ σ * ψ (swap a b) * (ψ σ)⁻¹ := by
  rw [swap_apply_apply, map_mul, map_mul, map_inv]

theorem hom_swap_adj {x : ℕ → H} {ψ : Perm (Fin (n + 1)) →* H}
    (hψ : ∀ i, i < n → ψ (adjSwap n i) = x i) {i : ℕ} (hi : i < n) :
    ψ (swap (⟨i, by omega⟩ : Fin (n + 1)) ⟨i + 1, by omega⟩) = x i := by
  rw [← adjSwap_of_lt hi]
  exact hψ i hi

theorem hom_swap_ne_overlap (hn : 2 ≤ n) {x : ℕ → H} {ψ : Perm (Fin (n + 1)) →* H}
    (hψ : ∀ i, i < n → ψ (adjSwap n i) = x i) (h01 : x 0 ≠ x 1)
    {p q r : Fin (n + 1)} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ψ (swap p q) ≠ ψ (swap p r) := by
  have hf : Function.Injective
      ![(⟨1, by omega⟩ : Fin (n + 1)), ⟨0, by omega⟩, ⟨2, by omega⟩] :=
    injective_vec3 (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
  obtain ⟨σ, hσ⟩ := Perm.exists_extending_pair _ ![p, q, r] hf (injective_vec3 hpq hpr hqr)
  have e1 : σ ⟨1, by omega⟩ = p := hσ 0
  have e0 : σ ⟨0, by omega⟩ = q := hσ 1
  have e2 : σ ⟨2, by omega⟩ = r := hσ 2
  have h0 := hom_swap_conj ψ σ ⟨0, by omega⟩ ⟨1, by omega⟩
  have h1 := hom_swap_conj ψ σ ⟨1, by omega⟩ ⟨2, by omega⟩
  rw [e0, e1, hom_swap_adj hψ (by omega : 0 < n)] at h0
  rw [e1, e2, hom_swap_adj hψ (by omega : 1 < n)] at h1
  intro h
  rw [swap_comm] at h0
  have h2 : ψ σ * x 0 * (ψ σ)⁻¹ = ψ σ * x 1 * (ψ σ)⁻¹ := h0.symm.trans (h.trans h1)
  exact h01 (mul_left_cancel (mul_right_cancel h2))

theorem hom_swap_ne_disjoint (hn : 3 ≤ n) {x : ℕ → H} {ψ : Perm (Fin (n + 1)) →* H}
    (hψ : ∀ i, i < n → ψ (adjSwap n i) = x i) (h02 : x 0 ≠ x 2)
    {p q r s : Fin (n + 1)} (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r)
    (hqs : q ≠ s) (hrs : r ≠ s) : ψ (swap p q) ≠ ψ (swap r s) := by
  have hf : Function.Injective
      ![(⟨0, by omega⟩ : Fin (n + 1)), ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩] :=
    injective_vec4 (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
      (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
  obtain ⟨σ, hσ⟩ := Perm.exists_extending_pair _ ![p, q, r, s] hf
    (injective_vec4 hpq hpr hps hqr hqs hrs)
  have e0 : σ ⟨0, by omega⟩ = p := hσ 0
  have e1 : σ ⟨1, by omega⟩ = q := hσ 1
  have e2 : σ ⟨2, by omega⟩ = r := hσ 2
  have e3 : σ ⟨3, by omega⟩ = s := hσ 3
  have h0 := hom_swap_conj ψ σ ⟨0, by omega⟩ ⟨1, by omega⟩
  have h1 := hom_swap_conj ψ σ ⟨2, by omega⟩ ⟨3, by omega⟩
  rw [e0, e1, hom_swap_adj hψ (by omega : 0 < n)] at h0
  rw [e2, e3, hom_swap_adj hψ (by omega : 2 < n)] at h1
  intro h
  have h2 : ψ σ * x 0 * (ψ σ)⁻¹ = ψ σ * x 2 * (ψ σ)⁻¹ := h0.symm.trans (h.trans h1)
  exact h02 (mul_left_cancel (mul_right_cancel h2))

theorem swap_eq_of_hom_swap_eq (hn : 2 ≤ n) {x : ℕ → H} {ψ : Perm (Fin (n + 1)) →* H}
    (hψ : ∀ i, i < n → ψ (adjSwap n i) = x i) (h01 : x 0 ≠ x 1) (h02 : 3 ≤ n → x 0 ≠ x 2)
    {a b c d : Fin (n + 1)} (hab : a ≠ b) (hcd : c ≠ d) (h : ψ (swap a b) = ψ (swap c d)) :
    swap a b = swap c d := by
  by_contra hne
  have ov := fun {p q r : Fin (n + 1)} => hom_swap_ne_overlap hn hψ h01 (p := p) (q := q) (r := r)
  by_cases hac : a = c
  · subst hac
    by_cases hbd : b = d
    · subst hbd
      exact hne rfl
    · exact ov hab hcd hbd h
  · by_cases had : a = d
    · subst had
      by_cases hbc : b = c
      · subst hbc
        exact hne (swap_comm _ _)
      · rw [swap_comm c a] at h
        exact ov hab hcd.symm hbc h
    · by_cases hbc : b = c
      · subst hbc
        rw [swap_comm a b] at h
        exact ov hab.symm hcd had h
      · by_cases hbd : b = d
        · subst hbd
          rw [swap_comm a b, swap_comm c b] at h
          exact ov hab.symm hcd.symm hac h
        · by_cases hn3 : 3 ≤ n
          · exact hom_swap_ne_disjoint hn3 hψ (h02 hn3) hab hac had hbc hbd hcd h
          · exfalso
            have : n = 2 := by omega
            subst this
            have hinj : Function.Injective ![a, b, c, d] :=
              injective_vec4 hab hac had hbc hbd hcd
            have := Fintype.card_le_of_injective _ hinj
            simp at this

theorem injective_of_adjSwap_images (hn : 2 ≤ n) {x : ℕ → H} {ψ : Perm (Fin (n + 1)) →* H}
    (hψ : ∀ i, i < n → ψ (adjSwap n i) = x i) (h01 : x 0 ≠ x 1) (h02 : 3 ≤ n → x 0 ≠ x 2) :
    Function.Injective ψ := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  refine eq_one_of_forall_swap_conj (by simp; omega) fun a b hab => ?_
  have h1 : ψ (swap (σ a) (σ b)) = ψ (swap a b) := by
    rw [hom_swap_conj, hσ]
    simp
  exact swap_eq_of_hom_swap_eq hn hψ h01 h02 (σ.injective.ne hab) hab h1

theorem exists_mulEquiv_closure (hn : 2 ≤ n) {x : ℕ → H} (hx : IsCoxeterA n x) (h01 : x 0 ≠ x 1)
    (h02 : 3 ≤ n → x 0 ≠ x 2) :
    ∃ e : Perm (Fin (n + 1)) ≃* ↥(Subgroup.closure (x '' Set.Iio n)),
      ∀ i, i < n → ((e (adjSwap n i) : ↥(Subgroup.closure (x '' Set.Iio n))) : H) = x i := by
  obtain ⟨ψ, hψ⟩ := exists_hom_perm n x hx
  have hinj := injective_of_adjSwap_images hn hψ h01 h02
  have hrange : ψ.range = Subgroup.closure (x '' Set.Iio n) := by
    rw [MonoidHom.range_eq_map, ← closure_adjSwap n, MonoidHom.map_closure, Set.image_image]
    congr 1
    refine Set.image_congr fun i hi => ?_
    exact hψ i hi
  refine ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange), fun i hi => ?_⟩
  exact hψ i hi

theorem exists_mulEquiv_of_pow_three (hn : 2 ≤ n) {x : ℕ → H} (hsq : ∀ i, i < n → x i * x i = 1)
    (hadj : ∀ i, i + 1 < n → (x i * x (i + 1)) ^ 3 = 1)
    (hcomm : ∀ i j, i + 2 ≤ j → j < n → x i * x j = x j * x i)
    (hne : ∀ i j, i < n → j < n → i ≠ j → x i ≠ x j) :
    ∃ e : Perm (Fin (n + 1)) ≃* ↥(Subgroup.closure (x '' Set.Iio n)),
      ∀ i, i < n → ((e (adjSwap n i) : ↥(Subgroup.closure (x '' Set.Iio n))) : H) = x i :=
  exists_mulEquiv_closure hn (isCoxeterA_of_pow_three hsq hadj hcomm)
    (hne 0 1 (by omega) (by omega) (by omega))
    (fun h3 => hne 0 2 (by omega) (by omega) (by omega))

end Kernel

theorem isCoxeterA_symm_adjSwap {E : Type*} [Group E] {m : ℕ} (θ : E ≃* Perm (Fin (m + 1))) :
    IsCoxeterA m (fun i => θ.symm (adjSwap m i)) :=
  IsCoxeterA.map θ.symm.toMonoidHom (isCoxeterA_adjSwap m)

theorem exists_mulEquiv_perm_of_isCoxeterA {Γ : Type*} [Group Γ] {k : ℕ} (hk : 2 ≤ k)
    (E : Subgroup Γ) (t : ℕ → Γ) (ht : IsCoxeterA k t) (htE : ∀ i < k, t i ∈ E)
    (hne : ∀ i < k, ∀ j < k, i ≠ j → t i ≠ t j) (_hne1 : ∀ i < k, t i ≠ 1)
    (hgen : Subgroup.closure (t '' Set.Iio k) = E) :
    ∃ θ : ↥E ≃* Perm (Fin (k + 1)), ∀ (i : ℕ) (hi : i < k), θ ⟨t i, htE i hi⟩ = adjSwap k i := by
  subst hgen
  obtain ⟨e, he⟩ := exists_mulEquiv_closure hk ht (hne 0 (by omega) 1 (by omega) (by omega))
    (fun _ => hne 0 (by omega) 2 (by omega) (by omega))
  refine ⟨e.symm, fun i hi => ?_⟩
  rw [MulEquiv.symm_apply_eq]
  exact Subtype.ext (he i hi).symm

end CFSG.CGT.PushingUpLit.BHSSym
