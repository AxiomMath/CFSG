module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTypesPerm

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPTwoThree

open Equiv Subgroup Janko

theorem sbar₁_mem_Ebar : sbar₁ ∈ Ebar :=
  subset_closure (by simp)

theorem ebar₂_mem_Ebar : ebar₂ ∈ Ebar :=
  subset_closure (by simp)

theorem ebar₃_mem_Ebar : ebar₃ ∈ Ebar :=
  subset_closure (by simp)

theorem sbar₂_eq : sbar₂ = ebar₂ * ebar₃ :=
  Subtype.ext (show (sbar₂ : Perm (Fin 9)) = ebar₂ * ebar₃ by decide)

theorem sbar₃_eq : sbar₃ = sbar₁ * ebar₂ * ebar₃ :=
  Subtype.ext (show (sbar₃ : Perm (Fin 9)) = sbar₁ * ebar₂ * ebar₃ by decide)

theorem sbar₂_mem_Ebar : sbar₂ ∈ Ebar := by
  rw [sbar₂_eq]
  exact mul_mem ebar₂_mem_Ebar ebar₃_mem_Ebar

theorem sbar₃_mem_Ebar : sbar₃ ∈ Ebar := by
  rw [sbar₃_eq]
  exact mul_mem (mul_mem sbar₁_mem_Ebar ebar₂_mem_Ebar) ebar₃_mem_Ebar

theorem Ebar_le_centralizer {g : alternatingGroup (Fin 9)} (h₁ : sbar₁ * g = g * sbar₁)
    (h₂ : ebar₂ * g = g * ebar₂) (h₃ : ebar₃ * g = g * ebar₃) : Ebar ≤ centralizer {g} := by
  rw [Ebar, closure_le]
  rintro x (rfl | rfl | rfl) <;> rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
  exacts [h₁, h₂, h₃]

theorem Ebar_le_centralizer_Ebar : Ebar ≤ centralizer (Ebar : Set (alternatingGroup (Fin 9))) := by
  rw [Ebar, centralizer_closure, closure_le]
  intro x hx
  rw [SetLike.mem_coe, mem_centralizer_iff]
  intro y hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    exact Subtype.ext (by decide)

theorem Ebar_le_centralizer_sbar₁ : Ebar ≤ centralizer {sbar₁} :=
  Ebar_le_centralizer rfl (Subtype.ext (by decide)) (Subtype.ext (by decide))

theorem Ebar_le_centralizer_sbar₂ : Ebar ≤ centralizer {sbar₂} :=
  Ebar_le_centralizer (Subtype.ext (by decide)) (Subtype.ext (by decide))
    (Subtype.ext (by decide))

theorem Ebar_le_centralizer_sbar₃ : Ebar ≤ centralizer {sbar₃} :=
  Ebar_le_centralizer (Subtype.ext (by decide)) (Subtype.ext (by decide))
    (Subtype.ext (by decide))

@[expose] def eword (p : Fin 3 × Fin 3 × Fin 3) : alternatingGroup (Fin 9) :=
  sbar₁ ^ (p.1 : ℕ) * ebar₂ ^ (p.2.1 : ℕ) * ebar₃ ^ (p.2.2 : ℕ)

theorem eword_mem (p : Fin 3 × Fin 3 × Fin 3) : eword p ∈ Ebar :=
  mul_mem (mul_mem (pow_mem sbar₁_mem_Ebar _) (pow_mem ebar₂_mem_Ebar _)) (pow_mem ebar₃_mem_Ebar _)

private theorem eword_apply_inj : ∀ p q : Fin 3 × Fin 3 × Fin 3,
    (eword p : Perm (Fin 9)) 0 = (eword q : Perm (Fin 9)) 0 →
    (eword p : Perm (Fin 9)) 3 = (eword q : Perm (Fin 9)) 3 →
    (eword p : Perm (Fin 9)) 6 = (eword q : Perm (Fin 9)) 6 → p = q := by
  decide +kernel

theorem eword_injective : Function.Injective eword := fun p q h =>
  eword_apply_inj p q (by rw [h]) (by rw [h]) (by rw [h])

private theorem eword_mem_injective :
    Function.Injective fun p : Fin 3 × Fin 3 × Fin 3 => (⟨eword p, eword_mem p⟩ : Ebar) :=
  fun _ _ h => eword_injective (congrArg Subtype.val h)

theorem card_Ebar : Nat.card Ebar = 27 := by
  have h1 : Nat.card Ebar ∣ 54 := card_centralizer_sbar₂ ▸ card_dvd_of_le Ebar_le_centralizer_sbar₂
  have h2 : Nat.card Ebar ∣ 81 := card_centralizer_sbar₃ ▸ card_dvd_of_le Ebar_le_centralizer_sbar₃
  have h3 : 27 ≤ Nat.card Ebar := by
    have := Nat.card_le_card_of_injective _ eword_mem_injective
    simpa using this
  have h4 : Nat.card Ebar ∣ 27 := by
    have := Nat.dvd_gcd h1 h2
    norm_num at this
    exact this
  exact le_antisymm (Nat.le_of_dvd (by norm_num) h4) h3

theorem exists_eword_eq {g : alternatingGroup (Fin 9)} (hg : g ∈ Ebar) : ∃ p, eword p = g := by
  obtain ⟨p, hp⟩ := (Function.Injective.bijective_of_nat_card_le eword_mem_injective
    (by rw [card_Ebar]; simp)).2 ⟨g, hg⟩
  exact ⟨p, congrArg Subtype.val hp⟩

private theorem eword_pow_three : ∀ p : Fin 3 × Fin 3 × Fin 3,
    ((eword p ^ 3 : alternatingGroup (Fin 9)) : Perm (Fin 9)) = 1 := by
  decide +kernel

theorem pow_three_of_mem_Ebar {g : alternatingGroup (Fin 9)} (hg : g ∈ Ebar) : g ^ 3 = 1 := by
  obtain ⟨p, rfl⟩ := exists_eword_eq hg
  exact Subtype.ext (eword_pow_three p)

theorem ρbar_mem_centralizer_sbar₃ : ρbar ∈ centralizer {sbar₃} :=
  mem_centralizer_singleton_iff.mpr (Subtype.ext (by decide))

theorem ρbar_mul_sbar₁_ne : ρbar * sbar₁ ≠ sbar₁ * ρbar := fun h =>
  absurd (congrArg Subtype.val h) (by decide)

theorem ρbar_not_mem_Ebar : ρbar ∉ Ebar := fun h =>
  ρbar_mul_sbar₁_ne (mem_centralizer_singleton_iff.mp (Ebar_le_centralizer_sbar₁ h))

theorem centralizer_Ebar : centralizer (Ebar : Set (alternatingGroup (Fin 9))) = Ebar := by
  set C := centralizer (Ebar : Set (alternatingGroup (Fin 9)))
  have h3 : C ≤ centralizer {sbar₃} := centralizer_le (Set.singleton_subset_iff.mpr sbar₃_mem_Ebar)
  have hd : Nat.card C ∣ 81 := card_centralizer_sbar₃ ▸ card_dvd_of_le h3
  have h27 : 27 ∣ Nat.card C := card_Ebar ▸ card_dvd_of_le Ebar_le_centralizer_Ebar
  have hne : Nat.card C ≠ 81 := by
    intro h
    have hC : C = centralizer {sbar₃} :=
      eq_of_le_of_card_ge h3 (by rw [h, card_centralizer_sbar₃])
    have hρ : ρbar ∈ C := hC ▸ ρbar_mem_centralizer_sbar₃
    exact ρbar_mul_sbar₁_ne (mem_centralizer_iff.mp hρ sbar₁ sbar₁_mem_Ebar).symm
  have hC : Nat.card C = 27 := by
    obtain ⟨k, hk⟩ := h27
    rw [hk] at hd hne ⊢
    have hk3 : k ∣ 3 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 27) (by simpa using hd)
    rcases (Nat.dvd_prime Nat.prime_three).mp hk3 with rfl | rfl <;> omega
  exact (eq_of_le_of_card_ge Ebar_le_centralizer_Ebar (by rw [hC, card_Ebar])).symm

theorem Ebar_le_Pbar : Ebar ≤ Pbar :=
  closure_mono (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto)

theorem ρbar_mem_Pbar : ρbar ∈ Pbar :=
  subset_closure (by simp)

theorem sbar₁_mem_Pbar : sbar₁ ∈ Pbar :=
  Ebar_le_Pbar sbar₁_mem_Ebar

theorem Pbar_le_centralizer_sbar₃ : Pbar ≤ centralizer {sbar₃} := by
  rw [Pbar, closure_le]
  rintro x (rfl | rfl | rfl | rfl) <;>
    exact mem_centralizer_singleton_iff.mpr (Subtype.ext (by decide))

theorem card_Pbar : Nat.card Pbar = 81 := by
  have hd : Nat.card Pbar ∣ 81 := card_centralizer_sbar₃ ▸ card_dvd_of_le Pbar_le_centralizer_sbar₃
  have h27 : 27 ∣ Nat.card Pbar := card_Ebar ▸ card_dvd_of_le Ebar_le_Pbar
  have hne : Nat.card Pbar ≠ 27 := fun h => ρbar_not_mem_Ebar
    ((eq_of_le_of_card_ge Ebar_le_Pbar (by rw [h, card_Ebar])) ▸ ρbar_mem_Pbar)
  obtain ⟨k, hk⟩ := h27
  rw [hk] at hd hne ⊢
  have hk3 : k ∣ 3 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 27) (by simpa using hd)
  rcases (Nat.dvd_prime Nat.prime_three).mp hk3 with rfl | rfl <;> omega

theorem centralizer_sbar₃_eq : centralizer {sbar₃} = Pbar :=
  (eq_of_le_of_card_ge Pbar_le_centralizer_sbar₃ (by rw [card_centralizer_sbar₃, card_Pbar])).symm

theorem card_centralizer_perm_of_cycleType_eq_two_two_two_two {σ : Perm (Fin 9)}
    (h : σ.cycleType = {2, 2, 2, 2}) : Nat.card (centralizer ({σ} : Set (Perm (Fin 9)))) = 384 := by
  rw [Perm.nat_card_centralizer, h, Fintype.card_fin]
  decide

theorem card_centralizer_tbar :
    Nat.card (centralizer ({tbar} : Set (alternatingGroup (Fin 9)))) = 192 := by
  have h := CFSG.GH74.GLS.Layer3.card_centralizer_alt_mul_two tbar (swap 1 2)
    (Perm.sign_swap (by decide)) (by decide)
  rw [card_centralizer_perm_of_cycleType_eq_two_two_two_two cycleType_tbar] at h
  omega

theorem orderOf_tbar : orderOf tbar = 2 :=
  orderOf_eq_prime (Subtype.ext (show (tbar : Perm (Fin 9)) ^ 2 = 1 by decide))
    (ne_one_of_cycleType_eq cycleType_tbar (by decide))

theorem sbar₂_mem_centralizer_tbar : sbar₂ ∈ centralizer {tbar} :=
  mem_centralizer_singleton_iff.mpr (Subtype.ext (by decide))

theorem Ebar_inf_centralizer_tbar : Ebar ⊓ centralizer {tbar} = zpowers sbar₂ := by
  have hle : zpowers sbar₂ ≤ Ebar ⊓ centralizer {tbar} :=
    zpowers_le.mpr ⟨sbar₂_mem_Ebar, sbar₂_mem_centralizer_tbar⟩
  refine (eq_of_le_of_card_ge hle ?_).symm
  rw [Nat.card_zpowers, orderOf_sbar₂]
  have h1 : Nat.card (Ebar ⊓ centralizer {tbar} : Subgroup _) ∣ 27 :=
    card_Ebar ▸ card_dvd_of_le inf_le_left
  have h2 : Nat.card (Ebar ⊓ centralizer {tbar} : Subgroup _) ∣ 192 :=
    card_centralizer_tbar ▸ card_dvd_of_le inf_le_right
  have := Nat.dvd_gcd h1 h2
  norm_num at this
  exact Nat.le_of_dvd (by norm_num) this

theorem tbar_mem_centralizer_sbar₂ : tbar ∈ centralizer {sbar₂} :=
  mem_centralizer_singleton_iff.mpr (Subtype.ext (by decide))

theorem centralizer_sbar₂_eq : centralizer {sbar₂} = Ebar ⊔ zpowers tbar := by
  have hle : Ebar ⊔ zpowers tbar ≤ centralizer {sbar₂} :=
    sup_le Ebar_le_centralizer_sbar₂ (zpowers_le.mpr tbar_mem_centralizer_sbar₂)
  refine (eq_of_le_of_card_ge hle ?_).symm
  rw [card_centralizer_sbar₂]
  have h27 : 27 ∣ Nat.card (Ebar ⊔ zpowers tbar : Subgroup _) :=
    card_Ebar ▸ card_dvd_of_le le_sup_left
  have h2 : 2 ∣ Nat.card (Ebar ⊔ zpowers tbar : Subgroup _) := by
    have := card_dvd_of_le (le_sup_right : zpowers tbar ≤ Ebar ⊔ zpowers tbar)
    rwa [Nat.card_zpowers, orderOf_tbar] at this
  exact Nat.le_of_dvd Nat.card_pos (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h27 h2)

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPTwoThree
