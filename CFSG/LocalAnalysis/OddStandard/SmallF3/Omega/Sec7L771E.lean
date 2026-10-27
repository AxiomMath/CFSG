module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L771Act

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private def sec7l771_ind (p₀ : Fin 5) : Fin 5 → ZMod 2 := fun i => if i = p₀ then 0 else 1

private theorem sec7l771_ind_even (p₀ : Fin 5) : IsEvenVec (sec7l771_ind p₀) := by
  unfold IsEvenVec
  fin_cases p₀ <;> decide +kernel

private theorem sec7l771_ind_perm {p₀ : Fin 5} {σ : Equiv.Perm (Fin 5)} (hσ : σ p₀ = p₀) :
    permVec σ (sec7l771_ind p₀) = sec7l771_ind p₀ := by
  funext i
  have hiff : σ.symm i = p₀ ↔ i = p₀ := by rw [Equiv.symm_apply_eq, hσ]
  simp only [permVec, Function.comp_apply, sec7l771_ind]
  by_cases h : σ.symm i = p₀
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]

private theorem sec7l771_ind_fix {p₀ : Fin 5} {σ : Equiv.Perm (Fin 5)}
    (hσ : permVec σ (sec7l771_ind p₀) = sec7l771_ind p₀) : σ p₀ = p₀ := by
  have h := congrFun hσ (σ p₀)
  simp only [permVec, Function.comp_apply, Equiv.symm_apply_apply] at h
  by_contra hp
  have h0 : sec7l771_ind p₀ p₀ = 0 := by simp [sec7l771_ind]
  have h1 : sec7l771_ind p₀ (σ p₀) = 1 := by simp [sec7l771_ind, hp]
  rw [h0, h1] at h
  exact zero_ne_one h

private theorem sec7l771_perm_W {p₀ : Fin 5} {σ : Equiv.Perm (Fin 5)} (hσ : σ p₀ = p₀)
    {v : Fin 5 → ZMod 2} (hv : IsEvenVec v) (hv0 : v p₀ = 0) :
    IsEvenVec (permVec σ v) ∧ permVec σ v p₀ = 0 := by
  have hsym : σ.symm p₀ = p₀ := by rw [Equiv.symm_apply_eq, hσ]
  refine ⟨sec7l77_even_permVec σ hv, ?_⟩
  simp only [permVec, Function.comp_apply, hsym, hv0]

private theorem sec7l771_even_add {v w : Fin 5 → ZMod 2} (hv : IsEvenVec v) (hw : IsEvenVec w) :
    IsEvenVec (v + w) := by
  unfold IsEvenVec at hv hw ⊢
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  rw [hv, hw, add_zero]

variable {N B : Subgroup G} {φ : (Fin 5 → ZMod 2) → G}

private def sec7l771_E (h : Sec7E16Act N B φ) (p₀ : Fin 5) : Subgroup G where
  carrier := {x | ∃ v, IsEvenVec v ∧ v p₀ = 0 ∧ φ v = x}
  one_mem' := ⟨0, by simp [IsEvenVec], rfl, h.phi_zero⟩
  mul_mem' := by
    rintro x y ⟨v, hv, hv0, hx⟩ ⟨w, hw, hw0, hy⟩
    rw [← hx, ← hy]
    exact ⟨v + w, sec7l771_even_add hv hw, by simp [Pi.add_apply, hv0, hw0], h.add hv hw⟩
  inv_mem' := by
    rintro x ⟨v, hv, hv0, hx⟩
    rw [← hx]
    refine ⟨v, hv, hv0, ?_⟩
    have h2 : (φ v) ^ 2 = 1 := h.elem.1.2 (φ v) (h.phi_mem hv)
    rw [pow_two] at h2
    exact (inv_eq_of_mul_eq_one_right h2).symm

private theorem sec7l771_E_le (h : Sec7E16Act N B φ) (p₀ : Fin 5) : sec7l771_E h p₀ ≤ B := by
  rintro x ⟨v, hv, -, hx⟩
  rw [← hx]
  exact h.phi_mem hv

private theorem sec7l771_E_elem [Finite G] (h : Sec7E16Act N B φ) (p₀ : Fin 5) :
    IsElemAb2 (sec7l771_E h p₀) 3 := by
  have hle := sec7l771_E_le h p₀
  have hB := h.elem.1
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine isMulCommutative_iff.mpr fun a b => Subtype.ext ?_
    exact congrArg (fun z : ↥B => z.1)
      (hB.1.is_comm.comm ⟨(a : G), hle a.2⟩ ⟨(b : G), hle b.2⟩)
  · intro x hx
    exact hB.2 x (hle hx)
  · have hcard : Nat.card ↥(sec7l771_E h p₀) =
        Nat.card {v : Fin 5 → ZMod 2 // IsEvenVec v ∧ v p₀ = 0} :=
      Nat.card_congr
        { toFun := fun x => ⟨Classical.choose x.2, (Classical.choose_spec x.2).1,
            (Classical.choose_spec x.2).2.1⟩
          invFun := fun v => ⟨φ v.1, ⟨v.1, v.2.1, v.2.2, rfl⟩⟩
          left_inv := fun x => by
            apply Subtype.ext
            exact (Classical.choose_spec x.2).2.2
          right_inv := fun v => by
            have hspec := Classical.choose_spec (show ∃ u, IsEvenVec u ∧ u p₀ = 0 ∧
              φ u = φ v.1 from ⟨v.1, v.2.1, v.2.2, rfl⟩)
            exact Subtype.ext (h.inj hspec.1 v.2.1 hspec.2.2) }
    rw [hcard, sec7l771_card_W p₀]
    norm_num

private theorem sec7l771_E_normalizes (h : Sec7E16Act N B φ) (p₀ : Fin 5) {x : G} (hx : x ∈ N)
    {σ : Equiv.Perm (Fin 5)} (hσ : ∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec σ v))
    (hp : σ p₀ = p₀) : x ∈ normalizer (sec7l771_E h p₀ : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  have hσ' : ∀ v, IsEvenVec v → x⁻¹ * φ v * x = φ (permVec σ⁻¹ v) := by
    intro v hv
    have h1 := hσ (permVec σ⁻¹ v) (sec7l77_even_permVec σ⁻¹ hv)
    rw [sec7l77_permVec_mul, mul_inv_cancel, sec7l77_permVec_one] at h1
    calc x⁻¹ * φ v * x = x⁻¹ * (x * φ (permVec σ⁻¹ v) * x⁻¹) * x := by rw [h1]
      _ = φ (permVec σ⁻¹ v) := by group
  constructor
  · rintro ⟨v, hv, hv0, hvφ⟩
    rw [← hvφ]
    exact ⟨permVec σ v, (sec7l771_perm_W hp hv hv0).1,
      (sec7l771_perm_W hp hv hv0).2, (hσ v hv).symm⟩
  · rintro ⟨v, hv, hv0, hvφ⟩
    have hsym : (σ⁻¹).symm p₀ = p₀ := by
      show σ p₀ = p₀
      exact hp
    refine ⟨permVec σ⁻¹ v, sec7l77_even_permVec σ⁻¹ hv,
      by simpa [permVec, hsym] using hv0, ?_⟩
    rw [← hσ' v hv, hvφ]
    group

private theorem sec7l771_cent_z_act (h : Sec7E16Act N B φ) {p₀ : Fin 5} {x : G} (hx : x ∈ N)
    (hxz : x * φ (sec7l771_ind p₀) = φ (sec7l771_ind p₀) * x) :
    ∃ σ : Equiv.Perm (Fin 5), (∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec σ v)) ∧
      σ p₀ = p₀ := by
  refine ⟨h.rho ⟨x, hx⟩, fun v hv => h.rho_spec ⟨x, hx⟩ hv, ?_⟩
  apply sec7l771_ind_fix
  apply h.inj (sec7l77_even_permVec _ (sec7l771_ind_even p₀)) (sec7l771_ind_even p₀)
  rw [← h.rho_spec ⟨x, hx⟩ (sec7l771_ind_even p₀), hxz]
  group

private theorem sec7l771_comm_z (h : Sec7E16Act N B φ) {p₀ : Fin 5} {x : G}
    {σ : Equiv.Perm (Fin 5)} (hσ : ∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec σ v))
    (hp : σ p₀ = p₀) : x * φ (sec7l771_ind p₀) = φ (sec7l771_ind p₀) * x := by
  have h1 : x * φ (sec7l771_ind p₀) * x⁻¹ = φ (sec7l771_ind p₀) := by
    rw [hσ _ (sec7l771_ind_even p₀), sec7l771_ind_perm hp]
  calc x * φ (sec7l771_ind p₀) = (x * φ (sec7l771_ind p₀) * x⁻¹) * x := by group
    _ = φ (sec7l771_ind p₀) * x := by rw [h1]

private theorem sec7l771_comm_form (h : Sec7E16Act N B φ) {u : Fin 5 → ZMod 2} (hu : IsEvenVec u)
    {ν : G} {σ : Equiv.Perm (Fin 5)} (hσ : ∀ v, IsEvenVec v → ν * φ v * ν⁻¹ = φ (permVec σ v)) :
    φ (u + permVec σ u) = φ u * (ν * (φ u)⁻¹ * ν⁻¹) := by
  have hmem : φ u ∈ B := h.phi_mem hu
  have hinv : (φ u)⁻¹ = φ u := by
    have h2 : (φ u) ^ 2 = 1 := h.elem.1.2 (φ u) hmem
    rw [pow_two] at h2
    exact inv_eq_of_mul_eq_one_right h2
  rw [h.add hu (sec7l77_even_permVec σ hu), hinv, ← hσ u hu]

theorem sec7l771_E_exists [Finite G] {P : Subgroup G} (h : Sec7E16Act N B φ)
    (hP : IsSylow2Of P N) {z : G} (hz : z ∈ B) (hz1 : z ≠ 1)
    (hPz : ∀ x ∈ P, x * z = z * x) :
    ∃ E : Subgroup G, E ≤ B ∧ IsElemAb2 E 3 ∧ z ∈ E ∧ P ≤ normalizer (E : Set G) ∧
      (∀ e ∈ E, ∃ b₁ ∈ B, ∃ b₂ ∈ B, ∃ ν₁ ∈ N, ∃ ν₂ ∈ N, ν₁ ^ 3 = 1 ∧ ν₂ ^ 3 = 1 ∧
        ν₁ * z = z * ν₁ ∧ ν₂ * z = z * ν₂ ∧
        e = (b₁ * (ν₁ * b₁⁻¹ * ν₁⁻¹)) * (b₂ * (ν₂ * b₂⁻¹ * ν₂⁻¹))) ∧
      ∃ ν ∈ N, ν ^ 3 = 1 ∧ ν ≠ 1 ∧ ν * z = z * ν ∧ ν ∈ normalizer (E : Set G) ∧
        ∀ e ∈ E, ν * e = e * ν → e = 1 ∨ e = z := by
  obtain ⟨⟨w, hw_even, hw_wt, hwz⟩, -⟩ := sec7l771_centralB h hP hz hz1 hPz
  obtain ⟨p₀, hp₀⟩ := sec7l771_weight4 hw_wt
  have hw_eq : w = sec7l771_ind p₀ := by
    funext i
    rw [hp₀ i]
    rfl
  have hzφ : φ (sec7l771_ind p₀) = z := by rw [← hw_eq, hwz]
  obtain ⟨σ₀, hσ₀p, hσ₀3, hσ₀ne, hσ₀fix⟩ := sec7l771_exists_cycle p₀
  obtain ⟨ν₀, hν₀N, hν₀3, hν₀act⟩ := h.exists_lift3 hσ₀3
  refine ⟨sec7l771_E h p₀, sec7l771_E_le h p₀, sec7l771_E_elem h p₀,
    ⟨sec7l771_ind p₀, sec7l771_ind_even p₀, by simp [sec7l771_ind], hzφ⟩, ?_, ?_, ?_⟩
  · intro x hx
    have hxN : x ∈ N := hP.1 hx
    have hxz : x * φ (sec7l771_ind p₀) = φ (sec7l771_ind p₀) * x := by
      rw [hzφ]
      exact hPz x hx
    obtain ⟨σ, hσ, hpσ⟩ := sec7l771_cent_z_act h hxN hxz
    exact sec7l771_E_normalizes h p₀ hxN hσ hpσ
  · rintro e ⟨v, hv, hv0, he⟩
    rw [← he]
    obtain ⟨u₁, u₂, σ₁, σ₂, hu₁, hu₂, hσ₁p, hσ₂p, hσ₁3, hσ₂3, hvsum⟩ :=
      sec7l771_W_gen p₀ hv hv0
    obtain ⟨ν₁, hν₁N, hν₁3, hν₁act⟩ := h.exists_lift3 hσ₁3
    obtain ⟨ν₂, hν₂N, hν₂3, hν₂act⟩ := h.exists_lift3 hσ₂3
    refine ⟨φ u₁, h.phi_mem hu₁, φ u₂, h.phi_mem hu₂, ν₁, hν₁N, ν₂, hν₂N,
      hν₁3, hν₂3, ?_, ?_, ?_⟩
    · rw [← hzφ]
      exact sec7l771_comm_z h hν₁act hσ₁p
    · rw [← hzφ]
      exact sec7l771_comm_z h hν₂act hσ₂p
    · rw [hvsum,
        h.add (sec7l771_even_add hu₁ (sec7l77_even_permVec σ₁ hu₁))
          (sec7l771_even_add hu₂ (sec7l77_even_permVec σ₂ hu₂)),
        sec7l771_comm_form h hu₁ hν₁act, sec7l771_comm_form h hu₂ hν₂act]
  · refine ⟨ν₀, hν₀N, hν₀3, ?_, ?_, ?_, ?_⟩
    · intro h1
      apply hσ₀ne
      refine sec7l77_perm_triv σ₀ fun v hv => ?_
      have hact := hν₀act v hv
      rw [h1] at hact
      simp only [one_mul, inv_one, mul_one] at hact
      exact (h.inj hv (sec7l77_even_permVec σ₀ hv) hact).symm
    · rw [← hzφ]
      exact sec7l771_comm_z h hν₀act hσ₀p
    · exact sec7l771_E_normalizes h p₀ hν₀N hν₀act hσ₀p
    · rintro e ⟨v, hv, hv0, he⟩ hec
      rw [← he] at hec ⊢
      have hfix : permVec σ₀ v = v := by
        refine h.inj (sec7l77_even_permVec σ₀ hv) hv ?_
        rw [← hν₀act v hv, hec]
        group
      rcases hσ₀fix v hv hv0 hfix with h0 | hind
      · left
        rw [h0, h.phi_zero]
      · right
        have hind' : v = sec7l771_ind p₀ := hind
        rw [hind', hzφ]

end CFSG.OddStandard.SmallF3.Omega
