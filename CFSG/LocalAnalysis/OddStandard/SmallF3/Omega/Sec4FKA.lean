module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FBlocks
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FFour

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private lemma conj_mul_of_sq_one {G : Type*} [Group G] {y u v : G} (hyy : y * y = 1) :
    y * (u * v) * y = (y * u * y) * (y * v * y) := by
  rw [show (y * u * y) * (y * v * y) = y * u * (y * y) * v * y by group, hyy]
  group

private lemma conj_conj_of_sq_one {G : Type*} [Group G] {y u : G} (hyy : y * y = 1) :
    y * (y * u * y) * y = u := by
  rw [show y * (y * u * y) * y = (y * y) * u * (y * y) by group, hyy]
  group

private lemma conj_mul_self_of_sq_one {G : Type*} [Group G] {y κ κ' : G}
    (hyy : y * y = 1) (h : y * κ * y = κ') (hc : κ * κ' = κ' * κ) :
    y * (κ * κ') * y = κ * κ' := by
  have hyκ' : y * κ' * y = κ := by
    rw [← h]
    exact conj_conj_of_sq_one hyy
  rw [conj_mul_of_sq_one hyy, h, hyκ']
  exact hc.symm

private lemma conj_eq_mul_of_sq_one {G : Type*} [Group G] {y κ κ' : G}
    (hyy : y * y = 1) (h : y * κ * y = κ') (hκ' : κ' * κ' = 1) :
    y * (κ * κ') = κ'⁻¹ * y * κ' := by
  have hyκ : y * κ = κ' * y := by
    have h1 : y * κ * y * y = κ' * y := congrArg (fun z => z * y) h
    rwa [show y * κ * y * y = y * κ by
      rw [show y * κ * y * y = y * κ * (y * y) by group, hyy]
      group] at h1
  have hκ'inv : κ'⁻¹ = κ' := inv_eq_of_mul_eq_one_right hκ'
  calc y * (κ * κ') = (y * κ) * κ' := by group
    _ = (κ' * y) * κ' := by rw [hyκ]
    _ = κ'⁻¹ * y * κ' := by rw [hκ'inv]

private lemma mul_conj_conj_of_sq_one {G : Type*} [Group G] {y W : G} (hyy : y * y = 1)
    (h : y * W * y = W) : W * y = y * W := by
  have h2 : y * W = W * y := by
    calc y * W = y * W * (y * y) := by rw [hyy, mul_one]
      _ = (y * W * y) * y := by group
      _ = W * y := by rw [h]
  exact h2.symm

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B P : Subgroup G}
  {x : G} {φ : (Fin 7 → ZMod 2) → G}

theorem Sec4FSetup.K_moved (h : Sec4FSetup t L S z A B φ) (hT : Sec4FTwo A P x) {y : G}
    (hy : ∃ g : G, y = g⁻¹ * t * g)
    (h1 : ∀ a, ∃ e, y * sec4MPt t φ a * y = sec4FD t φ x e)
    (h2 : ∀ c, ∃ q, y * sec4FD t φ x c * y = sec4MPt t φ q)
    {a a' c c' : Option (Fin 7)} (hb : Sec4FBlock (sec4FR t φ x) a a' c c')
    (hmoved : y * (sec4MPt t φ a * sec4MPt t φ a') * y ≠ sec4MPt t φ a * sec4MPt t φ a') :
    False := by
  have hyy : y * y = 1 := by
    obtain ⟨g, rfl⟩ := hy
    calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [h.t_sq]; group
  have hκ : sec4MPt t φ a * sec4MPt t φ a' = sec4FD t φ x c * sec4FD t φ x c' :=
    h.block_kappa hT hb
  obtain ⟨e₁, he₁⟩ := h1 a
  obtain ⟨e₂, he₂⟩ := h1 a'
  have hene : e₁ ≠ e₂ := by
    intro heq
    have h12 : y * sec4MPt t φ a * y = y * sec4MPt t φ a' * y := by
      rw [he₁, he₂, heq]
    exact hb.1 (h.pt_injective (mul_left_cancel (mul_right_cancel h12)))
  have hκ' : y * (sec4MPt t φ a * sec4MPt t φ a') * y =
      sec4FD t φ x e₁ * sec4FD t φ x e₂ := by
    rw [← he₁, ← he₂, conj_mul_of_sq_one hyy]
  obtain ⟨q₁, hq₁⟩ := h2 c
  obtain ⟨q₂, hq₂⟩ := h2 c'
  have hqne : q₁ ≠ q₂ := by
    intro hq
    have h12 : y * sec4FD t φ x c * y = y * sec4FD t φ x c' * y := by
      rw [hq₁, hq₂, hq]
    exact hb.2.1 (h.d_inj (mul_left_cancel (mul_right_cancel h12)))
  have hκ'' : y * (sec4FD t φ x c * sec4FD t φ x c') * y =
      sec4MPt t φ q₁ * sec4MPt t φ q₂ := by
    rw [← hq₁, ← hq₂, conj_mul_of_sq_one hyy]
  have hprod : sec4MPt t φ q₁ * sec4MPt t φ q₂ = sec4FD t φ x e₁ * sec4FD t φ x e₂ := by
    rw [← hκ'', ← hκ]
    exact hκ'
  set κ := sec4MPt t φ a * sec4MPt t φ a' with hκdef
  set κ' := sec4MPt t φ q₁ * sec4MPt t φ q₂ with hκ'def
  have hprod' : sec4MPt t φ q₁ * sec4MPt t φ q₂ = sec4FD t φ x e₁ * sec4FD t φ x e₂ := by
    rw [← hκ'def]
    exact hprod
  have hnb : ∀ e, sec4FR t φ x q₁ e ↔ sec4FR t φ x q₂ e :=
    h.kappa_nbr hT hqne hene hprod'
  have hne_of_q1 : q₁ = a ∨ q₁ = a' → False := by
    intro hq
    have hq2 : q₂ = a ∨ q₂ = a' :=
      sec4F_block_pair hb hq (fun hh => hqne hh.symm) hnb
    have hkp : κ' = κ := by
      rw [hκ'def, hκdef]
      rcases hq with h1 | h1 <;> rcases hq2 with h2 | h2
      · exact absurd (h1.trans h2.symm) hqne
      · rw [h1, h2]
      · rw [h1, h2]
        exact h.A_comm (sec4MPt_mem_A h.data a') (sec4MPt_mem_A h.data a)
      · exact absurd (h1.trans h2.symm) hqne
    apply hmoved
    calc y * κ * y = y * (sec4FD t φ x c * sec4FD t φ x c') * y := by rw [hκ]
      _ = κ' := hκ''
      _ = κ := hkp
  have hq1a : q₁ ≠ a ∧ q₁ ≠ a' :=
    ⟨fun hq => hne_of_q1 (Or.inl hq), fun hq => hne_of_q1 (Or.inr hq)⟩
  have hq2a : q₂ ≠ a ∧ q₂ ≠ a' := by
    constructor
    · intro hq
      exact hne_of_q1 (sec4F_block_pair hb (Or.inl hq) hqne (fun e => (hnb e).symm))
    · intro hq
      exact hne_of_q1 (sec4F_block_pair hb (Or.inr hq) hqne (fun e => (hnb e).symm))
  obtain ⟨k, hk⟩ := (h.four_pts hb.1 (fun hh => hq1a.1 hh.symm)
    (fun hh => hq2a.1 hh.symm) (fun hh => hq1a.2 hh.symm) (fun hh => hq2a.2 hh.symm) hqne).1
  have hκmem : κ ∈ A := by
    rw [hκdef]
    exact mul_mem (sec4MPt_mem_A h.data a) (sec4MPt_mem_A h.data a')
  have hκ'mem : κ' ∈ A := by
    rw [hκ'def]
    exact mul_mem (sec4MPt_mem_A h.data q₁) (sec4MPt_mem_A h.data q₂)
  have hκ'sq : κ' * κ' = 1 := h.A_sq hκ'mem
  have hκcomm : κ * κ' = κ' * κ := h.A_comm hκmem hκ'mem
  have hyκ : y * κ * y = κ' := hκ'.trans hprod.symm
  have hfixed : y * (κ * κ') * y = κ * κ' := conj_mul_self_of_sq_one hyy hyκ hκcomm
  have hwy : κ * κ' ∈ centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_conj_conj_of_sq_one hyy hfixed
  have hconj : y * (κ * κ') = κ'⁻¹ * y * κ' := conj_eq_mul_of_sq_one hyy hyκ hκ'sq
  have hyw : ∃ g : G, y * (κ * κ') = g⁻¹ * t * g := by
    obtain ⟨g, hg⟩ := hy
    refine ⟨g * κ', ?_⟩
    rw [hconj, hg]
    group
  have hk' : κ * κ' = k⁻¹ * z * k := by
    rw [hκdef, hκ'def]
    exact hk
  exact sec4_lemmaZ h.inputs.h43 h.ctx h.not_tz hy ⟨k, hk'⟩ hwy hyw

end CFSG.OddStandard.SmallF3.Omega
