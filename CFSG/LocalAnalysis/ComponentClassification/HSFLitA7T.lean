module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Skeleton
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitProd

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer DihedralGroup
open scoped Pointwise

namespace A7Base

variable {X : Type} [Group X] [Finite X] (S : A7Base X)

theorem z_mem : S.z ∈ S.data.R := pow_mem S.x_mem 2

theorem ψ_z : S.data.ψ ⟨S.z, S.z_mem.1⟩ = a0 ^ 2 := by
  have : (⟨S.z, S.z_mem.1⟩ : S.data.T) = (⟨S.x, S.x_mem.1⟩ : S.data.T) ^ 2 := rfl
  rw [this, map_pow, S.ψ_x]
  decide

theorem eq_of_ψ_eq' {a b : X} (ha : a ∈ S.data.R) (hb : b ∈ S.data.R) {σ : Perm (Fin 7)}
    (h₁ : S.data.ψ ⟨a, ha.1⟩ = σ) (h₂ : S.data.ψ ⟨b, hb.1⟩ = σ) : a = b :=
  S.data.eq_of_ψ_eq ha hb (h₁.trans h₂.symm)

theorem x_pow_four : S.x ^ 4 = 1 := by
  refine S.eq_of_ψ_eq' (pow_mem S.x_mem 4) (one_mem _) (σ := 1) ?_ (map_one _)
  have : (⟨S.x ^ 4, (pow_mem S.x_mem 4).1⟩ : S.data.T) = (⟨S.x, S.x_mem.1⟩ : S.data.T) ^ 4 :=
    rfl
  rw [this, map_pow, S.ψ_x]
  decide

theorem z_ne_one : S.z ≠ 1 := by
  intro h
  have h1 := S.ψ_z
  have : (⟨S.z, S.z_mem.1⟩ : S.data.T) = 1 := Subtype.ext h
  rw [this, map_one] at h1
  exact absurd h1 (by decide)

theorem y_sq : S.y ^ 2 = 1 := S.data.sq_eq_one_of_mem_R S.y_mem (by rw [S.ψ_y]; decide)

theorem y_mul_y : S.y * S.y = 1 := by rw [← pow_two, S.y_sq]

theorem y_x_y : S.y * S.x * S.y⁻¹ = S.x⁻¹ := by
  have hm : S.y * S.x * S.y⁻¹ ∈ S.data.R :=
    mul_mem (mul_mem S.y_mem S.x_mem) (inv_mem S.y_mem)
  refine S.eq_of_ψ_eq' hm (inv_mem S.x_mem) (σ := rho0⁻¹) ?_ ?_
  · have : (⟨S.y * S.x * S.y⁻¹, hm.1⟩ : S.data.T) =
        ⟨S.y, S.y_mem.1⟩ * ⟨S.x, S.x_mem.1⟩ * (⟨S.y, S.y_mem.1⟩)⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, S.ψ_x, S.ψ_y]
    decide
  · have : (⟨S.x⁻¹, (inv_mem S.x_mem).1⟩ : S.data.T) = (⟨S.x, S.x_mem.1⟩)⁻¹ := rfl
    rw [this, map_inv, S.ψ_x]

theorem orderOf_x : orderOf S.x = 4 := by
  apply orderOf_eq_prime_pow (p := 2) (n := 1)
  · rw [pow_one]
    exact S.z_ne_one
  · exact S.x_pow_four

theorem y_not_mem_zpowers_x : S.y ∉ zpowers S.x := by
  classical
  intro h
  rw [mem_zpowers_iff_mem_range_orderOf, S.orderOf_x] at h
  obtain ⟨i, hi, hiy⟩ := Finset.mem_image.mp h
  have hi4 : i < 4 := Finset.mem_range.mp hi
  have hm : S.x ^ i ∈ S.data.R := pow_mem S.x_mem i
  have h1 : S.data.ψ ⟨S.x ^ i, hm.1⟩ = rho0 ^ i := by
    have : (⟨S.x ^ i, hm.1⟩ : S.data.T) = (⟨S.x, S.x_mem.1⟩ : S.data.T) ^ i := rfl
    rw [this, map_pow, S.ψ_x]
  have h2 := S.ψ_y
  simp only [← hiy] at h2
  rw [h1] at h2
  revert h2
  interval_cases i <;> decide

theorem ψ_t : S.data.ψ ⟨S.t, S.data.t_mem_T⟩ = 1 :=
  (S.data.mem_K_iff S.data.t_mem_T).mp S.data.t_mem_K

theorem k_comm {r : X} (hr : r ∈ S.data.R) : S.k * r = r * S.k :=
  S.data.commute_of_ψ_eq_c0 S.k_mem S.ψ_k hr

theorem k_not_mem_R : S.k ∉ S.data.R := fun h => c0_not_mem_R0 (S.ψ_k ▸ S.data.ψ_mem_R0 h)

theorem t_ne_one : S.t ≠ 1 := by
  intro h
  have := S.data.orderOf_t
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem k_ne_one : S.k ≠ 1 := by
  intro h
  have h1 := S.ψ_k
  have : (⟨S.k, S.k_mem⟩ : S.data.T) = 1 := Subtype.ext h
  rw [this, map_one] at h1
  exact absurd h1 (by decide)

theorem k_ne_t : S.k ≠ S.t := by
  intro h
  have h1 := S.ψ_k
  have : (⟨S.k, S.k_mem⟩ : S.data.T) = ⟨S.t, S.data.t_mem_T⟩ := Subtype.ext h
  rw [this, S.ψ_t] at h1
  exact absurd h1 (by decide)

theorem t_sq : S.t ^ 2 = 1 := by rw [← S.data.orderOf_t, pow_orderOf_eq_one]

theorem k_t_k : S.k * S.t * S.k⁻¹ = S.t⁻¹ := by
  rw [S.data.commute_t S.k_mem, mul_inv_cancel_right, eq_inv_iff_mul_eq_one, ← pow_two, S.t_sq]

theorem exists_equiv_R : ∃ eR : S.data.R ≃* DihedralGroup 4,
    eR ⟨S.x, S.x_mem⟩ = r 1 ∧ eR ⟨S.y, S.y_mem⟩ = sr 0 := by
  set f := dihedralLift 4 S.x S.y S.x_pow_four S.y_mul_y S.y_x_y with hf
  have hinj : Function.Injective f :=
    injective_dihedralLift 4 _ _ _ _ _ S.orderOf_x S.y_not_mem_zpowers_x
  have hrange : f.range = S.data.R := by
    rw [hf, range_dihedralLift]
    refine Subgroup.eq_of_le_of_card_ge (sup_le (zpowers_le.mpr S.x_mem)
      (zpowers_le.mpr S.y_mem)) ?_
    rw [S.data.card_R, ← range_dihedralLift 4 S.x S.y S.x_pow_four S.y_mul_y S.y_x_y,
      ← hf, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, DihedralGroup.nat_card]
  set e : DihedralGroup 4 ≃* S.data.R :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  refine ⟨e.symm, ?_, ?_⟩
  · rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    change S.x = f (r 1)
    rw [hf, dihedralLift_r]
    exact (pow_one S.x).symm
  · rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    change S.y = f (sr 0)
    rw [hf, dihedralLift_sr, ZMod.val_zero, pow_zero, mul_one]

theorem exists_equiv_tk : ∃ eK : (zpowers S.t ⊔ zpowers S.k : Subgroup X) ≃* DihedralGroup 2,
    eK ⟨S.t, mem_sup_left (mem_zpowers _)⟩ = r 1 ∧
      eK ⟨S.k, mem_sup_right (mem_zpowers _)⟩ = sr 0 := by
  have ht2 : S.t ^ 2 = 1 := S.t_sq
  have hk2 : S.k * S.k = 1 := by rw [← pow_two, S.k_sq]
  have hot : orderOf S.t = 2 := S.data.orderOf_t
  have hkt : S.k ∉ zpowers S.t := by
    intro h
    rcases eq_one_or_eq_of_mem_zpowers ht2 h with h1 | h1
    · exact S.k_ne_one h1
    · exact S.k_ne_t h1
  set f := dihedralLift 2 S.t S.k ht2 hk2 S.k_t_k with hf
  have hinj : Function.Injective f := injective_dihedralLift 2 _ _ _ _ _ hot hkt
  have hrange : f.range = zpowers S.t ⊔ zpowers S.k := range_dihedralLift 2 _ _ _ _ _
  set e : DihedralGroup 2 ≃* (zpowers S.t ⊔ zpowers S.k : Subgroup X) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  refine ⟨e.symm, ?_, ?_⟩
  · rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    change S.t = f (r 1)
    rw [hf, dihedralLift_r]
    exact (pow_one S.t).symm
  · rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    change S.k = f (sr 0)
    rw [hf, dihedralLift_sr, ZMod.val_zero, pow_zero, mul_one]

theorem tk_le_T : (zpowers S.t ⊔ zpowers S.k : Subgroup X) ≤ S.data.T :=
  sup_le (zpowers_le.mpr S.data.t_mem_T) (zpowers_le.mpr S.k_mem)

theorem card_T : Nat.card S.data.T = 32 := by
  rw [S.data.card_T_eq, S.data.card_range_of_ψ_eq_c0 S.k_mem S.ψ_k, S.card_K]

theorem R_inf_tk : S.data.R ⊓ (zpowers S.t ⊔ zpowers S.k : Subgroup X) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hgR, hgK⟩ := mem_inf.mp hg
  rw [mem_bot]
  have hN : zpowers S.k ≤ normalizer (zpowers S.t : Set X) := by
    rw [zpowers_le]
    refine centralizer_le_normalizer _ ?_
    rw [mem_centralizer_iff]
    intro a ha
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp ha
    exact ((Commute.zpow_left (S.data.commute_t S.k_mem).symm n)).eq
  have hg' : g ∈ (zpowers S.t : Set X) * (zpowers S.k : Set X) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hN]
    exact hgK
  obtain ⟨a, ha, b, hb, rfl⟩ := hg'
  have hk2 : S.k ^ 2 = 1 := S.k_sq
  rcases eq_one_or_eq_of_mem_zpowers S.t_sq ha with rfl | rfl <;>
    rcases eq_one_or_eq_of_mem_zpowers hk2 hb with rfl | rfl
  · exact mul_one 1
  · exact absurd (by simpa using hgR) S.k_not_mem_R
  · exact absurd (by simpa using hgR.2) S.data.t_not_mem_L
  · exfalso
    have hm : S.t * S.k ∈ S.data.T := mul_mem S.data.t_mem_T S.k_mem
    have h1 : S.data.ψ ⟨S.t * S.k, hm⟩ = c0 := by
      have : (⟨S.t * S.k, hm⟩ : S.data.T) = ⟨S.t, S.data.t_mem_T⟩ * ⟨S.k, S.k_mem⟩ := rfl
      rw [this, map_mul, S.ψ_t, S.ψ_k, one_mul]
    exact c0_not_mem_R0 (h1 ▸ S.data.ψ_mem_R0 hgR)

theorem R_comm_tk {r : X} (hr : r ∈ S.data.R) {b : X}
    (hb : b ∈ (zpowers S.t ⊔ zpowers S.k : Subgroup X)) : r * b = b * r := by
  have hle : (zpowers S.t ⊔ zpowers S.k : Subgroup X) ≤ centralizer ({r} : Set X) := by
    refine sup_le ?_ ?_ <;> rw [zpowers_le, mem_centralizer_singleton_iff]
    · exact (S.data.commute_t hr.1).symm
    · exact S.k_comm hr
  exact (mem_centralizer_singleton_iff.mp (hle hb)).symm

theorem exists_coords : ∃ φ : S.data.T ≃* DihedralGroup 4 × DihedralGroup 2,
    φ ⟨S.x, S.x_mem.1⟩ = (r 1, 1) ∧ φ ⟨S.y, S.y_mem.1⟩ = (sr 0, 1) ∧
      φ ⟨S.t, S.data.t_mem_T⟩ = (1, r 1) ∧ φ ⟨S.k, S.k_mem⟩ = (1, sr 0) := by
  obtain ⟨eR, heRx, heRy⟩ := S.exists_equiv_R
  obtain ⟨eK, heKt, heKk⟩ := S.exists_equiv_tk
  have hRT : S.data.R ≤ S.data.T := inf_le_left
  obtain ⟨φ, hφA, hφB⟩ := exists_mulEquiv_prod (G := S.data.T)
    (A := S.data.R.subgroupOf S.data.T)
    (B := (zpowers S.t ⊔ zpowers S.k : Subgroup X).subgroupOf S.data.T)
    (by
      rw [eq_bot_iff]
      intro g hg
      rw [mem_bot]
      have h1 : (g : X) ∈ S.data.R ⊓ (zpowers S.t ⊔ zpowers S.k : Subgroup X) :=
        ⟨(mem_inf.mp hg).1, (mem_inf.mp hg).2⟩
      rw [S.R_inf_tk, mem_bot] at h1
      exact Subtype.ext h1)
    (fun a ha b hb => Subtype.ext (S.R_comm_tk ha hb))
    (by
      rw [Nat.card_congr (subgroupOfEquivOfLe hRT).toEquiv,
        Nat.card_congr (subgroupOfEquivOfLe S.tk_le_T).toEquiv, S.data.card_R,
        Nat.card_congr eK.toEquiv, DihedralGroup.nat_card, S.card_T])
    ((subgroupOfEquivOfLe hRT).trans eR) ((subgroupOfEquivOfLe S.tk_le_T).trans eK)
  refine ⟨φ, ?_, ?_, ?_, ?_⟩
  · rw [show (⟨S.x, S.x_mem.1⟩ : S.data.T) = ((⟨⟨S.x, S.x_mem.1⟩, S.x_mem⟩ :
      S.data.R.subgroupOf S.data.T) : S.data.T) from rfl, hφA]
    simp only [MulEquiv.trans_apply]
    rw [← heRx]
    rfl
  · rw [show (⟨S.y, S.y_mem.1⟩ : S.data.T) = ((⟨⟨S.y, S.y_mem.1⟩, S.y_mem⟩ :
      S.data.R.subgroupOf S.data.T) : S.data.T) from rfl, hφA]
    simp only [MulEquiv.trans_apply]
    rw [← heRy]
    rfl
  · rw [show (⟨S.t, S.data.t_mem_T⟩ : S.data.T) = ((⟨⟨S.t, S.data.t_mem_T⟩,
      mem_sup_left (mem_zpowers _)⟩ : (zpowers S.t ⊔ zpowers S.k : Subgroup X).subgroupOf
        S.data.T) : S.data.T) from rfl, hφB]
    simp only [MulEquiv.trans_apply]
    rw [← heKt]
    rfl
  · rw [show (⟨S.k, S.k_mem⟩ : S.data.T) = ((⟨⟨S.k, S.k_mem⟩,
      mem_sup_right (mem_zpowers _)⟩ : (zpowers S.t ⊔ zpowers S.k : Subgroup X).subgroupOf
        S.data.T) : S.data.T) from rfl, hφB]
    simp only [MulEquiv.trans_apply]
    rw [← heKk]
    rfl

end A7Base

end CFSG.ComponentClassification.HSFLit
