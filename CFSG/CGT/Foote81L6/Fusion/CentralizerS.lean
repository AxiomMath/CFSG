module

public import CFSG.CGT.Foote81L6.Fusion.Squares

public section

namespace CFSG.CGT.Foote81L6

open Subgroup DihedralGroup

@[expose] def dihedralFourMap (A₁ A₂ : DihedralGroup 4) : DihedralGroup 4 → DihedralGroup 4
  | r i => A₁ ^ i.val
  | sr i => A₂ * A₁ ^ i.val

theorem exists_sq_eq_r_two_dihedral : ∀ A₁ A₂ c : DihedralGroup 4,
    (∀ x, dihedralFourMap A₁ A₂ (dihedralFourMap A₁ A₂ x) = c * x * c⁻¹) →
      dihedralFourMap A₁ A₂ c = c → (∀ x, x * dihedralFourMap A₁ A₂ x * c ≠ 1) →
        ∃ x, (x * dihedralFourMap A₁ A₂ x * c) ^ 2 = r 2 := by
  decide

theorem comm_eq_one_or_r_two_dihedral :
    ∀ x y : DihedralGroup 4, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = r 2 := by
  decide

namespace FooteCore

variable {G : Type*} [Group G] {T : Subgroup G} {m n : ℕ} (D : FooteCore G T m n)

theorem not_mul_self_eq_one_of_comm_s {v : G} (hvT : v ∈ T) (hv0 : v ∉ D.T₀)
    (hvs : v * D.s = D.s * v) : v * v ≠ 1 := by
  intro hv2
  have hw : v * D.t ∈ D.T₀ := (D.mem_T_iff.1 hvT).resolve_left hv0
  have hvw : v = v * D.t * D.t := by rw [mul_assoc, D.t_mul_t, mul_one]
  rcases D.mem_T₁_or_mul_s_mem_T₁ hw with h1 | h1
  ·
    have hc := D.conj_t_mem_T₁ (D.B_le_T₀ D.s_mem_B)
    apply D.no_involution_T₁st (mul_mem h1 hc)
    have e : v * D.t * (D.t * D.s * D.t⁻¹ * D.s⁻¹) * D.s * D.t = v * D.s := by
      rw [D.t_inv]
      calc v * D.t * (D.t * D.s * D.t * D.s⁻¹) * D.s * D.t
          = v * (D.t * D.t) * D.s * (D.s⁻¹ * D.s) * (D.t * D.t) := by group
        _ = v * D.s := by rw [D.t_mul_t, inv_mul_cancel]; group
    rw [e]
    calc v * D.s * (v * D.s) = v * (D.s * v) * D.s := by group
      _ = v * (v * D.s) * D.s := by rw [hvs]
      _ = (v * v) * (D.s * D.s) := by group
      _ = 1 := by rw [hv2, D.s_mul_s, one_mul]
  ·
    apply D.no_involution_T₁st h1
    have e : v * D.t * D.s * D.s * D.t = v := by
      rw [mul_assoc (v * D.t) D.s D.s, D.s_mul_s, mul_one, mul_assoc, D.t_mul_t, mul_one]
    rw [e]
    exact hv2

theorem exists_comm_s_not_mem_T₀ :
    ∃ y ∈ T, y ∉ D.T₀ ∧ y * D.s = D.s * y ∧ y * y ∈ D.B₀ ⊔ D.B₁ := by
  have hsB := D.s_mem_B
  have htsB : D.t * D.s * D.t⁻¹ ∈ D.B := D.conj_t_B D.s hsB
  have hts0 : D.t * D.s * D.t⁻¹ ∈ D.T₀ := D.B_le_T₀ htsB
  have hts1 : D.t * D.s * D.t⁻¹ ∉ D.T₁ := by
    intro h
    apply D.s_not_mem_T₁
    have := D.conj_mem_T₁ (inv_mem D.t_mem_T) h
    rwa [show D.t⁻¹ * (D.t * D.s * D.t⁻¹) * D.t⁻¹⁻¹ = D.s by group] at this
  have hts2 : D.t * D.s * D.t⁻¹ * (D.t * D.s * D.t⁻¹) = 1 := by
    rw [show D.t * D.s * D.t⁻¹ * (D.t * D.s * D.t⁻¹) = D.t * (D.s * D.s) * D.t⁻¹ by group,
      D.s_mul_s, mul_one, mul_inv_cancel]
  obtain ⟨a'', ha'', -, β, hβ, hβs⟩ := D.exists_conj_mul_s hts0 hts1 hts2
  have hβB : β ∈ D.B := D.B₀_le_B hβ
  have ha''1 : a'' = 1 := by
    have h1 : a'' * D.s ∈ D.B := by
      have : a'' * D.s = β⁻¹ * (D.t * D.s * D.t⁻¹) * β := by rw [← hβs]; group
      rw [this]
      exact mul_mem (mul_mem (inv_mem hβB) htsB) hβB
    have h2 : a'' ∈ D.B := by
      have := mul_mem h1 (inv_mem hsB)
      rwa [mul_inv_cancel_right] at this
    have := mem_inf.2 ⟨ha'', h2⟩
    rwa [D.A_inf_B, mem_bot] at this
  rw [ha''1, one_mul] at hβs
  have hβT : β ∈ T := D.B_le_T hβB
  refine ⟨β⁻¹ * D.t, mul_mem (inv_mem hβT) D.t_mem_T, fun h => D.t_not_mem_T₀ ?_, ?_, ?_⟩
  · have := mul_mem (D.B_le_T₀ hβB) h
    rwa [mul_inv_cancel_left] at this
  · calc β⁻¹ * D.t * D.s = β⁻¹ * (D.t * D.s * D.t⁻¹) * D.t := by group
      _ = β⁻¹ * (β * D.s * β⁻¹) * D.t := by rw [hβs]
      _ = D.s * (β⁻¹ * D.t) := by group
  · rw [show β⁻¹ * D.t * (β⁻¹ * D.t) = β⁻¹ * (D.t * β⁻¹ * D.t⁻¹) * (D.t * D.t) by group,
      D.t_mul_t, mul_one]
    exact mul_mem (mem_sup_left (inv_mem hβ))
      (D.conj_mem_B₀B₁ D.t_mem_T (mem_sup_left (inv_mem hβ)))

private theorem zc_two_eq : zc 2 = (r 2 : DihedralGroup (2 ^ 2)) := by
  rw [← rho_pow (by norm_num : 1 ≤ 2), r_one_pow]
  rfl

theorem exists_pow_four_eq_b_comm_s (D : FooteCore G T m 3) :
    ∃ q ∈ T, q * D.s = D.s * q ∧ q ^ 4 = D.b := by
  obtain ⟨y, hyT, hy0, hys, hy2⟩ := D.exists_comm_s_not_mem_T₀
  obtain ⟨e₀⟩ := D.B₀_iso
  let ψ : DihedralGroup 4 →* G := D.sDiag.comp e₀.symm.toMonoidHom
  have hψ : Function.Injective ψ := D.sDiag_injective.comp e₀.symm.injective
  have hψB : ∀ d, ψ d ∈ D.B₀ ⊔ D.B₁ := by
    intro d
    have h : ψ d ∈ D.sDiag.range := ⟨e₀.symm d, rfl⟩
    rw [D.sDiag_range] at h
    exact (mem_inf.1 h).1
  have hψs : ∀ d, ψ d * D.s = D.s * ψ d := fun d => D.sDiag_comm_s _
  have hmem : ∀ x : G, x ∈ D.B₀ ⊔ D.B₁ → x * D.s = D.s * x → ∃ d, ψ d = x := by
    intro x hx hxs
    have hxr : x ∈ D.sDiag.range := by
      rw [D.sDiag_range]
      exact mem_inf.2 ⟨hx, mem_centralizer_singleton_iff.2 hxs⟩
    obtain ⟨w, rfl⟩ := hxr
    exact ⟨e₀ w, by simp [ψ]⟩
  have hyψ : ∀ d, ∃ d', ψ d' = y * ψ d * y⁻¹ := fun d =>
    hmem _ (D.conj_mem_B₀B₁ hyT (hψB d)) (by
      calc y * ψ d * y⁻¹ * D.s = y * ψ d * (y⁻¹ * D.s * y) * y⁻¹ := by group
        _ = y * (ψ d * D.s) * y⁻¹ := by
            rw [show y⁻¹ * D.s * y = D.s by
              rw [mul_assoc, ← hys, ← mul_assoc, inv_mul_cancel, one_mul]]; group
        _ = D.s * (y * ψ d * y⁻¹) := by
            rw [hψs d]
            calc y * (D.s * ψ d) * y⁻¹ = (y * D.s) * ψ d * y⁻¹ := by group
              _ = D.s * (y * ψ d * y⁻¹) := by rw [hys]; group)
  choose α hα using hyψ
  obtain ⟨c, hc⟩ := hmem (y * y) hy2 (by
    calc y * y * D.s = y * (y * D.s) := by group
      _ = D.s * (y * y) := by rw [hys, ← mul_assoc, hys, mul_assoc])
  have hα1 : α 1 = 1 := hψ (by rw [hα, map_one, mul_one, mul_inv_cancel])
  have hαmul : ∀ d d', α (d * d') = α d * α d' := fun d d' =>
    hψ (by rw [hα, map_mul, map_mul, hα, hα]; group)
  have hαpow : ∀ (d : DihedralGroup 4) (k : ℕ), α (d ^ k) = α d ^ k := by
    intro d k
    induction k with
    | zero => rw [pow_zero, pow_zero, hα1]
    | succ k ih => rw [pow_succ, pow_succ, hαmul, ih]
  have hαD : ∀ d, α d = dihedralFourMap (α (r 1)) (α (sr 0)) d := by
    intro d
    cases d with
    | r i =>
      show α (r i) = α (r 1) ^ i.val
      rw [← hαpow, r_one_pow, ZMod.natCast_zmod_val]
    | sr i =>
      show α (sr i) = α (sr 0) * α (r 1) ^ i.val
      rw [← hαpow, ← hαmul, r_one_pow, ZMod.natCast_zmod_val, sr_mul_r, zero_add]
  have h1 : ∀ x, dihedralFourMap (α (r 1)) (α (sr 0))
      (dihedralFourMap (α (r 1)) (α (sr 0)) x) = c * x * c⁻¹ := by
    intro x
    rw [← hαD, ← hαD]
    apply hψ
    rw [hα, hα, map_mul, map_mul, map_inv, hc]
    group
  have h2 : dihedralFourMap (α (r 1)) (α (sr 0)) c = c := by
    rw [← hαD]
    apply hψ
    rw [hα, hc]
    group
  have h3 : ∀ x, x * dihedralFourMap (α (r 1)) (α (sr 0)) x * c ≠ 1 := by
    intro x hx
    rw [← hαD] at hx
    have hv : ψ x * y * (ψ x * y) = 1 := by
      have := congrArg ψ hx
      rw [map_mul, map_mul, hα, hc, map_one] at this
      rw [← this]
      group
    have hvT : ψ x * y ∈ T := mul_mem (D.B_le_T (D.B₀B₁_le_B (hψB x))) hyT
    have hv0 : ψ x * y ∉ D.T₀ := fun h => hy0 (by
      have := mul_mem (inv_mem (D.B_le_T₀ (D.B₀B₁_le_B (hψB x)))) h
      rwa [inv_mul_cancel_left] at this)
    have hvs : ψ x * y * D.s = D.s * (ψ x * y) := by
      rw [mul_assoc, hys, ← mul_assoc, hψs x, mul_assoc]
    exact D.not_mul_self_eq_one_of_comm_s hvT hv0 hvs hv
  obtain ⟨x, hx⟩ := exists_sq_eq_r_two_dihedral _ _ c h1 h2 h3
  rw [← hαD] at hx
  refine ⟨ψ x * y, mul_mem (D.B_le_T (D.B₀B₁_le_B (hψB x))) hyT, ?_, ?_⟩
  · rw [mul_assoc, hys, ← mul_assoc, hψs x, mul_assoc]
  ·
    have hsq : (ψ x * y) * (ψ x * y) = ψ (x * α x * c) := by
      rw [map_mul, map_mul, hα, hc]
      group
    have hr2 : ψ (r 2) = D.b := by
      have hb₀ : e₀.symm (r 2) = ⟨D.b₀, D.b₀_mem⟩ := by
        rw [MulEquiv.symm_apply_eq, D.B₀_iso_apply_b₀ e₀]
        exact zc_two_eq.symm
      show D.sDiag (e₀.symm (r 2)) = D.b₀ * D.b₁
      rw [hb₀, sDiag_apply]
      show D.b₀ * (D.s * D.b₀ * D.s⁻¹) = D.b₀ * D.b₁
      rw [D.conj_s_b₀]
    have h4 : (ψ x * y) ^ 4 = ψ (x * α x * c) ^ 2 := by
      rw [← hsq, ← pow_two, ← pow_mul]
    rw [h4, ← map_pow, hx, hr2]

theorem conj_A_of_two (D : FooteCore G T 2 n) {x α' : G} (hx : x ∈ T) (hα' : α' ∈ D.A) :
    x * α' * x⁻¹ = α' ∨ x * α' * x⁻¹ = D.a * α' := by
  obtain ⟨α, hα, hαA, -⟩ := D.exists_At_conj_A hx
  rw [hαA α' hα']
  obtain ⟨e⟩ := D.At_iso
  have hea := D.At_iso_apply_a e
  have hα'' : α' ∈ D.A ⊔ zpowers D.t := mem_sup_left hα'
  rcases comm_eq_one_or_r_two_dihedral (e ⟨α, hα⟩) (e ⟨α', hα''⟩) with h | h
  · left
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← e.map_one] at h
    have h' := congrArg Subtype.val (e.injective h)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one] at h'
    calc α * α' * α⁻¹ = α * α' * α⁻¹ * α'⁻¹ * α' := by group
      _ = α' := by rw [h', one_mul]
  · right
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← zc_two_eq, ← hea] at h
    have h' := congrArg Subtype.val (e.injective h)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h'
    calc α * α' * α⁻¹ = α * α' * α⁻¹ * α'⁻¹ * α' := by group
      _ = D.a * α' := by rw [h']

end FooteCore

end CFSG.CGT.Foote81L6
