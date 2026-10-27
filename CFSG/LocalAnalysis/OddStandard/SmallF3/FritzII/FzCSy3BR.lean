module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3BRE
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3Norm

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho q : G}

private theorem fzc_sy3_pow_odd {f : G} (hf : f ^ 2 = 1) {k : ℕ} (hk : k % 2 = 1) :
    f ^ k = f := by
  obtain ⟨m, hm⟩ : ∃ m, k = 2 * m + 1 := by
    refine ⟨k / 2, ?_⟩
    have h := Nat.div_add_mod k 2
    omega
  rw [hm, pow_succ]
  rw [show f ^ (2 * m) = (f ^ 2) ^ m by rw [pow_mul]]
  rw [hf, one_pow, one_mul]

theorem fzc_sy3_R_sq (h : Ctx0 t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hK : twoCore t = zpowers q) (hq4 : orderOf q = 4) (hqt : q ^ 2 = t) :
    ∀ r ∈ fzR t x₁ x₂, r * r ∈ baseGrp x₁ x₂ ⊔ zpowers t := by
  intro r hr
  have hEW : baseGrp x₁ x₂ ≤ ctxW t x₁ x₂ := le_sup_right
  by_cases hrW : r ∈ ctxW t x₁ x₂
  · obtain ⟨k, e₂, he₂, -, hrk⟩ := fzc_sy3_W_dec h hK hq4 r hrW
    have hqcomm : Commute q e₂ := fzc_sy3_q_comm_W h hK e₂ (hEW he₂)
    have hsq : (q ^ k * e₂) ^ 2 = (q ^ k) ^ 2 * e₂ ^ 2 := (hqcomm.pow_left k).mul_pow 2
    have hpow : (q ^ k) ^ 2 = t ^ k := by
      rw [← pow_mul, Nat.mul_comm k 2, pow_mul, hqt]
    have hrr : r * r = t ^ k * e₂ ^ 2 := by
      rw [hrk, ← pow_two, hsq, hpow]
    rw [hrr]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_right ((Subgroup.zpowers t).pow_mem (Subgroup.mem_zpowers t) k))
      (Subgroup.mem_sup_left (S4A.pt_four_le_base x₁ x₂ (fzc_sy2_E_sq h e₂ he₂)))
  · by_contra hr2
    obtain ⟨k, e, he, hk4, hr2eq⟩ := fzc_sy3_W_dec h hK hq4 (r * r) (hq.R_sq_mem_W r hr)
    have hkodd : k % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one k with h0 | h1
      · exfalso
        apply hr2
        have hk_even : k = 0 ∨ k = 2 := by
          interval_cases k
          · left; rfl
          · norm_num at h0
          · right; rfl
          · norm_num at h0
        rcases hk_even with rfl | rfl
        · rw [hr2eq]; simpa using Subgroup.mem_sup_left he
        · rw [hr2eq, show q ^ 2 = t from hqt]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
            (Subgroup.mem_sup_left he)
      · exact h1
    have hWcomm := fzc_sy2_W_comm h
    have hqW : q ∈ ctxW t x₁ x₂ := fzc_sy3_q_mem_W hK
    have htW : t ∈ ctxW t x₁ x₂ := fzc_sy2_t_mem h
    obtain ⟨f, hfZ, hrt⟩ := hq.R_act_t r hr
    have hf2 : f ^ 2 = 1 := (WreathRel.fourGrp_eq_omega h.wreath).2.1.2 f hfZ
    set g : G := r * q * r⁻¹ * q⁻¹ with hg_def
    have hgW : g ∈ ctxW t x₁ x₂ := by
      rw [hg_def]
      exact (ctxW t x₁ x₂).mul_mem (fzc_sy3_R_W r hr q hqW)
        ((ctxW t x₁ x₂).inv_mem hqW)
    have hgq : r * q * r⁻¹ = g * q := by rw [hg_def]; group
    have hg2 : g ^ 2 = f := by
      have hsq : (r * q * r⁻¹) ^ 2 = r * t * r⁻¹ := by
        rw [pow_two, ← hqt, pow_two]
        group
      have hsq2 : (g * q) ^ 2 = g ^ 2 * t := by
        rw [(show Commute g q from hWcomm g hgW q hqW).mul_pow 2, hqt]
      have hkey : g ^ 2 * t = t * f := by
        rw [← hsq2, ← hgq, hsq, hrt]
      have hcomm_gt : g ^ 2 * t = t * (g ^ 2) :=
        hWcomm (g ^ 2) ((ctxW t x₁ x₂).pow_mem hgW 2) t htW
      rw [hcomm_gt] at hkey
      exact mul_left_cancel hkey
    set ζ : G := r * e * r⁻¹ * e⁻¹ with hζ_def
    have hζZ : ζ ∈ fourGrp x₁ x₂ := by
      rw [hζ_def]
      exact fzc_sy3_R_E h hq hK hq4 hqt r hr e he
    have hζE : ζ ∈ baseGrp x₁ x₂ := S4A.pt_four_le_base x₁ x₂ hζZ
    have hζW : ζ ∈ ctxW t x₁ x₂ := Subgroup.mem_sup_right hζE
    have hre : r * e * r⁻¹ = ζ * e := by rw [hζ_def]; group
    have hfix : r * (q ^ k * e) * r⁻¹ = q ^ k * e := by
      rw [← hr2eq]; group
    have hrqk : r * q ^ k * r⁻¹ = g ^ k * q ^ k := by
      have h1 : r * q ^ k * r⁻¹ = (r * q * r⁻¹) ^ k := by
        simpa [MulAut.conj_apply] using map_pow (MulAut.conj r) q k
      rw [h1, hgq]
      exact (show Commute g q from hWcomm g hgW q hqW).mul_pow k
    have hexpand : r * (q ^ k * e) * r⁻¹ = g ^ k * q ^ k * (r * e * r⁻¹) := by
      calc r * (q ^ k * e) * r⁻¹ = (r * q ^ k * r⁻¹) * (r * e * r⁻¹) := by group
        _ = g ^ k * q ^ k * (r * e * r⁻¹) := by rw [hrqk]
    have hmain : g ^ k * ζ = 1 := by
      have h1 : q ^ k * e = g ^ k * q ^ k * ζ * e := by
        rw [← hfix, hexpand, hre]
        group
      have h2 : q ^ k = g ^ k * q ^ k * ζ := mul_right_cancel h1
      have h4 : g ^ k * q ^ k * ζ = (g ^ k * ζ) * q ^ k := by
        rw [show g ^ k * q ^ k * ζ = g ^ k * (q ^ k * ζ) by group,
            show (g ^ k * ζ) * q ^ k = g ^ k * (ζ * q ^ k) by group,
            (show Commute (q ^ k) ζ from
              (show Commute q ζ from hWcomm q hqW ζ hζW).pow_left k).eq]
      have h3 : q ^ k = (g ^ k * ζ) * q ^ k := by rw [← h4]; exact h2
      have h5 : 1 * q ^ k = (g ^ k * ζ) * q ^ k := by rw [one_mul]; exact h3
      exact mul_right_cancel h5.symm
    have hgkZ : g ^ k ∈ fourGrp x₁ x₂ := by
      rw [mul_eq_one_iff_eq_inv.mp hmain]
      exact (fourGrp x₁ x₂).inv_mem hζZ
    have hgk2 : (g ^ k) ^ 2 = 1 := (WreathRel.fourGrp_eq_omega h.wreath).2.1.2 (g ^ k) hgkZ
    have hfk : f ^ k = 1 := by
      have h1 : f ^ k = (g ^ k) ^ 2 := by
        rw [← hg2]
        conv_lhs => rw [← pow_mul]
        conv_rhs => rw [← pow_mul]
        rw [Nat.mul_comm 2 k]
      rw [h1, hgk2]
    have hf1 : f = 1 := by
      rw [← fzc_sy3_pow_odd hf2 hkodd, hfk]
    have hrt1 : r * t * r⁻¹ = t := by rw [hrt, hf1, mul_one]
    have hmem : r ∈ fzR t x₁ x₂ ⊓ invCent t := by
      refine Subgroup.mem_inf.mpr ⟨hr, ?_⟩
      show r ∈ Subgroup.centralizer ({t} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc r * t = r * t * r⁻¹ * r := by group
        _ = t * r := by rw [hrt1]
    rw [hq.cent_R_t] at hmem
    exact hrW hmem

theorem fzc_sy3_R_comm (h : Ctx0 t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hK : twoCore t = zpowers q) (hq4 : orderOf q = 4) (hqt : q ^ 2 = t) :
    ∀ a ∈ fzR t x₁ x₂, ∀ b ∈ fzR t x₁ x₂, a * b * a⁻¹ * b⁻¹ ∈ baseGrp x₁ x₂ ⊔ zpowers t := by
  intro a ha b hb
  have hab : a * b ∈ fzR t x₁ x₂ := (fzR t x₁ x₂).mul_mem ha hb
  have haib : a⁻¹ * a⁻¹ ∈ baseGrp x₁ x₂ ⊔ zpowers t :=
    fzc_sy3_R_sq h hq hK hq4 hqt a⁻¹ ((fzR t x₁ x₂).inv_mem ha)
  have hb2 : b⁻¹ * b⁻¹ ∈ baseGrp x₁ x₂ ⊔ zpowers t :=
    fzc_sy3_R_sq h hq hK hq4 hqt b⁻¹ ((fzR t x₁ x₂).inv_mem hb)
  have hconj : b⁻¹ * (a⁻¹ * a⁻¹) * b ∈ baseGrp x₁ x₂ ⊔ zpowers t := by
    simpa using fzc_sy3_R_Wp h hq hK hq4 hqt b⁻¹ ((fzR t x₁ x₂).inv_mem hb) _ haib
  have hprod : a * b * a⁻¹ * b⁻¹ =
      (a * b) * (a * b) * (b⁻¹ * (a⁻¹ * a⁻¹) * b) * (b⁻¹ * b⁻¹) := by group
  rw [hprod]
  exact (baseGrp x₁ x₂ ⊔ zpowers t).mul_mem
    ((baseGrp x₁ x₂ ⊔ zpowers t).mul_mem
      (fzc_sy3_R_sq h hq hK hq4 hqt (a * b) hab) hconj) hb2

theorem fzc_sy3_P_eq (hq : FzCQFacts t S x₁ x₂ lam rho) :
    fzP t x₁ x₂ rho = ⁅fzR t x₁ x₂, zpowers rho⁆ := by
  rw [fzP, hq.Q_eq]

theorem fzc_sy3_q_notin_P (h : Ctx0 t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hK : twoCore t = zpowers q) (hq4 : orderOf q = 4) (hqt : q ^ 2 = t) :
    q ∉ fzP t x₁ x₂ rho := by
  intro hqP
  have hWp_le_R : baseGrp x₁ x₂ ⊔ zpowers t ≤ fzR t x₁ x₂ :=
    (fzc_sy3_Wp_le_W h).trans hq.W_le_R
  have hrho3 : rho ^ 3 = 1 := by simpa [h.ord_rho] using pow_orderOf_eq_one rho
  have hx : q ∈ ⁅fzR t x₁ x₂, zpowers rho⁆ := by
    rw [← fzc_sy3_P_eq hq]
    exact hqP
  have hnorm := fzc_sy3_norm_fix (R := fzR t x₁ x₂)
    (N := baseGrp x₁ x₂ ⊔ zpowers t) hWp_le_R (fzc_sy3_R_Wp h hq hK hq4 hqt)
    hq.rho_norm_R (fzc_sy3_rho_Wp h) (fzc_sy3_R_comm h hq hK hq4 hqt) hrho3 hx
    (fzc_sy3_q_rho h hK)
  have hq3Wp : q ^ 3 ∈ baseGrp x₁ x₂ ⊔ zpowers t := hnorm
  apply fzc_sy3_q_notin_Wp h hK hq4 hqt
  have hq4' : q ^ 4 = 1 := by simpa [hq4] using pow_orderOf_eq_one q
  have hqeq : q = (q ^ 3)⁻¹ := by
    have h : q ^ 3 * q = 1 := by rw [← pow_succ, hq4']
    exact eq_inv_of_mul_eq_one_right h
  rw [hqeq]
  exact (baseGrp x₁ x₂ ⊔ zpowers t).inv_mem hq3Wp

theorem fzc_sy3_E_le_P (h : Ctx0 t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho) :
    baseGrp x₁ x₂ ≤ fzP t x₁ x₂ rho := by
  rw [← h.comm_rho, fzc_sy3_P_eq hq]
  exact Subgroup.commutator_mono hq.W_le_R le_rfl

theorem fzc_sy3_rho_RW (h : Ctx0 t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho) :
    ∀ r ∈ fzR t x₁ x₂, rho * r * rho⁻¹ * r⁻¹ ∈ ctxW t x₁ x₂ → r ∈ ctxW t x₁ x₂ := by
  intro r hr hc
  obtain ⟨f, hfZ, hf⟩ := hq.R_act_t r hr
  have hfW : f ∈ ctxW t x₁ x₂ := Subgroup.mem_sup_right (S4A.pt_four_le_base x₁ x₂ hfZ)
  have htW : t ∈ ctxW t x₁ x₂ := fzc_sy2_t_mem h
  have hrt := fzc_sy2_rho_t h
  have hrt' : rho⁻¹ * t * rho = t := by
    calc rho⁻¹ * t * rho = rho⁻¹ * (rho * t * rho⁻¹) * rho := by rw [hrt]
      _ = t := by group
  have h1 : (rho * r * rho⁻¹) * t * (rho * r * rho⁻¹)⁻¹ = t * f := by
    have hr1 : rho * r * rho⁻¹ = (rho * r * rho⁻¹ * r⁻¹) * r := by group
    rw [hr1]
    calc rho * r * rho⁻¹ * r⁻¹ * r * t * (rho * r * rho⁻¹ * r⁻¹ * r)⁻¹
        = (rho * r * rho⁻¹ * r⁻¹) * (r * t * r⁻¹) * (rho * r * rho⁻¹ * r⁻¹)⁻¹ := by group
      _ = (rho * r * rho⁻¹ * r⁻¹) * (t * f) * (rho * r * rho⁻¹ * r⁻¹)⁻¹ := by rw [hf]
      _ = t * f := by
        rw [fzc_sy2_W_comm h _ hc (t * f) (mul_mem htW hfW)]
        group
  have h2 : (rho * r * rho⁻¹) * t * (rho * r * rho⁻¹)⁻¹ = t * (rho * f * rho⁻¹) := by
    calc (rho * r * rho⁻¹) * t * (rho * r * rho⁻¹)⁻¹
        = rho * (r * (rho⁻¹ * t * rho) * r⁻¹) * rho⁻¹ := by group
      _ = rho * (t * f) * rho⁻¹ := by rw [hrt', hf]
      _ = (rho * t * rho⁻¹) * (rho * f * rho⁻¹) := by group
      _ = t * (rho * f * rho⁻¹) := by rw [hrt]
  have hfix : rho * f * rho⁻¹ = f := (mul_left_cancel (h1.symm.trans h2)).symm
  have hfC : f ∈ fzR t x₁ x₂ ⊓ centralizer ({rho} : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨hq.W_le_R hfW, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc f * rho = rho * f * rho⁻¹ * rho := by rw [hfix]
      _ = rho * f := by group
  rw [hq.cent_R_rho] at hfC
  have hf1 : f = 1 := by
    have hmem : f ∈ twoCore t ⊓ baseGrp x₁ x₂ :=
      Subgroup.mem_inf.mpr ⟨hfC, S4A.pt_four_le_base x₁ x₂ hfZ⟩
    rw [S4A.pt_inf_base h, Subgroup.mem_bot] at hmem
    exact hmem
  have hrt1 : r * t * r⁻¹ = t := by rw [hf, hf1, mul_one]
  have hmem : r ∈ fzR t x₁ x₂ ⊓ invCent t := by
    refine Subgroup.mem_inf.mpr ⟨hr, ?_⟩
    show r ∈ Subgroup.centralizer ({t} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc r * t = r * t * r⁻¹ * r := by group
      _ = t * r := by rw [hrt1]
  rwa [hq.cent_R_t] at hmem

end CFSG.OddStandard.SmallF3.FritzII
