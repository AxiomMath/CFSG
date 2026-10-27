module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1Dec
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GConj

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {A : Type} [Group A] [Finite A] {H : Subgroup A} {𝒮 : Set (Subgroup A)} {x : A}

private theorem l34g_conj_self {S : Subgroup A} (hx2 : x * x = 1) :
    CFSG.conjugate (CFSG.conjugate S x) x = S := by
  rw [l34g_conjugate_conjugate, hx2]
  ext g
  rw [sec63P_mem_conjugate_iff]
  simp

private theorem l34g_conj_pow_of_conj {S : Subgroup A} {g : A}
    (h : CFSG.conjugate S g = S) (k : ℕ) : CFSG.conjugate S (g ^ k) = S := by
  rw [sec63P_conjugate_eq_iff] at h ⊢
  exact (normalizer (S : Set A)).pow_mem h k

private theorem l34g_conj_sq_of_eq {S : Subgroup A} {p : A}
    (hx2 : x * x = 1) (hpx : p * x = x * p)
    (h : CFSG.conjugate S p = CFSG.conjugate S x) :
    CFSG.conjugate S (p * p) = S := by
  rw [← l34g_conjugate_conjugate S p p, h, l34g_conjugate_conjugate S x p, hpx.symm,
    ← l34g_conjugate_conjugate S p x, h, l34g_conj_self hx2]

private theorem l34g_pow_two_eq_of_pow_eq_one {p : A} {m : ℕ} (hp : p ^ (3 ^ m) = 1) :
    ∃ k : ℕ, p = (p * p) ^ k := by
  have hodd : Odd (3 ^ m) := Odd.pow (by norm_num : Odd 3)
  obtain ⟨k, hk⟩ := exists_pow_eq_pow_two_mul hp hodd 1
  refine ⟨k, ?_⟩
  have h2 : (p * p) ^ k = p ^ (2 * k) := by rw [← pow_two p, ← pow_mul]
  rw [h2, ← hk, pow_one]

private theorem l34g_conj_eq_of_conj_sq_eq {S : Subgroup A} {p : A} {m : ℕ}
    (hp : p ^ (3 ^ m) = 1) (h : CFSG.conjugate S (p * p) = S) :
    CFSG.conjugate S p = S := by
  obtain ⟨k, hk⟩ := l34g_pow_two_eq_of_pow_eq_one hp
  rw [hk]
  exact l34g_conj_pow_of_conj h k

private theorem l34g_eq_conj_of_conj_eq {K T : Subgroup A} (hx2 : x * x = 1)
    (h : CFSG.conjugate K x = T) : K = CFSG.conjugate T x := by
  rw [← h, l34g_conj_self hx2]

private theorem l34g_conj_mem_conj {S : Subgroup A} {d : A} (hx2 : x * x = 1) (hd : d ∈ S) :
    x * d * x⁻¹ ∈ CFSG.conjugate S x := by
  rw [sec63P_mem_conjugate_iff]
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_left hx2
  have hxx : x * (x * d * x⁻¹) * x⁻¹ = d := by
    rw [hxi]
    rw [show x * (x * d * x) * x = (x * x) * d * (x * x) by group, hx2]
    group
  rw [hxx]
  exact hd

private theorem l34g_mul_comm_of_comm {R S T : Subgroup A}
    (hSR : ∀ a ∈ S, ∀ b ∈ R, a * b = b * a)
    (hTR : ∀ a ∈ T, ∀ b ∈ R, a * b = b * a)
    {d e r : A} (hd : d ∈ S) (he : e ∈ T) (hr : r ∈ R) :
    (d * e) * r = r * (d * e) := by
  rw [mul_assoc, hTR e he r hr, ← mul_assoc, hSR d hd r hr, mul_assoc]

private theorem l34g_norm_fixed (hF : L34GFac H 𝒮 x) {S : Subgroup A} {p c : A} (hS : S ∈ 𝒮)
    (hSp : CFSG.conjugate S p ∈ 𝒮) (hcS : c ∈ S) (hcne : c ≠ 1) (hpc : p * c = c * p) :
    CFSG.conjugate S p = S := by
  have hpcc : p * c * p⁻¹ = c := by rw [hpc]; group
  have hcSp : c ∈ CFSG.conjugate S p := by
    rw [sec63P_mem_conjugate_iff, hpcc]
    exact hcS
  by_contra hne
  have hbot : S ⊓ CFSG.conjugate S p = ⊥ := hF.inf_eq_bot hS hSp (fun h => hne h.symm)
  have hcbot : c ∈ (⊥ : Subgroup A) := by
    rw [← hbot]
    exact Subgroup.mem_inf.mpr ⟨hcS, hcSp⟩
  exact hcne (Subgroup.mem_bot.mp hcbot)

private theorem l34g_norm_diag_eq {p d : A} (hpx : p * x = x * p)
    (hpz : p * (d * (x * d * x⁻¹)) = (d * (x * d * x⁻¹)) * p) :
    d * (x * d * x⁻¹) = (p⁻¹ * d * p) * (x * (p⁻¹ * d * p) * x⁻¹) := by
  have hcx : p⁻¹ * x * p = x := by
    calc p⁻¹ * x * p = p⁻¹ * (x * p) := by rw [mul_assoc]
      _ = p⁻¹ * (p * x) := by rw [← hpx]
      _ = x := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  have hcxi : p⁻¹ * x⁻¹ * p = x⁻¹ := by
    have h := congrArg Inv.inv hcx
    simpa [mul_inv_rev, mul_assoc] using h
  have hzp : p⁻¹ * (d * (x * d * x⁻¹)) * p = d * (x * d * x⁻¹) := by
    calc p⁻¹ * (d * (x * d * x⁻¹)) * p = p⁻¹ * ((d * (x * d * x⁻¹)) * p) := by rw [mul_assoc]
      _ = p⁻¹ * (p * (d * (x * d * x⁻¹))) := by rw [← hpz]
      _ = d * (x * d * x⁻¹) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  have hdiag : p⁻¹ * (x * d * x⁻¹) * p = x * (p⁻¹ * d * p) * x⁻¹ := by
    rw [show p⁻¹ * (x * d * x⁻¹) * p
          = (p⁻¹ * x * p) * (p⁻¹ * d * p) * (p⁻¹ * x⁻¹ * p) by group, hcx, hcxi]
  calc d * (x * d * x⁻¹) = p⁻¹ * (d * (x * d * x⁻¹)) * p := hzp.symm
    _ = (p⁻¹ * d * p) * (p⁻¹ * (x * d * x⁻¹) * p) := by group
    _ = (p⁻¹ * d * p) * (x * (p⁻¹ * d * p) * x⁻¹) := by rw [hdiag]

private theorem l34g_norm_diag_central (hF : L34GFac H 𝒮 x) {S S' : Subgroup A} (hS : S ∈ 𝒮)
    (hS' : S' ∈ 𝒮) (hne : S' ≠ S) (hne' : S' ≠ CFSG.conjugate S x) {d d' : A}
    (hd : d ∈ S) (hd' : d' ∈ S')
    (hz : d * (x * d * x⁻¹) = d' * (x * d' * x⁻¹)) : d * (x * d * x⁻¹) = 1 := by
  have hx2 : x * x = 1 := hF.invol
  have hSx : CFSG.conjugate S x ∈ 𝒮 := hF.perm S hS
  have hS'x : CFSG.conjugate S' x ∈ 𝒮 := hF.perm S' hS'
  have hS'x_S : CFSG.conjugate S' x ≠ S := fun h => hne' (l34g_eq_conj_of_conj_eq hx2 h)
  have hS'x_Sx : CFSG.conjugate S' x ≠ CFSG.conjugate S x := by
    intro h
    have h' := congrArg (fun T => CFSG.conjugate T x) h
    rw [l34g_conj_self hx2, l34g_conj_self hx2] at h'
    exact hne h'
  have he' : x * d' * x⁻¹ ∈ CFSG.conjugate S' x := l34g_conj_mem_conj hx2 hd'
  have hxd : x * d * x⁻¹ ∈ CFSG.conjugate S x := l34g_conj_mem_conj hx2 hd
  refine hF.eq_one_of_centralizes fun R hR r hr => ?_
  by_cases hRS : R = S
  · subst R
    rw [hz]
    exact l34g_mul_comm_of_comm (hF.comm S' hS' S hS hne)
      (hF.comm (CFSG.conjugate S' x) hS'x S hS hS'x_S) hd' he' hr
  · by_cases hRSx : R = CFSG.conjugate S x
    · subst R
      rw [hz]
      exact l34g_mul_comm_of_comm (hF.comm S' hS' (CFSG.conjugate S x) hSx hne')
        (hF.comm (CFSG.conjugate S' x) hS'x (CFSG.conjugate S x) hSx hS'x_Sx) hd' he' hr
    · exact l34g_mul_comm_of_comm (fun a ha b hb => (hF.comm R hR S hS hRS b hb a ha).symm)
        (fun a ha b hb => (hF.comm R hR (CFSG.conjugate S x) hSx hRSx b hb a ha).symm)
        hd hxd hr

private theorem l34g_norm_swapped (hF : L34GFac H 𝒮 x) {C0 : Subgroup A}
    (hswap : ∀ S ∈ 𝒮, CFSG.conjugate S x ≠ S → ∀ d ∈ S, d * (x * d * x⁻¹) ∈ C0)
    {p : A} {m : ℕ} (hp : p ^ 3 ^ m = 1) (hpx : p * x = x * p)
    (hperm : ∀ S ∈ 𝒮, CFSG.conjugate S p ∈ 𝒮) (hpC : ∀ c ∈ C0, p * c = c * p)
    {S : Subgroup A} (hS : S ∈ 𝒮) (hSx : CFSG.conjugate S x ≠ S) :
    CFSG.conjugate S p = S := by
  by_contra hSp
  have hSpSx : CFSG.conjugate S p = CFSG.conjugate S x := by
    by_contra hne
    obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (hF.ne_bot hS)
    have hdne : (a : A) ≠ 1 := fun h => ha (Subtype.ext h)
    have hd'Sp : p⁻¹ * (a : A) * p ∈ CFSG.conjugate S p := by
      rw [sec63P_mem_conjugate_iff, show p * (p⁻¹ * (a : A) * p) * p⁻¹ = a by group]
      exact a.2
    have hdeq := l34g_norm_diag_eq hpx (hpC _ (hswap S hS hSx a a.2))
    exact hdne (hF.diag_eq_one hS hSx a.2
      (l34g_norm_diag_central hF hS (hperm S hS) hSp hne a.2 hd'Sp hdeq))
  exact hSp (l34g_conj_eq_of_conj_sq_eq hp (l34g_conj_sq_of_eq hF.invol hpx hSpSx))

theorem l34g_propU_norm (hF : L34GFac H 𝒮 x) {C0 : Subgroup A}
    (hfix : ∀ S ∈ 𝒮, CFSG.conjugate S x = S → ∃ c ∈ C0, c ∈ S ∧ c ≠ 1)
    (hswap : ∀ S ∈ 𝒮, CFSG.conjugate S x ≠ S → ∀ d ∈ S, d * (x * d * x⁻¹) ∈ C0)
    {p : A} {m : ℕ} (hp : p ^ 3 ^ m = 1) (hpx : p * x = x * p)
    (hperm : ∀ S ∈ 𝒮, CFSG.conjugate S p ∈ 𝒮) (hpC : ∀ c ∈ C0, p * c = c * p) :
    ∀ S ∈ 𝒮, CFSG.conjugate S p = S := by
  intro S hS
  by_cases hSx : CFSG.conjugate S x = S
  · obtain ⟨c, hcC0, hcS, hcne⟩ := hfix S hS hSx
    exact l34g_norm_fixed hF hS (hperm S hS) hcS hcne (hpC c hcC0)
  · exact l34g_norm_swapped hF hswap hp hpx hperm hpC hS hSx

end CFSG.OddStandard.SmallF3.Omega
