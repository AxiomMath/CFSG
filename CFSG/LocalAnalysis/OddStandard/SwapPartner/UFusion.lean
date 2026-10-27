module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UBasic
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapRetract
public import CFSG.LocalAnalysis.OddStandard.AltStdSmallSylow
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UD8C
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UPerm

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

open scoped commutatorElement

variable {G : Type} [Group G] {z : G} {ι ιd : Perm (Fin 10) →* G}

private theorem u_exists_sq_of_isConj {H : Type*} [Group H] {a b : H} (h : IsConj a b)
    (ha : ∃ y : H, y * y = a) : ∃ y : H, y * y = b := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  obtain ⟨y, rfl⟩ := ha
  exact ⟨c * y * c⁻¹, by rw [← hc]; group⟩

private theorem u_mul_self_of_isConj {H : Type*} [Group H] {a b : H} (h : IsConj a b)
    (ha : a * a = 1) : b * b = 1 := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  rw [← hc]
  calc (c * a * c⁻¹) * (c * a * c⁻¹) = c * (a * a) * c⁻¹ := by group
    _ = 1 := by rw [ha, mul_one, mul_inv_cancel]

private theorem u_sign_of_isConj {a b : Perm (Fin 8)} (h : IsConj a b) : sign a = sign b := by
  have h' : IsConj (sign a) (sign b) := (Equiv.Perm.sign : Perm (Fin 8) →* ℤˣ).map_isConj h
  rwa [isConj_iff_eq] at h'

private theorem u_sign_eq_neg_one_of_mul_eq_one {s : ℤˣ} (h : (-1 : ℤˣ) * s = 1) : s = -1 := by
  rcases Int.units_eq_one_or s with hs | hs
  · rw [hs, mul_one] at h
    exact absurd h (by decide)
  · exact hs

theorem exists_sq_of_sign_one_perm_ten {π : Perm (Fin 10)} (h2 : π * π = 1) (hs : sign π = 1) :
    ∃ γ : Perm (Fin 10), γ * γ = π := by
  have hk5 : Multiset.card π.cycleType ≤ 5 := card_cycleType_le_five h2
  have heven : Even (Multiset.card π.cycleType) := by
    have hsg := CFSG.OddStandard.AltStdSmall.sign_eq_neg_one_pow_of_mul_self h2
    rw [hs] at hsg
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    rw [hodd.neg_one_pow] at hsg
    exact absurd hsg (by decide)
  obtain ⟨k, hk⟩ := even_iff_exists_two_mul.1 heven
  have hk2 : k ≤ 2 := by
    rw [hk] at hk5
    omega
  interval_cases k
  · refine ⟨1, ?_⟩
    have hπ : π = 1 := card_cycleType_eq_zero.1 (by omega)
    rw [hπ, mul_one]
  · refine u_exists_sq_of_isConj (IsConj.symm ?_) exists_sq_r₂
    exact (isConj_rep_of_card_cycleType h2).2.1 (by omega)
  · refine u_exists_sq_of_isConj (IsConj.symm ?_) exists_sq_ρ₄
    exact (isConj_rep_of_card_cycleType h2).2.2.2.1 (by omega)

theorem exists_sq_x₂_mul (F : UFrame z ι ιd) {ρ : Perm (Fin 8)} (hs : sign ρ = 1) (h2 : ρ * ρ = 1) :
    (∃ w : G, w * w = (z * ι τ₀) * ι (liftS8 ρ)) ∧ ∃ w : G, w * w = ι (liftS8 ρ) := by
  obtain ⟨r, hr⟩ := exists_sq_of_sign_eq_one h2 hs
  have hsq_s : ι (liftS8 r) * ι (liftS8 r) = ι (liftS8 ρ) := by
    rw [← map_mul, ← map_mul, hr]
  have hcomm : (z * gElt ιd) * ι (liftS8 r) = ι (liftS8 r) * (z * gElt ιd) := by
    rw [mul_assoc, F.g_comm r, ← mul_assoc, F.z_comm_sigma r, mul_assoc]
  have hsq_a : (z * gElt ιd) * (z * gElt ιd) = z * ι τ₀ := by
    rw [← mul_assoc]
    exact F.d8.x_eq
  refine ⟨⟨(z * gElt ιd) * ι (liftS8 r), ?_⟩, ⟨ι (liftS8 r), hsq_s⟩⟩
  calc ((z * gElt ιd) * ι (liftS8 r)) * ((z * gElt ιd) * ι (liftS8 r))
      = (z * gElt ιd) * (ι (liftS8 r) * (z * gElt ιd)) * ι (liftS8 r) := by group
    _ = (z * gElt ιd) * ((z * gElt ιd) * ι (liftS8 r)) * ι (liftS8 r) := by
        rw [hcomm]
    _ = ((z * gElt ιd) * (z * gElt ιd)) * (ι (liftS8 r) * ι (liftS8 r)) := by group
    _ = (z * ι τ₀) * ι (liftS8 ρ) := by rw [hsq_a, hsq_s]

theorem exists_sq_g_mul (F : UFrame z ι ιd) {ρ : Perm (Fin 8)} (hs : sign ρ = 1) (h2 : ρ * ρ = 1) :
    ∃ w : G, w * w = gElt ιd * ι (liftS8 ρ) := by
  obtain ⟨τ, ρ', i, hρ'0, hρ'1, hconj⟩ := exists_conj_swap_mul h2
  let ρ'' : Perm (Fin 8) := swap (0 : Fin 8) 1 ^ (i : ℕ) * ρ'
  have hconj'' : τ * ρ * τ⁻¹ = ρ'' := hconj
  have hconjIs : IsConj ρ ρ'' := isConj_iff.2 ⟨τ, hconj''⟩
  have h2'' : ρ'' * ρ'' = 1 := u_mul_self_of_isConj hconjIs h2
  have hsign'' : sign ρ'' = 1 := by rw [← u_sign_of_isConj hconjIs, hs]
  obtain ⟨v, hv⟩ := (exists_sq_x₂_mul F hsign'' h2'').1
  have hd : Commute (yElt ιd) (ι (swap (0 : Fin 10) 1)) := F.y_comm_d
  have hdy : Commute (yElt ιd) ((ι (swap (0 : Fin 10) 1)) ^ (i : ℕ)) := hd.pow_right _
  have hs' : Commute (yElt ιd) (ι (liftS8 ρ')) := F.y_comm_sigma hρ'0 hρ'1
  have hρ''m : ι (liftS8 ρ'') =
      (ι (swap (0 : Fin 10) 1)) ^ (i : ℕ) * ι (liftS8 ρ') := by
    have h1 : liftS8 ρ'' = (liftS8 (swap (0 : Fin 8) 1)) ^ (i : ℕ) * liftS8 ρ' := by
      show liftS8 ((swap (0 : Fin 8) 1) ^ (i : ℕ) * ρ') = _
      rw [map_mul, map_pow]
    rw [h1, map_mul, map_pow, liftS8_swap_zero_one]
  have hyρ'' : Commute (yElt ιd) (ι (liftS8 ρ'')) := by
    rw [hρ''m]
    exact hdy.mul_right hs'
  have hye : yElt ιd * ((z * ι τ₀) * ι (liftS8 ρ'')) * (yElt ιd)⁻¹
      = gElt ιd * ι (liftS8 ρ'') := by
    calc yElt ιd * ((z * ι τ₀) * ι (liftS8 ρ'')) * (yElt ιd)⁻¹
        = (yElt ιd * (z * ι τ₀) * (yElt ιd)⁻¹) *
            (yElt ιd * ι (liftS8 ρ'') * (yElt ιd)⁻¹) := by group
      _ = (yElt ιd * (z * ι τ₀) * (yElt ιd)⁻¹) * ι (liftS8 ρ'') := by
          rw [show yElt ιd * ι (liftS8 ρ'') * (yElt ιd)⁻¹ = ι (liftS8 ρ'') by
            rw [hyρ''.eq]; group]
      _ = gElt ιd * ι (liftS8 ρ'') := by rw [F.y_conj]
  have hc₁ : ∃ w : G, w * w = gElt ιd * ι (liftS8 ρ'') := by
    refine ⟨yElt ιd * v * (yElt ιd)⁻¹, ?_⟩
    rw [← hye, ← hv]
    group
  have hq : ι (liftS8 τ) * ι (liftS8 ρ) * (ι (liftS8 τ))⁻¹ = ι (liftS8 ρ'') := by
    rw [← map_mul, ← map_inv, ← map_mul, ← map_inv, ← map_mul, ← map_mul, hconj'']
  have hconj_c : IsConj (gElt ιd * ι (liftS8 ρ)) (gElt ιd * ι (liftS8 ρ'')) := by
    refine isConj_iff.2 ⟨ι (liftS8 τ), ?_⟩
    calc ι (liftS8 τ) * (gElt ιd * ι (liftS8 ρ)) * (ι (liftS8 τ))⁻¹
        = (ι (liftS8 τ) * gElt ιd) * (ι (liftS8 ρ) * (ι (liftS8 τ))⁻¹) := by group
      _ = (gElt ιd * ι (liftS8 τ)) * (ι (liftS8 ρ) * (ι (liftS8 τ))⁻¹) := by
          rw [← F.g_comm τ]
      _ = gElt ιd * (ι (liftS8 τ) * ι (liftS8 ρ) * (ι (liftS8 τ))⁻¹) := by group
      _ = gElt ιd * ι (liftS8 ρ'') := by rw [hq]
  exact u_exists_sq_of_isConj hconj_c.symm hc₁

theorem exists_sq_z_mul (F : UFrame z ι ιd) {ρ : Perm (Fin 8)} (hs : sign ρ = -1)
    (h2 : ρ * ρ = 1) : ∃ w : G, w * w = z * ι (liftS8 ρ) := by
  obtain ⟨c₁, ρ', hρ'2, hsign', hc₁⟩ := exists_conj_of_sign_neg_one h2 hs
  obtain ⟨v, hv⟩ := (exists_sq_x₂_mul F hsign' hρ'2).1
  have hconj : IsConj (z * ι (liftS8 ρ)) ((z * ι τ₀) * ι (liftS8 ρ')) := by
    refine isConj_iff.2 ⟨ι c₁, ?_⟩
    calc ι c₁ * (z * ι (liftS8 ρ)) * (ι c₁)⁻¹
        = z * (ι c₁ * ι (liftS8 ρ) * (ι c₁)⁻¹) := by
          rw [show ι c₁ * (z * ι (liftS8 ρ)) * (ι c₁)⁻¹
                = (ι c₁ * z) * (ι (liftS8 ρ) * (ι c₁)⁻¹) by group,
              (F.cent.comm c₁).symm]
          group
      _ = z * ι (c₁ * liftS8 ρ * c₁⁻¹) := by
          rw [← map_mul, ← map_inv, ← map_mul]
      _ = z * ι (τ₀ * liftS8 ρ') := by rw [hc₁]
      _ = (z * ι τ₀) * ι (liftS8 ρ') := by rw [map_mul]; group
  exact u_exists_sq_of_isConj hconj.symm ⟨v, hv⟩

theorem exists_sq_x₁_mul (F : UFrame z ι ιd) {ρ : Perm (Fin 8)} (hs : sign ρ = -1)
    (h2 : ρ * ρ = 1) : ∃ w : G, w * w = ι τ₀ * ι (liftS8 ρ) := by
  have ha : liftS8 ρ * liftS8 ρ = 1 := by rw [← map_mul, h2, map_one]
  have hπ2 : (τ₀ * liftS8 ρ) * (τ₀ * liftS8 ρ) = 1 := by
    calc (τ₀ * liftS8 ρ) * (τ₀ * liftS8 ρ)
        = τ₀ * (liftS8 ρ * τ₀) * liftS8 ρ := by group
      _ = τ₀ * (τ₀ * liftS8 ρ) * liftS8 ρ := by rw [liftS8_mul_τ₀ ρ]
      _ = (τ₀ * τ₀) * (liftS8 ρ * liftS8 ρ) := by group
      _ = 1 := by rw [τ₀_mul_self, ha, mul_one]
  have hπs : sign (τ₀ * liftS8 ρ) = 1 := by
    rw [map_mul, sign_τ₀, sign_liftS8, hs]
    decide
  obtain ⟨γ, hγ⟩ := exists_sq_of_sign_one_perm_ten hπ2 hπs
  exact ⟨ι γ, by rw [← map_mul, hγ, map_mul]⟩

theorem exists_sq_of_chi (F : UFrame z ι ιd)
    (ε : closure ({z, gElt ιd} : Set G) →* ℤˣ)
    (hz : ε ⟨z, D8Rel.z_mem z (gElt ιd)⟩ = -1) (hg : ε ⟨gElt ιd, D8Rel.g_mem z (gElt ιd)⟩ = 1)
    {q : G} (hq : q ∈ closure ({z, gElt ιd} : Set G)) {ρ : Perm (Fin 8)} (hqq : q * q = 1)
    (hρ : ρ * ρ = 1) (hε : ε ⟨q, hq⟩ * sign ρ = 1) : ∃ w : G, w * w = q * ι (liftS8 ρ) := by
  rcases (D8Rel.sq_eq_one_iff F.d8 hq).1 hqq with h1 | h2 | h3 | h4 | h5 | h6
  · subst q
    have hεq : ε ⟨(1 : G), hq⟩ = 1 := by
      rw [show (⟨(1 : G), hq⟩ : closure ({z, gElt ιd} : Set G)) = 1 from Subtype.ext rfl,
        map_one]
    have hsign : sign ρ = 1 := by
      have := hε
      rw [hεq, one_mul] at this
      exact this
    simpa using (exists_sq_x₂_mul F hsign hρ).2
  · subst q
    have hεq : ε ⟨z, hq⟩ = -1 := by
      rw [show (⟨z, hq⟩ : closure ({z, gElt ιd} : Set G)) =
            ⟨z, D8Rel.z_mem z (gElt ιd)⟩ from Subtype.ext rfl]
      exact hz
    have hsign : sign ρ = -1 := by
      have := hε
      rw [hεq] at this
      exact u_sign_eq_neg_one_of_mul_eq_one this
    exact exists_sq_z_mul F hsign hρ
  · subst q
    have hεq : ε ⟨gElt ιd, hq⟩ = 1 := by
      rw [show (⟨gElt ιd, hq⟩ : closure ({z, gElt ιd} : Set G)) =
            ⟨gElt ιd, D8Rel.g_mem z (gElt ιd)⟩ from Subtype.ext rfl]
      exact hg
    have hsign : sign ρ = 1 := by
      have := hε
      rw [hεq, one_mul] at this
      exact this
    exact exists_sq_g_mul F hsign hρ
  · subst q
    have hεq : ε ⟨z * gElt ιd * z, hq⟩ = 1 := by
      rw [show (⟨z * gElt ιd * z, hq⟩ : closure ({z, gElt ιd} : Set G)) =
            (⟨z, D8Rel.z_mem z (gElt ιd)⟩ : closure ({z, gElt ιd} : Set G)) *
            (⟨gElt ιd, D8Rel.g_mem z (gElt ιd)⟩ : closure ({z, gElt ιd} : Set G)) *
            (⟨z, D8Rel.z_mem z (gElt ιd)⟩ : closure ({z, gElt ιd} : Set G)) from
          Subtype.ext rfl,
          map_mul, map_mul, hz, hg]
      decide
    have hsign : sign ρ = 1 := by
      have := hε
      rw [hεq, one_mul] at this
      exact this
    obtain ⟨v, hv⟩ := exists_sq_g_mul F hsign hρ
    have hconj : IsConj (gElt ιd * ι (liftS8 ρ)) ((z * gElt ιd * z) * ι (liftS8 ρ)) := by
      refine isConj_iff.2 ⟨z, ?_⟩
      have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right F.d8.z_sq
      calc z * (gElt ιd * ι (liftS8 ρ)) * z⁻¹
          = z * gElt ιd * (ι (liftS8 ρ) * z) := by rw [hzinv]; group
        _ = z * gElt ιd * (z * ι (liftS8 ρ)) := by rw [← F.z_comm_sigma ρ]
        _ = (z * gElt ιd * z) * ι (liftS8 ρ) := by group
    exact u_exists_sq_of_isConj hconj ⟨v, hv⟩
  · subst q
    have hεq : ε ⟨gElt ιd * z * gElt ιd, hq⟩ = -1 := by
      rw [show (⟨gElt ιd * z * gElt ιd, hq⟩ : closure ({z, gElt ιd} : Set G)) =
            (⟨gElt ιd, D8Rel.g_mem z (gElt ιd)⟩ : closure ({z, gElt ιd} : Set G)) *
            (⟨z, D8Rel.z_mem z (gElt ιd)⟩ : closure ({z, gElt ιd} : Set G)) *
            (⟨gElt ιd, D8Rel.g_mem z (gElt ιd)⟩ : closure ({z, gElt ιd} : Set G)) from
          Subtype.ext rfl,
          map_mul, map_mul, hz, hg]
      decide
    have hsign : sign ρ = -1 := by
      have := hε
      rw [hεq] at this
      exact u_sign_eq_neg_one_of_mul_eq_one this
    rw [F.g_z_g]
    exact exists_sq_x₁_mul F hsign hρ
  · subst q
    have hεq : ε ⟨z * ι τ₀, hq⟩ = 1 := by
      rw [show (⟨z * ι τ₀, hq⟩ : closure ({z, gElt ιd} : Set G)) =
            (⟨z, D8Rel.z_mem z (gElt ιd)⟩ : closure ({z, gElt ιd} : Set G)) *
            (⟨gElt ιd, D8Rel.g_mem z (gElt ιd)⟩ : closure ({z, gElt ιd} : Set G)) *
            (⟨z, D8Rel.z_mem z (gElt ιd)⟩ : closure ({z, gElt ιd} : Set G)) *
            (⟨gElt ιd, D8Rel.g_mem z (gElt ιd)⟩ : closure ({z, gElt ιd} : Set G)) from
          Subtype.ext F.d8.x_eq.symm,
          map_mul, map_mul, map_mul, hz, hg]
      decide
    have hsign : sign ρ = 1 := by
      have := hε
      rw [hεq, one_mul] at this
      exact this
    exact (exists_sq_x₂_mul F hsign hρ).1

theorem not_isConj_of_chi (F : UFrame z ι ιd)
    (ε : closure ({z, gElt ιd} : Set G) →* ℤˣ)
    (hz : ε ⟨z, D8Rel.z_mem z (gElt ιd)⟩ = -1) (hg : ε ⟨gElt ιd, D8Rel.g_mem z (gElt ιd)⟩ = 1)
    {q : G} (hq : q ∈ closure ({z, gElt ιd} : Set G)) {ρ : Perm (Fin 8)} (hqq : q * q = 1)
    (hρ : ρ * ρ = 1) (hε : ε ⟨q, hq⟩ * sign ρ = 1) (a : G) :
    a⁻¹ * z * a ≠ q * ι (liftS8 ρ) := by
  intro h
  obtain ⟨w, hw⟩ := exists_sq_of_chi F ε hz hg hq hqq hρ hε
  exact F.cent.not_sq (a * w * a⁻¹) (by
    calc (a * w * a⁻¹) * (a * w * a⁻¹) = a * (w * w) * a⁻¹ := by group
      _ = a * (q * ι (liftS8 ρ)) * a⁻¹ := by rw [hw]
      _ = a * (a⁻¹ * z * a) * a⁻¹ := by rw [← h]
      _ = z := by group)

end CFSG.OddStandard.AltStdSec.SwapPartner
