module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big13
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big14

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W CFSG.GorensteinWalter
open CFSG.Blueprint

section CentB

variable {X : Type} [Group X] [Finite X] {F : Type} [Field F] [Finite F] {Q : Subgroup X} {r : ℕ}
  {p f : ℕ}

theorem arith_dvd {n r : ℕ} (h : n % 2 ^ (r + 1) = 2 ^ r + 1) :
    2 ^ r ∣ n - 1 ∧ ¬ 2 ^ (r + 1) ∣ n - 1 := by
  have hdecomp : n = n / 2 ^ (r + 1) * 2 ^ (r + 1) + (2 ^ r + 1) := by
    conv_lhs => rw [← Nat.div_add_mod n (2 ^ (r + 1))]
    rw [h]
    ring
  have hnm1 : n - 1 = 2 ^ r * (2 * (n / 2 ^ (r + 1)) + 1) := by
    have hpow : 2 ^ (r + 1) = 2 ^ r * 2 := by rw [pow_succ]
    conv_lhs => rw [hdecomp]
    rw [hpow]
    have hkey : n / (2 ^ r * 2) * (2 ^ r * 2) + (2 ^ r + 1) =
        (2 ^ r * (2 * (n / (2 ^ r * 2)) + 1)) + 1 := by ring
    omega
  refine ⟨⟨2 * (n / 2 ^ (r + 1)) + 1, hnm1⟩, ?_⟩
  intro hd
  have hmod0 : (n - 1) % 2 ^ (r + 1) = 0 := Nat.mod_eq_zero_of_dvd hd
  have hn : 1 ≤ n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    rw [hn0] at h
    simp at h
  have hmod1 : n % 2 ^ (r + 1) = 1 := by
    have hM : 1 < 2 ^ (r + 1) := by
      have h2 : 2 ≤ 2 ^ (r + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (r + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h1mod : 1 % 2 ^ (r + 1) = 1 := Nat.mod_eq_of_lt hM
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    rw [Nat.add_mod, hmod0, h1mod, Nat.zero_add]
    exact Nat.mod_eq_of_lt hM
  have hpos : 0 < 2 ^ r := pow_pos (by norm_num : (0 : ℕ) < 2) r
  omega

theorem rho_fix_field_sq [Fact p.Prime] (E : PGamEmb X F)
    (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    (h4 : 4 ≤ p ^ f) (hf : Even f) (hidx : (genFittingFStar X).index ≤ 2) (hr : 4 ≤ r)
    (hz : E.ρ (MulAut.conj (quatInvolution r e)) = SemidirectProduct.inl (pD (-1)))
    {σ₀ : F ≃+* F} (hσ₀1 : σ₀ ≠ 1) (hσ₀2 : σ₀ * σ₀ = 1)
    (hq : ∀ x : F, σ₀ x = x ^ (p ^ (f / 2))) (harith : p ^ f % 2 ^ (r + 1) = 2 ^ r + 1)
    {β : MulAut X} (hβ : ∀ x ∈ Q, β x = x) {k : ℕ} (hk : β ^ 2 ^ k = 1) :
    (E.ρ β).right * (E.ρ β).right = 1 := by
  have h2 : (2 : F) ≠ 0 := (field_facts (Fact.out : p.Prime) hp2 hF h4).2
  obtain ⟨x₀, _, hx₀, hA, _⟩ := quat_structure E e hF hp2 h4 hidx hr hz hσ₀1 hσ₀2
  have hmon : IsMon (E.ρ β) :=
    (isMon_iff_comm_ubar h2).mpr
      (rho_comm_ubar E hr e hz (fun x hx => by rw [hβ x hx]; exact hx))
  have hgA : E.ρ β * gD x₀ 1 = gD x₀ 1 * E.ρ β := by
    rw [← hA]
    exact rho_comm_qEmb E e hβ _
  have hfix : autU (E.ρ β).right x₀ = x₀ ∨ autU (E.ρ β).right x₀ = x₀⁻¹ :=
    autU_fix_of_comm_A hmon hgA
  have hτ : (E.ρ β).right ^ 2 ^ k = 1 := by
    rw [← right_pow, ← map_pow, hk, map_one]
    rfl
  exact aut_sq_eq_one_of_fix hF hp2 h4 hf hσ₀1 hσ₀2 hq hr (arith_dvd harith).1
    (arith_dvd harith).2 hx₀ hτ hfix

theorem z2BigModelCent_holds (r : ℕ) : Z2BigModelCent r := by
  intro hr X _ _ p f hL Q e
  obtain ⟨F, _, _, hF, h4, hp, E, hz⟩ :=
    exists_normalized_emb hL.simple hL.odd hL.even hL.model
      (quatInvolution_sq hr e) (quatInvolution_ne_one hr e)
      (quatInvolution_mem_fstar hL.index hr e)
  haveI : Fact p.Prime := ⟨hp⟩
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp only [pow_zero] at hF h4
    omega
  obtain ⟨σ₀, hσ₀1, hσ₀2, hq⟩ := exists_frob_half hF hL.even hf0
  refine ⟨?_, ?_⟩
  · intro x hx hk
    exact cent_two_elements E e hF hL.odd h4 hL.even hL.index hr hz hσ₀1 hσ₀2 hq hx hk
  · intro H hH hHQ
    let θ : MulAut X →* (F ≃+* F) := SemidirectProduct.rightHom.comp E.ρ
    let ζ : MulAut X := MulAut.conj (quatInvolution r e)
    have hright : ∀ β : MulAut X, θ β = (E.ρ β).right := fun β => rfl
    have hub : ubar F = E.ρ ζ := by
      change ubar F = E.ρ (MulAut.conj (quatInvolution r e))
      rw [ubar_eq, ← inl_pD_eq, ← hz]
    have hζ2 : ζ * ζ = 1 := by
      change MulAut.conj (quatInvolution r e) * MulAut.conj (quatInvolution r e) = 1
      rw [← map_mul, quatInvolution_sq hr e, map_one]
    have hζ1 : ζ ≠ 1 := by
      intro h
      apply quatInvolution_ne_one hr e
      apply E.conjInj
      change MulAut.conj (quatInvolution r e) = MulAut.conj (1 : X)
      rw [show MulAut.conj (quatInvolution r e) = 1 from h, map_one]
    have hθ : ∀ β ∈ H, θ β = 1 ∨ θ β = σ₀ := by
      intro β hβ
      obtain ⟨k, hkord⟩ := (IsPGroup.iff_orderOf.mp hH) ⟨β, hβ⟩
      rw [Subgroup.orderOf_mk] at hkord
      have hk : β ^ 2 ^ k = 1 := by rw [← hkord]; exact pow_orderOf_eq_one β
      have hgr : (E.ρ β).right * (E.ρ β).right = 1 :=
        rho_fix_field_sq E e hF hL.odd h4 hL.even hL.index hr hz hσ₀1 hσ₀2 hq hL.arith
          (hHQ β hβ) hk
      rcases ringAut_sq_eq_one hF hL.odd h4 hσ₀1 hσ₀2 hgr with h | h
      · left; rw [hright β, h]
      · right; rw [hright β, h]
    have h1 : ∀ β ∈ H, θ β = 1 → β = 1 ∨ β = ζ := by
      intro β hβ hθβ
      obtain ⟨k, hkord⟩ := (IsPGroup.iff_orderOf.mp hH) ⟨β, hβ⟩
      rw [Subgroup.orderOf_mk] at hkord
      have hk : β ^ 2 ^ k = 1 := by rw [← hkord]; exact pow_orderOf_eq_one β
      have hgr : (E.ρ β).right * (E.ρ β).right = 1 :=
        rho_fix_field_sq E e hF hL.odd h4 hL.even hL.index hr hz hσ₀1 hσ₀2 hq hL.arith
          (hHQ β hβ) hk
      have hk' : (E.ρ β) ^ 2 ^ k = 1 := by rw [← map_pow, hk, map_one]
      have htri := centralizer_qEmb E e hF hL.odd h4 hL.even hL.index hr hz hσ₀1 hσ₀2 hq
        (fun c => rho_comm_qEmb E e (hHQ β hβ) c) hgr hk'
      rcases htri with h | h | h
      · left
        exact E.inj (by rw [h, map_one])
      · right
        exact E.inj (by rw [h, hub])
      · exfalso
        have h1r : (E.ρ β).right = 1 := by rw [← hright β, hθβ]
        exact hσ₀1 (h.1.symm.trans h1r)
    have h2 : ∀ β ∈ H, θ β ≠ 1 → β * β = ζ := by
      intro β hβ hθβ
      obtain ⟨k, hkord⟩ := (IsPGroup.iff_orderOf.mp hH) ⟨β, hβ⟩
      rw [Subgroup.orderOf_mk] at hkord
      have hk : β ^ 2 ^ k = 1 := by rw [← hkord]; exact pow_orderOf_eq_one β
      have hgr : (E.ρ β).right * (E.ρ β).right = 1 :=
        rho_fix_field_sq E e hF hL.odd h4 hL.even hL.index hr hz hσ₀1 hσ₀2 hq hL.arith
          (hHQ β hβ) hk
      have hk' : (E.ρ β) ^ 2 ^ k = 1 := by rw [← map_pow, hk, map_one]
      have htri := centralizer_qEmb E e hF hL.odd h4 hL.even hL.index hr hz hσ₀1 hσ₀2 hq
        (fun c => rho_comm_qEmb E e (hHQ β hβ) c) hgr hk'
      rcases htri with h | h | h
      · exfalso
        apply hθβ
        exact (hright β).trans (by rw [h]; rfl)
      · exfalso
        apply hθβ
        exact (hright β).trans (by rw [h, ubar_eq]; rfl)
      · have hEq : E.ρ (β * β) = E.ρ ζ := by
          rw [map_mul, h.2.1]
          exact hub
        exact E.inj hEq
    exact isCyclic_of_small θ σ₀ ζ hσ₀2 hζ2 hζ1 H hθ h1 h2

end CentB

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
