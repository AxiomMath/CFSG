module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCRho2

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

private theorem fzc_rho_mem_normalizer_R (hs : FzCSteps t L S x₁ x₂ lam rho) :
    rho ∈ Subgroup.normalizer (fzR t x₁ x₂ : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact fzc_rho_norm_R hs hy
  · intro hy
    have h3 : rho ^ 3 = 1 := fzc_rho_cube hs
    have hz1 : rho * (rho * y * rho⁻¹) * rho⁻¹ ∈ fzR t x₁ x₂ :=
      fzc_rho_norm_R hs hy
    have hz2 : rho * (rho * (rho * y * rho⁻¹) * rho⁻¹) * rho⁻¹ ∈ fzR t x₁ x₂ :=
      fzc_rho_norm_R hs hz1
    have hz2' : rho ^ 2 * (rho * y * rho⁻¹) * (rho ^ 2)⁻¹ ∈ fzR t x₁ x₂ := by
      convert hz2 using 1
      rw [pow_two]
      group
    have heq : rho ^ 2 * (rho * y * rho⁻¹) * (rho ^ 2)⁻¹ = y := by
      have e1 : rho ^ 2 * rho = 1 := by
        rw [← pow_succ]
        exact h3
      have e2 : rho⁻¹ * (rho ^ 2)⁻¹ = 1 := by
        rw [← mul_inv_rev, e1, inv_one]
      calc rho ^ 2 * (rho * y * rho⁻¹) * (rho ^ 2)⁻¹
          = (rho ^ 2 * rho) * y * (rho⁻¹ * (rho ^ 2)⁻¹) := by group
        _ = y := by rw [e1, e2]; group
    rwa [heq] at hz2'

private theorem fzc_P_le_R (hs : FzCSteps t L S x₁ x₂ lam rho) :
    fzP t x₁ x₂ rho ≤ fzR t x₁ x₂ := by
  rw [fzP, fzc_Q_eq hs]
  exact (Subgroup.le_normalizer_iff_commutator_le_left (H := zpowers rho)
    (K := fzR t x₁ x₂)).mp (Subgroup.zpowers_le.mpr (fzc_rho_mem_normalizer_R hs))

private theorem fzc_card_sup {H K : Subgroup G}
    (h : K ≤ Subgroup.normalizer (H : Set G)) (hdisj : H ⊓ K = ⊥) :
    Nat.card (H ⊔ K : Subgroup G) = Nat.card H * Nat.card K := by
  let A : Subgroup G := H ⊔ K
  have hA : A = H ⊔ K := rfl
  have hset : (↑A : Set G) = (↑H : Set G) * (↑K : Set G) := by
    rw [hA]
    exact Subgroup.coe_mul_of_right_le_normalizer_left H K h
  let f : H × K → A := fun p =>
    ⟨(p.1 : G) * p.2, by rw [← SetLike.mem_coe, hset]; exact Set.mul_mem_mul p.1.2 p.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨h1, k1⟩ ⟨h2, k2⟩ heq
      have hG : (h1 : G) * k1 = (h2 : G) * k2 := by
        have := congrArg (Subtype.val) heq
        simpa [f] using this
      have hrel : (h2 : G)⁻¹ * h1 = k2 * (k1 : G)⁻¹ := by
        calc (h2 : G)⁻¹ * h1 = (h2 : G)⁻¹ * ((h1 : G) * k1) * (k1 : G)⁻¹ := by group
          _ = (h2 : G)⁻¹ * ((h2 : G) * k2) * (k1 : G)⁻¹ := by rw [hG]
          _ = k2 * (k1 : G)⁻¹ := by group
      have hmem : (h2 : G)⁻¹ * h1 ∈ H ⊓ K := by
        rw [Subgroup.mem_inf]
        exact ⟨H.mul_mem (H.inv_mem h2.2) h1.2,
          by rw [hrel]; exact K.mul_mem k2.2 (K.inv_mem k1.2)⟩
      have h1' : (h2 : G)⁻¹ * h1 = 1 := by
        rw [hdisj] at hmem
        exact Subgroup.mem_bot.mp hmem
      have hk : k2 * (k1 : G)⁻¹ = 1 := by rw [← hrel, h1']
      have hh : h1 = h2 := by
        apply Subtype.ext
        have h := congrArg (fun z => (h2 : G) * z) h1'
        simpa [mul_assoc] using h
      have hk' : k1 = k2 := by
        apply Subtype.ext
        have h := congrArg (fun z => z * (k1 : G)) hk
        exact (by simpa [mul_assoc] using h : (k2 : G) = k1).symm
      rw [hh, hk']
    · intro y
      have hy : (y : G) ∈ (↑H : Set G) * (↑K : Set G) := by
        rw [← hset]
        exact y.2
      obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hy
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  have hcard := Nat.card_congr (Equiv.ofBijective f hf)
  rw [Nat.card_prod] at hcard
  rw [← hA]
  exact hcard.symm

private theorem fzc_exists_orderOf_eq_two_of_isPGroup_ne_bot {X : Subgroup G}
    (hX : IsPGroup 2 X) (hne : X ≠ ⊥) : ∃ x ∈ X, orderOf x = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hxX, hx1⟩ : ∃ x ∈ X, x ≠ 1 := by
    by_contra h
    have hbot : X = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro z hz
      by_contra hz1
      exact h ⟨z, hz, hz1⟩
    exact hne hbot
  have hdvd : 2 ∣ Nat.card X := by
    have h2 : 2 ∣ orderOf (⟨x, hxX⟩ : X) := hX.dvd_orderOf (by simpa using hx1)
    exact h2.trans (orderOf_dvd_natCard _)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := X) 2 hdvd
  exact ⟨(y : G), y.2, by rwa [Subgroup.orderOf_coe]⟩

theorem fzc_rho_norm_P (hs : FzCSteps t L S x₁ x₂ lam rho) {x : G}
    (hx : x ∈ fzP t x₁ x₂ rho) : rho * x * rho⁻¹ ∈ fzP t x₁ x₂ rho := by
  rw [fzP, fzc_Q_eq hs] at hx ⊢
  exact (Subgroup.mem_normalizer_iff.mp
    (Subgroup.normalizer_commutator_ge_right (H₁ := fzR t x₁ x₂)
      (H₂ := zpowers rho) (Subgroup.mem_zpowers rho)) x).mp hx

theorem fzc_lam_norm_P (hs : FzCSteps t L S x₁ x₂ lam rho) {x : G}
    (hx : x ∈ fzP t x₁ x₂ rho) : lam * x * lam⁻¹ ∈ fzP t x₁ x₂ rho := by
  rw [fzP, fzc_Q_eq hs] at hx ⊢
  refine fzc_comm_conj_mem (H := fzR t x₁ x₂) (ρ := rho) (g := lam) ?_ ?_ hx
  · intro y hy
    exact fzc_lam_norm_R hs hy
  · rw [hs.ctx.lam_rho]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers rho)

theorem fzc_P_normal_R (hs : FzCSteps t L S x₁ x₂ lam rho) {r : G} (hr : r ∈ fzR t x₁ x₂)
    {x : G} (hx : x ∈ fzP t x₁ x₂ rho) : r * x * r⁻¹ ∈ fzP t x₁ x₂ rho := by
  rw [fzP, fzc_Q_eq hs] at hx ⊢
  exact (Subgroup.mem_normalizer_iff.mp
    (Subgroup.normalizer_commutator_ge_left (H₁ := fzR t x₁ x₂)
      (H₂ := zpowers rho) hr) x).mp hx

theorem fzc_K_invol (hs : FzCSteps t L S x₁ x₂ lam rho) {u : G} (hu : u ∈ twoCore t)
    (hu2 : u * u = 1) (hu1 : u ≠ 1) : u = t := by
  rcases hs.ctx.hyp.eq_one_or_eq u hu (by rw [pow_two]; exact hu2) with h1 | ht
  · exact absurd h1 hu1
  · exact ht

theorem fzc_inf_P_K (hs : FzCSteps t L S x₁ x₂ lam rho) (ht : t ∉ fzP t x₁ x₂ rho) :
    fzP t x₁ x₂ rho ⊓ twoCore t = ⊥ := by
  by_contra hne
  have hXp : IsPGroup 2 (fzP t x₁ x₂ rho ⊓ twoCore t : Subgroup G) :=
    (fzc_K_pGroup t).to_le
      (inf_le_right : fzP t x₁ x₂ rho ⊓ twoCore t ≤ twoCore t)
  obtain ⟨u, huX, huord⟩ := fzc_exists_orderOf_eq_two_of_isPGroup_ne_bot hXp hne
  have hu2 : u * u = 1 := by
    rw [← pow_two, ← huord]
    exact pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at huord
    omega
  have hut : u = t := fzc_K_invol hs huX.2 hu2 hu1
  exact ht (hut ▸ huX.1)

theorem fzc_card_P (hs : FzCSteps t L S x₁ x₂ lam rho) (ht : t ∉ fzP t x₁ x₂ rho) :
    Nat.card (fzP t x₁ x₂ rho) * Nat.card (twoCore t) = Nat.card (fzR t x₁ x₂) := by
  rw [fzc_R_eq_PK hs]
  refine (fzc_card_sup (H := fzP t x₁ x₂ rho) (K := twoCore t) ?_
    (fzc_inf_P_K hs ht)).symm
  refine (le_sup_left : twoCore t ≤ ctxW t x₁ x₂).trans ((fzc_W_le_R hs).trans ?_)
  exact Subgroup.le_normalizer_iff.mpr (fun r hr x hx => fzc_P_normal_R hs hr hx)

theorem fzc_P_fpf (hs : FzCSteps t L S x₁ x₂ lam rho) (ht : t ∉ fzP t x₁ x₂ rho) {x : G}
    (hx : x ∈ fzP t x₁ x₂ rho) (h : rho * x * rho⁻¹ = x) : x = 1 := by
  have hxR : x ∈ fzR t x₁ x₂ := fzc_P_le_R hs hx
  have hcent : x ∈ Subgroup.centralizer ({rho} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have := congrArg (fun z => z * rho) h
    simpa [mul_assoc] using this
  have hxK : x ∈ twoCore t := by
    have hmem : x ∈ fzR t x₁ x₂ ⊓ Subgroup.centralizer ({rho} : Set G) := ⟨hxR, hcent⟩
    rwa [fzc_cent_R_rho hs] at hmem
  have hxbot : x ∈ fzP t x₁ x₂ rho ⊓ twoCore t := ⟨hx, hxK⟩
  rwa [fzc_inf_P_K hs ht, Subgroup.mem_bot] at hxbot

end CFSG.OddStandard.SmallF3.FritzII
