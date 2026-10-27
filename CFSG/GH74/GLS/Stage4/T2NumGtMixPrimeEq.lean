module

public import CFSG.GH74.GLS.Stage4.T2NumGtMixOmega
public import CFSG.GH74.GLS.Stage4.T2NumGtMixSteps
public import CFSG.GH74.GLS.Stage4.T2NumGtMixArith
public import CFSG.GH74.GLS.Stage4.T2NumGtSecSurj
public import CFSG.GH74.GLS.Stage4.T2NumGtRankDouble
public import CFSG.GH74.GLS.Stage4.T2NumGtSL2CD
public import CFSG.GH74.GLS.Stage4.T6Mod
public import CFSG.GH74.GLS.Stage4.T6X.T6Rle
public import CFSG.GH74.GLS.Stage4.T6X.T6Sec
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.Stage4.Rest.T6X CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem mx_cube_zero {V : Type*} [AddCommGroup V] [Module (ZMod 3) V] (T : Module.End (ZMod 3) V)
    (hT : T ^ 3 = 1) : (T - 1) ^ 3 = 0 := by
  have h3 : (3 : Module.End (ZMod 3) V) = 0 := by
    have h : (3 : ZMod 3) = 0 := by decide
    have := map_ofNat (algebraMap (ZMod 3) (Module.End (ZMod 3) V)) 3
    rw [h, map_zero] at this
    exact this.symm
  calc (T - 1) ^ 3 = T ^ 3 - 3 * T ^ 2 + 3 * T - 1 := by noncomm_ring
    _ = 0 := by rw [hT, h3]; simp

theorem mx_nilp_eq_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (N : V →ₗ[K] V)
    (hN : N ^ 3 = 0) (hkr : LinearMap.range N ⊓ LinearMap.ker N = ⊥) : N = 0 := by
  have h3 : ∀ v, N (N (N v)) = 0 := fun v => by
    have := congrArg (fun f => f v) hN
    simpa [pow_succ] using this
  have h2 : ∀ v, N (N v) = 0 := by
    intro v
    have hmem : N (N v) ∈ LinearMap.range N ⊓ LinearMap.ker N :=
      ⟨⟨N v, rfl⟩, by simpa using h3 v⟩
    rw [hkr] at hmem
    exact (Submodule.mem_bot K).1 hmem
  ext v
  have hmem : N v ∈ LinearMap.range N ⊓ LinearMap.ker N := ⟨⟨v, rfl⟩, by simpa using h2 v⟩
  rw [hkr] at hmem
  simpa using (Submodule.mem_bot K).1 hmem

theorem mx_comm_aux {G : Type*} [Group G] {a r y κ : G}
    (hκ : κ = a * r * a⁻¹ * r⁻¹) (h1 : y * r = r * y) (hκa : κ * a = a * κ)
    (hκy : y * κ = κ * y) : (y * a * y⁻¹ * a⁻¹) * r = r * (y * a * y⁻¹ * a⁻¹) := by
  have e1 : a * r = κ * (r * a) := by rw [hκ]; group
  have hyr : y * r * y⁻¹ = r := by rw [h1]; group
  have hyκ : y * κ * y⁻¹ = κ := by rw [hκy]; group
  have hyr' : y⁻¹ * r = r * y⁻¹ := by
    calc y⁻¹ * r = y⁻¹ * (r * y) * y⁻¹ := by group
      _ = y⁻¹ * (y * r) * y⁻¹ := by rw [h1]
      _ = r * y⁻¹ := by group
  have e2 : (y * a * y⁻¹) * r = κ * (r * (y * a * y⁻¹)) := by
    have : (y * a * y⁻¹) * r = y * (a * r) * y⁻¹ := by
      calc (y * a * y⁻¹) * r = y * a * (y⁻¹ * r) := by group
        _ = y * a * (r * y⁻¹) := by rw [hyr']
        _ = y * (a * r) * y⁻¹ := by group
    rw [this, e1]
    calc y * (κ * (r * a)) * y⁻¹ = (y * κ * y⁻¹) * (y * r * y⁻¹) * (y * a * y⁻¹) := by group
      _ = κ * (r * (y * a * y⁻¹)) := by rw [hyκ, hyr]; group
  have hκy' : κ * y⁻¹ = y⁻¹ * κ := by
    calc κ * y⁻¹ = y⁻¹ * (y * κ) * y⁻¹ := by group
      _ = y⁻¹ * (κ * y) * y⁻¹ := by rw [hκy]
      _ = y⁻¹ * κ := by group
  have hκb : κ * (y * a * y⁻¹) = (y * a * y⁻¹) * κ := by
    calc κ * (y * a * y⁻¹) = (κ * y) * a * y⁻¹ := by group
      _ = (y * κ) * a * y⁻¹ := by rw [hκy]
      _ = y * (κ * a) * y⁻¹ := by group
      _ = y * (a * κ) * y⁻¹ := by rw [hκa]
      _ = y * a * (κ * y⁻¹) := by group
      _ = y * a * (y⁻¹ * κ) := by rw [hκy']
      _ = (y * a * y⁻¹) * κ := by group
  have hκa' : κ * a⁻¹ = a⁻¹ * κ := by
    calc κ * a⁻¹ = a⁻¹ * (a * κ) * a⁻¹ := by group
      _ = a⁻¹ * (κ * a) * a⁻¹ := by rw [hκa]
      _ = a⁻¹ * κ := by group
  have e3 : a⁻¹ * r = κ⁻¹ * (r * a⁻¹) := by
    have h2 : κ * (a⁻¹ * r) = r * a⁻¹ := by
      calc κ * (a⁻¹ * r) = a⁻¹ * (κ * r) := by
            calc κ * (a⁻¹ * r) = (κ * a⁻¹) * r := by group
              _ = (a⁻¹ * κ) * r := by rw [hκa']
              _ = a⁻¹ * (κ * r) := by group
        _ = a⁻¹ * (a * r * a⁻¹) := by
            congr 1
            rw [hκ]; group
        _ = r * a⁻¹ := by group
    calc a⁻¹ * r = κ⁻¹ * (κ * (a⁻¹ * r)) := by group
      _ = κ⁻¹ * (r * a⁻¹) := by rw [h2]
  have hκb' : (y * a * y⁻¹) * κ⁻¹ = κ⁻¹ * (y * a * y⁻¹) := by
    calc (y * a * y⁻¹) * κ⁻¹ = κ⁻¹ * (κ * (y * a * y⁻¹)) * κ⁻¹ := by group
      _ = κ⁻¹ * ((y * a * y⁻¹) * κ) * κ⁻¹ := by rw [hκb]
      _ = κ⁻¹ * (y * a * y⁻¹) := by group
  calc (y * a * y⁻¹ * a⁻¹) * r = (y * a * y⁻¹) * (a⁻¹ * r) := by group
    _ = (y * a * y⁻¹) * (κ⁻¹ * (r * a⁻¹)) := by rw [e3]
    _ = ((y * a * y⁻¹) * κ⁻¹) * (r * a⁻¹) := by group
    _ = (κ⁻¹ * (y * a * y⁻¹)) * (r * a⁻¹) := by rw [hκb']
    _ = κ⁻¹ * ((y * a * y⁻¹) * r) * a⁻¹ := by group
    _ = κ⁻¹ * (κ * (r * (y * a * y⁻¹))) * a⁻¹ := by rw [e2]
    _ = r * (y * a * y⁻¹ * a⁻¹) := by group

theorem ch6Mix_primeEq :
    ∀ (G : Type) [Group G] [Finite G] (Gs : Type) [Group Gs] (q₁ q₂ : ℕ), q₂ < q₁ → q₁ % 4 ≠ q₂ % 4 →
      ∀ (z : G) (K₁ K₂ : Subgroup G) (F₁ F₂ : Type) [Field F₁] [Field F₂] (t : G),
        Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂ → Ch6Rem z K₁ K₂ F₁ F₂ t →
          ∀ (p n : ℕ), p.Prime → p ≠ 2 → q₂ = p ^ n →
            ∀ (N : T2N3 G) (u : G), N.z = z → N.K₁ = K₁ → N.K₂ = K₂ → N.q₁ = q₁ → N.q₂ = q₂ →
              Ch6Coord2 N.toT2N2.toT2N1 → Ch6Sec5M N u →
                ∀ (y : G) (R : Subgroup G), Ch6MixTSdata N p y R → ∃ m : ℕ, q₁ = p ^ m := by
  intro G _ _ Gs _ q₁ q₂ hlt hmod z K₁ K₂ F₁ F₂ _ _ t hSet hRem p n hp hp2 hq₂p N u hz hK₁ hK₂ hq₁ hq₂
    hCoord hSec y R hTS
  by_contra hnp
  subst hz hK₁ hK₂ hq₁ hq₂
  have hctx : T6CtxW N u p := t6CtxW_of hSet hRem rfl rfl rfl rfl rfl hp hp2 ⟨n, hq₂p⟩ hCoord hSec.toW
  have hloc := hSec.loc
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hp1 : 1 < p := hp.one_lt
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · have := hloc.q₂_ge; rw [hq₂p, h0] at this; simp at this
    · exact h0
  have hq₂pos : 0 < N.q₂ := by have := hloc.q₂_ge; omega
  have hfin₁ := hSet.finite₁
  have hfin₂ := hSet.finite₂
  have hpq₁ : ¬ p ∣ N.q₁ := by
    intro hd
    have : Fintype F₁ := Fintype.ofFinite F₁
    obtain ⟨p₁, -, ⟨a, hp₁, hcard⟩⟩ := FiniteField.card' F₁
    have hq₁a : N.q₁ = p₁ ^ (a : ℕ) := by rw [← hSet.card₁, Nat.card_eq_fintype_card, hcard]
    rw [hq₁a] at hd
    have hpp : p ∣ p₁ := hp.dvd_of_dvd_pow hd
    have hpe : p = p₁ := (Nat.prime_dvd_prime_iff_eq hp hp₁).1 hpp
    exact hnp ⟨a, by rw [hq₁a, ← hpe]⟩
  obtain ⟨⟨e₁, he₁⟩, ⟨e₂, he₂⟩⟩ := t2C_coords hSet
  have hodd : Odd (Nat.card F₁) := by rw [hSet.card₁]; exact hSet.odd₁
  have hF₂p : Nat.card F₂ = p ^ n := by rw [hSet.card₂]; exact hq₂p
  have hF₁p : ¬ p ∣ Nat.card F₁ := by rw [hSet.card₁]; exact hpq₁
  have hF5 : 5 ≤ Nat.card F₁ := by rw [hSet.card₁]; exact hSet.five
  obtain ⟨Ω, hΩ⟩ := mx_omega_exists hctx
  have hΩR : Ω ≤ R₂ N p := fun r hr => ((hΩ r).1 hr).1
  have hX₂R := X₂_le_R₂ hctx
  have hXΩ : N.X₂ ≤ Ω := fun x hx => (hΩ x).2 ⟨hX₂R hx, N.X₂.pow_mem hx p⟩
  have hΩM : ∀ g ∈ M₂ N, ∀ r ∈ Ω, g * r * g⁻¹ ∈ Ω := fun g hg r hr => mx_omega_inv hΩ hg hr
  have hΩU : ∀ g ∈ t2U N.z u, ∀ k ∈ Ω, g * k * g⁻¹ ∈ Ω := fun g hg k hk =>
    hΩM g (U_le_M₂ hctx hg) k hk
  have h4 := card_four_decomp hctx hXΩ hΩR hΩU
  obtain ⟨hz2, hu2, hzu, -⟩ := zu_facts hctx
  have hw₁K : N.w₁ ∈ N.K₁ := hloc.w₁_mem
  have hw₁M : N.w₁ ∈ M₂ N := K₁_le_M₂ hctx hw₁K
  have hconj : N.w₁ * u * N.w₁⁻¹ = N.z * u := by rw [hloc.w₁_u, hzu]
  have h45 := t6_card_cent_conj (R := Ω) (w := N.w₁) (fun r hr => hΩM _ hw₁M r hr)
    (fun r hr => by simpa using hΩM _ ((M₂ N).inv_mem hw₁M) r hr) u
  rw [hconj] at h45
  rw [← h45] at h4
  have hcle : Nat.card ↥(Ω ⊓ Subgroup.centralizer {u}) ≤ p ^ n * Nat.gcd p (Nat.card ↥N.K₁) :=
    mx_Omega_u_card_le hctx hp hp2 hΩ e₁ e₂ hodd hF₂p hF₁p
  have hΩcomm : ∀ a ∈ Ω, ∀ a' ∈ Ω, ⁅a, a'⁆ ∈ N.X₂ := fun a ha a' ha' =>
    (R₂_inv_comm hctx).2 a (hΩR ha) a' (hΩR ha')
  have hΩinv : ∀ a ∈ Ω, N.z * a * N.z⁻¹ * a ∈ N.X₂ := fun a ha => (R₂_inv_comm hctx).1 a (hΩR ha)
  have hΩexp : ∀ a ∈ Ω, a ^ p ∈ N.X₂ := fun a ha => ((hΩ a).1 ha).2
  have hKΩ : ∀ k ∈ N.K₁, ∀ a ∈ Ω, k * a * k⁻¹ ∈ Ω := fun k hk a ha =>
    hΩM k (K₁_le_M₂ hctx hk) a ha
  have hKX : ∀ k ∈ N.K₁, ∀ b ∈ N.X₂, k * b * k⁻¹ ∈ N.X₂ := (K₁_sec_X₂R₂ hctx).2
  obtain ⟨V, _, _, _, ρ, π, hcard, hπ0, hπadd, hρπ⟩ :=
    t6_sec_rep (p := p) (K := N.K₁) (A := Ω) (B := N.X₂) hKΩ hKX hΩcomm hΩexp
  have hπsurj : Function.Surjective π := ng_sec_surj π hcard hπ0 hπadd
  have hrel : N.X₂.relIndex Ω * N.q₂ = Nat.card ↥Ω := by
    have := Subgroup.relIndex_mul_card N.X₂ Ω
    rwa [inf_eq_left.2 hXΩ, hloc.card_X₂] at this
  have hVc : Nat.card V = Nat.card ↥(Ω ⊓ Subgroup.centralizer {u}) ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_right hq₂pos
    rw [hcard, hrel, h4]; ring
  have hfV : p ^ Module.finrank (ZMod p) V ≤ (p ^ n * Nat.gcd p (Nat.card ↥N.K₁)) ^ 2 := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rw [Nat.card_zmod, hVc] at h1
    rw [← h1]
    exact Nat.pow_le_pow_left hcle 2
  have hRR : R ≤ R₂ N p := R_le_R₂ hctx hTS.R_p hTS.R_cent hTS.R_inv
  have hRΩ : R ≤ Ω := fun r hr => (hΩ r).2 ⟨hRR hr, hTS.R_exp r hr⟩
  obtain ⟨Eadd, hE1, hE2, hEcard⟩ := mx_sec_image π hπ0 hπadd hTS.X_le hRΩ
  let E : Submodule (ZMod p) V := AddSubgroup.toZModSubmodule p Eadd
  have hEmem : ∀ v, v ∈ E ↔ v ∈ Eadd := fun v => Iff.rfl
  have hEdim : Module.finrank (ZMod p) E = 2 * n := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := E)
    rw [Nat.card_zmod] at h1
    have hEc : Nat.card ↥E = Nat.card ↥Eadd := Nat.card_congr (Equiv.refl _)
    have hE3 : Nat.card ↥Eadd = N.q₂ ^ 2 := by
      have h2 := hEcard
      rw [hloc.card_X₂, hTS.R_card] at h2
      apply Nat.eq_of_mul_eq_mul_right hq₂pos
      rw [h2]; ring
    rw [hEc, hE3, hq₂p, ← pow_mul] at h1
    have := Nat.pow_right_injective hp.two_le h1
    omega
  have hyK : y ∈ N.K₁ := hTS.yK
  have hEfix : ∀ v ∈ E, ρ ⟨y, hyK⟩ v = v := by
    intro v hv
    obtain ⟨r, hrR, rfl⟩ := hE2 v ((hEmem v).1 hv)
    have e2 : y * (r : G) * y⁻¹ = r := by rw [hTS.y_cent r hrR]; group
    rw [hρπ ⟨y, hyK⟩ r]
    congr 1
    exact Subtype.ext e2
  have hzK : N.z ∈ N.K₁ := hloc.z_mem_K₁
  have hρz : ∀ v, ρ ⟨N.z, hzK⟩ v = -v := by
    intro v
    obtain ⟨a, rfl⟩ := hπsurj v
    have e1 := hρπ ⟨N.z, hzK⟩ a
    have h1 : π (⟨N.z * a * N.z⁻¹, hKΩ _ hzK a a.2⟩ * a) = 0 := by
      rw [hπ0]; exact hΩinv a a.2
    rw [hπadd] at h1
    rw [e1]; exact eq_neg_of_add_eq_zero_left h1
  have hq₂lt : N.q₂ < N.q₂ ^ 3 := by
    calc N.q₂ = N.q₂ ^ 1 := (pow_one _).symm
      _ < N.q₂ ^ 3 := Nat.pow_lt_pow_right (by have := hloc.q₂_ge; omega) (by norm_num)
  have hne : N.X₂ ≠ Ω := by
    intro heq
    have h1 : Nat.card ↥R ≤ Nat.card ↥Ω := Subgroup.card_le_of_le hRΩ
    rw [← heq, hloc.card_X₂, hTS.R_card] at h1
    omega
  have hinjρ : Function.Injective ρ :=
    t6_sec_faithful hp hp2 hodd e₁ hloc.z_mem_K₁ he₁ hXΩ hKΩ hΩinv hne ρ π hπ0 hπadd hρπ
  have hy1 : y ≠ 1 := fun e => hTS.y_ne (e ▸ Subgroup.one_mem _)
  have hy1' : (⟨y, hyK⟩ : ↥N.K₁) ≠ 1 := fun h => hy1 (by simpa using congrArg Subtype.val h)
  have hyodd' : Odd (orderOf (⟨y, hyK⟩ : ↥N.K₁)) := by
    rw [Subgroup.orderOf_mk]; exact hTS.y_odd
  have hrank := l64_rank_double hp hp2 (K := ↥N.K₁) (F := F₁) ⟨hodd, by omega⟩ e₁
    (z := ⟨N.z, hzK⟩) he₁ ρ hρz hy1' hyodd' E hEfix
  have hpd : p ∣ Nat.card ↥N.K₁ := by
    by_contra hpd
    have hg : Nat.gcd p (Nat.card ↥N.K₁) = 1 := (Nat.Prime.coprime_iff_not_dvd hp).2 hpd
    rw [hg, mul_one, ← pow_mul] at hfV
    have := (Nat.pow_le_pow_iff_right hp1).1 hfV
    omega
  have hgle : Nat.gcd p (Nat.card ↥N.K₁) ≤ p := Nat.gcd_le_left _ hp.pos
  have hfV2 : Module.finrank (ZMod p) V ≤ 2 * n + 2 := by
    have h2 : p ^ Module.finrank (ZMod p) V ≤ p ^ (2 * n + 2) := by
      calc p ^ Module.finrank (ZMod p) V ≤ (p ^ n * Nat.gcd p (Nat.card ↥N.K₁)) ^ 2 := hfV
        _ ≤ (p ^ n * p) ^ 2 := Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hgle) 2
        _ = p ^ (2 * n + 2) := by rw [← pow_succ, ← pow_mul]; ring_nf
    exact (Nat.pow_le_pow_iff_right hp1).1 h2
  have hn1' : n = 1 := by omega
  have hcross := sl2_cross_dim p hp hp2 F₁ hodd hF5 hF₁p V (ρ.comp (e₁.symm : _ →* ↥N.K₁))
    (hinjρ.comp e₁.symm.injective)
  have h9 : N.q₁ ≤ 9 := by
    rw [hSet.card₁] at hcross
    rcases hSet.odd₁ with ⟨k, hk⟩
    subst hn1'
    omega
  have hKcard : Nat.card ↥N.K₁ = N.q₁ * (N.q₁ ^ 2 - 1) := by
    rw [Nat.card_congr e₁.toEquiv, CFSG.BenderSuzuki.External.huppert614_card_specialLinearGroup,
      hSet.card₁]
  have hpq : p ∣ N.q₁ ^ 2 - 1 := by
    rw [hKcard] at hpd
    exact (hp.dvd_mul.1 hpd).resolve_left hpq₁
  have hq₂p1 : N.q₂ = p := by rw [hq₂p, hn1', pow_one]
  obtain ⟨hq₁5, hp3⟩ := mixed_five_three hp hp2 hSet.odd₁ hSet.five
    (by rw [← hq₂p1]; exact hlt) h9 hpq (by rw [← hq₂p1]; exact hmod)
  have hy3 : orderOf y = 3 := by
    have h1 := hTS.y_dvd
    rw [hq₁5] at h1
    have hpr := hTS.y_prime
    have hodd' := hTS.y_odd
    rcases (Nat.Prime.dvd_mul hpr).1 (show orderOf y ∣ 2 * 3 by simpa using h1) with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).1 h
      rw [this] at hodd'
      exact absurd hodd' (by decide)
    · exact (Nat.prime_dvd_prime_iff_eq hpr Nat.prime_three).1 h
  have hy1V : ∀ v : V, ρ ⟨y, hyK⟩ v = v + (ρ ⟨y, hyK⟩ v - v) := fun v => by abel
  have hπ1 : π 1 = 0 := by
    have h := hπadd 1 1
    rw [mul_one] at h
    have h' : π 1 + π 1 = π 1 + 0 := by rw [← h, add_zero]
    exact add_left_cancel h'
  have hπinv : ∀ a, π a⁻¹ = - π a := fun a => by
    have := hπadd a⁻¹ a
    rw [inv_mul_cancel, hπ1] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  subst hp3
  let Nl : Module.End (ZMod 3) V := ρ ⟨y, hyK⟩ - 1
  have hρ3 : (ρ ⟨y, hyK⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨y, hyK⟩ : ↥N.K₁) ^ 3 = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← hy3]
      exact pow_orderOf_eq_one y
    rw [this, map_one]
  have hN3 : Nl ^ 3 = 0 := mx_cube_zero _ hρ3
  have hNl : ∀ v, Nl v = ρ ⟨y, hyK⟩ v - v := fun v => by simp [Nl]
  have hEle : E ≤ LinearMap.ker Nl := fun v hv => by
    rw [LinearMap.mem_ker, hNl, hEfix v hv, sub_self]
  have hkerfix : ∀ v ∈ LinearMap.ker Nl, ρ ⟨y, hyK⟩ v = v := fun v hv => by
    have := LinearMap.mem_ker.1 hv
    rw [hNl, sub_eq_zero] at this
    exact this
  have hker2 := l64_rank_double hp hp2 (K := ↥N.K₁) (F := F₁) ⟨hodd, by omega⟩ e₁
    (z := ⟨N.z, hzK⟩) he₁ ρ hρz hy1' hyodd' (LinearMap.ker Nl) hkerfix
  have hkerE : E = LinearMap.ker Nl :=
    Submodule.eq_of_le_of_finrank_le hEle (by omega)
  have hrE : ∀ w ∈ LinearMap.range Nl, w ∈ E → w = 0 := by
    rintro w ⟨v, rfl⟩ hwE
    obtain ⟨a, rfl⟩ := hπsurj v
    have hya : y * (a : G) * y⁻¹ ∈ Ω := hKΩ y hyK a a.2
    have hc : y * (a : G) * y⁻¹ * (a : G)⁻¹ ∈ Ω := Ω.mul_mem hya (Ω.inv_mem a.2)
    have hπc : π ⟨y * (a : G) * y⁻¹ * (a : G)⁻¹, hc⟩ = Nl (π a) := by
      have h1 : (⟨y * (a : G) * y⁻¹ * (a : G)⁻¹, hc⟩ : ↥Ω) = ⟨y * (a : G) * y⁻¹, hya⟩ * a⁻¹ :=
        Subtype.ext rfl
      rw [h1, hπadd, hπinv, hNl, hρπ ⟨y, hyK⟩ a, sub_eq_add_neg]
      rfl
    have hcR : ∀ r ∈ R, (y * (a : G) * y⁻¹ * (a : G)⁻¹) * r = r * (y * (a : G) * y⁻¹ * (a : G)⁻¹) := by
      intro r hr
      have hrR₂ : r ∈ R₂ N 3 := hRR hr
      have hκX : ⁅(a : G), r⁆ ∈ N.X₂ := hΩcomm a a.2 r (hRΩ hr)
      have hκa : ⁅(a : G), r⁆ * (a : G) = (a : G) * ⁅(a : G), r⁆ := by
        have := R₂_cent hctx a (hΩR a.2) _ hκX
        calc ⁅(a : G), r⁆ * (a : G) = ((a : G) * ⁅(a : G), r⁆ * (a : G)⁻¹) * (a : G) := by rw [this]
          _ = (a : G) * ⁅(a : G), r⁆ := by group
      have hκy : y * ⁅(a : G), r⁆ = ⁅(a : G), r⁆ * y := by
        have := K₁_cent_X₂ hctx hyK hκX
        calc y * ⁅(a : G), r⁆ = (y * ⁅(a : G), r⁆ * y⁻¹) * y := by group
          _ = ⁅(a : G), r⁆ * y := by rw [this]
      exact mx_comm_aux (by rw [commutatorElement_def]) (hTS.y_cent r hr) hκa hκy
    rw [← hπc] at hwE ⊢
    obtain ⟨r', hr'R, hr'π⟩ := hE2 _ ((hEmem _).1 hwE)
    have hdiff : π (⟨y * (a : G) * y⁻¹ * (a : G)⁻¹, hc⟩ * r'⁻¹) = 0 := by
      rw [hπadd, hπinv, hr'π, add_neg_cancel]
    have hxX : y * (a : G) * y⁻¹ * (a : G)⁻¹ * (r' : G)⁻¹ ∈ N.X₂ := (hπ0 _).1 hdiff
    set x : G := y * (a : G) * y⁻¹ * (a : G)⁻¹ * (r' : G)⁻¹ with hx
    have hr'eq : (r' : G) = x⁻¹ * (y * (a : G) * y⁻¹ * (a : G)⁻¹) := by rw [hx]; group
    have hr'cent : ∀ s ∈ R, (r' : G) * s = s * (r' : G) := by
      intro s hs
      have hsR₂ : s ∈ R₂ N 3 := hRR hs
      have hxs : x⁻¹ * s = s * x⁻¹ := by
        have := R₂_cent hctx s hsR₂ x⁻¹ (N.X₂.inv_mem hxX)
        calc x⁻¹ * s = (s * x⁻¹ * s⁻¹) * s := by rw [this]
          _ = s * x⁻¹ := by group
      rw [hr'eq]
      calc x⁻¹ * (y * (a : G) * y⁻¹ * (a : G)⁻¹) * s
          = x⁻¹ * ((y * (a : G) * y⁻¹ * (a : G)⁻¹) * s) := by group
        _ = x⁻¹ * (s * (y * (a : G) * y⁻¹ * (a : G)⁻¹)) := by rw [hcR s hs]
        _ = (x⁻¹ * s) * (y * (a : G) * y⁻¹ * (a : G)⁻¹) := by group
        _ = (s * x⁻¹) * (y * (a : G) * y⁻¹ * (a : G)⁻¹) := by rw [hxs]
        _ = s * (x⁻¹ * (y * (a : G) * y⁻¹ * (a : G)⁻¹)) := by group
    have hr'X : (r' : G) ∈ N.X₂ := hTS.R_center _ hr'R hr'cent
    rw [← hr'π]
    exact (hπ0 r').2 hr'X
  have hkr : LinearMap.range Nl ⊓ LinearMap.ker Nl = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [← hkerE] at hw
    exact (Submodule.mem_bot _).2 (hrE w hw.1 hw.2)
  have hNl0 : Nl = 0 := mx_nilp_eq_zero Nl hN3 hkr
  have hρ1 : ρ ⟨y, hyK⟩ = 1 := by
    have := sub_eq_zero.1 hNl0
    exact this
  have hy1'' : (⟨y, hyK⟩ : ↥N.K₁) = 1 := hinjρ (by rw [hρ1, map_one])
  exact hy1 (by simpa using congrArg Subtype.val hy1'')

end CFSG.GH74.GLS.Stage4.Rest
