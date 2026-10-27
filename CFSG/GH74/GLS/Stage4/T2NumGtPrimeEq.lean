module

public import CFSG.GH74.GLS.Stage4.T2NumGtOmega
public import CFSG.GH74.GLS.Stage4.T2NumGtSecSurj
public import CFSG.GH74.GLS.Stage4.T2NumGtDefs
public import CFSG.GH74.GLS.Stage4.T2NumGtRankDouble
public import CFSG.GH74.GLS.Stage4.T2NumGtArith
public import CFSG.GH74.GLS.Stage4.T2NumGtTwoPart
public import CFSG.GH74.GLS.Stage4.T2NumGtSL2CD
public import CFSG.GH74.GLS.Stage4.T6W.T6Rle
public import CFSG.GH74.GLS.Stage4.T6W.T6Sec

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.Stage4.Rest.T6W CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem ch6Gt_primeEq : Ch6GtP := by
  intro G _ _ Gs _ q₁ q₂ hlt hmod z K₁ K₂ F₁ F₂ _ _ t hSet hRem p n hp hp2 hq₂p N u hz hK₁ hK₂ hq₁ hq₂
    hCoord hSec y R hTS
  by_contra hnp
  push Not at hnp
  have hctx : T6CtxW N u p := t6CtxW_of hSet hRem hz hK₁ hK₂ hq₁ hq₂ hp hp2 ⟨n, hq₂p⟩ hCoord hSec
  have hn : N.q₂ = p ^ n := by rw [hq₂]; exact hq₂p
  have hloc := hSec.loc
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hp1 : 1 < p := hp.one_lt
  have h5 : 5 ≤ q₁ := hSet.five
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · have := hloc.q₂_ge; rw [hn, h0] at this; simp at this
    · exact h0
  have hq₂pos : 0 < N.q₂ := by have := hloc.q₂_ge; omega
  have hpq₁ : ¬ p ∣ q₁ := by
    intro hd
    have := hSet.finite₁
    have : Fintype F₁ := Fintype.ofFinite F₁
    obtain ⟨p₁, -, ⟨a, hp₁, hcard⟩⟩ := FiniteField.card' F₁
    have hq₁a : q₁ = p₁ ^ (a : ℕ) := by rw [← hSet.card₁, Nat.card_eq_fintype_card, hcard]
    rw [hq₁a] at hd
    have hpp : p ∣ p₁ := hp.dvd_of_dvd_pow hd
    have hpe : p = p₁ := (Nat.prime_dvd_prime_iff_eq hp hp₁).1 hpp
    exact hnp a (by rw [hq₁a, ← hpe])
  obtain ⟨F, iF, fF, φ, hcardF, hinj, hrange, hzφ, -, -, -, -⟩ := hctx.coord.coord₁
  obtain ⟨e₁, he₁⟩ := t6_coord_equiv hinj hrange hzφ hloc.z_mem_K₁
  obtain ⟨F', iF', fF', φ', hcardF', hinj', hrange', hzφ', -, -, -, -⟩ := hctx.coord.coord₂
  obtain ⟨e₂, he₂⟩ := t6_coord_equiv hinj' hrange' hzφ' hloc.z_mem_K₂
  have hFq : Nat.card F = q₁ := hcardF.trans hq₁
  have hodd : Odd (Nat.card F) := by rw [hFq]; exact hSet.odd₁
  have hF'p : Nat.card F' = p ^ n := hcardF'.trans hn
  have hFp : ¬ p ∣ Nat.card F := by rw [hFq]; exact hpq₁
  obtain ⟨Ω, hΩ⟩ := ng_omega_exists hctx
  have hΩR : Ω ≤ R₂ N p := fun r hr => ((hΩ r).1 hr).1
  have hX₂R := X₂_le_R₂ hctx
  have hXΩ : N.X₂ ≤ Ω := fun x hx => (hΩ x).2 ⟨hX₂R hx, N.X₂.pow_mem hx p⟩
  have hΩM : ∀ g ∈ M₂ N, ∀ r ∈ Ω, g * r * g⁻¹ ∈ Ω := fun g hg r hr => ng_omega_inv hΩ hg hr
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
  have hcle : Nat.card ↥(Ω ⊓ Subgroup.centralizer {u}) ≤ p ^ (n + 1) :=
    ng_Omega_u_card_le hctx hp hp2 hΩ e₁ e₂ hodd hF'p hFp
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
  have hfV : Module.finrank (ZMod p) V ≤ 2 * n + 2 := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rw [Nat.card_zmod, hVc] at h1
    have h2 : p ^ Module.finrank (ZMod p) V ≤ p ^ (2 * n + 2) := by
      rw [← h1]
      calc Nat.card ↥(Ω ⊓ Subgroup.centralizer {u}) ^ 2 ≤ (p ^ (n + 1)) ^ 2 :=
            Nat.pow_le_pow_left hcle 2
        _ = p ^ (2 * n + 2) := by rw [← pow_mul]; ring_nf
    exact (Nat.pow_le_pow_iff_right hp1).1 h2
  have hRR : R ≤ R₂ N p := R_le_R₂ hctx hTS.R_p hTS.R_cent hTS.R_inv
  have hRΩ : R ≤ Ω := fun r hr => (hΩ r).2 ⟨hRR hr, hTS.R_exp r hr⟩
  obtain ⟨Eadd, hE1, hE2, hEcard⟩ := ng_sec_image π hπ0 hπadd hTS.X_le hRΩ
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
    rw [hEc, hE3, hn, ← pow_mul] at h1
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
  have hF5 : 5 ≤ Nat.card F := by rw [hFq]; exact h5
  have hrank := l64_rank_double hp hp2 (K := ↥N.K₁) (F := F) ⟨hodd, by omega⟩ e₁
    (z := ⟨N.z, hzK⟩) he₁ ρ hρz hy1' hyodd' E hEfix
  have hn1' : n = 1 := by omega
  have hcross := sl2_cross_dim p hp hp2 F hodd hF5 hFp V (ρ.comp (e₁.symm : _ →* ↥N.K₁))
    (hinjρ.comp e₁.symm.injective)
  have h9 : q₁ ≤ 9 := by
    rw [hFq] at hcross
    have hodd₁ := hSet.odd₁
    rcases hodd₁ with ⟨k, hk⟩
    subst hn1'
    omega
  have hq₂p1 : q₂ = p := by rw [hq₂p, hn1', pow_one]
  have hv := t5_two_part_sq hSet
  rw [hq₂p1] at hv
  refine arith_P q₁ p hp hp2 h5 (by rw [← hq₂p1]; exact hlt) h9 (by rw [← hq₂p1]; exact hmod) hv ?_
  rintro ⟨m, hm⟩
  exact hnp m hm

end CFSG.GH74.GLS.Stage4.Rest
