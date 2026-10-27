module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2Offender

public section

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG CFSG.GorensteinWalter

section OddOrder

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Module.Finite (ZMod 2) E]

theorem orderOf_dvd_card_aut_of_odd (g : E ≃ₗ[ZMod 2] E) (hodd : Odd (orderOf g)) :
    orderOf g ∣ ∏ i : Fin (Module.finrank (ZMod 2)
        (LinearMap.range ((g : E →ₗ[ZMod 2] E) - LinearMap.id))),
      (2 ^ Module.finrank (ZMod 2) (LinearMap.range ((g : E →ₗ[ZMod 2] E) - LinearMap.id)) -
        2 ^ (i : ℕ)) := by
  set D : E →ₗ[ZMod 2] E := (g : E →ₗ[ZMod 2] E) - LinearMap.id with hD
  set N : Submodule (ZMod 2) E := LinearMap.ker D with hN
  have hmem : ∀ x, x ∈ N ↔ g x = x := fun x => by
    rw [hN, LinearMap.mem_ker, hD, LinearMap.sub_apply, sub_eq_zero]
    rfl
  have hgN : N.map (g : E →ₗ[ZMod 2] E) = N := by
    refine le_antisymm ?_ fun x hx => ⟨x, hx, (hmem x).1 hx⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [LinearEquiv.coe_coe, (hmem x).1 hx]
    exact hx
  let ĝ : (E ⧸ N) ≃ₗ[ZMod 2] (E ⧸ N) := Submodule.Quotient.equiv N N g hgN
  have hĝ : ∀ x : E, ĝ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (g x) := fun x => rfl
  have hpow : ∀ (j : ℕ) (x : E), (ĝ ^ j) (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((g ^ j) x) := by
    intro j
    induction j with
    | zero => intro x; rfl
    | succ j ih =>
      intro x
      rw [pow_succ, LinearEquiv.mul_apply, hĝ, ih, pow_succ, LinearEquiv.mul_apply]
  have hfixpow : ∀ (j : ℕ), ∀ y ∈ N, (g ^ j) y = y := by
    intro j
    induction j with
    | zero => intro y _; rfl
    | succ j ih =>
      intro y hy
      rw [pow_succ, LinearEquiv.mul_apply, (hmem y).1 hy, ih y hy]
  have hsq : ∀ j : ℕ, ĝ ^ j = 1 → g ^ (2 * j) = 1 := by
    intro j hj
    ext x
    have h1 : (g ^ j) x - x ∈ N := by
      have := congrArg (fun f : (E ⧸ N) ≃ₗ[ZMod 2] (E ⧸ N) => f (Submodule.Quotient.mk x)) hj
      simp only [hpow, LinearEquiv.coe_one, id_eq] at this
      exact (Submodule.Quotient.eq N).1 this
    have h2 : (g ^ j) ((g ^ j) x - x) = (g ^ j) x - x := hfixpow j _ h1
    rw [map_sub] at h2
    have h3 : (g ^ j) ((g ^ j) x) = x := by
      have hy2 : (g ^ j) x + (g ^ j) x = 0 := add_self_eq_zero_of_zmod_two _
      have hx2 : x + x = 0 := add_self_eq_zero_of_zmod_two x
      have h4 : (g ^ j) ((g ^ j) x) = (g ^ j) x - x + (g ^ j) x := by
        rw [← h2]
        abel
      rw [h4]
      calc (g ^ j) x - x + (g ^ j) x = ((g ^ j) x + (g ^ j) x) - x := by abel
        _ = -x := by rw [hy2, zero_sub]
        _ = x := by rw [neg_eq_iff_add_eq_zero]; exact hx2
    rw [pow_mul', pow_two, LinearEquiv.mul_apply, h3]
    rfl
  have hodd2 : ∀ j : ℕ, ĝ ^ j = 1 → g ^ j = 1 := by
    intro j hj
    have hd : orderOf g ∣ 2 * j := orderOf_dvd_of_pow_eq_one (hsq j hj)
    have hcop : Nat.Coprime (orderOf g) 2 := Nat.coprime_two_right.2 hodd
    exact orderOf_dvd_iff_pow_eq_one.1 (hcop.dvd_of_dvd_mul_left hd)
  have hdvd1 : orderOf g ∣ orderOf ĝ :=
    orderOf_dvd_of_pow_eq_one (hodd2 _ (pow_orderOf_eq_one ĝ))
  have hdvd2 : orderOf ĝ ∣ Nat.card ((E ⧸ N) ≃ₗ[ZMod 2] (E ⧸ N)) := orderOf_dvd_natCard ĝ
  have hfin : Module.finrank (ZMod 2) (E ⧸ N) = Module.finrank (ZMod 2) (LinearMap.range D) := by
    have hrn := LinearMap.finrank_range_add_finrank_ker D
    have hq := Submodule.finrank_quotient_add_finrank N
    rw [← hN] at hrn
    omega
  have hcard := card_automorphisms_binary (W := E ⧸ N)
    (n := Module.finrank (ZMod 2) (E ⧸ N)) rfl
  rw [hfin] at hcard
  rw [hcard] at hdvd2
  exact hdvd1.trans hdvd2

end OddOrder

theorem card_GL_dvd_of_le_four {k : ℕ} (hk : k ≤ 4) :
    (∏ i : Fin k, (2 ^ k - 2 ^ (i : ℕ))) ∣ 20160 := by
  interval_cases k <;> simp [Fin.prod_univ_succ]

theorem not_dvd_of_square {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : ¬ ((p ^ 2 + 1) / 2 ∣ 20160) := by
  intro h
  have hle : (p ^ 2 + 1) / 2 ≤ 20160 := Nat.le_of_dvd (by norm_num) h
  have hp200 : p ≤ 200 := by
    by_contra hcon
    push Not at hcon
    have : 201 * 201 ≤ p ^ 2 := by nlinarith
    omega
  interval_cases p <;> first | (norm_num at hp; done) | norm_num at h

theorem psl2_square_inner_involution_rank {p : ℕ} [hpf : Fact p.Prime] (hp5 : 5 ≤ p) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = p ^ 2) {E : Type*} [AddCommGroup E]
    [Module (ZMod 2) E] [Module.Finite (ZMod 2) E] (ρ : PSL2 K →* (E ≃ₗ[ZMod 2] E))
    (hρ : Function.Injective ρ) {t : PSL2 K} (ht1 : t ≠ 1) (ht2 : t * t = 1) :
    3 ≤ Module.finrank (ZMod 2) (LinearMap.range (disp ρ t)) := by
  have hp : p.Prime := hpf.out
  have hp2 : p ≠ 2 := by omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hKodd : IsOddPrimePower (Nat.card K) := ⟨p, 2, hp, hodd, by norm_num, hK⟩
  obtain ⟨S, hScyc, hScard, -, ⟨w, -, hwS, hw2, hinv, -, -⟩, -⟩ :=
    Glauberman.Dickson.h84_nonsplit_torus_data (F := K) (p := p) (f := 2) hK
  have hw1 : w ≠ 1 := by
    rintro rfl
    exact hwS S.one_mem
  obtain ⟨g, hg⟩ := psl2_involutions_conjugate_of_odd_prime_power K hKodd t w
    ⟨ht1, by rw [pow_two]; exact ht2⟩ ⟨hw1, by rw [pow_two]; exact hw2⟩
  have hrank_t : Module.finrank (ZMod 2) (LinearMap.range (disp ρ t)) =
      Module.finrank (ZMod 2) (LinearMap.range (disp ρ w)) := by
    rw [← hg]
    exact (finrank_range_disp_conj ρ t g).symm
  rw [hrank_t]
  by_contra hlt
  push Not at hlt
  have hgcd : Nat.gcd (Nat.card K - 1) 2 = 2 := by
    rw [hK]
    exact gcd_sub_one_two_of_odd' (hodd.pow (n := 2))
  have hm : Nat.card S = (p ^ 2 + 1) / 2 := by
    rw [hScard, hK, ← hK, hgcd, hK]
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := S)
  have hxord : orderOf (x : PSL2 K) = (p ^ 2 + 1) / 2 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hx, hm]
  have hmodd : Odd ((p ^ 2 + 1) / 2) := by
    obtain ⟨k, hk⟩ := hodd
    have h1 : p ^ 2 + 1 = 2 * (2 * k * k + 2 * k + 1) := by subst hk; ring
    rw [h1, Nat.mul_div_cancel_left _ (by norm_num)]
    exact ⟨k * k + k, by ring⟩
  have hwx : w * (x : PSL2 K) * w = (x : PSL2 K)⁻¹ := by
    have := hinv x x.2
    rwa [inv_eq_of_mul_eq_one_right hw2] at this
  set c : PSL2 K := w * ((x : PSL2 K) * w * (x : PSL2 K)⁻¹) with hc
  have hcx : c = ((x : PSL2 K) ^ 2)⁻¹ := by
    have h1 : c = (w * (x : PSL2 K) * w) * (x : PSL2 K)⁻¹ := by rw [hc]; group
    rw [h1, hwx, pow_two, mul_inv_rev]
  have hcord : orderOf c = (p ^ 2 + 1) / 2 := by
    rw [hcx, orderOf_inv, orderOf_pow' _ (by norm_num), hxord]
    have : Nat.gcd ((p ^ 2 + 1) / 2) 2 = 1 := (Nat.coprime_two_right.2 hmodd)
    rw [this, Nat.div_one]
  have hrank_c : Module.finrank (ZMod 2) (LinearMap.range (disp ρ c)) ≤ 4 := by
    have h1 := finrank_range_disp_mul_le ρ w ((x : PSL2 K) * w * (x : PSL2 K)⁻¹)
    have h2 := finrank_range_disp_conj ρ w (x : PSL2 K)
    rw [← hc] at h1
    omega
  have hρc : orderOf (ρ c) = (p ^ 2 + 1) / 2 := by rw [orderOf_injective ρ hρ c, hcord]
  have hdvd := orderOf_dvd_card_aut_of_odd (E := E) (ρ c) (by rw [hρc]; exact hmodd)
  rw [hρc] at hdvd
  exact not_dvd_of_square hp hp5
    (hdvd.trans (card_GL_dvd_of_le_four hrank_c))

end CFSG.QuasithinUnique.Setup.Family
