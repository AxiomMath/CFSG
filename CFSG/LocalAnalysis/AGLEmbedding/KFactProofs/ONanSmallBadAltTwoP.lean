module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallInvolveWit
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanRankOneCoreData
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallBad.AltTwoP

open Equiv Equiv.Perm CFSG.AGLEmbedding.KFactProofs.RankOneCore

variable {p : ℕ}

@[expose] def base (f : Fin 2 → Perm (ZMod p)) : Perm (Fin 2 × ZMod p) := Equiv.prodCongrRight f

@[simp] theorem base_apply (f : Fin 2 → Perm (ZMod p)) (i : Fin 2) (z : ZMod p) :
    base f (i, z) = (i, f i z) := rfl

@[expose] def swapS : Perm (Fin 2 × ZMod p) :=
  Equiv.prodCongrLeft (fun _ => Equiv.swap (0 : Fin 2) 1)

@[simp] theorem swapS_apply (i : Fin 2) (z : ZMod p) :
    (swapS : Perm (Fin 2 × ZMod p)) (i, z) = (Equiv.swap (0 : Fin 2) 1 i, z) := rfl

@[expose] def trp (t₀ t₁ : ZMod p) : Perm (Fin 2 × ZMod p) :=
  base ![Equiv.addRight t₀, Equiv.addRight t₁]

@[expose] def bmul (c₀ c₁ : (ZMod p)ˣ) : Perm (Fin 2 × ZMod p) :=
  base ![Units.mulLeft c₀, Units.mulLeft c₁]

theorem trp_mul (s₀ s₁ t₀ t₁ : ZMod p) : trp s₀ s₁ * trp t₀ t₁ = trp (s₀ + t₀) (s₁ + t₁) := by
  ext ⟨i, z⟩ <;> fin_cases i <;> simp [trp, add_comm, add_left_comm]

theorem trp_zero : (trp 0 0 : Perm (Fin 2 × ZMod p)) = 1 := by
  ext ⟨i, z⟩ <;> fin_cases i <;> simp [trp]

theorem bmul_mul (c₀ c₁ d₀ d₁ : (ZMod p)ˣ) :
    bmul c₀ c₁ * bmul d₀ d₁ = bmul (c₀ * d₀) (c₁ * d₁) := by
  ext ⟨i, z⟩ <;> fin_cases i <;> simp [bmul, mul_assoc]

theorem bmul_one : (bmul 1 1 : Perm (Fin 2 × ZMod p)) = 1 := by
  ext ⟨i, z⟩ <;> fin_cases i <;> simp [bmul]

theorem bmul_inv (c₀ c₁ : (ZMod p)ˣ) : (bmul c₀ c₁ : Perm (Fin 2 × ZMod p))⁻¹ = bmul c₀⁻¹ c₁⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, bmul_mul]
  simp [bmul_one]

theorem bmul_comm (c₀ c₁ d₀ d₁ : (ZMod p)ˣ) :
    bmul c₀ c₁ * bmul d₀ d₁ = bmul d₀ d₁ * bmul c₀ c₁ := by
  rw [bmul_mul, bmul_mul, mul_comm c₀ d₀, mul_comm c₁ d₁]

theorem bmul_conj_trp (c₀ c₁ : (ZMod p)ˣ) (t₀ t₁ : ZMod p) :
    bmul c₀ c₁ * trp t₀ t₁ * (bmul c₀ c₁)⁻¹ = trp ((c₀ : ZMod p) * t₀) ((c₁ : ZMod p) * t₁) := by
  rw [bmul_inv]
  ext ⟨i, z⟩ <;> fin_cases i <;> simp [bmul, trp, mul_add]

theorem swapS_mul_self : (swapS : Perm (Fin 2 × ZMod p)) * swapS = 1 := by
  ext ⟨i, z⟩ <;> fin_cases i <;> simp

theorem swapS_inv : (swapS : Perm (Fin 2 × ZMod p))⁻¹ = swapS := by
  rw [inv_eq_iff_mul_eq_one]; exact swapS_mul_self

theorem swapS_conj_trp (t₀ t₁ : ZMod p) :
    swapS * trp t₀ t₁ * swapS⁻¹ = trp t₁ t₀ := by
  rw [swapS_inv]
  ext ⟨i, z⟩ <;> fin_cases i <;> simp [trp]

theorem swapS_conj_bmul (c₀ c₁ : (ZMod p)ˣ) :
    swapS * bmul c₀ c₁ * swapS⁻¹ = bmul c₁ c₀ := by
  rw [swapS_inv]
  ext ⟨i, z⟩ <;> fin_cases i <;> simp [bmul]

@[expose] def μ (p : ℕ) : (ZMod p)ˣ →* Perm (ZMod p) := MulAction.toPermHom (ZMod p)ˣ (ZMod p)

theorem μ_apply (u : (ZMod p)ˣ) (z : ZMod p) : μ p u z = (u : ZMod p) * z := rfl

theorem sign_μ_generator [Fact p.Prime] (hp2 : p ≠ 2) (g : (ZMod p)ˣ)
    (hg : ∀ u : (ZMod p)ˣ, u ∈ Subgroup.zpowers g) : sign (μ p g) = -1 := by
  have hp : p.Prime := Fact.out
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hg1 : (g : ZMod p) ≠ 1 := by
    intro h
    have hg1' : g = 1 := Units.ext h
    have : ∀ u : (ZMod p)ˣ, u = 1 := fun u => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg u)
      simp [hg1']
    have hcard : Fintype.card (ZMod p)ˣ = 1 := by
      rw [Fintype.card_eq_one_iff]
      exact ⟨1, this⟩
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hp] at hcard
    have := hp.two_le
    omega
  have hmove : ∀ y : ZMod p, μ p g y ≠ y ↔ y ≠ 0 := by
    intro y
    rw [μ_apply]
    constructor
    · rintro h rfl
      simp at h
    · intro hy h
      have : ((g : ZMod p) - 1) * y = 0 := by rw [sub_mul, h, one_mul, sub_self]
      rcases mul_eq_zero.mp this with h0 | h0
      · exact hg1 (sub_eq_zero.mp h0)
      · exact hy h0
  have hcyc : (μ p g).IsCycle := by
    refine ⟨1, ?_, ?_⟩
    · rw [μ_apply, mul_one]; exact hg1
    · intro y hy
      have hy0 : y ≠ 0 := (hmove y).mp hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg (Units.mk0 y hy0))
      refine ⟨k, ?_⟩
      have : ((μ p g) ^ k) 1 = ((g ^ k : (ZMod p)ˣ) : ZMod p) * 1 := by
        rw [← map_zpow, μ_apply]
      rw [this, hk]
      simp
  have hsupp : (μ p g).support = Finset.univ.erase 0 := by
    ext y
    simp [Equiv.Perm.mem_support, hmove]
  rw [hcyc.sign, hsupp, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    ZMod.card]
  obtain ⟨k, hk⟩ := hodd
  have : (-1 : ℤˣ) ^ (p - 1) = 1 := by
    rw [hk]
    simp [pow_mul]
  rw [this]

section Main

variable [Fact p.Prime]

theorem trp_pow (t₀ t₁ : ZMod p) (n : ℕ) :
    (trp t₀ t₁ : Perm (Fin 2 × ZMod p)) ^ n = trp (n • t₀) (n • t₁) := by
  induction n with
  | zero => simpa using trp_zero.symm
  | succ n ih =>
    rw [pow_succ, ih, trp_mul, succ_nsmul, succ_nsmul]

theorem trp_eq_pow (t₀ t₁ : ZMod p) :
    (trp t₀ t₁ : Perm (Fin 2 × ZMod p)) =
      (trp 1 0 : Perm (Fin 2 × ZMod p)) ^ t₀.val * (trp 0 1) ^ t₁.val := by
  rw [trp_pow, trp_pow, trp_mul]
  simp

theorem trp_apply_zero (t₀ t₁ z : ZMod p) :
    (trp t₀ t₁ : Perm (Fin 2 × ZMod p)) (0, z) = (0, z + t₀) :=
  rfl

theorem trp_apply_one (t₀ t₁ z : ZMod p) :
    (trp t₀ t₁ : Perm (Fin 2 × ZMod p)) (1, z) = (1, z + t₁) :=
  rfl

theorem sign_eq_one_of_pow_eq_one (hp2 : p ≠ 2) {σ : Perm (Fin 2 × ZMod p)} (h : σ ^ p = 1) :
    sign σ = 1 := by
  have hp : p.Prime := Fact.out
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have h1 : sign σ ^ p = 1 := by rw [← map_pow, h, map_one]
  rcases Int.units_eq_one_or (sign σ) with h2 | h2
  · exact h2
  · rw [h2, hodd.neg_one_pow] at h1
    exact absurd h1 (by decide)

theorem sign_trp (hp2 : p ≠ 2) (t₀ t₁ : ZMod p) : sign (trp t₀ t₁ : Perm (Fin 2 × ZMod p)) = 1 := by
  refine sign_eq_one_of_pow_eq_one hp2 ?_
  rw [trp_pow]
  simp [← trp_zero]

theorem sign_swapS (hp2 : p ≠ 2) : sign (swapS : Perm (Fin 2 × ZMod p)) = -1 := by
  have hp : p.Prime := Fact.out
  have hodd : Odd p := hp.odd_of_ne_two hp2
  unfold swapS
  rw [sign_prodCongrLeft]
  simp [hodd.neg_one_pow, ZMod.card]

theorem sign_bmul (c₀ c₁ : (ZMod p)ˣ) :
    sign (bmul c₀ c₁ : Perm (Fin 2 × ZMod p)) = sign (μ p c₀) * sign (μ p c₁) := by
  unfold bmul
  rw [show (Units.mulLeft c₀ : Perm (ZMod p)) = μ p c₀ from rfl,
    show (Units.mulLeft c₁ : Perm (ZMod p)) = μ p c₁ from rfl, base, sign_prodCongrRight]
  simp [Fin.prod_univ_two]

theorem padic_fact (hp3 : 3 ≤ p) : padicValNat p ((2 * p).factorial) = 2 := by
  have hlog : Nat.log p (2 * p) < 2 := by
    apply Nat.log_lt_of_lt_pow (by omega)
    nlinarith
  rw [padicValNat_factorial hlog]
  have h1 : 2 * p / p = 2 := Nat.mul_div_cancel _ (by omega)
  simp [h1]

theorem card_alt_aux (hp5 : 5 ≤ p) :
    ∃ m, Nat.card (alternatingGroup (Fin 2 × ZMod p)) = p ^ 2 * m ∧ ¬ p ∣ m := by
  have hp : p.Prime := Fact.out
  have hcard : Nat.card (alternatingGroup (Fin 2 × ZMod p)) = (2 * p).factorial / 2 := by
    rw [nat_card_alternatingGroup]
    simp [ZMod.card]
  have hdvd : 2 ∣ (2 * p).factorial := Nat.dvd_factorial (by norm_num) (by omega)
  obtain ⟨N, hN⟩ := hdvd
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact (Nat.factorial_pos _).ne' (by simpa using hN)
  have hdiv : (2 * p).factorial / 2 = N := by omega
  rw [hcard, hdiv]
  obtain ⟨e, m, hm, hNe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0 p hp.ne_one
  have hv : padicValNat p ((2 * p).factorial) = 2 := padic_fact (by omega)
  have hv2 : padicValNat p ((2 * p).factorial) = e := by
    rw [hN, padicValNat.mul (by norm_num) hN0, hNe, padicValNat.mul (pow_ne_zero _ hp.ne_zero)
      (by rintro rfl; simp at hNe; omega),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hm,
      padicValNat.eq_zero_of_not_dvd (by
        intro h
        have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h
        omega)]
    simp
  have he : e = 2 := by omega
  exact ⟨m, by rw [hNe, he], hm⟩

theorem trp_pow_prime (t₀ t₁ : ZMod p) : (trp t₀ t₁ : Perm (Fin 2 × ZMod p)) ^ p = 1 := by
  rw [trp_pow]
  simp [← trp_zero]

theorem trp_pow_mul_pow (i j : ℕ) :
    (trp 1 0 : Perm (Fin 2 × ZMod p)) ^ i * (trp 0 1) ^ j = trp (i : ZMod p) (j : ZMod p) := by
  rw [trp_pow, trp_pow, trp_mul]
  simp

theorem xinv_conj (c : (ZMod p)ˣ) (t₀ t₁ : ZMod p) :
    (bmul c c⁻¹)⁻¹ * trp t₀ t₁ * bmul c c⁻¹ =
      trp (((c⁻¹ : (ZMod p)ˣ) : ZMod p) * t₀) ((c : ZMod p) * t₁) := by
  have h := bmul_conj_trp c⁻¹ c t₀ t₁
  rw [bmul_inv, inv_inv] at h
  rw [bmul_inv, inv_inv]
  exact h

theorem y_conj (g : (ZMod p)ˣ) (t₀ t₁ : ZMod p) :
    (swapS * bmul g 1) * trp t₀ t₁ * (swapS * bmul g 1)⁻¹ = trp t₁ ((g : ZMod p) * t₀) := by
  have h : (swapS * bmul g 1) * trp t₀ t₁ * (swapS * bmul g 1)⁻¹ =
      swapS * (bmul g 1 * trp t₀ t₁ * (bmul g 1)⁻¹) * swapS⁻¹ := by
    simp only [mul_inv_rev, mul_assoc]
  rw [h, bmul_conj_trp, swapS_conj_trp]
  simp

theorem yinv_conj (g : (ZMod p)ˣ) (t₀ t₁ : ZMod p) :
    (swapS * bmul g 1)⁻¹ * trp t₀ t₁ * (swapS * bmul g 1) =
      trp (((g⁻¹ : (ZMod p)ˣ) : ZMod p) * t₁) t₀ := by
  have h := bmul_conj_trp g⁻¹ 1 t₁ t₀
  have h2 := swapS_conj_trp (p := p) t₀ t₁
  rw [bmul_inv, inv_inv, inv_one] at h
  rw [← h2] at h
  have h3 : (swapS * bmul g 1)⁻¹ * trp t₀ t₁ * (swapS * bmul g 1) =
      bmul g⁻¹ 1 * (swapS * trp t₀ t₁ * swapS⁻¹) * bmul g 1 := by
    rw [mul_inv_rev, bmul_inv, inv_one, swapS_inv]
    simp only [mul_assoc]
  rw [h3, h, Units.val_one, one_mul]

theorem comm_xy (c g : (ZMod p)ˣ) :
    bmul c c⁻¹ * (swapS * bmul g 1) * (bmul c c⁻¹)⁻¹ * (swapS * bmul g 1)⁻¹ =
      bmul (c * c) (c⁻¹ * c⁻¹) := by
  have hx' : (bmul c c⁻¹)⁻¹ = bmul c⁻¹ c := by rw [bmul_inv, inv_inv]
  have hc : bmul g 1 * bmul c⁻¹ c = bmul c⁻¹ c * bmul g 1 := bmul_comm _ _ _ _
  have hsw : swapS * bmul c⁻¹ c * swapS⁻¹ = bmul c c⁻¹ := swapS_conj_bmul _ _
  calc bmul c c⁻¹ * (swapS * bmul g 1) * (bmul c c⁻¹)⁻¹ * (swapS * bmul g 1)⁻¹
      = bmul c c⁻¹ * (swapS * (bmul g 1 * bmul c⁻¹ c * (bmul g 1)⁻¹) * swapS⁻¹) := by
        rw [hx']; simp only [mul_inv_rev, mul_assoc]
    _ = bmul c c⁻¹ * (swapS * bmul c⁻¹ c * swapS⁻¹) := by
        rw [hc, mul_inv_cancel_right]
    _ = bmul c c⁻¹ * bmul c c⁻¹ := by rw [hsw]
    _ = bmul (c * c) (c⁻¹ * c⁻¹) := bmul_mul _ _ _ _

theorem sign_bmul_diag (c : (ZMod p)ˣ) : sign (bmul c c⁻¹ : Perm (Fin 2 × ZMod p)) = 1 := by
  rw [sign_bmul, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]

theorem sign_swapS_bmul (hp2 : p ≠ 2) (g : (ZMod p)ˣ)
    (hg : ∀ u : (ZMod p)ˣ, u ∈ Subgroup.zpowers g) :
    sign (swapS * bmul g 1 : Perm (Fin 2 × ZMod p)) = 1 := by
  rw [map_mul, sign_swapS hp2, sign_bmul, sign_μ_generator hp2 g hg, map_one, map_one]
  decide

theorem nat_eq_of_cast {i i' : ℕ} (hi : i < p) (hi' : i' < p) (h : (i : ZMod p) = i') :
    i = i' := by
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] at this

theorem not_normalizerQuotientComm_alt_aux (hp2 : p ≠ 2) (c g : (ZMod p)ˣ)
    (hg : ∀ u : (ZMod p)ˣ, u ∈ Subgroup.zpowers g) (hc : (c : ZMod p) * c ≠ 1) {m : ℕ}
    (hM : Nat.card (alternatingGroup (Fin 2 × ZMod p)) = p ^ 2 * m) (hm : ¬ p ∣ m) :
    ¬ NormalizerQuotientComm p (alternatingGroup (Fin 2 × ZMod p)) := by
  classical
  refine not_normalizerQuotientComm_of_elemAbelian (alternatingGroup (Fin 2 × ZMod p)) hM hm
    (trp 1 0) (trp 0 1) (bmul c c⁻¹) (swapS * bmul g 1) ?_ ?_ ?_ ?_ ?_ (trp_pow_prime _ _)
    (trp_pow_prime _ _) ?_ ?_ ?_ ?_
  · exact mem_alternatingGroup.mpr (sign_trp hp2 _ _)
  · exact mem_alternatingGroup.mpr (sign_trp hp2 _ _)
  · exact mem_alternatingGroup.mpr (sign_bmul_diag _)
  · exact mem_alternatingGroup.mpr (sign_swapS_bmul hp2 g hg)
  · rw [trp_mul, trp_mul]
    simp [add_comm]
  · intro i hi j hj i' hi' j' hj' h
    rw [trp_pow_mul_pow, trp_pow_mul_pow] at h
    have h0 := congrArg (fun σ : Perm (Fin 2 × ZMod p) => (σ (0, 0)).2) h
    have h1 := congrArg (fun σ : Perm (Fin 2 × ZMod p) => (σ (1, 0)).2) h
    simp only [trp_apply_zero, trp_apply_one, zero_add] at h0 h1
    exact ⟨nat_eq_of_cast hi hi' h0, nat_eq_of_cast hj hj' h1⟩
  · exact ⟨⟨_, _, (bmul_conj_trp c c⁻¹ 1 0).trans (trp_eq_pow _ _)⟩,
      ⟨_, _, (bmul_conj_trp c c⁻¹ 0 1).trans (trp_eq_pow _ _)⟩,
      ⟨_, _, (xinv_conj c 1 0).trans (trp_eq_pow _ _)⟩,
      ⟨_, _, (xinv_conj c 0 1).trans (trp_eq_pow _ _)⟩⟩
  · exact ⟨⟨_, _, (y_conj g 1 0).trans (trp_eq_pow _ _)⟩,
      ⟨_, _, (y_conj g 0 1).trans (trp_eq_pow _ _)⟩,
      ⟨_, _, (yinv_conj g 1 0).trans (trp_eq_pow _ _)⟩,
      ⟨_, _, (yinv_conj g 0 1).trans (trp_eq_pow _ _)⟩⟩
  · intro i hi j hj h
    rw [comm_xy, trp_pow_mul_pow] at h
    have h0 : (i : ZMod p) = 0 := by
      have := congrArg (fun σ : Perm (Fin 2 × ZMod p) => (σ (0, 0)).2) h
      simpa [bmul, trp] using this.symm
    have h1 : (c : ZMod p) * c = 1 := by
      have := congrArg (fun σ : Perm (Fin 2 × ZMod p) => (σ (0, 1)).2) h
      simpa [bmul, trp, h0] using this
    exact hc h1

theorem not_normalizerQuotientComm_alt (hp5 : 5 ≤ p) :
    ¬ NormalizerQuotientComm p (alternatingGroup (Fin 2 × ZMod p)) := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 p).mp h')
    omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  obtain ⟨m, hM, hm⟩ := card_alt_aux hp5
  refine not_normalizerQuotientComm_alt_aux hp2 (Units.mk0 2 h2) g hg ?_ hM hm
  intro h
  have h3 : ((3 : ℕ) : ZMod p) = 0 := by
    rw [Units.val_mk0] at h
    push_cast
    linear_combination h
  have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 3 p).mp h3)
  omega

end Main

theorem not_normalizerQuotientComm_altTwoP {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {L : Type}
    [Group L] [Finite L] (_ : IsSimpleGroup L) (hL : IsAltTwoP p L) :
    ¬ NormalizerQuotientComm p L := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := hL
  have hcard : Fintype.card (Fin 2 × ZMod p) = Fintype.card (Fin (2 * p)) := by
    simp [ZMod.card]
  let σ : (Fin 2 × ZMod p) ≃ Fin (2 * p) := Fintype.equivOfCardEq hcard
  intro h
  exact not_normalizerQuotientComm_alt hp5 (h.of_mulEquiv (e.trans σ.symm.altCongrHom))

end CFSG.AGLEmbedding.KFactProofs.SmallBad.AltTwoP
