module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL2Field

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Sylow

variable {K : Type} [Group K] [Finite K]

theorem mem_of_normalizes_card_three {C X : Subgroup K} (hXC : X ≤ C) (hC : Nat.card ↥C = 24)
    (hX : Nat.card ↥X = 3) {u : K} (huC : u ∈ C) (hu : orderOf u = 3)
    (hN : u ∈ normalizer (X : Set K)) : u ∈ X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X' : Subgroup ↥C := X.subgroupOf C with hX'
  have hX'card : Nat.card ↥X' = 3 := by
    rw [← hX]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXC).toEquiv
  have hfac : (Nat.factorization 24) 3 = 1 := by decide +kernel
  let Q : Sylow 3 ↥C := Sylow.ofCard X' (by rw [hX'card, hC, hfac]; norm_num)
  have hQ : (Q : Subgroup ↥C) = X' := rfl
  set u' : ↥C := ⟨u, huC⟩ with hu'
  have hu'ord : orderOf u' = 3 := by
    rw [hu', Subgroup.orderOf_mk]
    exact hu
  have hP : IsPGroup 3 ↥(Subgroup.zpowers u') := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, hu'ord]
    exact ⟨1, by norm_num⟩
  have hnorm : u' ∈ normalizer (X' : Set ↥C) := by
    rw [Subgroup.mem_normalizer_iff] at hN ⊢
    intro g
    have := hN (g : K)
    rw [hX', Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa [hu'] using this
  have hle : Subgroup.zpowers u' ≤ normalizer (Q : Set ↥C) := by
    rw [Subgroup.zpowers_le]
    exact hnorm
  have hmem : u' ∈ Subgroup.zpowers u' ⊓ normalizer (Q : Set ↥C) :=
    ⟨Subgroup.mem_zpowers u', hle (Subgroup.mem_zpowers u')⟩
  rw [hP.inf_normalizer_sylow Q] at hmem
  have h2 : u' ∈ (Q : Subgroup ↥C) := hmem.2
  rw [hQ, hX', Subgroup.mem_subgroupOf] at h2
  exact h2

end Sylow

section Matrices

variable {F : Type} [Field F]

theorem kaSlU_pow_three (h3 : (3 : F) = 0) :
    (kaSlU : Matrix.SpecialLinearGroup (Fin 2) F) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, pow_succ, pow_succ, pow_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kaSlU, Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination h3

theorem kaSlL_pow_three (h3 : (3 : F) = 0) :
    (kaSlL : Matrix.SpecialLinearGroup (Fin 2) F) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, pow_succ, pow_succ, pow_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kaSlL, Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination h3

theorem kaSl_not_central (ζ : Matrix.SpecialLinearGroup (Fin 2) F)
    (hζ : (kaSlU : Matrix.SpecialLinearGroup (Fin 2) F) * kaSlL = kaSlL * kaSlU * ζ)
    (hc : (kaSlU : Matrix.SpecialLinearGroup (Fin 2) F) * ζ = ζ * kaSlU) : False := by
  have hU : ((kaSlU : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![1, 1; 0, 1] := rfl
  have hL : ((kaSlL : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![1, 0; 1, 1] := rfl
  have h1 := congrArg
    (fun A : Matrix.SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F)) hζ
  have h2 := congrArg
    (fun A : Matrix.SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F)) hc
  simp only [Matrix.SpecialLinearGroup.coe_mul, hU, hL] at h1 h2
  have e1 := congrFun (congrFun h1 0) 0
  have e2 := congrFun (congrFun h1 1) 0
  have e3 := congrFun (congrFun h2 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e1 e2 e3
  apply one_ne_zero (α := F)
  linear_combination e1 - e2 - e3

end Matrices

section Nine

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem kaL2_no_hyp_nine (hF : L2Field F) (e : K ≃* L2 F) (σ₀ : F ≃+* F)
    (hσ₀ : orderOf σ₀ = 2) (h3 : Nat.card (fixedField σ₀) = 3) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {P : Subgroup (MulAut K)} (hP : KAHyp (fieldAutHom e σ₀) p P) : False := by
  obtain ⟨hPp, hP1, hcomm, hnorm⟩ := hP
  have h9 : Nat.card F = 9 := by
    have := fixedField_card_pow σ₀
    rw [hσ₀, h3] at this
    omega
  have hinn : ∀ e' ∈ P, e' ∈ innAut K := by
    intro e' he'
    obtain ⟨g, τ, hdec, hτord⟩ := kaL2_aut_decomp e e'
    have hodd' := ka_odd_of_mem_pGroup hp hp2 hPp he'
    have hτ1 : τ = 1 := kaL2_aut_nine h9 τ (Odd.of_dvd_nat hodd' hτord)
    have hmem : e' ∈ innDiagSub e := by
      rw [hdec, hτ1, map_one, mul_one]
      exact ⟨g, rfl⟩
    exact kaL2_odd_mem_innAut hF e hmem hodd'
  have hcard : Nat.card ↥(fixedSubgroup K (fieldAutHom e σ₀)) = 24 := by
    rw [card_fixedSubgroup_of_even e σ₀ (by rw [hσ₀]; exact even_two), h3]
    norm_num
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := conj_injective_of_L2 e
  have hX0p := kaInner_isPGroup hinj hPp
  have hX0C : kaInner P ≤ fixSub (fieldAutHom e σ₀) := kaInner_le_fixSub hinj hcomm
  have hX0ne : kaInner P ≠ ⊥ := by
    intro hbot
    apply hP1
    rw [eq_bot_iff]
    intro e' he'
    obtain ⟨y, hy⟩ := hinn e' he'
    have hyX : y ∈ kaInner P := by rw [mem_kaInner, hy]; exact he'
    rw [hbot, Subgroup.mem_bot] at hyX
    rw [← hy, hyX, map_one]
    exact Subgroup.one_mem _
  have hX0card : Nat.card ↥(kaInner P) = 3 := by
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨m, hm⟩ := hX0p.exists_card_eq
    have hdvd : Nat.card ↥(kaInner P) ∣ 24 := by
      rw [← hcard]
      exact Subgroup.card_dvd_of_le hX0C
    rw [hm] at hdvd
    have hc8 : Nat.Coprime (p ^ m) (2 ^ 3) :=
      Nat.Coprime.pow m 3 ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    have h3' : p ^ m ∣ 3 := hc8.dvd_of_dvd_mul_left (by simpa using hdvd)
    rcases (Nat.dvd_prime Nat.prime_three).mp h3' with h | h
    · exfalso
      exact hX0ne (Subgroup.eq_bot_of_card_eq _ (by rw [hm, h]))
    · rw [hm, h]
  have h3F : (3 : F) = 0 := by
    have hF9 : (9 : F) = 0 := by
      have : Fintype F := Fintype.ofFinite F
      have h' := Nat.cast_card_eq_zero F
      rw [← Nat.card_eq_fintype_card, h9] at h'
      exact_mod_cast h'
    have : (3 : F) * 3 = 0 := by linear_combination hF9
    exact mul_self_eq_zero.mp this
  set u : K := kaL2Cover e kaSlU with hu
  set l : K := kaL2Cover e kaSlL with hl
  have huC : u ∈ fixSub (fieldAutHom e σ₀) := by
    rw [mem_fixSub, hu, kaL2Cover_field, mem_kaFix.mp (kaSlU_mem σ₀)]
  have hlC : l ∈ fixSub (fieldAutHom e σ₀) := by
    rw [mem_fixSub, hl, kaL2Cover_field, mem_kaFix.mp (kaSlL_mem σ₀)]
  have hnc : u * l ≠ l * u := by
    intro h
    have hker : (kaSlL * kaSlU)⁻¹ * (kaSlU * kaSlL) ∈ (kaL2Cover e).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, ← hu, ← hl, h]
      group
    have hcen := kaL2Cover_central e _ hker kaSlU
    refine kaSl_not_central ((kaSlL * kaSlU)⁻¹ * (kaSlU * kaSlL)) ?_ hcen
    group
  have hu1 : u ≠ 1 := fun h1 => hnc (by rw [h1, one_mul, mul_one])
  have hl1 : l ≠ 1 := fun h1 => hnc (by rw [h1, one_mul, mul_one])
  have hu3 : u ^ 3 = 1 := by rw [hu, ← map_pow, kaSlU_pow_three h3F, map_one]
  have hl3 : l ^ 3 = 1 := by rw [hl, ← map_pow, kaSlL_pow_three h3F, map_one]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have huo : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hlo : orderOf l = 3 := orderOf_eq_prime hl3 hl1
  have hN3 : ∀ c, c ∈ fixSub (fieldAutHom e σ₀) → orderOf c = 3 → c ∈ kaInner P := by
    intro c hc hco
    have hN := hnorm c hc (by rw [hco]; decide)
    exact mem_of_normalizes_card_three hX0C hcard hX0card hc hco (mem_normalizer_kaInner hN)
  have huX := hN3 u huC huo
  have hlX := hN3 l hlC hlo
  have : IsCyclic ↥(kaInner P) := isCyclic_of_prime_card hX0card
  have hcomm' : (⟨u, huX⟩ : ↥(kaInner P)) * ⟨l, hlX⟩ = ⟨l, hlX⟩ * ⟨u, huX⟩ :=
    IsMulCommutative.is_comm.comm _ _
  exact hnc (congrArg Subtype.val hcomm')

end Nine

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K2
