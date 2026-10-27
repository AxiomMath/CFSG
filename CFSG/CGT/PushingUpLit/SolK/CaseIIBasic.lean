module

public import CFSG.CGT.PushingUpLit.SolK.RSmallI

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)

theorem mem_of_pow_mem_of_coprime {G : Type*} [Group G] (H : Subgroup G) {y : G} {a b : ℕ}
    (hab : Nat.Coprime a b) (ha : y ^ a ∈ H) (hb : y ^ b ∈ H) : y ∈ H := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hab
  have h1 : y = y ^ ((a : ℤ) * u + (b : ℤ) * v) := by
    have : (a : ℤ) * u + (b : ℤ) * v = 1 := by linarith [huv]
    rw [this, zpow_one]
  rw [h1, zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
  exact H.mul_mem (H.zpow_mem ha u) (H.zpow_mem hb v)

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : SolCfg G M X n)

namespace SolCfg

include S

omit [Finite G] S in
theorem X_comm_R {x r : G} (hx : x ∈ X) (hr : r ∈ rOf M X) : x * r * x⁻¹ = r := by
  have := Subgroup.mem_centralizer_iff.1 hr.2 x hx
  rw [this]
  group

theorem comm_R_of_two_alt (hP : TightDataPlus S) {p : G} (hpM : p ∈ M)
    (hp2 : ∃ j : ℕ, p ^ (2 ^ j) = 1)
    (hpa : S.θ ⟨p, hpM⟩ ∈ alternatingGroup (Fin (2 * n + 1))) {r : G} (hr : r ∈ rOf M X) :
    p * r * p⁻¹ = r := by
  classical
  obtain ⟨j, hj⟩ := hp2
  obtain ⟨x, hx⟩ := S.D.ρ_surj _ hpa
  have hxM : (x : G) ∈ M := S.hyp.le x.2
  have hθx : S.θ ⟨(x : G), hxM⟩ = S.θ ⟨p, hpM⟩ := by
    rw [S.θ_X x]
    exact hx
  set d : G := (x : G)⁻¹ * p with hd
  have hdM : d ∈ M := M.mul_mem (M.inv_mem hxM) hpM
  have hdmk : (⟨d, hdM⟩ : ↥M) = (⟨(x : G), hxM⟩ : ↥M)⁻¹ * ⟨p, hpM⟩ := rfl
  have hθd : S.θ ⟨d, hdM⟩ = 1 := by
    rw [hdmk, map_mul, map_inv, hθx, inv_mul_cancel]
  have hpd : p = (x : G) * d := by
    rw [hd]
    group
  have hxc : ∀ r' ∈ rOf M X, (x : G) * r' * (x : G)⁻¹ = r' := fun r' hr' => X_comm_R x.2 hr'
  have hact : ∀ r' ∈ rOf M X, p * r' * p⁻¹ = d * r' * d⁻¹ := by
    intro r' hr'
    have h1 : d * r' * d⁻¹ ∈ rOf M X := S.R_normalized hdM hr'
    calc p * r' * p⁻¹ = (x : G) * (d * r' * d⁻¹) * (x : G)⁻¹ := by rw [hpd]; group
      _ = d * r' * d⁻¹ := hxc _ h1
  have hpow : ∀ i : ℕ, ∀ r' ∈ rOf M X, p ^ i * r' * (p ^ i)⁻¹ = d ^ i * r' * (d ^ i)⁻¹ := by
    intro i
    induction i with
    | zero => intro r' _; simp
    | succ i ih =>
      intro r' hr'
      have h1 : d ^ i * r' * (d ^ i)⁻¹ ∈ rOf M X := S.R_normalized (M.pow_mem hdM i) hr'
      calc p ^ (i + 1) * r' * (p ^ (i + 1))⁻¹
          = p * (p ^ i * r' * (p ^ i)⁻¹) * p⁻¹ := by rw [pow_succ']; group
        _ = p * (d ^ i * r' * (d ^ i)⁻¹) * p⁻¹ := by rw [ih r' hr']
        _ = d * (d ^ i * r' * (d ^ i)⁻¹) * d⁻¹ := hact _ h1
        _ = d ^ (i + 1) * r' * (d ^ (i + 1))⁻¹ := by rw [pow_succ']; group
  obtain ⟨k, m', hm', hm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos d).ne'
  have hdm'M : d ^ m' ∈ M := M.pow_mem hdM m'
  have hθdm' : S.θ ⟨d ^ m', hdm'M⟩ = 1 := by
    have : (⟨d ^ m', hdm'M⟩ : ↥M) = (⟨d, hdM⟩ : ↥M) ^ m' := rfl
    rw [this, map_pow, hθd, one_pow]
  have hdm'2 : ∃ i : ℕ, (d ^ m') ^ (2 ^ i) = 1 := by
    refine ⟨k, ?_⟩
    rw [← pow_mul, mul_comm, ← hm]
    exact pow_orderOf_eq_one d
  have hdm'Q : d ^ m' ∈ pCoreOf 2 M := hP.ker_two ⟨d ^ m', hdm'M⟩ hθdm' hdm'2
  have h1 : d ^ m' ∈ Subgroup.centralizer ({r} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hP.abelian _ hdm'Q r hr.1
  have h2 : d ^ (2 ^ j) ∈ Subgroup.centralizer ({r} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hpow (2 ^ j) r hr
    rw [hj, one_mul, inv_one, mul_one] at this
    calc d ^ (2 ^ j) * r = (d ^ (2 ^ j) * r * (d ^ (2 ^ j))⁻¹) * d ^ (2 ^ j) := by group
      _ = r * d ^ (2 ^ j) := by rw [← this]
  have hcop : Nat.Coprime m' (2 ^ j) := (Nat.coprime_two_right.2 hm').pow_right j
  have hdC : d ∈ Subgroup.centralizer ({r} : Set G) :=
    mem_of_pow_mem_of_coprime _ hcop h1 h2
  rw [Subgroup.mem_centralizer_singleton_iff] at hdC
  rw [hact r hr]
  calc d * r * d⁻¹ = (r * d) * d⁻¹ := by rw [hdC]
    _ = r := by group

theorem exists_comm_in_T (hP : TightDataPlus S) {g : G} (hTM : conjSubgroup g (rOf M X) ≤ M)
    (hcard : 3 ≤ Nat.card ↥(rOf M X)) :
    ∃ t ∈ conjSubgroup g (rOf M X), t ≠ 1 ∧ ∀ r ∈ rOf M X, t * r * t⁻¹ = r := by
  classical
  have : Fintype G := Fintype.ofFinite G
  set T := conjSubgroup g (rOf M X) with hT
  set T' : Subgroup ↥M := T.subgroupOf M with hT'
  have hcardT : Nat.card T' = Nat.card (rOf M X) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTM).toEquiv]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hc : Fintype.card ℤˣ < Fintype.card ↥T' := by
    rw [Fintype.card_units_int, ← Nat.card_eq_fintype_card, hcardT]
    omega
  let f : ↥T' → ℤˣ := fun u => Equiv.Perm.sign (S.θ (u : ↥M))
  obtain ⟨u, u', hne, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f hc
  set τ : ↥M := (u : ↥M)⁻¹ * (u' : ↥M) with hτ
  have hτT : τ ∈ T' := T'.mul_mem (T'.inv_mem u.2) u'.2
  have hτ1 : τ ≠ 1 := by
    intro h
    apply hne
    apply Subtype.ext
    have h1 : (u : ↥M) * τ = u' := by rw [hτ]; group
    rw [h, mul_one] at h1
    exact h1
  have hsign : Equiv.Perm.sign (S.θ τ) = 1 := by
    have h2 : Equiv.Perm.sign (S.θ (u : ↥M)) = Equiv.Perm.sign (S.θ (u' : ↥M)) := hf
    rw [hτ, map_mul, map_inv, map_mul, map_inv, h2]
    exact inv_mul_cancel _
  have hτalt : S.θ τ ∈ alternatingGroup (Fin (2 * n + 1)) :=
    Equiv.Perm.mem_alternatingGroup.2 hsign
  have hτG : (τ : G) ∈ T := Subgroup.mem_subgroupOf.1 hτT
  refine ⟨(τ : G), hτG, fun h => hτ1 (Subtype.ext h), fun r hr => ?_⟩
  exact S.comm_R_of_two_alt hP τ.2 (conjR_two g hτG) hτalt hr

omit [Finite G] S in
theorem comm_symm {t r : G} (h : t * r * t⁻¹ = r) : r * t * r⁻¹ = t := by
  have h1 : t * r = r * t := mul_inv_eq_iff_eq_mul.1 h
  calc r * t * r⁻¹ = t * r * r⁻¹ := by rw [h1]
    _ = t := by group

theorem R_le_conj (hP : TightDataPlus S) {g : G} (hTM : conjSubgroup g (rOf M X) ≤ M)
    (hcard : 3 ≤ Nat.card ↥(rOf M X)) : ∀ r ∈ rOf M X, g⁻¹ * r * g ∈ M := by
  obtain ⟨t₀, ht₀, ht₀1, hc⟩ := S.exists_comm_in_T hP hTM hcard
  intro r hr
  have hr₀ : g⁻¹ * t₀ * g ∈ rOf M X := mem_conjSubgroup.1 ht₀
  have hr₀1 : g⁻¹ * t₀ * g ≠ 1 := by
    intro h
    apply ht₀1
    have : t₀ = g * (g⁻¹ * t₀ * g) * g⁻¹ := by group
    rw [this, h]
    group
  refine S.mem_M_of_comm_R hr₀ hr₀1 ?_
  calc (g⁻¹ * r * g) * (g⁻¹ * t₀ * g) * (g⁻¹ * r * g)⁻¹ = g⁻¹ * (r * t₀ * r⁻¹) * g := by group
    _ = g⁻¹ * t₀ * g := by rw [comm_symm (hc r hr)]

theorem comm_RT (hP : TightDataPlus S) {g : G} (hgM : g ∉ M)
    (hTM : conjSubgroup g (rOf M X) ≤ M) (hcard : 3 ≤ Nat.card ↥(rOf M X)) :
    ∀ r ∈ rOf M X, ∀ τ ∈ conjSubgroup g (rOf M X), r * τ * r⁻¹ = τ := by
  obtain ⟨t₀, ht₀, ht₀1, hc⟩ := S.exists_comm_in_T hP hTM hcard
  intro r hr τ hτ
  have h1 : r * τ * r⁻¹ ∈ conjSubgroup g (rOf M X) :=
    S.conjR_normal_of_comm g ht₀ ht₀1 (comm_symm (hc r hr)) hτ
  have hτM : τ ∈ M := hTM hτ
  have h2 : τ * r⁻¹ * τ⁻¹ ∈ rOf M X := S.R_normalized hτM ((rOf M X).inv_mem hr)
  have h3 : (r * τ * r⁻¹) * τ⁻¹ ∈ conjSubgroup g (rOf M X) :=
    (conjSubgroup g (rOf M X)).mul_mem h1 ((conjSubgroup g (rOf M X)).inv_mem hτ)
  have h4 : (r * τ * r⁻¹) * τ⁻¹ ∈ rOf M X := by
    have : (r * τ * r⁻¹) * τ⁻¹ = r * (τ * r⁻¹ * τ⁻¹) := by group
    rw [this]
    exact (rOf M X).mul_mem hr h2
  have h5 : (r * τ * r⁻¹) * τ⁻¹ ∈ rOf M X ⊓ conjSubgroup g (rOf M X) := ⟨h4, h3⟩
  rw [hP.ti g hgM] at h5
  have h6 := Subgroup.mem_bot.1 h5
  calc r * τ * r⁻¹ = (r * τ * r⁻¹ * τ⁻¹) * τ := by group
    _ = τ := by rw [h6, one_mul]

end SolCfg

end CFSG.CGT.PushingUpLit.SolK
