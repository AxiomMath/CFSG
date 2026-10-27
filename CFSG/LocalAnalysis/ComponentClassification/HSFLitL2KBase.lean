module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2Skeleton
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitConjOrbit

public section

namespace CFSG.ComponentClassification.HSFLit.L2K

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

theorem k8_comm_of_mem_R8 {σ : Perm (ZMod 8)} (hσ : σ ∈ R8) : k8 * σ = σ * k8 := by
  obtain ⟨u, c, hu, rfl⟩ := hσ
  rw [aff8_mul, aff8_mul, mul_comm u5 u]
  congr 1
  rcases hu with rfl | rfl <;> revert c <;> decide

theorem comm_mem_R8 {σ τ : Perm (ZMod 8)} (hσ : σ ∈ R8) (hτ : τ ∈ R8) :
    σ * τ * σ⁻¹ * τ⁻¹ = 1 ∨ σ * τ * σ⁻¹ * τ⁻¹ = z8 := by
  obtain ⟨u, c, hu, rfl⟩ := hσ
  obtain ⟨u', c', hu', rfl⟩ := hτ
  rw [aff8_inv, aff8_inv, aff8_mul, aff8_mul, aff8_mul, ← aff8_one]
  rcases hu with rfl | rfl <;> rcases hu' with rfl | rfl <;> revert c c' <;> decide

theorem z8_comm_aff8' (u : (ZMod 8)ˣ) (b : ZMod 8) : aff8 u b * z8 = z8 * aff8 u b := by
  rw [aff8_mul, aff8_mul, mul_one, one_mul]
  congr 1
  revert u b
  decide

theorem k8_sq : k8 ^ 2 = 1 := by
  rw [pow_two, aff8_mul, ← aff8_one]
  decide

theorem k8_not_mem_R8 : k8 ∉ R8 := by decide

theorem z8_mul_k8_not_mem_R8 : z8 * k8 ∉ R8 := by decide

theorem x8_mem_R8 : x8 ∈ R8 := ⟨1, 1, Or.inl rfl, by rw [mul_one]⟩

theorem y8_mem_R8 : y8 ∈ R8 := ⟨-1, 0, Or.inr rfl, by rw [mul_zero]⟩

theorem z8_mem_R8 : z8 ∈ R8 := ⟨1, 2, Or.inl rfl, rfl⟩

theorem x8_sq : x8 ^ 2 = z8 := by rw [pow_two, aff8_mul]; rfl

theorem x8_pow_four : x8 ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, x8_sq, pow_two, aff8_mul, ← aff8_one]
  rfl

theorem z8_ne_one : z8 ≠ 1 := by decide

theorem y8_sq : y8 ^ 2 = 1 := by rw [pow_two, aff8_mul, ← aff8_one]; rfl

theorem y8_x8_y8 : y8 * x8 * y8⁻¹ = x8⁻¹ := by
  rw [aff8_inv, aff8_inv, aff8_mul, aff8_mul]
  decide

theorem y8_ne_one : y8 ≠ 1 := by decide

theorem y8_ne_z8 : y8 ≠ z8 := by decide

theorem x8_mul_y8_ne_one : x8 * y8 ≠ 1 := by decide

theorem x8_mul_y8_ne_z8 : x8 * y8 ≠ z8 := by decide

variable {X : Type} [Group X] {t : X} {L : Subgroup X}

@[expose] noncomputable def ψX (A : L2Data t L) (g : X) : Perm (ZMod 8) :=
  open Classical in if h : g ∈ A.T then A.ψ ⟨g, h⟩ else 1

variable {A : L2Data t L}

theorem ψX_of_mem {g : X} (hg : g ∈ A.T) : ψX A g = A.ψ ⟨g, hg⟩ := by
  simp [ψX, hg]

theorem ψX_mul {g h : X} (hg : g ∈ A.T) (hh : h ∈ A.T) : ψX A (g * h) = ψX A g * ψX A h := by
  rw [ψX_of_mem hg, ψX_of_mem hh, ψX_of_mem (mul_mem hg hh), ← map_mul]
  rfl

theorem ψX_inv {g : X} (hg : g ∈ A.T) : ψX A g⁻¹ = (ψX A g)⁻¹ := by
  rw [ψX_of_mem hg, ψX_of_mem (inv_mem hg), ← map_inv]
  rfl

theorem ψX_one : ψX A (1 : X) = 1 := by
  rw [ψX_of_mem (one_mem _), show (⟨1, _⟩ : A.T) = 1 from rfl, map_one]

theorem ψX_pow {g : X} (hg : g ∈ A.T) (n : ℕ) : ψX A (g ^ n) = ψX A g ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, ψX_one]
  | succ n ih => rw [pow_succ, ψX_mul (pow_mem hg n) hg, ih, pow_succ]

theorem ψX_conj {g h : X} (hg : g ∈ A.T) (hh : h ∈ A.T) :
    ψX A (g * h * g⁻¹) = ψX A g * ψX A h * (ψX A g)⁻¹ := by
  rw [ψX_mul (mul_mem hg hh) (inv_mem hg), ψX_mul hg hh, ψX_inv hg]

theorem ψX_comm {g h : X} (hg : g ∈ A.T) (hh : h ∈ A.T) :
    ψX A (g * h * g⁻¹ * h⁻¹) = ψX A g * ψX A h * (ψX A g)⁻¹ * (ψX A h)⁻¹ := by
  rw [ψX_mul (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh), ψX_conj hg hh, ψX_inv hh]

theorem ψX_eq_one_iff {g : X} (hg : g ∈ A.T) : ψX A g = 1 ↔ g ∈ A.K := by
  rw [ψX_of_mem hg, A.mem_K_iff hg]

theorem ψX_mem_R8 {g : X} (hg : g ∈ A.R) : ψX A g ∈ R8 := by
  rw [ψX_of_mem hg.1]
  exact A.ψ_mem_R8' hg

theorem ψX_t : ψX A t = 1 := (ψX_eq_one_iff A.t_mem_T).mpr A.t_mem_K

theorem exists_mem_R_ψX_eq {σ : Perm (ZMod 8)} (hσ : σ ∈ R8) : ∃ r ∈ A.R, ψX A r = σ := by
  obtain ⟨r, hr, hψ⟩ := A.exists_mem_R_ψ_eq hσ
  exact ⟨r, hr, by rw [ψX_of_mem hr.1, hψ]⟩

include A in
theorem t_ne_one : t ≠ 1 := by
  intro h
  have := A.orderOf_t
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

include A in
theorem t_sq : t ^ 2 = 1 := by
  rw [← A.orderOf_t]
  exact pow_orderOf_eq_one t

theorem t_mem_C : t ∈ centralizer ({t} : Set X) := mem_centralizer_singleton_iff.mpr rfl

theorem commute_t_of_mem_C {g : X} (hg : g ∈ centralizer ({t} : Set X)) : g * t = t * g :=
  mem_centralizer_singleton_iff.mp hg

include A in
theorem L_le_C : L ≤ centralizer ({t} : Set X) := A.config.le_centralizer

theorem isPGroup_zpowers_of_sq {G : Type*} [Group G] {g : G} (hg2 : g ^ 2 = 1) :
    IsPGroup 2 (zpowers g) := by
  intro h
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp h.2
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one, ← hn, ← zpow_natCast, ← zpow_mul,
    mul_comm, zpow_mul, zpow_natCast, hg2, one_zpow]

variable (C : A.CaseK)

theorem k_mem_C : C.k ∈ centralizer ({t} : Set X) := A.T_le_centralizer C.k_mem

theorem ψX_k : ψX A C.k = k8 := by rw [ψX_of_mem C.k_mem, C.ψ_k]

theorem k_inv : C.k⁻¹ = C.k := by rw [inv_eq_iff_mul_eq_one, ← pow_two, C.k_sq]

theorem ψX_k_not_mem_R8 : ψX A C.k ∉ R8 := by rw [ψX_k C]; exact k8_not_mem_R8

structure Gens (A : L2Data t L) where
  x₀ : X
  y₀ : X
  x₀_mem : x₀ ∈ A.R
  y₀_mem : y₀ ∈ A.R
  ψ_x₀ : ψX A x₀ = x8
  ψ_y₀ : ψX A y₀ = y8

include A in
theorem nonempty_gens : Nonempty (Gens A) := by
  obtain ⟨x₀, hx, hψx⟩ := exists_mem_R_ψX_eq (A := A) x8_mem_R8
  obtain ⟨y₀, hy, hψy⟩ := exists_mem_R_ψX_eq (A := A) y8_mem_R8
  exact ⟨⟨x₀, y₀, hx, hy, hψx, hψy⟩⟩

namespace Gens

variable (S : Gens A)

abbrev z : X := S.x₀ ^ 2

theorem z_mem : S.z ∈ A.R := pow_mem S.x₀_mem 2

theorem ψ_z : ψX A S.z = z8 := by rw [ψX_pow S.x₀_mem.1, S.ψ_x₀, x8_sq]

theorem z_ne_one : S.z ≠ 1 := by
  intro h
  have := S.ψ_z
  rw [h, ψX_one] at this
  exact z8_ne_one this.symm

theorem xy_mem : S.x₀ * S.y₀ ∈ A.R := mul_mem S.x₀_mem S.y₀_mem

theorem ψ_xy : ψX A (S.x₀ * S.y₀) = x8 * y8 := by
  rw [ψX_mul S.x₀_mem.1 S.y₀_mem.1, S.ψ_x₀, S.ψ_y₀]

end Gens

variable [Finite X]

include A in
theorem le_normalizer : centralizer ({t} : Set X) ≤ normalizer (L : Set X) :=
  A.config.le_normalizer

include A in
theorem conj_mem_L {g l : X} (hg : g ∈ centralizer ({t} : Set X)) (hl : l ∈ L) :
    g * l * g⁻¹ ∈ L :=
  (mem_normalizer_iff.mp (le_normalizer (A := A) hg) l).mp hl

theorem eq_of_ψX_eq {g h : X} (hg : g ∈ A.R) (hh : h ∈ A.R)
    (hgh : ψX A g = ψX A h) : g = h := by
  rw [ψX_of_mem hg.1, ψX_of_mem hh.1] at hgh
  exact A.eq_of_ψ_eq hg hh hgh

theorem eq_one_of_ψX {g : X} (hg : g ∈ A.R) (h1 : ψX A g = 1) : g = 1 :=
  eq_of_ψX_eq hg (one_mem _) (by rw [h1, ψX_one])

include C in
theorem eq_one_or_eq_t_of_mem_K {g : X} (hg : g ∈ A.K) : g = 1 ∨ g = t := by
  by_contra hne
  push Not at hne
  have hsub : ({1, t, g} : Set X) ⊆ (A.K : Set X) := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · exact one_mem _
    · exact A.t_mem_K
    · exact hg
  have h3 : ({1, t, g} : Set X).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨1, t, g, (t_ne_one (A := A)).symm, hne.1.symm, hne.2.symm, rfl⟩
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [h3, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, C.card_K] at h1
  omega

theorem commute_k {r : X} (hr : r ∈ A.R) : C.k * r = r * C.k := by
  have hc : C.k * r * C.k⁻¹ * r⁻¹ ∈ A.K ⊓ L := by
    refine Subgroup.mem_inf.mpr ⟨(ψX_eq_one_iff (mul_mem (mul_mem (mul_mem C.k_mem hr.1)
      (inv_mem C.k_mem)) (inv_mem hr.1))).mp ?_,
      mul_mem (conj_mem_L (A := A) (k_mem_C C) hr.2) (inv_mem hr.2)⟩
    rw [ψX_comm C.k_mem hr.1, ψX_k C, k8_comm_of_mem_R8 (ψX_mem_R8 hr)]
    group
  rw [A.K_inf_L, mem_bot] at hc
  calc C.k * r = C.k * r * C.k⁻¹ * r⁻¹ * (r * C.k) := by group
    _ = r * C.k := by rw [hc, one_mul]

theorem exists_eq_of_mem_T {g : X} (hg : g ∈ A.T) :
    ∃ r ∈ A.R, ∃ c d : ℕ, c < 2 ∧ d < 2 ∧ g = r * t ^ c * C.k ^ d := by
  have hk8N : k8 ∈ normalizer (R8 : Set (Perm (ZMod 8))) := by
    refine centralizer_le_normalizer _ ?_
    rw [mem_centralizer_iff]
    intro σ hσ
    exact (k8_comm_of_mem_R8 hσ).symm
  have hR : ∀ {h : X}, h ∈ A.T → ψX A h ∈ R8 → ∃ r ∈ A.R, ∃ c : ℕ, c < 2 ∧ h = r * t ^ c := by
    intro h hh hψ
    obtain ⟨r, hr, hrψ⟩ := exists_mem_R_ψX_eq (A := A) hψ
    have hK : r⁻¹ * h ∈ A.K := by
      rw [← ψX_eq_one_iff (mul_mem (inv_mem hr.1) hh), ψX_mul (inv_mem hr.1) hh, ψX_inv hr.1,
        hrψ, inv_mul_cancel]
    rcases eq_one_or_eq_t_of_mem_K C hK with h1 | h1
    · refine ⟨r, hr, 0, by norm_num, ?_⟩
      calc h = r * (r⁻¹ * h) := by group
        _ = r * t ^ 0 := by rw [h1, pow_zero]
    · refine ⟨r, hr, 1, by norm_num, ?_⟩
      calc h = r * (r⁻¹ * h) := by group
        _ = r * t ^ 1 := by rw [h1, pow_one]
  have hψ := C.range_le ⟨g, hg⟩
  rw [← ψX_of_mem hg] at hψ
  rcases mem_or_mul_mem_of_mem_sup_zpowers k8_sq hk8N hψ with h | h
  · obtain ⟨r, hr, c, hc, rfl⟩ := hR hg h
    exact ⟨r, hr, c, 0, hc, by norm_num, by rw [pow_zero, mul_one]⟩
  · rw [← ψX_k C, ← ψX_mul hg C.k_mem] at h
    obtain ⟨r, hr, c, hc, hgk⟩ := hR (mul_mem hg C.k_mem) h
    refine ⟨r, hr, c, 1, hc, by norm_num, ?_⟩
    calc g = g * C.k * C.k⁻¹ := by group
      _ = r * t ^ c * C.k ^ 1 := by rw [hgk, k_inv C, pow_one]

theorem card_T_eq_two_pow :
    Nat.card A.T = 2 ^ (Nat.card (centralizer ({t} : Set X))).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [L2Data.T, Config.sylowIn, card_map_of_injective (subtype_injective _),
    Sylow.card_eq_multiplicity]

theorem card_T_eq_of_le {H : Subgroup X} (hTH : A.T ≤ H)
    (hH : H ≤ centralizer ({t} : Set X)) :
    Nat.card A.T = 2 ^ (Nat.card H).factorization 2 := by
  have hC := card_T_eq_two_pow (A := A)
  have h1 : Nat.card H ∣ Nat.card (centralizer ({t} : Set X)) := Subgroup.card_dvd_of_le hH
  have h2 : Nat.card A.T ∣ Nat.card H := Subgroup.card_dvd_of_le hTH
  have hpos : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hposC : Nat.card (centralizer ({t} : Set X)) ≠ 0 := Nat.card_pos.ne'
  have h3 : (Nat.card H).factorization 2 ≤
      (Nat.card (centralizer ({t} : Set X))).factorization 2 :=
    (Nat.factorization_le_iff_dvd hpos hposC).mpr h1 2
  have h4 : (Nat.card (centralizer ({t} : Set X))).factorization 2 ≤
      (Nat.card H).factorization 2 := by
    rw [hC] at h2
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos).mp h2
  rw [hC, le_antisymm h3 h4]

theorem exists_conj_le_T {P : Subgroup X} (hP : IsPGroup 2 P)
    (hPt : P ≤ centralizer ({t} : Set X)) :
    ∃ h ∈ centralizer ({t} : Set X), P.map (MulAut.conj h).toMonoidHom ≤ A.T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : IsPGroup 2 (P.subgroupOf (centralizer ({t} : Set X))) :=
    hP.comap_of_injective _ (subtype_injective _)
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (centralizer ({t} : Set X)) Q A.syl
  refine ⟨h, h.2, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  have hpC : p ∈ centralizer ({t} : Set X) := hPt hp
  have hpQ : (⟨p, hpC⟩ : centralizer ({t} : Set X)) ∈ (Q : Subgroup _) := hQ hp
  have : h * (⟨p, hpC⟩ : centralizer ({t} : Set X)) * h⁻¹ ∈ (A.syl : Subgroup _) := by
    rw [← hh, Sylow.coe_subgroup_smul]
    exact ⟨_, hpQ, rfl⟩
  exact ⟨_, this, rfl⟩

include C in
theorem eq_one_or_eq_t_of_sq {g : X} (hg : g ∈ centralizer ({t} : Set X))
    (hgC : g ∈ coreActionKernel L) (hg2 : g ^ 2 = 1) : g = 1 ∨ g = t := by
  obtain ⟨c, hc, hcP⟩ := exists_conj_le_T (A := A) (isPGroup_zpowers_of_sq hg2)
    (zpowers_le.mpr hg)
  have hcgT : c * g * c⁻¹ ∈ A.T := hcP ⟨g, mem_zpowers g, rfl⟩
  have hcgK : c * g * c⁻¹ ∈ A.K := by
    refine Subgroup.mem_inf.mpr ⟨hcgT, ?_⟩
    have hcN := le_normalizer (A := A) hc
    have hN := normalizer_le_normalizer_coreActionKernel L
    exact (mem_normalizer_iff.mp (hN hcN) g).mp hgC
  have htc : c⁻¹ * t * c = t := by
    have := mem_centralizer_singleton_iff.mp hc
    calc c⁻¹ * t * c = c⁻¹ * (t * c) := by group
      _ = c⁻¹ * (c * t) := by rw [this]
      _ = t := by group
  rcases eq_one_or_eq_t_of_mem_K C hcgK with h | h
  · left
    calc g = c⁻¹ * (c * g * c⁻¹) * c := by group
      _ = 1 := by rw [h]; group
  · right
    calc g = c⁻¹ * (c * g * c⁻¹) * c := by group
      _ = t := by rw [h, htc]

theorem conj_eq_of_mem_pair {G' : Subgroup X} (hTG : A.T ≤ G')
    (hG : G' ≤ centralizer ({t} : Set X)) {e : X}
    (hTe : A.T ≤ centralizer ({e} : Set X))
    (hpair : ∀ n ∈ G', n * e * n⁻¹ = e ∨ n * e * n⁻¹ = t * e) {n : X} (hn : n ∈ G') :
    n * e * n⁻¹ = e := by
  classical
  have hsub : {y | ∃ g ∈ G', g * e * g⁻¹ = y} ⊆ ({e, t * e} : Set X) := by
    rintro _ ⟨g, hg, rfl⟩
    rcases hpair g hg with h | h <;> simp [h]
  have hle2 : (G' ⊓ centralizer ({e} : Set X)).relIndex G' ≤ 2 := by
    rw [relIndex_inf_centralizer_eq_ncard]
    calc _ ≤ ({e, t * e} : Set X).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ({t * e} : Set X).ncard + 1 := Set.ncard_insert_le _ _
      _ = 2 := by rw [Set.ncard_singleton]
  have hT₁ := card_T_eq_of_le (A := A) hTG hG
  have hT₂ := card_T_eq_of_le (A := A) (le_inf hTG hTe) (inf_le_left.trans hG)
  have hidx : (G' ⊓ centralizer ({e} : Set X)).relIndex G' = 1 := by
    by_contra hne
    have h2 : (G' ⊓ centralizer ({e} : Set X)).relIndex G' = 2 := by
      have hpos : (G' ⊓ centralizer ({e} : Set X)).relIndex G' ≠ 0 := by
        intro h0
        have := relIndex_mul_card (H := G' ⊓ centralizer ({e} : Set X)) (K := G')
        rw [h0, zero_mul] at this
        exact Nat.card_pos.ne' this.symm
      omega
    have h3 := card_eq_mul_two_pow (P := A.T) (Q := A.T) inf_le_left hT₁ hT₂
    rw [h2, Nat.Prime.factorization_self Nat.prime_two, pow_one] at h3
    have : 0 < Nat.card A.T := Nat.card_pos
    omega
  have := (relIndex_eq_one.mp hidx) hn
  rw [mem_inf, mem_centralizer_singleton_iff] at this
  calc n * e * n⁻¹ = e * n * n⁻¹ := by rw [this.2]
    _ = e := by group

namespace Gens

variable (S : Gens A)

theorem z_sq : S.z ^ 2 = 1 :=
  eq_one_of_ψX (pow_mem S.z_mem 2) (by rw [ψX_pow S.z_mem.1, S.ψ_z]; decide)

theorem x₀_pow_four : S.x₀ ^ 4 = 1 :=
  eq_one_of_ψX (pow_mem S.x₀_mem 4) (by rw [ψX_pow S.x₀_mem.1, S.ψ_x₀, x8_pow_four])

theorem orderOf_x₀ : orderOf S.x₀ = 4 :=
  orderOf_eq_prime_pow (p := 2) (n := 1) (by rw [pow_one]; exact S.z_ne_one)
    (by rw [show (2 : ℕ) ^ (1 + 1) = 4 by rfl]; exact S.x₀_pow_four)

theorem y₀_sq : S.y₀ ^ 2 = 1 :=
  eq_one_of_ψX (pow_mem S.y₀_mem 2) (by rw [ψX_pow S.y₀_mem.1, S.ψ_y₀, y8_sq])

theorem y₀_x₀_y₀ : S.y₀ * S.x₀ * S.y₀⁻¹ = S.x₀⁻¹ := by
  have hm : S.y₀ * S.x₀ * S.y₀⁻¹ ∈ A.R := mul_mem (mul_mem S.y₀_mem S.x₀_mem) (inv_mem S.y₀_mem)
  refine eq_of_ψX_eq hm (inv_mem S.x₀_mem) ?_
  rw [ψX_conj S.y₀_mem.1 S.x₀_mem.1, ψX_inv S.x₀_mem.1, S.ψ_x₀, S.ψ_y₀, y8_x8_y8]

theorem xy_sq : (S.x₀ * S.y₀) ^ 2 = 1 :=
  eq_one_of_ψX (pow_mem S.xy_mem 2) (by rw [ψX_pow S.xy_mem.1, S.ψ_xy]; decide)

theorem z_comm_R {r : X} (hr : r ∈ A.R) : S.z * r = r * S.z := by
  have hm : S.z * r * S.z⁻¹ * r⁻¹ ∈ A.R :=
    mul_mem (mul_mem (mul_mem S.z_mem hr) (inv_mem S.z_mem)) (inv_mem hr)
  have h1 : S.z * r * S.z⁻¹ * r⁻¹ = 1 := by
    refine eq_one_of_ψX hm ?_
    obtain ⟨u, c, -, hc⟩ := ψX_mem_R8 hr
    rw [ψX_comm S.z_mem.1 hr.1, S.ψ_z, ← hc, ← z8_comm_aff8']
    group
  calc S.z * r = S.z * r * S.z⁻¹ * r⁻¹ * (r * S.z) := by group
    _ = r * S.z := by rw [h1, one_mul]

theorem comm_mem_R {r s : X} (hr : r ∈ A.R) (hs : s ∈ A.R) :
    r * s * r⁻¹ * s⁻¹ = 1 ∨ r * s * r⁻¹ * s⁻¹ = S.z := by
  have hm : r * s * r⁻¹ * s⁻¹ ∈ A.R := mul_mem (mul_mem (mul_mem hr hs) (inv_mem hr)) (inv_mem hs)
  rcases comm_mem_R8 (ψX_mem_R8 hr) (ψX_mem_R8 hs) with h | h
  · exact Or.inl (eq_one_of_ψX hm (by rw [ψX_comm hr.1 hs.1, h]))
  · exact Or.inr (eq_of_ψX_eq hm S.z_mem (by rw [ψX_comm hr.1 hs.1, h, S.ψ_z]))

end Gens

end CFSG.ComponentClassification.HSFLit.L2K
