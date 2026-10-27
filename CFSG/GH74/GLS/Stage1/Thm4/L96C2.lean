module

public import CFSG.GH74.GLS.Stage1.Thm4.L96Main
public import CFSG.GH74.GLS.Stage1.Thm4.L96Norm
public import CFSG.GH74.GLS.Stage1.Thm4.L96Sylow
public import CFSG.GH74.GLS.Stage1.Thm4.L96Perm2
public import CFSG.GH74.GLS.Stage1.Thm4.L96Chain

public section

namespace CFSG.GH74.GLS.Stage1.Thm4.L96

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3 CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm4
  CFSG.GH74.Uniqueness.SU.SU13.TA CFSG.GH74.GLS.IVK.Lifted
open scoped commutatorElement

open Equiv Equiv.Perm

theorem ncard_pair_le' {α : Type*} (a b : α) : ({a, b} : Set α).ncard ≤ 2 := by
  calc ({a, b} : Set α).ncard ≤ ({b} : Set α).ncard + 1 := Set.ncard_insert_le a {b}
    _ = 2 := by rw [Set.ncard_singleton]

section C2

variable {G : Type} [Group G] [Finite G] {Lh : Type} [Group Lh] {z t : G} {S K : Subgroup G}
  {h : Ctx98 G Lh z t S K} {n : ℕ}

variable (A : Act h n) {g : G} (hg : g * z * g⁻¹ = t)

include A

theorem exists_decomp_z (hn : 8 ≤ n) {σ : Perm (Fin n)} (htρ : A.ρ ⟨t, h.std.t_cen⟩ = σ)
    (hσ : σ.cycleType = {2, 2, 2}) :
    ∃ y₁ y₂ o : ↥(K ⊓ Cz t), (∃ a : ℕ, (y₁ : G) ^ (3 ^ a) = 1) ∧ (∃ a : ℕ, (y₂ : G) ^ (3 ^ a) = 1) ∧
      Odd (orderOf (o : G)) ∧
      (⟨z, h.z_mem, z_mem_Cz_t h⟩ : ↥(K ⊓ Cz t)) = (y₁ * y₂) ^ 2 * o⁻¹ := by
  classical
  obtain ⟨γ₁, γ₂, h₁, h₂, hc₁', hc₂', hct⟩ := exists_two_order_three_commuting hσ
  have hodd3 : Odd (orderOf γ₁) := by rw [h₁]; decide
  have hodd3' : Odd (orderOf γ₂) := by rw [h₂]; decide
  have hs₁ : γ₁ ∈ alternatingGroup (Fin n) :=
    Equiv.Perm.mem_alternatingGroup.2 (sign_eq_one_of_odd_orderOf hodd3)
  have hs₂ : γ₂ ∈ alternatingGroup (Fin n) :=
    Equiv.Perm.mem_alternatingGroup.2 (sign_eq_one_of_odd_orderOf hodd3')
  set G₁ : alternatingGroup (Fin n) := ⟨γ₁, hs₁⟩ with hG₁
  set G₂ : alternatingGroup (Fin n) := ⟨γ₂, hs₂⟩ with hG₂
  have hG₁o : orderOf G₁ = 3 := by rw [← Subgroup.orderOf_coe]; exact h₁
  have hG₂o : orderOf G₂ = 3 := by rw [← Subgroup.orderOf_coe]; exact h₂
  have hc₁ : (G₁ : Perm (Fin n)) * A.ρ ⟨t, h.std.t_cen⟩ = A.ρ ⟨t, h.std.t_cen⟩ * (G₁ : Perm (Fin n)) := by
    rw [htρ]; exact hc₁'.eq
  have hc₂ : (G₂ : Perm (Fin n)) * A.ρ ⟨t, h.std.t_cen⟩ = A.ρ ⟨t, h.std.t_cen⟩ * (G₂ : Perm (Fin n)) := by
    rw [htρ]; exact hc₂'.eq
  have hp3 : Nat.Prime 3 := by norm_num
  obtain ⟨x₁, hx₁t, ⟨m₁, hx₁o⟩, hx₁π⟩ := A.exists_lift_pElement hp3 (by norm_num) G₁ hG₁o hc₁
  obtain ⟨x₂, hx₂t, ⟨m₂, hx₂o⟩, hx₂π⟩ := A.exists_lift_pElement hp3 (by norm_num) G₂ hG₂o hc₂
  let mem : ∀ x : ↥K, (x : G) * t = t * (x : G) → (x : G) ∈ K ⊓ Cz t := fun x hx =>
    ⟨x.2, Subgroup.mem_centralizer_singleton_iff.2 hx⟩
  let y₁ : ↥(K ⊓ Cz t) := ⟨x₁, mem x₁ hx₁t⟩
  let y₂ : ↥(K ⊓ Cz t) := ⟨x₂, mem x₂ hx₂t⟩
  let yz : ↥(K ⊓ Cz t) := ⟨z, h.z_mem, z_mem_Cz_t h⟩
  let w : ↥(K ⊓ Cz t) := y₁ * y₂
  let o : ↥(K ⊓ Cz t) := yz⁻¹ * w ^ 2
  have hyz : yz = w ^ 2 * o⁻¹ := by simp [o]
  have hπw : ((A.π (QuotientGroup.mk (x₁ * x₂)) : alternatingGroup (Fin n)) : Perm (Fin n)).cycleType
      = {2, 2} := by
    rw [QuotientGroup.mk_mul, map_mul, hx₁π, hx₂π]
    exact hct
  obtain ⟨hk, hne⟩ := A.cover.sq_mem_ker_ne_one_of_cycleType_two_two (by omega)
    (x := QuotientGroup.mk (x₁ * x₂)) hπw
  have hzk : (QuotientGroup.mk (⟨z, h.z_mem⟩ : ↥K) : HatT K) ∈ A.π.ker := A.π_z (by omega)
  have hsq : (QuotientGroup.mk (x₁ * x₂) : HatT K) ^ 2 = QuotientGroup.mk ⟨z, h.z_mem⟩ :=
    A.ker_unique hk hzk hne (Act.mk_z_ne_one (h := h))
  have hoK : (⟨z, h.z_mem⟩ : ↥K)⁻¹ * (x₁ * x₂) ^ 2 ∈ pPrimeCore 2 ↥K := by
    have : (QuotientGroup.mk ((x₁ * x₂) ^ 2) : HatT K) = QuotientGroup.mk ⟨z, h.z_mem⟩ := by
      rw [QuotientGroup.mk_pow]; exact hsq
    exact QuotientGroup.eq.1 this.symm
  have hodd_o : Odd (orderOf (o : G)) := by
    have h1 : orderOf (⟨(⟨z, h.z_mem⟩ : ↥K)⁻¹ * (x₁ * x₂) ^ 2, hoK⟩ : pPrimeCore 2 ↥K) ∣
        Nat.card (pPrimeCore 2 ↥K) := orderOf_dvd_natCard _
    have h2 : Odd (orderOf ((⟨z, h.z_mem⟩ : ↥K)⁻¹ * (x₁ * x₂) ^ 2)) := by
      rw [← Subgroup.orderOf_mk _ hoK]
      exact Odd.of_dvd_nat odd_card_pPrimeCore h1
    have h3 : (o : G) = (((⟨z, h.z_mem⟩ : ↥K)⁻¹ * (x₁ * x₂) ^ 2 : ↥K) : G) := by
      simp [o, yz, w, y₁, y₂]
    rw [h3, Subgroup.orderOf_coe]
    exact h2
  exact ⟨y₁, y₂, o, ⟨m₁, hx₁o⟩, ⟨m₂, hx₂o⟩, hodd_o, hyz⟩


include hg

theorem orderOf_zeta : orderOf (Theta A hg ⟨z, h.z_mem, z_mem_Cz_t h⟩) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ (zeta_ne_one A hg)
  rw [← map_pow]
  have : (⟨z, h.z_mem, z_mem_Cz_t h⟩ : ↥(K ⊓ Cz t)) ^ 2 = 1 := by
    apply Subtype.ext
    have h2 : z ^ 2 = 1 := by rw [← h.z_ord]; exact pow_orderOf_eq_one z
    simpa using h2
  rw [this, map_one]

theorem zeta_even_and_exists_three (hn : 8 ≤ n) {σ : Perm (Fin n)}
    (htρ : A.ρ ⟨t, h.std.t_cen⟩ = σ) (hσ : σ.cycleType = {2, 2, 2}) :
    Equiv.Perm.sign (Theta A hg ⟨z, h.z_mem, z_mem_Cz_t h⟩) = 1 ∧
      ∃ x : ↥(K ⊓ Cz t), (∃ a : ℕ, (x : G) ^ (3 ^ a) = 1) ∧ Theta A hg x ≠ 1 := by
  classical
  obtain ⟨y₁, y₂, o, ⟨a₁, hy₁⟩, ⟨a₂, hy₂⟩, hodd_o, hyz⟩ := exists_decomp_z A hn htρ hσ
  have hodd_Θo : Odd (orderOf (Theta A hg o)) := by
    have h1 : orderOf (Theta A hg o) ∣ orderOf o := orderOf_map_dvd _ _
    have h2 : Odd (orderOf o) := by rw [← Subgroup.orderOf_coe]; exact hodd_o
    exact Odd.of_dvd_nat h2 h1
  have hso : Equiv.Perm.sign (Theta A hg o) = 1 := sign_eq_one_of_odd_orderOf hodd_Θo
  refine ⟨?_, ?_⟩
  · rw [hyz]
    simp only [map_mul, map_pow, map_inv]
    rw [hso]
    simp
  · by_contra hcon
    push Not at hcon
    have h1 := hcon y₁ ⟨a₁, hy₁⟩
    have h2 := hcon y₂ ⟨a₂, hy₂⟩
    have h3 : Theta A hg ⟨z, h.z_mem, z_mem_Cz_t h⟩ = (Theta A hg o)⁻¹ := by
      rw [hyz]
      simp only [map_mul, map_pow, map_inv]
      rw [h1, h2]
      simp
    have h4 := orderOf_zeta A hg
    rw [h3, orderOf_inv] at h4
    rw [h4] at hodd_Θo
    exact absurd hodd_Θo (by decide)

theorem zeta_cycleType (hn8 : 8 ≤ n) (hn11 : n ≤ 11)
    (hsign : Equiv.Perm.sign (Theta A hg ⟨z, h.z_mem, z_mem_Cz_t h⟩) = 1) :
    (Theta A hg ⟨z, h.z_mem, z_mem_Cz_t h⟩).cycleType = {2, 2, 2, 2} := by
  classical
  set c : ↥(Cz z) := conjC hg ⟨z, z_mem_Cz_t h⟩ with hc
  have hcg : (c : G) = g⁻¹ * z * g := rfl
  have hρc : A.ρ c = Theta A hg ⟨z, h.z_mem, z_mem_Cz_t h⟩ := rfl
  have hc2 : (c : G) ^ (2 ^ 1) = 1 := by
    have : (g⁻¹ * z * g) ^ 2 = g⁻¹ * z ^ 2 * g := by rw [pow_two, pow_two]; group
    rw [hcg, pow_one, this, ← h.z_ord, pow_orderOf_eq_one]; group
  have hcK : (c : G) ∈ K := A.mem_K_of_sign (by rw [hρc]; exact hsign) hc2
  set k : ↥K := ⟨(c : G), hcK⟩ with hk
  have hρk : A.ρ ⟨(k : G), h.K_le k.2⟩ = Theta A hg ⟨z, h.z_mem, z_mem_Cz_t h⟩ := hρc
  have hπk : ((A.π (QuotientGroup.mk k) : alternatingGroup (Fin n)) : Perm (Fin n)) =
      Theta A hg ⟨z, h.z_mem, z_mem_Cz_t h⟩ := by rw [← A.ρ_K k]; exact hρk
  have hord : orderOf (c : G) = 2 := by
    rw [hcg, orderOf_conj_inv]; exact h.z_ord
  have hS : IsPGroup 2 ↥(zpowers (c : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  have hSK : zpowers (c : G) ≤ K := (Subgroup.zpowers_le).2 hcK
  have hordk : orderOf (QuotientGroup.mk k : HatT K) = 2 := by
    have := orderOf_hatMk (K := K) hSK hS (a := (c : G)) (Subgroup.mem_zpowers _)
    rw [hord] at this
    exact this
  have hnk : (QuotientGroup.mk k : HatT K) ∉ A.π.ker := by
    intro hker
    have h1 : A.π (QuotientGroup.mk k) = 1 := hker
    apply zeta_ne_one A hg
    rw [← hπk, h1]; rfl
  have hct := A.cover.cycleType_of_orderOf_eq_two hn8 hn11 hordk hnk
  rw [← hπk]
  exact hct


omit A hg in
theorem exists_pow_orderOf_eq_prime {M : Type*} [Monoid M] {p : ℕ} (hp : p.Prime) {w : M} {a : ℕ}
    (hw : w ^ (p ^ a) = 1) (hw1 : w ≠ 1) : ∃ k : ℕ, orderOf (w ^ k) = p := by
  obtain ⟨b', hb'm, hb'⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hw)
  have hb'1 : 1 ≤ b' := by
    by_contra hb0
    have : b' = 0 := by omega
    rw [this, pow_zero] at hb'
    exact hw1 (orderOf_eq_one_iff.1 hb')
  refine ⟨p ^ (b' - 1), ?_⟩
  rw [orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) (by rw [hb']; exact pow_dvd_pow p (by omega)), hb']
  rw [Nat.pow_div (by omega : b' - 1 ≤ b') hp.pos]
  have : b' - (b' - 1) = 1 := by omega
  rw [this, pow_one]

omit A hg in
theorem Act.surjective_of_odd (A : Act h n) {c₀ : ↥(Cz z)}
    (hc₀ : Equiv.Perm.sign (A.ρ c₀) = -1) : Function.Surjective A.ρ := by
  intro σ
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
  · obtain ⟨k, hk⟩ := A.exists_K σ h1
    exact ⟨_, hk⟩
  · have h2 : Equiv.Perm.sign (σ * (A.ρ c₀)⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, hc₀]; decide
    obtain ⟨k, hk⟩ := A.exists_K _ h2
    refine ⟨⟨(k : G), h.K_le k.2⟩ * c₀, ?_⟩
    rw [map_mul, hk]; group

theorem odd_card_ker_Theta (htK : t ∉ K) : Odd (Nat.card (Theta A hg).ker) := by
  classical
  by_contra hodd
  have hev : 2 ∣ Nat.card (Theta A hg).ker := by
    rcases Nat.even_or_odd (Nat.card (Theta A hg).ker) with he | ho
    · exact even_iff_two_dvd.1 he
    · exact absurd ho hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 hev
  set y : ↥(K ⊓ Cz t) := (u : ↥(K ⊓ Cz t)) with hy
  have hΘy : Theta A hg y = 1 := u.2
  have hy2 : y ^ 2 = 1 := by
    have : (u : ↥(Theta A hg).ker) ^ 2 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
    exact congrArg Subtype.val this
  have hyG : (y : G) ^ (2 ^ 1) = 1 := by
    have := congrArg (fun a : ↥(K ⊓ Cz t) => (a : G)) hy2
    simpa using this
  have hyc : (⟨(y : G), y.2.2⟩ : ↥(Cz t)) ∈
      (zpowers t).subgroupOf (Cz t) ⊔ (Ot g z).subgroupOf (Cz t) :=
    ThetaAll_ker_mem A hg (k := ⟨(y : G), y.2.2⟩) hΘy
  have hyc2 : (⟨(y : G), y.2.2⟩ : ↥(Cz t)) ^ (2 ^ 1) = 1 := Subtype.ext (by simpa using hyG)
  have := zpowers_subgroupOf_normal t
  have hmem := mem_of_mem_sup_odd (K := (zpowers t).subgroupOf (Cz t))
    (N := (Ot g z).subgroupOf (Cz t)) (Ot_subgroupOf_odd hg) hyc2 hyc
  have hyt : (y : G) ∈ zpowers t := hmem
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hyt
  have ht2 : t ^ 2 = 1 := by rw [← h.std.t_ord]; exact pow_orderOf_eq_one t
  have hjj : t ^ j = 1 ∨ t ^ j = t := by
    have hjj' : j = j % 2 + 2 * (j / 2) := (Int.emod_add_mul_ediv j 2).symm
    have ht2' : t ^ (2 : ℤ) = 1 := by simpa using ht2
    rw [hjj', zpow_add, zpow_mul, ht2', one_zpow, mul_one]
    rcases Int.emod_two_eq_zero_or_one j with h0 | h1
    · left; rw [h0, zpow_zero]
    · right; rw [h1, zpow_one]
  rcases hjj with h1 | h1
  ·
    have hy1 : y = 1 := Subtype.ext (by rw [← hj, h1]; rfl)
    have : u = 1 := Subtype.ext hy1
    rw [this, orderOf_one] at hu
    omega
  ·
    exact htK (by rw [← h1, hj]; exact y.2.1)


omit hg in
theorem cycleType_of_involution_in_K (hn8 : 8 ≤ n) (hn11 : n ≤ 11) {y : ↥K} (hy2 : (y : G) ^ 2 = 1)
    (hρ : A.ρ ⟨(y : G), h.K_le y.2⟩ ≠ 1) : (A.ρ ⟨(y : G), h.K_le y.2⟩).cycleType = {2, 2, 2, 2} := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy1 : (y : G) ≠ 1 := by
    intro h1
    apply hρ
    have : (⟨(y : G), h.K_le y.2⟩ : ↥(Cz z)) = 1 := Subtype.ext h1
    rw [this, map_one]
  have hord : orderOf (y : G) = 2 := orderOf_eq_prime hy2 hy1
  have hS : IsPGroup 2 ↥(zpowers (y : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  have hSK : zpowers (y : G) ≤ K := (Subgroup.zpowers_le).2 y.2
  have hordk : orderOf (QuotientGroup.mk y : HatT K) = 2 := by
    have := orderOf_hatMk (K := K) hSK hS (a := (y : G)) (Subgroup.mem_zpowers _)
    rw [hord] at this
    exact this
  have hnk : (QuotientGroup.mk y : HatT K) ∉ A.π.ker := by
    intro hker
    have h1 : A.π (QuotientGroup.mk y) = 1 := hker
    apply hρ
    rw [A.ρ_K y, h1]; rfl
  have hct := A.cover.cycleType_of_orderOf_eq_two hn8 hn11 hordk hnk
  rw [A.ρ_K y]
  exact hct

theorem exists_elemAbelian_in_T (hnp : n = 8 ∨ n = 9) {σ : Perm (Fin n)}
    (htρ : A.ρ ⟨t, h.std.t_cen⟩ = σ) (hσ : σ.cycleType = {2, 2, 2}) :
    ∃ E : Subgroup ↥(K ⊓ Cz t), (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ 2 = 1) ∧
      8 ≤ Nat.card E := by
  classical
  have hn8 : 8 ≤ n := by omega
  have hn11 : n ≤ 11 := by omega
  have hσodd : Equiv.Perm.sign σ = -1 := by
    rw [Equiv.Perm.sign_of_cycleType, hσ]; decide
  have hsurj : Function.Surjective A.ρ :=
    Act.surjective_of_odd A (c₀ := ⟨t, h.std.t_cen⟩) (by rw [htρ]; exact hσodd)
  have htK : t ∉ K := by
    intro htK
    have h1 := A.sign_K ⟨t, htK⟩
    have h2 : A.ρ ⟨(⟨t, htK⟩ : ↥K), h.K_le htK⟩ = σ := htρ
    rw [h2, hσodd] at h1
    exact absurd h1 (by decide)
  obtain ⟨hsign, x, ⟨a, hxa⟩, hΘx⟩ := zeta_even_and_exists_three A hg hn8 htρ hσ
  have hζct := zeta_cycleType A hg hn8 hn11 hsign
  have hwx : Theta A hg x ^ (3 ^ a) = 1 := by
    rw [← map_pow]
    have : x ^ (3 ^ a) = 1 := Subtype.ext (by simpa using hxa)
    rw [this, map_one]
  obtain ⟨k, hk⟩ := exists_pow_orderOf_eq_prime (p := 3) (by norm_num) hwx hΘx
  set ζ : Perm (Fin n) := Theta A hg ⟨z, h.z_mem, z_mem_Cz_t h⟩ with hζ
  set Q : Subgroup (Perm (Fin n)) := ((Cz z).subgroupOf (Cz t)).map (ThetaAll A hg) with hQdef
  set U : Subgroup (Perm (Fin n)) := (Theta A hg).range with hUdef
  have hdz : ∀ d : ↥(Cz t), (d : G) ∈ Cz z →
      d * (⟨z, z_mem_Cz_t h⟩ : ↥(Cz t)) = (⟨z, z_mem_Cz_t h⟩ : ↥(Cz t)) * d := fun d hd =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hd)
  have hQcomm : ∀ q ∈ Q, Commute q ζ := by
    rintro q ⟨d, hd, rfl⟩
    have hd' : (d : G) ∈ Cz z := hd
    show ThetaAll A hg d * ThetaAll A hg ⟨z, z_mem_Cz_t h⟩ = ThetaAll A hg ⟨z, z_mem_Cz_t h⟩ * ThetaAll A hg d
    rw [← map_mul, ← map_mul, hdz d hd']
  have hQH : ∀ q ∈ Q, ∀ x : Perm (Fin n), Commute x ζ → x * q * x⁻¹ ∈ Q := by
    rintro q ⟨d, hd, rfl⟩ x hx
    obtain ⟨d', hd', he⟩ := ThetaAll_conj_mem A hg hsurj (x := x) hx (d := d) hd
    rw [he]
    exact ⟨d', hd', rfl⟩
  have hUQ : U ≤ Q := by
    rintro u ⟨y, rfl⟩
    exact ⟨⟨(y : G), y.2.2⟩, h.K_le y.2.1, rfl⟩
  have hUnorm : ∀ u ∈ U, ∀ q ∈ Q, q * u * q⁻¹ ∈ U := by
    rintro u ⟨y, rfl⟩ q ⟨d, hd, rfl⟩
    have hd' : (d : G) ∈ Cz z := hd
    have hdK : (d : G) ∈ normalizer (K : Set G) := h.mem_normalizer hd'
    have hmemK : (d : G) * (y : G) * (d : G)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hdK _).1 y.2.1
    have hmemC : (d : G) * (y : G) * (d : G)⁻¹ ∈ Cz t :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ d.2 y.2.2) (Subgroup.inv_mem _ d.2)
    refine ⟨⟨(d : G) * (y : G) * (d : G)⁻¹, hmemK, hmemC⟩, ?_⟩
    show ThetaAll A hg ⟨(d : G) * (y : G) * (d : G)⁻¹, hmemC⟩ = ThetaAll A hg d * ThetaAll A hg ⟨(y : G), y.2.2⟩ * (ThetaAll A hg d)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hζU : ζ ∈ U := ⟨⟨z, h.z_mem, z_mem_Cz_t h⟩, rfl⟩
  have hwU : Theta A hg x ^ k ∈ U := U.pow_mem ⟨x, rfl⟩ k
  obtain ⟨E, hEU, hEc, hE2, hE8⟩ := exists_elemAbelian_of_normal_chain hnp hζct Q U hQcomm hQH hUQ
    hUnorm hζU hwU hk
  obtain ⟨E', hE'c, hE'2, hcard⟩ := exists_elemAbelian_of_odd_kernel (Theta A hg)
    (odd_card_ker_Theta A hg htK) E hEU hEc hE2
  exact ⟨E', hE'c, hE'2, le_trans hE8 hcard⟩


theorem false_of_three_transpositions (hnp : n = 8 ∨ n = 9) {σ : Perm (Fin n)}
    (htρ : A.ρ ⟨t, h.std.t_cen⟩ = σ) (hσ : σ.cycleType = {2, 2, 2}) : False := by
  classical
  have hn8 : 8 ≤ n := by omega
  have hn11 : n ≤ 11 := by omega
  obtain ⟨E, hEc, hE2, hE8⟩ := exists_elemAbelian_in_T A hg hnp htρ hσ
  let Rho : ↥(K ⊓ Cz t) →* Perm (Fin n) :=
    A.ρ.comp (Subgroup.inclusion (inf_le_left.trans h.K_le))
  have hRho : ∀ y : ↥(K ⊓ Cz t), Rho y = A.ρ ⟨(y : G), h.K_le y.2.1⟩ := fun y => rfl
  let φ : ↥E →* Perm (Fin n) := Rho.comp E.subtype
  have hker : Nat.card φ.ker ≤ 2 := by
    have hmem : ∀ e : ↥φ.ker, ((e : ↥E) : ↥(K ⊓ Cz t)) = 1 ∨
        (((e : ↥E) : ↥(K ⊓ Cz t)) : G) = z := by
      intro e
      have h1 : Rho ((e : ↥E) : ↥(K ⊓ Cz t)) = 1 := e.2
      have h2 : (((e : ↥E) : ↥(K ⊓ Cz t)) : G) ^ (2 ^ 1) = 1 := by
        have := hE2 _ (e : ↥E).2
        have h3 := congrArg (fun a : ↥(K ⊓ Cz t) => (a : G)) this
        simpa using h3
      have h4 := A.mem_zpowers_of_ker (c := ⟨(((e : ↥E) : ↥(K ⊓ Cz t)) : G), h.K_le (e : ↥E).1.2.1⟩)
        (by rw [← hRho]; exact h1) (m := 1) h2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 h4
      have hz2 : z ^ 2 = 1 := by rw [← h.z_ord]; exact pow_orderOf_eq_one z
      have hz2' : z ^ (2 : ℤ) = 1 := by simpa using hz2
      have hjj : z ^ j = 1 ∨ z ^ j = z := by
        have hjj' : j = j % 2 + 2 * (j / 2) := (Int.emod_add_mul_ediv j 2).symm
        rw [hjj', zpow_add, zpow_mul, hz2', one_zpow, mul_one]
        rcases Int.emod_two_eq_zero_or_one j with h0 | h1
        · left; rw [h0, zpow_zero]
        · right; rw [h1, zpow_one]
      rcases hjj with h5 | h5
      · left; exact Subtype.ext (by rw [← hj, h5]; rfl)
      · right; rw [← hj, h5]
    have hinj : Function.Injective (fun e : ↥φ.ker =>
        (⟨(((e : ↥E) : ↥(K ⊓ Cz t)) : G), by
          rcases hmem e with h1 | h1
          · left; rw [h1]; rfl
          · right; exact h1⟩ : ↥({1, z} : Set G))) := by
      intro e e' hee
      have := congrArg Subtype.val hee
      exact Subtype.ext (Subtype.ext (Subtype.ext this))
    calc Nat.card φ.ker ≤ Nat.card ↥({1, z} : Set G) := Nat.card_le_card_of_injective _ hinj
      _ = Set.ncard ({1, z} : Set G) := Nat.card_coe_set_eq _
      _ ≤ 2 := ncard_pair_le' 1 z
  have hcard : Nat.card E = Nat.card φ.range * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have hrange : 4 ≤ Nat.card φ.range := by
    by_contra hlt
    push Not at hlt
    have : Nat.card φ.range * Nat.card φ.ker ≤ 3 * 2 := Nat.mul_le_mul (by omega) hker
    omega
  have hfin : (φ.range : Set (Perm (Fin n))).Finite := Set.toFinite _
  have hncard : (φ.range : Set (Perm (Fin n))).ncard = Nat.card φ.range := by
    rw [← Nat.card_coe_set_eq]; rfl
  obtain ⟨α, hαR, hα1⟩ : ∃ α ∈ (φ.range : Set (Perm (Fin n))), α ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : (φ.range : Set (Perm (Fin n))) ⊆ {1} := fun a ha => hcon a ha
    have := Set.ncard_le_ncard this (Set.finite_singleton _)
    rw [Set.ncard_singleton] at this
    omega
  obtain ⟨β, hβR, hβ1, hβα⟩ : ∃ β ∈ (φ.range : Set (Perm (Fin n))), β ≠ 1 ∧ β ≠ α := by
    by_contra hcon
    push Not at hcon
    have : (φ.range : Set (Perm (Fin n))) ⊆ {1, α} := by
      intro a ha
      by_cases h1 : a = 1
      · exact Or.inl h1
      · exact Or.inr (hcon a ha h1)
    have := Set.ncard_le_ncard this (Set.toFinite _)
    have h2 : ({1, α} : Set (Perm (Fin n))).ncard ≤ 2 := ncard_pair_le' 1 α
    omega
  obtain ⟨y₁, hy₁⟩ := hαR
  obtain ⟨y₂, hy₂⟩ := hβR
  have hφ : ∀ y : ↥E, φ y = Rho (y : ↥(K ⊓ Cz t)) := fun y => rfl
  have hct : ∀ y : ↥E, φ y ≠ 1 → (φ y).cycleType = {2, 2, 2, 2} := by
    intro y hy
    have hy2 : ((y : ↥(K ⊓ Cz t)) : G) ^ 2 = 1 := by
      have := hE2 _ y.2
      have h3 := congrArg (fun a : ↥(K ⊓ Cz t) => (a : G)) this
      simpa using h3
    have := cycleType_of_involution_in_K A hn8 hn11 (y := ⟨((y : ↥(K ⊓ Cz t)) : G), (y : ↥(K ⊓ Cz t)).2.1⟩)
      hy2 (by rw [← hRho]; exact hy)
    rw [hφ, hRho]
    exact this
  have hcommσ : ∀ y : ↥(K ⊓ Cz t), Commute (Rho y) σ := by
    intro y
    rw [hRho, ← htρ]
    show A.ρ ⟨(y : G), h.K_le y.2.1⟩ * A.ρ ⟨t, h.std.t_cen⟩ = A.ρ ⟨t, h.std.t_cen⟩ * A.ρ ⟨(y : G), h.K_le y.2.1⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.1 y.2.2
  have hβ2 : β ^ 2 = 1 := by
    rw [← hy₂, hφ, ← map_pow]
    have := hE2 _ y₂.2
    rw [show ((y₂ : ↥(K ⊓ Cz t)) ^ 2) = 1 from this, map_one]
  have hαβ1 : α * β ≠ 1 := by
    intro h1
    apply hβα
    have : α = β⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact (inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hβ2)).symm
  have hφmul : φ (y₁ * y₂) = α * β := by rw [map_mul, hy₁, hy₂]
  have hαct : α.cycleType = {2, 2, 2, 2} := by rw [← hy₁]; exact hct y₁ (by rw [hy₁]; exact hα1)
  have hβct : β.cycleType = {2, 2, 2, 2} := by rw [← hy₂]; exact hct y₂ (by rw [hy₂]; exact hβ1)
  have hαβct : (α * β).cycleType = {2, 2, 2, 2} := by
    rw [← hφmul]; exact hct (y₁ * y₂) (by rw [hφmul]; exact hαβ1)
  have hα' : Commute α σ := by rw [← hy₁, hφ]; exact hcommσ _
  have hβ' : Commute β σ := by rw [← hy₂, hφ]; exact hcommσ _
  exact no_two_four_of_commuting hnp hσ hαct hβct hαβct hα' hβ'


omit hg in
theorem exists_conj_of_actsAsPerm (hn8 : 8 ≤ n) (hn11 : n ≤ 11) (hcov : IsDoubleCoverOfAlt Lh n)
    {e : (HatT K ⧸ center (HatT K)) ≃* alternatingGroup (Fin n)} {σ : Perm (Fin n)}
    (hact : ActsAsPerm t K n e σ) : ∃ τ : Perm (Fin n), A.ρ ⟨t, h.std.t_cen⟩ = τ⁻¹ * σ * τ := by
  classical
  have hn5 : 5 ≤ n := by omega
  have hn6 : n ≠ 6 := by omega
  set eA : (HatT K ⧸ center (HatT K)) ≃* alternatingGroup (Fin n) :=
    (QuotientGroup.quotientMulEquivOfEq (A.ker_eq_center hcov).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective A.π A.cover.surj) with heA
  have heA_mk : ∀ x : HatT K, eA (QuotientGroup.mk x) = A.π x := fun x => rfl
  let θ : MulAut (alternatingGroup (Fin n)) := eA.symm.trans e
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn5 hn6
  obtain ⟨τ, hτ⟩ := hbij.2 θ
  have key : ∀ a : alternatingGroup (Fin n),
      ((θ a : alternatingGroup (Fin n)) : Perm (Fin n)) = τ * a * τ⁻¹ := fun a => by
    rw [← hτ, MulAut.conjNormal_apply]
  have he_mk : ∀ x : HatT K, e (QuotientGroup.mk x) = θ (A.π x) := by
    intro x
    show e (QuotientGroup.mk x) = e (eA.symm (A.π x))
    rw [← heA_mk x, MulEquiv.symm_apply_apply]
  refine ⟨τ, ?_⟩
  apply CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n (by omega)
  refine MulEquiv.ext fun a => ?_
  obtain ⟨y, rfl⟩ := A.cover.surj a
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨k', hk'G, hk'⟩ := hact k
  have htN : t ∈ normalizer (K : Set G) := h.mem_normalizer h.std.t_cen
  have h1 := A.ρ_K k'
  have h2 := A.ρ_K k
  have e1 : (⟨(k' : G), h.K_le k'.2⟩ : ↥(Cz z)) =
      ⟨t, h.std.t_cen⟩ * ⟨(k : G), h.K_le k.2⟩ * ⟨t, h.std.t_cen⟩⁻¹ := Subtype.ext (by simpa using hk'G)
  rw [e1, map_mul, map_mul, map_inv, h2] at h1
  have h3 : ((A.π (QuotientGroup.mk k') : alternatingGroup (Fin n)) : Perm (Fin n)) =
      A.ρ ⟨t, h.std.t_cen⟩ * ((A.π (QuotientGroup.mk k) : alternatingGroup (Fin n)) : Perm (Fin n)) *
        (A.ρ ⟨t, h.std.t_cen⟩)⁻¹ := h1.symm
  have h4 := hk'
  rw [he_mk, he_mk, key, key] at h4
  have h5 : ((A.π (QuotientGroup.mk k') : alternatingGroup (Fin n)) : Perm (Fin n)) =
      (τ⁻¹ * σ * τ) * ((A.π (QuotientGroup.mk k) : alternatingGroup (Fin n)) : Perm (Fin n)) *
        (τ⁻¹ * σ * τ)⁻¹ := by
    have h6 : τ * ((A.π (QuotientGroup.mk k') : alternatingGroup (Fin n)) : Perm (Fin n)) * τ⁻¹ =
        σ * (τ * ((A.π (QuotientGroup.mk k) : alternatingGroup (Fin n)) : Perm (Fin n)) * τ⁻¹) * σ⁻¹ := h4
    calc ((A.π (QuotientGroup.mk k') : alternatingGroup (Fin n)) : Perm (Fin n))
        = τ⁻¹ * (τ * ((A.π (QuotientGroup.mk k') : alternatingGroup (Fin n)) : Perm (Fin n)) * τ⁻¹) * τ := by group
      _ = τ⁻¹ * (σ * (τ * ((A.π (QuotientGroup.mk k) : alternatingGroup (Fin n)) : Perm (Fin n)) * τ⁻¹) * σ⁻¹) * τ := by rw [h6]
      _ = _ := by group
  apply Subtype.ext
  rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply]
  rw [← h3, h5]

end C2



end CFSG.GH74.GLS.Stage1.Thm4.L96

namespace CFSG.GH74.GLS.Stage1.Thm4

open Equiv Equiv.Perm

theorem lemma9_6Outer3_thm : Lemma9_6Outer3 := by
  intro G _ _ Lh _ z t S K hstd hr1 hq1 n hn hcov e σ hct hact
  have h : Ctx98 G Lh z t S K := ⟨hstd, hr1, hq1⟩
  have hn8 : 8 ≤ n := by omega
  have hn11 : n ≤ 11 := by omega
  obtain ⟨A⟩ := L96.Act.exists h hn8 hn11 hcov
  obtain ⟨g, hg⟩ := isConj_iff.1 (h.isConj_z_t hcov)
  obtain ⟨τ, hτ⟩ := L96.exists_conj_of_actsAsPerm A hn8 hn11 hcov hact
  have hσ' : (A.ρ ⟨t, hstd.t_cen⟩).cycleType = {2, 2, 2} := by
    rw [hτ]
    have := Equiv.Perm.cycleType_conj (σ := σ) (τ := τ⁻¹)
    rw [inv_inv] at this
    rw [this]
    exact hct
  exact L96.false_of_three_transpositions A hg hn rfl hσ'

theorem lemma9_6_thm : Lemma9_6 := lemma9_6_of_outer3 lemma9_6Outer3_thm

end CFSG.GH74.GLS.Stage1.Thm4
