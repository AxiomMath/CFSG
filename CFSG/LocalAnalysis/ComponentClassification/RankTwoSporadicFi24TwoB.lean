module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24TwoBJ
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24Census
public import Certificates.Certificate1004
public import Certificates.Certificate1005
public import Certificates.Certificate1011
public import Certificates.Certificate1012
public import Certificates.Certificate1013
public import Certificates.Certificate1014
public import Certificates.Certificate1016
public import Certificates.Certificate1018
public import Certificates.Certificate1019
public import Certificates.Certificate2065
public import Certificates.Certificate2066
public import Certificates.Certificate2067
public import Certificates.Certificate2068
public import Certificates.Certificate2069
public import Certificates.Certificate2070
public import Certificates.Certificate2071
public import Certificates.Certificate2073
public import Certificates.Certificate2074
public import Certificates.Certificate2075
public import Certificates.Certificate2076
public import Certificates.Certificate2077
public import Certificates.Certificate2078
public import Certificates.Certificate3037
public import Certificates.Certificate3038
public import Certificates.Certificate3039
public import Certificates.Certificate3147
public import Certificates.Certificate3148
public import Certificates.Certificate3150
public import Certificates.Certificate3151
public import Certificates.Certificate3152
public import Certificates.Certificate3153
public import Certificates.Certificate3154
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24TwoBK

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime

open Subgroup
open scoped commutatorElement

theorem mul_comm_of_mul_self {G : Type*} [Group G] {H : Subgroup G} (h : ∀ x ∈ H, x * x = 1)
    {x y : G} (hx : x ∈ H) (hy : y ∈ H) : x * y = y * x := by
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (h x hx)
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (h y hy)
  calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right (h _ (H.mul_mem hx hy))).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hx', hy']

theorem commutatorElement_mul_central {G : Type*} [Group G] {a b k₁ k₂ : G}
    (h₁ : ∀ g, k₁ * g = g * k₁) (h₂ : ∀ g, k₂ * g = g * k₂) : ⁅a * k₁, b * k₂⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev, mul_inv_rev]
  calc a * k₁ * (b * k₂) * (k₁⁻¹ * a⁻¹) * (k₂⁻¹ * b⁻¹)
      = a * (k₁ * b) * (k₂ * (k₁⁻¹ * a⁻¹)) * k₂⁻¹ * b⁻¹ := by simp only [mul_assoc]
    _ = a * (b * k₁) * (k₁⁻¹ * a⁻¹ * k₂) * k₂⁻¹ * b⁻¹ := by rw [h₁ b, h₂ (k₁⁻¹ * a⁻¹)]
    _ = a * b * a⁻¹ * b⁻¹ := by group

section Abstract

variable {C S : Type*} [Group C] [Group S]

structure TwoBModel (z : C) (ρ : C →* S) (K N : Subgroup S) : Prop where
  central : ∀ c : C, c * z = z * c
  ker : ∀ c : C, ρ c = 1 ↔ c = 1 ∨ c = z
  range : ρ.range = K
  perfect : ⁅⁅K, K⁆, ⁅K, K⁆⁆ = ⁅K, K⁆
  le : N ≤ ⁅K, K⁆
  normal : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N
  sq : ∀ n ∈ N, n * n = 1
  irred : ∀ M : Subgroup S, M ≤ N → (∀ k ∈ ⁅K, K⁆, ∀ y ∈ M, k * y * k⁻¹ ∈ M) → M = ⊥ ∨ M = N
  selfCent : ∀ x ∈ K, (∀ n ∈ N, x * n = n * x) → x ∈ N
  cent : ∀ c : S, (∀ k ∈ ⁅K, K⁆, c * k = k * c) → c = 1
  noncomm : ∃ q₁ q₂ : C, ρ q₁ ∈ N ∧ ρ q₂ ∈ N ∧ q₁ * q₂ ≠ q₂ * q₁

namespace TwoBModel

variable {z : C} {ρ : C →* S} {K N : Subgroup S}

theorem rho_z (hm : TwoBModel z ρ K N) : ρ z = 1 := (hm.ker z).2 (Or.inr rfl)

theorem central_of_ker (hm : TwoBModel z ρ K N) {k : C} (hk : ρ k = 1) (g : C) :
    k * g = g * k := by
  rcases (hm.ker k).1 hk with rfl | rfl
  · rw [one_mul, mul_one]
  · exact (hm.central g).symm

omit [Group S] in
theorem exists_eq_mul {T : Type*} [Group T] {σ : C →* T} {c d : C} (h : σ c = σ d) :
    ∃ k, σ k = 1 ∧ c = d * k :=
  ⟨d⁻¹ * c, by rw [map_mul, map_inv, h, inv_mul_cancel], by rw [mul_inv_cancel_left]⟩

theorem ker_le (hm : TwoBModel z ρ K N) {H : Subgroup C} (hz : z ∈ H) :
    ∀ k, ρ k = 1 → k ∈ H := fun k hk => by
  rcases (hm.ker k).1 hk with rfl | rfl
  · exact H.one_mem
  · exact hz

theorem mem_of_map (hm : TwoBModel z ρ K N) {H : Subgroup C} (hz : z ∈ H) {c : C}
    (hc : ρ c ∈ H.map ρ) : c ∈ H := by
  obtain ⟨d, hd, e⟩ := hc
  obtain ⟨k, hk, rfl⟩ := exists_eq_mul e.symm
  exact H.mul_mem hd (hm.ker_le hz k hk)

theorem mem_K (hm : TwoBModel z ρ K N) (c : C) : ρ c ∈ K := by
  rw [← hm.range]
  exact ⟨c, rfl⟩

theorem map_commutator_top (hm : TwoBModel z ρ K N) : (commutator C).map ρ = ⁅K, K⁆ := by
  rw [commutator_def, map_commutator, ← MonoidHom.range_eq_map, hm.range]

theorem commutator_eq_z (hm : TwoBModel z ρ K N) {q₁ q₂ : C} (h₁ : ρ q₁ ∈ N) (h₂ : ρ q₂ ∈ N)
    (hne : q₁ * q₂ ≠ q₂ * q₁) {H : Subgroup C} (hH : ρ q₁ ∈ H.map ρ ∧ ρ q₂ ∈ H.map ρ) :
    z ∈ ⁅H, H⁆ := by
  obtain ⟨⟨p₁, hp₁, e₁⟩, ⟨p₂, hp₂, e₂⟩⟩ := hH
  obtain ⟨k₁, hk₁, rfl⟩ := exists_eq_mul e₁.symm
  obtain ⟨k₂, hk₂, rfl⟩ := exists_eq_mul e₂.symm
  have hcomm := commutatorElement_mul_central (a := p₁) (b := p₂)
    (fun g => hm.central_of_ker hk₁ g) (fun g => hm.central_of_ker hk₂ g)
  have hker : ρ ⁅p₁ * k₁, p₂ * k₂⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm_of_mul_self hm.sq h₁ h₂
  rcases (hm.ker _).1 hker with h1 | hz
  · exact absurd (commutatorElement_eq_one_iff_mul_comm.1 h1) hne
  · rw [← hz, hcomm]
    exact commutator_mem_commutator hp₁ hp₂

theorem z_mem_commutator (hm : TwoBModel z ρ K N) :
    z ∈ ⁅commutator C, commutator C⁆ := by
  obtain ⟨q₁, q₂, h₁, h₂, hne⟩ := hm.noncomm
  refine hm.commutator_eq_z h₁ h₂ hne ⟨?_, ?_⟩
  · rw [hm.map_commutator_top]
    exact hm.le h₁
  · rw [hm.map_commutator_top]
    exact hm.le h₂

theorem z_mem (hm : TwoBModel z ρ K N) : z ∈ commutator C :=
  commutator_le_self _ hm.z_mem_commutator

theorem perfect' (hm : TwoBModel z ρ K N) :
    ⁅commutator C, commutator C⁆ = commutator C := by
  refine le_antisymm (commutator_le_self _) fun p hp => ?_
  have hD : (⁅commutator C, commutator C⁆).map ρ = ⁅K, K⁆ := by
    rw [map_commutator, hm.map_commutator_top, hm.perfect]
  apply hm.mem_of_map hm.z_mem_commutator
  rw [hD, ← hm.map_commutator_top]
  exact mem_map_of_mem ρ hp

theorem Q_le (hm : TwoBModel z ρ K N) : N.comap ρ ≤ commutator C := fun q hq => by
  apply hm.mem_of_map hm.z_mem
  rw [hm.map_commutator_top]
  exact hm.le hq

theorem Q_normal (hm : TwoBModel z ρ K N) :
    ∀ p ∈ commutator C, ∀ q ∈ N.comap ρ, p * q * p⁻¹ ∈ N.comap ρ := by
  intro p _ q hq
  show ρ (p * q * p⁻¹) ∈ N
  rw [map_mul, map_mul, map_inv]
  exact hm.normal _ (hm.mem_K p) _ hq

theorem irreducible (hm : TwoBModel z ρ K N) (M : Subgroup C) (hM : M ≤ N.comap ρ)
    (hinv : ∀ p ∈ commutator C, ∀ y ∈ M, p * y * p⁻¹ ∈ M) :
    M ≤ zpowers z ∨ M = N.comap ρ := by
  have hMN : M.map ρ ≤ N := map_le_iff_le_comap.2 hM
  have hinv' : ∀ k ∈ ⁅K, K⁆, ∀ y ∈ M.map ρ, k * y * k⁻¹ ∈ M.map ρ := by
    rintro k hk _ ⟨y, hy, rfl⟩
    rw [← hm.map_commutator_top] at hk
    obtain ⟨p, hp, rfl⟩ := hk
    exact ⟨p * y * p⁻¹, hinv p hp y hy, by rw [map_mul, map_mul, map_inv]⟩
  rcases hm.irred _ hMN hinv' with hbot | htop
  · left
    intro y hy
    have hy1 : ρ y = 1 := by
      have := mem_map_of_mem ρ hy
      rwa [hbot, mem_bot] at this
    rcases (hm.ker y).1 hy1 with rfl | rfl
    · exact one_mem _
    · exact mem_zpowers _
  · right
    obtain ⟨q₁, q₂, h₁, h₂, hne⟩ := hm.noncomm
    have hzM : z ∈ M := by
      have := hm.commutator_eq_z h₁ h₂ hne (H := M) ⟨by rw [htop]; exact h₁, by rw [htop]; exact h₂⟩
      exact commutator_le_self _ this
    refine le_antisymm hM fun q hq => hm.mem_of_map hzM ?_
    rw [htop]
    exact hq

theorem faithful (hm : TwoBModel z ρ K N) (x : C)
    (h : ∀ q ∈ N.comap ρ, ⁅x, q⁆ ∈ zpowers z) : x ∈ N.comap ρ := by
  show ρ x ∈ N
  refine hm.selfCent _ (hm.mem_K x) fun n hn => ?_
  obtain ⟨q, rfl⟩ : n ∈ ρ.range := by
    rw [hm.range]
    exact commutator_le_self _ (hm.le hn)
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (h q hn)
  have h1 : ρ ⁅x, q⁆ = 1 := by rw [← hk, map_zpow, hm.rho_z, one_zpow]
  rwa [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1

theorem orderFour (hm : TwoBModel z ρ K N) : ∃ y ∈ N.comap ρ, 4 ∣ orderOf y := by
  obtain ⟨q₁, q₂, h₁, h₂, hne⟩ := hm.noncomm
  have hy : ∃ y ∈ N.comap ρ, y * y ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hne (mul_comm_of_mul_self hall h₁ h₂)
  obtain ⟨y, hyQ, hy1⟩ := hy
  have hz : y * y = z := by
    have h1 : ρ (y * y) = 1 := by rw [map_mul]; exact hm.sq _ hyQ
    rcases (hm.ker _).1 h1 with h | h
    · exact absurd h hy1
    · exact h
  have hzz : z * z = 1 := by
    have h1 : ρ (z * z) = 1 := by rw [map_mul, hm.rho_z, one_mul]
    rcases (hm.ker _).1 h1 with h | h
    · exact h
    · have hz1 : z = 1 := mul_left_cancel (a := z) (by rw [mul_one]; exact h)
      exact absurd (hz.trans hz1) hy1
  have hord : orderOf y = 2 ^ (1 + 1) := by
    refine orderOf_eq_prime_pow (p := 2) ?_ ?_
    · rw [pow_one, pow_two]
      exact hy1
    · rw [show (2 : ℕ) ^ (1 + 1) = 2 * 2 from rfl, pow_mul, pow_two y, hz, pow_two, hzz]
  exact ⟨y, hyQ, by rw [hord]; norm_num⟩

theorem centralizer (hm : TwoBModel z ρ K N) (c : C)
    (hc : ∀ p ∈ commutator C, c * p = p * c) : c ∈ zpowers z := by
  have h1 : ρ c = 1 := by
    apply hm.cent
    intro k hk
    rw [← hm.map_commutator_top] at hk
    obtain ⟨p, hp, rfl⟩ := hk
    rw [← map_mul, ← map_mul, hc p hp]
  rcases (hm.ker c).1 h1 with rfl | rfl
  · exact one_mem _
  · exact mem_zpowers _

variable {H : Type*} [Group H] {f : C →* H}

theorem map_perfect (hm : TwoBModel z ρ K N) :
    ⁅(commutator C).map f, (commutator C).map f⁆ = (commutator C).map f := by
  rw [← map_commutator, hm.perfect']

theorem map_Q_le (hm : TwoBModel z ρ K N) : (N.comap ρ).map f ≤ (commutator C).map f :=
  map_mono hm.Q_le

theorem map_Q_normal (hm : TwoBModel z ρ K N) : ∀ p ∈ (commutator C).map f,
    ∀ q ∈ (N.comap ρ).map f, p * q * p⁻¹ ∈ (N.comap ρ).map f := by
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
  exact ⟨p * q * p⁻¹, hm.Q_normal p hp q hq, by rw [map_mul, map_mul, map_inv]⟩

theorem map_irreducible (hm : TwoBModel z ρ K N) (hf : Function.Injective f) (M : Subgroup H)
    (hM : M ≤ (N.comap ρ).map f)
    (hinv : ∀ p ∈ (commutator C).map f, ∀ y ∈ M, p * y * p⁻¹ ∈ M) :
    M ≤ zpowers (f z) ∨ M = (N.comap ρ).map f := by
  have hMeq : (M.comap f).map f = M := map_comap_eq_self (hM.trans (map_le_range f _))
  have hM' : M.comap f ≤ N.comap ρ := by
    intro x hx
    obtain ⟨y, hy, e⟩ := hM hx
    rw [← hf e]
    exact hy
  have hinv' : ∀ p ∈ commutator C, ∀ y ∈ M.comap f, p * y * p⁻¹ ∈ M.comap f := by
    intro p hp y hy
    show f (p * y * p⁻¹) ∈ M
    rw [map_mul, map_mul, map_inv]
    exact hinv _ ⟨p, hp, rfl⟩ _ hy
  rcases hm.irreducible _ hM' hinv' with h | h
  · left
    rw [← hMeq, ← MonoidHom.map_zpowers]
    exact map_mono h
  · right
    rw [← hMeq, h]

theorem map_faithful (hm : TwoBModel z ρ K N) (hf : Function.Injective f) (x : H)
    (hx : x ∈ (commutator C).map f)
    (h : ∀ q ∈ (N.comap ρ).map f, ⁅x, q⁆ ∈ zpowers (f z)) : x ∈ (N.comap ρ).map f := by
  obtain ⟨x', -, rfl⟩ := hx
  refine ⟨x', hm.faithful x' fun q hq => ?_, rfl⟩
  have h1 := h (f q) ⟨q, hq, rfl⟩
  rw [← map_commutatorElement, ← MonoidHom.map_zpowers] at h1
  obtain ⟨w, hw, e⟩ := h1
  rw [← hf e]
  exact hw

theorem map_orderFour (hm : TwoBModel z ρ K N) (hf : Function.Injective f) :
    ∃ y ∈ (N.comap ρ).map f, 4 ∣ orderOf y := by
  obtain ⟨y, hy, h4⟩ := hm.orderFour
  exact ⟨f y, ⟨y, hy, rfl⟩, by rw [orderOf_injective f hf y]; exact h4⟩

theorem map_centralizer (hm : TwoBModel z ρ K N) (hf : Function.Injective f) (c : H)
    (hcr : c ∈ f.range) (hc : ∀ p ∈ (commutator C).map f, c * p = p * c) :
    c ∈ zpowers (f z) := by
  obtain ⟨c', rfl⟩ := hcr
  rw [← MonoidHom.map_zpowers]
  refine ⟨c', hm.centralizer c' fun p hp => hf ?_, rfl⟩
  rw [map_mul, map_mul]
  exact hc _ ⟨p, hp, rfl⟩

theorem map_z_mem (hm : TwoBModel z ρ K N) : f z ∈ (commutator C).map f :=
  ⟨z, hm.z_mem, rfl⟩

end TwoBModel

end Abstract

theorem mk_mul_mk_ne {G : Type*} [Group G] {H : Subgroup G} {a b : G} (ha : a ∈ H) (hb : b ∈ H)
    (h : a * b ≠ b * a) : (⟨a, ha⟩ : H) * ⟨b, hb⟩ ≠ ⟨b, hb⟩ * ⟨a, ha⟩ :=
  fun e => h (congrArg Subtype.val e)

theorem wordG_mem {G : Type*} [Group G] {H : Subgroup G} {g : ℤ → G} (hg : ∀ z, g z ∈ H)
    (w : List ℤ) : CFSG.Sporadic.Th.wordG g w ∈ H := by
  induction w with
  | nil =>
    rw [wordG_nil]
    exact H.one_mem
  | cons z w ih =>
    rw [wordG_cons]
    exact H.mul_mem (hg z) ih

theorem wordG_map {G H : Type*} [Group G] [Group H] (f : G →* H) (g : ℤ → G) (w : List ℤ) :
    f (CFSG.Sporadic.Th.wordG g w) = CFSG.Sporadic.Th.wordG (fun z => f (g z)) w := by
  induction w with
  | nil => rw [wordG_nil, wordG_nil, map_one]
  | cons z w ih => rw [wordG_cons, wordG_cons, map_mul, ih]

theorem wordG_congr {G : Type*} [Group G] {g g' : ℤ → G} {w : List ℤ}
    (h : ∀ z ∈ w, g z = g' z) : CFSG.Sporadic.Th.wordG g w = CFSG.Sporadic.Th.wordG g' w := by
  induction w with
  | nil => rw [wordG_nil, wordG_nil]
  | cons z w ih =>
    rw [wordG_cons, wordG_cons, h z List.mem_cons_self,
      ih fun z hz => h z (List.mem_cons_of_mem _ hz)]

section Concrete

open CFSG.Sporadic.FischerOddCore
open CFSG.Sporadic.Fi24 (R J tR jR JR)

attribute [local instance] CFSG.Sporadic.Fi24.rAction

@[expose] noncomputable def fi24Rho :
    ↥fi24C →* Equiv.Perm (Fin 504) :=
  Classical.choose (exists_famHom ((MulAction.toPermHom J (Fin 306936)).comp fi24C.subtype)
    fi24FPt_injective fi24C_inv)

theorem fi24Rho_spec
    (c : ↥fi24C) (j : Fin 504) : fi24FPt (fi24Rho c j) = (c : J) • fi24FPt j :=
  Classical.choose_spec (exists_famHom ((MulAction.toPermHom J (Fin 306936)).comp fi24C.subtype)
    fi24FPt_injective fi24C_inv) c j

theorem fi24Rho_a :
    fi24Rho ⟨fi24Ca, fi24Ca_mem⟩ = fi24Sa :=
  Equiv.ext fun j => fi24FPt_injective (by rw [fi24Rho_spec]; exact fi24Ca_smul j)

theorem fi24Rho_b :
    fi24Rho ⟨fi24Cb, fi24Cb_mem⟩ = fi24Sb :=
  Equiv.ext fun j => fi24FPt_injective (by rw [fi24Rho_spec]; exact fi24Cb_smul j)

theorem fi24Rho_z :
    fi24Rho ⟨fi24R2, fi24R2_mem_C⟩ = 1 :=
  Equiv.ext fun j => fi24FPt_injective (by
    rw [fi24Rho_spec, Equiv.Perm.one_apply]
    exact fi24R2_smul_fi24FPt j)

theorem fi24Rho_range_card :
    fi24Rho.range = fi24K ∧ Nat.card fi24Rho.ker = 2 := by
  have hKle : fi24K ≤ fi24Rho.range := by
    rw [fi24K_eq, closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨_, fi24Rho_a⟩
    · exact ⟨_, fi24Rho_b⟩
  have hker2 : 2 ≤ Nat.card fi24Rho.ker := by
    have hne : fi24Rho.ker ≠ ⊥ := fun h => by
      have hz : (⟨fi24R2, fi24R2_mem_C⟩ : ↥fi24C) ∈ fi24Rho.ker := fi24Rho_z
      rw [h, mem_bot] at hz
      exact fi24R2_ne_one (congrArg Subtype.val hz)
    exact (one_lt_card_iff_ne_bot _).2 hne
  have hcard := card_mul_index fi24Rho.ker
  rw [index_ker] at hcard
  have hrange : Nat.card fi24K ≤ Nat.card fi24Rho.range := card_le_of_le hKle
  rw [card_fi24K] at hrange
  have hC := card_fi24C_le
  have hb : Nat.card fi24Rho.range = 80263249920 := by
    have h2b : 2 * Nat.card fi24Rho.range ≤ Nat.card fi24Rho.ker * Nat.card fi24Rho.range :=
      Nat.mul_le_mul_right _ hker2
    have h1 : 2 * Nat.card fi24Rho.range ≤ 2 * 80263249920 :=
      h2b.trans (hcard.le.trans (hC.trans (by norm_num)))
    exact le_antisymm (Nat.le_of_mul_le_mul_left h1 (by norm_num)) hrange
  refine ⟨(eq_of_le_of_card_ge hKle (by rw [hb, card_fi24K])).symm, ?_⟩
  rw [hb] at hcard
  have h1 : Nat.card fi24Rho.ker * 80263249920 ≤ 2 * 80263249920 :=
    hcard.le.trans (hC.trans (by norm_num))
  exact le_antisymm (Nat.le_of_mul_le_mul_right h1 (by norm_num)) hker2

theorem fi24Rho_eq_one_iff
    (c : ↥fi24C) : fi24Rho c = 1 ↔ c = 1 ∨ c = ⟨fi24R2, fi24R2_mem_C⟩ := by
  constructor
  · intro hc
    by_cases h1 : c = 1
    · exact Or.inl h1
    · right
      obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥fi24Rho.ker)).1 fi24Rho_range_card.2
      have hz1 : (⟨⟨fi24R2, fi24R2_mem_C⟩, fi24Rho_z⟩ : ↥fi24Rho.ker) ≠ 1 := fun h =>
        fi24R2_ne_one (congrArg (fun x : ↥fi24Rho.ker => ((x : ↥fi24C) : J)) h)
      have hc1 : (⟨c, hc⟩ : ↥fi24Rho.ker) ≠ 1 := fun h => h1 (congrArg Subtype.val h)
      exact congrArg Subtype.val ((huniq _ hc1).trans (huniq _ hz1).symm)
  · rintro (rfl | rfl)
    · exact map_one _
    · exact fi24Rho_z

@[expose] noncomputable def fi24Phi :
    ↥fi24K →* Equiv.Perm (Fin 378) :=
  Classical.choose (exists_famHom (conjPerm.comp fi24K.subtype) fi24Sj_injective
    fun h j => fi24K_conj_inv h.2 j)

theorem fi24Phi_spec
    (h : ↥fi24K) (j : Fin 378) :
    fi24Sj (fi24Phi h j) = (h : Equiv.Perm (Fin 504)) * fi24Sj j * (h : Equiv.Perm (Fin 504))⁻¹ :=
  Classical.choose_spec (exists_famHom (conjPerm.comp fi24K.subtype) fi24Sj_injective
    fun h j => fi24K_conj_inv h.2 j) h j

theorem fi24Phi_eq_one_iff
    (h : ↥fi24K) :
    fi24Phi h = 1 ↔ ∀ j, (h : Equiv.Perm (Fin 504)) * fi24Sj j = fi24Sj j * h := by
  constructor
  · intro h1 j
    have e := fi24Phi_spec h j
    rw [h1, Equiv.Perm.one_apply] at e
    calc (h : Equiv.Perm (Fin 504)) * fi24Sj j =
        (h : Equiv.Perm (Fin 504)) * fi24Sj j * (h : Equiv.Perm (Fin 504))⁻¹ * h := by group
      _ = fi24Sj j * h := by rw [← e]
  · intro hc
    exact Equiv.ext fun j => fi24Sj_injective (by
      rw [fi24Phi_spec, Equiv.Perm.one_apply, hc j, mul_inv_cancel_right])

theorem card_fi24Phi_ker_le :
    Nat.card fi24Phi.ker ≤ 4096 := by
  have hφa : fi24Phi ⟨fi24Sa, fi24Sa_mem⟩ = fi24Pa :=
    Equiv.ext fun j => fi24Sj_injective (by rw [fi24Phi_spec]; exact fi24Sj_conj_a j)
  have hφb : fi24Phi ⟨fi24Sb, fi24Sb_mem⟩ = fi24Pb :=
    Equiv.ext fun j => fi24Sj_injective (by rw [fi24Phi_spec]; exact fi24Sj_conj_b j)
  have hle : fi24P ≤ fi24Phi.range := by
    rw [fi24P_eq, closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨_, hφa⟩
    · exact ⟨_, hφb⟩
  have h1 := card_mul_index fi24Phi.ker
  rw [index_ker, card_fi24K] at h1
  have h2 := card_le_of_le hle
  rw [card_fi24P] at h2
  have h3 := Nat.mul_le_mul_left (Nat.card fi24Phi.ker) h2
  have h4 : Nat.card fi24Phi.ker * 19595520 ≤ 4096 * 19595520 :=
    h3.trans (h1.le.trans (by norm_num))
  exact Nat.le_of_mul_le_mul_right h4 (by norm_num)

theorem fi24N_le_fi24K
    (hK : fi24TwoBKCheck = true) : fi24N ≤ fi24K := by
  obtain ⟨hc, hN, -, -⟩ := fi24TwoBKCheck_parts hK
  refine (fi24N_le_fi24Kd hc hN).trans ?_
  rw [fi24Kd_eq hc]
  exact commutator_le_self _

theorem fi24N_subgroupOf_eq_ker
    (hK : fi24TwoBKCheck = true) : fi24N.subgroupOf fi24K = fi24Phi.ker := by
  obtain ⟨-, hN, -, -⟩ := fi24TwoBKCheck_parts hK
  have hle : fi24N.subgroupOf fi24K ≤ fi24Phi.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, fi24Phi_eq_one_iff]
    intro j
    exact mul_comm_of_mul_self (fun y hy => fi24N_mul_self hN hy) (mem_subgroupOf.1 hx)
      (fi24Sj_mem_fi24N hN j)
  refine eq_of_le_of_card_ge hle ?_
  rw [Nat.card_congr (subgroupOfEquivOfLe (fi24N_le_fi24K hK)).toEquiv, card_fi24N hN]
  exact card_fi24Phi_ker_le

theorem fi24N_normal_K
    (hK : fi24TwoBKCheck = true) : ∀ k ∈ fi24K, ∀ n ∈ fi24N, k * n * k⁻¹ ∈ fi24N := by
  intro k hk n hn
  have hker : (⟨n, fi24N_le_fi24K hK hn⟩ : ↥fi24K) ∈ fi24Phi.ker := by
    rw [← fi24N_subgroupOf_eq_ker hK]
    exact hn
  have h := fi24Phi.normal_ker.conj_mem _ hker ⟨k, hk⟩
  rw [← fi24N_subgroupOf_eq_ker hK] at h
  exact h

theorem fi24N_selfCent
    (hK : fi24TwoBKCheck = true) :
    ∀ x ∈ fi24K, (∀ n ∈ fi24N, x * n = n * x) → x ∈ fi24N := by
  obtain ⟨-, hN, -, -⟩ := fi24TwoBKCheck_parts hK
  intro x hx hc
  have hker : (⟨x, hx⟩ : ↥fi24K) ∈ fi24Phi.ker := by
    rw [MonoidHom.mem_ker, fi24Phi_eq_one_iff]
    exact fun j => hc _ (fi24Sj_mem_fi24N hN j)
  rw [← fi24N_subgroupOf_eq_ker hK] at hker
  exact hker

theorem fi24QElt_mem
    (e : List ℤ × ℕ) : fi24QElt e ∈ fi24C := by
  refine pow_mem (wordG_mem (fun z => ?_) e.1) e.2
  by_cases hz : z = 1
  · rw [ite_eq_left hz]
    exact fi24Ca_mem
  · rw [ite_eq_right hz]
    exact fi24Cb_mem

theorem fi24Rho_QElt
    (e : List ℤ × ℕ) (hl : ∀ z ∈ e.1, z = 1 ∨ z = 2) :
    fi24Rho ⟨fi24QElt e, fi24QElt_mem e⟩ = (CFSG.Sporadic.Th.wordG fi24KLetterG e.1) ^ e.2 := by
  let g : ℤ → ↥fi24C := fun z => if z = 1 then ⟨fi24Ca, fi24Ca_mem⟩ else ⟨fi24Cb, fi24Cb_mem⟩
  have h1 : (⟨fi24QElt e, fi24QElt_mem e⟩ : ↥fi24C) = (CFSG.Sporadic.Th.wordG g e.1) ^ e.2 := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow]
    have h2 := wordG_map fi24C.subtype g e.1
    rw [Subgroup.coe_subtype] at h2
    show fi24QElt e = _
    rw [fi24QElt, h2]
    congr 1
    apply wordG_congr
    intro z _
    by_cases hz : z = 1
    · simp only [g, hz, ite_true]
    · simp only [g, hz, ite_false]
  rw [h1, map_pow, wordG_map]
  congr 1
  apply wordG_congr
  intro z hz
  rcases hl z hz with rfl | rfl
  · simp only [g, ite_true, fi24Rho_a, fi24KLetterG]
  · simp only [g, fi24KLetterG]
    norm_num
    exact fi24Rho_b

theorem fi24TwoBModel
    (hK : fi24TwoBKCheck = true) (hJ : TwoBJFacts) :
    TwoBModel (⟨fi24R2, fi24R2_mem_C⟩ : ↥fi24C) fi24Rho fi24K fi24N := by
  obtain ⟨hc, hN, -, -⟩ := fi24TwoBKCheck_parts hK
  refine ⟨fun c => Subtype.ext (mem_centralizer_singleton_iff.1 c.2), fi24Rho_eq_one_iff,
    fi24Rho_range_card.1, ?_, ?_, fi24N_normal_K hK, fun n hn => fi24N_mul_self hN hn,
    fun M hM hinv => fi24N_irreducible hK M hM ?_, fi24N_selfCent hK,
    fun c hc' => eq_one_of_commute_fi24Kd hK ?_, ?_⟩
  · rw [← fi24Kd_eq hc, commutator_fi24Kd hc]
  · rw [← fi24Kd_eq hc]
    exact fi24N_le_fi24Kd hc hN
  · rw [fi24Kd_eq hc]
    exact hinv
  · rw [fi24Kd_eq hc]
    exact hc'
  · obtain ⟨e, he, hne⟩ := exists_fi24Q_ne hJ
    have h0 : fi24QWords[0]! ∈ fi24QWords := by
      have hl : 0 < fi24QWords.length := by simp [fi24QWords]
      rw [getElem!_pos fi24QWords 0 hl]
      exact List.getElem_mem hl
    obtain ⟨hl0, hN0⟩ := fi24QWord_mem hK h0
    obtain ⟨hle, hNe⟩ := fi24QWord_mem hK (List.mem_of_mem_tail he)
    refine ⟨⟨fi24QElt fi24QWords[0]!, fi24QElt_mem _⟩, ⟨fi24QElt e, fi24QElt_mem _⟩, ?_, ?_,
      mk_mul_mk_ne _ _ hne⟩
    · rw [fi24Rho_QElt _ hl0]
      exact hN0
    · rw [fi24Rho_QElt _ hle]
      exact hNe

end Concrete

section Transport

open CFSG.Sporadic.FischerOddCore
open CFSG.Sporadic.Fi24 (R J tR jR JR jR_injective jR_mem_JR range_jR eq_jR_or jR_comm_tR
  jR_smul)

attribute [local instance] CFSG.Sporadic.Fi24.rAction

@[expose] noncomputable def fi24CR :
    ↥fi24C →* R :=
  jR.comp fi24C.subtype

theorem fi24CR_injective :
    Function.Injective fi24CR :=
  jR_injective.comp Subtype.val_injective

theorem fi24CR_z :
    fi24CR ⟨fi24R2, fi24R2_mem_C⟩ = zR :=
  rfl

theorem fi24CR_range :
    fi24CR.range = JR ⊓ centralizer ({zR} : Set R) := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨jR_mem_JR _, mem_centralizer_singleton_iff.2 ?_⟩
    show jR (c : J) * jR fi24R2 = jR fi24R2 * jR (c : J)
    rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 c.2]
  · rintro ⟨hx, hxc⟩
    obtain ⟨g, rfl⟩ : x ∈ jR.range := by
      rw [range_jR]
      exact hx
    have h := mem_centralizer_singleton_iff.1 hxc
    unfold zR at h
    rw [← map_mul, ← map_mul] at h
    exact ⟨⟨g, mem_centralizer_singleton_iff.2 (jR_injective h)⟩, rfl⟩

theorem PB_eq :
    PB = (commutator ↥fi24C).map fi24CR := by
  rw [PB, centDer, ← fi24CR_range, commutator_def, map_commutator, ← MonoidHom.range_eq_map]

@[expose] noncomputable def fi24QR :
    Subgroup R :=
  (fi24N.comap fi24Rho).map fi24CR

theorem fi24_not_outer
    (hK : fi24TwoBKCheck = true) (hJ : TwoBJFacts) (g : J)
    (hc : ∀ p ∈ (commutator ↥fi24C).map fi24CR, jR g * tR * p = p * (jR g * tR)) : False := by
  have hm := fi24TwoBModel hK hJ
  have hcz : jR g * tR * zR = zR * (jR g * tR) := hc _ hm.map_z_mem
  have htz : jR fi24R2 * tR = tR * jR fi24R2 := jR_comm_tR fi24R2_mem_M
  have hgz : g * fi24R2 = fi24R2 * g := by
    apply jR_injective
    rw [map_mul, map_mul]
    refine mul_right_cancel (b := tR) ?_
    calc jR g * jR fi24R2 * tR = jR g * tR * zR := by rw [mul_assoc, htz, ← mul_assoc]; rfl
      _ = zR * (jR g * tR) := hcz
      _ = jR fi24R2 * jR g * tR := by rw [← mul_assoc]; rfl
  have hgC : g ∈ fi24C := mem_centralizer_singleton_iff.2 hgz
  have hσex : ∀ j : Fin 504, ∃ j', fi24FPt j' = tR • fi24FPt j := fun j => by
    apply exists_fi24FPt
    rw [← jR_smul, smul_smul, htz, mul_smul, jR_smul, fi24R2_smul_fi24FPt]
  choose σf hσf using hσex
  have hσinj : Function.Injective σf := fun i j h =>
    fi24FPt_injective (smul_left_cancel tR (by rw [← hσf, ← hσf, h]))
  let σ : Equiv.Perm (Fin 504) := Equiv.ofBijective σf (Finite.injective_iff_bijective.1 hσinj)
  have hσ : ∀ j, fi24FPt (σ j) = tR • fi24FPt j := hσf
  obtain ⟨τ, hτdef⟩ : ∃ τ, τ = fi24Rho ⟨g, hgC⟩ * σ := ⟨_, rfl⟩
  have hτ : ∀ j, fi24FPt (τ j) = (jR g * tR) • fi24FPt j := fun j => by
    rw [hτdef, Equiv.Perm.mul_apply, fi24Rho_spec, hσ, mul_smul, jR_smul]
  have hτ1 : τ = 1 := by
    apply hm.cent
    intro k hk
    rw [← hm.map_commutator_top] at hk
    obtain ⟨p, hp, rfl⟩ := hk
    have hcp : jR g * tR * jR (p : J) = jR (p : J) * (jR g * tR) := hc _ ⟨p, hp, rfl⟩
    refine Equiv.ext fun j => fi24FPt_injective ?_
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hτ, fi24Rho_spec, fi24Rho_spec, hτ,
      ← jR_smul, ← jR_smul (p : J), smul_smul, smul_smul, hcp]
  have hmem : σ ∈ fi24K := by
    rw [hτdef] at hτ1
    rw [eq_inv_of_mul_eq_one_right hτ1, ← fi24Rho_range_card.1]
    exact inv_mem ⟨_, rfl⟩
  exact not_mem_fi24K_of_tR hJ hσ hmem

theorem twoBPerfect_of_checks
    (hK : fi24TwoBKCheck = true) (hJ : TwoBJFacts) :
    TwoBPerfect := by
  show ⁅PB, PB⁆ = PB
  rw [PB_eq]
  exact (fi24TwoBModel hK hJ).map_perfect

theorem twoBQ_of_checks
    (hK : fi24TwoBKCheck = true) (hJ : TwoBJFacts) :
    TwoBQ fi24QR := by
  unfold TwoBQ
  rw [PB_eq]
  exact ⟨(fi24TwoBModel hK hJ).map_Q_le, (fi24TwoBModel hK hJ).map_Q_normal⟩

theorem twoBIrreducible_of_checks
    (hK : fi24TwoBKCheck = true) (hJ : TwoBJFacts) :
    TwoBIrreducible fi24QR := by
  unfold TwoBIrreducible
  rw [PB_eq, ← fi24CR_z]
  exact (fi24TwoBModel hK hJ).map_irreducible fi24CR_injective

theorem twoBFaithful_of_checks
    (hK : fi24TwoBKCheck = true) (hJ : TwoBJFacts) :
    TwoBFaithful fi24QR := by
  unfold TwoBFaithful
  rw [PB_eq, ← fi24CR_z]
  exact (fi24TwoBModel hK hJ).map_faithful fi24CR_injective

theorem twoBOrderFour_of_checks
    (hK : fi24TwoBKCheck = true) (hJ : TwoBJFacts) :
    TwoBOrderFour fi24QR :=
  (fi24TwoBModel hK hJ).map_orderFour fi24CR_injective

theorem twoBCentralizer_of_checks
    (hK : fi24TwoBKCheck = true) (hJ : TwoBJFacts) :
    TwoBCentralizer := by
  intro c _ hc
  have hm := fi24TwoBModel hK hJ
  rw [PB_eq] at hc
  have hcomm : ∀ p ∈ (commutator ↥fi24C).map fi24CR, c * p = p * c :=
    fun p hp => (mem_centralizer_iff.1 hc p hp).symm
  obtain ⟨g, rfl | rfl⟩ := eq_jR_or c
  · have hcz : jR g * zR = zR * jR g := hcomm _ hm.map_z_mem
    rw [← fi24CR_z]
    refine hm.map_centralizer fi24CR_injective _ ?_ hcomm
    rw [fi24CR_range]
    exact ⟨jR_mem_JR g, mem_centralizer_singleton_iff.2 hcz⟩
  · exact (fi24_not_outer hK hJ g hcomm).elim

theorem twoB_facts
    (hK : fi24TwoBKCheck = true) (hJ : TwoBJFacts) :
    TwoBPerfect ∧ TwoBQ fi24QR ∧ TwoBIrreducible fi24QR ∧ TwoBFaithful fi24QR ∧
      TwoBOrderFour fi24QR ∧ TwoBCentralizer :=
  ⟨twoBPerfect_of_checks hK hJ, twoBQ_of_checks hK hJ, twoBIrreducible_of_checks hK hJ,
    twoBFaithful_of_checks hK hJ, twoBOrderFour_of_checks hK hJ,
    twoBCentralizer_of_checks hK hJ⟩

end Transport

end CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime
