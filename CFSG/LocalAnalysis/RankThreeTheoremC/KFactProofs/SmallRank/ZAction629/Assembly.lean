module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction629.PartI
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction629.FData
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction629.LinearAlgebra
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction629.TwoGroups
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62xDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629

section
open Subgroup
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K] {p d f : ℕ} {S F : Subgroup K} {z t : K}

theorem ccInv_conj_fix_zpowers {g u : K} (hgu : Commute g u) :
    ∀ x ∈ zpowers u, g * x * g⁻¹ = x := by
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  calc g * u ^ k * g⁻¹ = u ^ k * g * g⁻¹ := by rw [(hgu.zpow_right k).eq]
    _ = u ^ k := mul_inv_cancel_right _ _

theorem ccInv_mem_normalizer_zpowers {g u : K} (hgu : Commute g u) :
    g ∈ normalizer ((zpowers u : Subgroup K) : Set K) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [ccInv_conj_fix_zpowers hgu x hx]
    exact hx
  · intro hx
    have h1 := ccInv_conj_fix_zpowers hgu.inv_left _ hx
    have h2 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rw [h2] at h1
    rw [h1]
    exact hx

theorem ccInv_zpowers_le_normalizer {g u : K} (hgu : Commute g u) :
    zpowers g ≤ normalizer ((zpowers u : Subgroup K) : Set K) :=
  Subgroup.zpowers_le.mpr (ccInv_mem_normalizer_zpowers hgu)

theorem ccInv_centralizer_singleton_le {u : K} :
    centralizer ({u} : Set K) ≤ centralizer ((zpowers u : Subgroup K) : Set K) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff] at hg ⊢
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hgu : Commute u g := hg u (Set.mem_singleton u)
  exact (hgu.zpow_left k).eq

theorem ccInv_centralizer_bot {c : K} (hcS : c ∈ S) (hc1 : c ≠ 1) (hzc : Commute z c)
    (hb : ∀ S₀ : Subgroup K, S₀ ≤ S → S₀ ≠ ⊥ → zpowers z ≤ normalizer (S₀ : Set K) →
      F ⊓ centralizer (S₀ : Set K) = ⊥) :
    F ⊓ centralizer ({c} : Set K) = ⊥ := by
  have hb' := hb (zpowers c) (Subgroup.zpowers_le.mpr hcS)
    (fun h' => hc1 (Subgroup.zpowers_eq_bot.mp h')) (ccInv_zpowers_le_normalizer hzc)
  rw [eq_bot_iff]
  intro g hg
  have hgC : g ∈ F ⊓ centralizer ((zpowers c : Subgroup K) : Set K) :=
    Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hg).1,
      ccInv_centralizer_singleton_le (u := c) (Subgroup.mem_inf.mp hg).2⟩
  rw [hb'] at hgC
  exact hgC

theorem Setup.t_mem_CC (h : Setup p d S z t) : t ∈ CC S z := by
  refine Subgroup.mem_inf.mpr ⟨Setup.RR_le h h.shape.t_mem, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  exact h.shape.t_comm r hr

theorem Setup.isPGroup_CC (h : Setup p d S z t) : IsPGroup 2 (CC S z) :=
  IsPGroup.to_le h.two inf_le_left

theorem inv_t (h : Setup p d S z t) (hF : FData f F) (hNF : S ⊔ zpowers z ≤ normalizer (F : Set K))
    (hb : ∀ S₀ : Subgroup K, S₀ ≤ S → S₀ ≠ ⊥ → zpowers z ≤ normalizer (S₀ : Set K) →
      F ⊓ centralizer (S₀ : Set K) = ⊥) : ∀ a ∈ F, t * a * t⁻¹ = a⁻¹ := by
  have ht_S : t ∈ S := Setup.RR_le h h.shape.t_mem
  exact FData.inv_of_centralizer_eq_bot hF (hNF (Subgroup.mem_sup_left ht_S)) h.shape.t_sq
    (ccInv_centralizer_bot ht_S h.shape.t_ne h.z_comm_t hb)

theorem CC_unique_involution (h : Setup p d S z t) (hF : FData f F)
    (hNF : S ⊔ zpowers z ≤ normalizer (F : Set K))
    (hb : ∀ S₀ : Subgroup K, S₀ ≤ S → S₀ ≠ ⊥ → zpowers z ≤ normalizer (S₀ : Set K) →
      F ⊓ centralizer (S₀ : Set K) = ⊥) : ∀ c ∈ CC S z, c ^ 2 = 1 → c = 1 ∨ c = t := by
  intro c hc hc2
  by_contra hne
  have hc1 : c ≠ 1 := fun h' => hne (Or.inl h')
  have hct : c ≠ t := fun h' => hne (Or.inr h')
  obtain ⟨e₁, he₁, e₂, he₂, h1sq, h2sq, he₁1, he₂1, he12, hcomm⟩ :=
    exists_commuting_involutions (Setup.isPGroup_CC h) hc (Setup.t_mem_CC h) hc2
      h.shape.t_sq hc1 h.shape.t_ne hct
  have he₁S : e₁ ∈ S := (Subgroup.mem_inf.mp he₁).1
  have he₂S : e₂ ∈ S := (Subgroup.mem_inf.mp he₂).1
  have hprodS : e₁ * e₂ ∈ S := mul_mem he₁S he₂S
  have hprod : e₁ * e₂ ∈ CC S z := mul_mem he₁ he₂
  have hprod1 : e₁ * e₂ ≠ 1 := by
    intro h12
    apply he12
    have hsq : e₁ * e₁ = 1 := (sq e₁).symm.trans h1sq
    calc e₁ = e₁ * 1 := (mul_one e₁).symm
      _ = e₁ * (e₁ * e₂) := by rw [h12]
      _ = e₁ * e₁ * e₂ := (mul_assoc _ _ _).symm
      _ = e₂ := by rw [hsq, one_mul]
  have hC₁ : F ⊓ centralizer ({e₁} : Set K) = ⊥ :=
    ccInv_centralizer_bot he₁S he₁1 (Setup.z_comm_CC h e₁ he₁) hb
  have hC₂ : F ⊓ centralizer ({e₂} : Set K) = ⊥ :=
    ccInv_centralizer_bot he₂S he₂1 (Setup.z_comm_CC h e₂ he₂) hb
  have hC₁₂ : F ⊓ centralizer ({e₁ * e₂} : Set K) = ⊥ :=
    ccInv_centralizer_bot hprodS hprod1 (Setup.z_comm_CC h (e₁ * e₂) hprod) hb
  exact FData.false_of_klein hF (hNF (Subgroup.mem_sup_left he₁S))
    (hNF (Subgroup.mem_sup_left he₂S)) h1sq h2sq he12 hcomm hC₁ hC₂ hC₁₂
end

section
open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K] {p d f : ℕ} {S F : Subgroup K} {z t : K}

theorem centerEq_mem_zpowers_cases {u y : K} (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1) (hy : y ∈ zpowers u) :
    y = 1 ∨ y = u := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hord : orderOf u = 2 := orderOf_eq_prime hu2 hu1
  have hk : u ^ k = u ^ (k % (orderOf u : ℤ)) := (zpow_mod_orderOf u k).symm
  rw [hk, hord]
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    simp [h0]
  · right
    simp [h1]

theorem centerEq_zpowers_comm {R : Subgroup K} {u y : K} (hu : ∀ r ∈ R, r * u = u * r)
    (hy : y ∈ zpowers u) : ∀ r ∈ R, r * y = y * r := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  intro r hr
  exact (Commute.zpow_right (show Commute r u from hu r hr) k).eq

theorem centerEq_orderOf_two {u : K} (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1) : orderOf u = 2 :=
  orderOf_eq_prime hu2 hu1

theorem Setup.center_eq (h : Setup p d S z t) : smallRankCenter (RR S z) = zpowers t := by
  unfold smallRankCenter
  ext y
  constructor
  · rintro ⟨hyR, hyC⟩
    exact h.shape.center_le y hyR fun r hr => (Subgroup.mem_centralizer_iff.mp hyC r hr).symm
  · intro hy
    refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_centralizer_iff.mpr (centerEq_zpowers_comm h.shape.t_comm hy)⟩
    exact Subgroup.zpowers_le.mpr h.shape.t_mem hy

theorem Setup.card_RR_inf_CC (h : Setup p d S z t) :
    Nat.card ↥(RR S z ⊓ CC S z : Subgroup K) = 2 := by
  rw [h.RR_inf_CC, Nat.card_zpowers]
  exact centerEq_orderOf_two h.shape.t_sq h.shape.t_ne

theorem Setup.center_inv (h : Setup p d S z t) (hF : FData f F)
    (hNF : S ⊔ zpowers z ≤ normalizer (F : Set K))
    (hb : ∀ S₀ : Subgroup K, S₀ ≤ S → S₀ ≠ ⊥ → zpowers z ≤ normalizer (S₀ : Set K) →
      F ⊓ centralizer (S₀ : Set K) = ⊥) :
    ∀ y ∈ smallRankCenter (RR S z), y ≠ 1 → ∀ a ∈ F, y * a * y⁻¹ = a⁻¹ := by
  intro y hy hy1 a ha
  have hyt : y ∈ zpowers t := by
    rw [← h.center_eq]
    exact hy
  rcases centerEq_mem_zpowers_cases h.shape.t_sq h.shape.t_ne hyt with hy0 | hy0
  · exact absurd hy0 hy1
  · rw [hy0]
    exact inv_t h hF hNF hb a ha

theorem Setup.omega_center_eq (h : Setup p d S z t) (hF : FData f F)
    (hNF : S ⊔ zpowers z ≤ normalizer (F : Set K))
    (hb : ∀ S₀ : Subgroup K, S₀ ≤ S → S₀ ≠ ⊥ → zpowers z ≤ normalizer (S₀ : Set K) →
      F ⊓ centralizer (S₀ : Set K) = ⊥) :
    smallRankOmega 2 (smallRankCenter S) = zpowers t := by
  refine le_antisymm ?_ ?_
  · unfold smallRankOmega
    rw [Subgroup.closure_le]
    rintro a ⟨haC, ha2⟩
    obtain ⟨haS, haZ⟩ := Subgroup.mem_inf.mp haC
    have haCC : a ∈ CC S z :=
      Subgroup.mem_inf.mpr ⟨haS, Subgroup.mem_centralizer_iff.mpr fun r hr =>
        Subgroup.mem_centralizer_iff.mp haZ r (h.RR_le hr)⟩
    rcases CC_unique_involution h hF hNF hb a haCC ha2 with ha0 | ha0
    · rw [ha0]
      exact Subgroup.one_mem _
    · rw [ha0]
      exact Subgroup.mem_zpowers t
  · unfold smallRankOmega
    rw [Subgroup.zpowers_le]
    have ht : t ∈ smallRankCenter S :=
      Subgroup.mem_inf.mpr ⟨h.RR_le h.shape.t_mem,
        Subgroup.mem_centralizer_iff.mpr fun s hs => h.t_comm_S s hs⟩
    exact Subgroup.subset_closure
      (show t ∈ {a : K | a ∈ smallRankCenter S ∧ a ^ 2 = 1} from ⟨ht, h.shape.t_sq⟩)
end

section
open Subgroup
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K] {p d f : ℕ} {S F : Subgroup K} {z t : K}

theorem fiveCard_comm_conj {i s a : K} (his : i * s = s * i) :
    i * a * i⁻¹ * s = s * (i * a * i⁻¹) ↔ a * s = s * a := by
  have hc : i⁻¹ * s * i = s := by
    calc i⁻¹ * s * i = i⁻¹ * (s * i) := by group
      _ = i⁻¹ * (i * s) := by rw [his]
      _ = s := by group
  constructor
  · intro h
    calc a * s = a * (i⁻¹ * s * i) := by rw [hc]
      _ = i⁻¹ * (i * a * i⁻¹ * s) * i := by group
      _ = i⁻¹ * (s * (i * a * i⁻¹)) * i := by rw [h]
      _ = (i⁻¹ * s * i) * a := by group
      _ = s * a := by rw [hc]
  · intro h
    calc i * a * i⁻¹ * s = i * a * (i⁻¹ * s * i) * i⁻¹ := by group
      _ = i * (a * s) * i⁻¹ := by rw [hc]; group
      _ = i * (s * a) * i⁻¹ := by rw [h]
      _ = (i * s) * a * i⁻¹ := by group
      _ = (s * i) * a * i⁻¹ := by rw [his]
      _ = s * (i * a * i⁻¹) := by group

theorem fiveCard_normalizer_inf {i s : K} (hiN : i ∈ normalizer (F : Set K)) (his : i * s = s * i) :
    i ∈ normalizer ((F ⊓ centralizer ({s} : Set K) : Subgroup K) : Set K) := by
  rw [Subgroup.mem_set_normalizer_iff] at hiN ⊢
  intro a
  have hA := hiN a
  have hC := fiveCard_comm_conj (a := a) his
  simp only [SetLike.mem_coe, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff] at hA ⊢
  rw [hA, hC]

theorem fiveCard_fData_inf (hF : FData f F) {s : K}
    (h1 : 1 < Nat.card ↥(F ⊓ centralizer ({s} : Set K))) :
    FData f (F ⊓ centralizer ({s} : Set K)) :=
  { prime := hF.prime
    odd := hF.odd
    comm := fun a ha b hb => hF.comm a (Subgroup.mem_inf.mp ha).1 b (Subgroup.mem_inf.mp hb).1
    exp := fun a ha => hF.exp a (Subgroup.mem_inf.mp ha).1
    ne := (Subgroup.one_lt_card_iff_ne_bot (F ⊓ centralizer ({s} : Set K))).mp h1 }

theorem fiveCard_card_sq {n k : ℕ} (hf : 2 ≤ f) (hk : n = f ^ (2 * k)) (h1 : 1 < n)
    (hle : n ≤ f ^ 3) : n = f ^ 2 := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [Nat.mul_zero, pow_zero] at hk
    omega
  have hk1 : k ≤ 1 := by
    by_contra hcon
    have h4 : f ^ 4 ≤ f ^ (2 * k) := Nat.pow_le_pow_right (by omega) (by omega)
    have h34 : f ^ 3 < f ^ 4 := pow_lt_pow_right₀ (by omega) (by norm_num)
    omega
  have hk' : k = 1 := by omega
  subst hk'
  simpa using hk

theorem five_card (h : Setup 5 4 S z t) (hF : FData f F)
    (hNF : S ⊔ zpowers z ≤ normalizer (F : Set K))
    (hb : ∀ S₀ : Subgroup K, S₀ ≤ S → S₀ ≠ ⊥ → zpowers z ≤ normalizer (S₀ : Set K) →
      F ⊓ centralizer (S₀ : Set K) = ⊥)
    (hrank : ∀ y ∈ S, y ^ 2 = 1 → y ≠ 1 → CFSG.Open.pRank f (F ⊓ centralizer ({y} : Set K)) ≤ 3)
    {i j r s : K} (hi : i ∈ RR S z) (hj : j ∈ RR S z) (hr : r ∈ RR S z) (hs : s ∈ RR S z)
    (hi2 : i ^ 2 = t) (hj2 : j ^ 2 = t) (hji : j * i * j⁻¹ = t * i)
    (hr2 : r ^ 2 = t) (hs2 : s ^ 2 = 1) (hs1 : s ≠ 1) (hrs : r * s * r⁻¹ = t * s)
    (his : i * s = s * i) (hjs : j * s = s * j) : Nat.card F = f ^ 4 := by
  have hSN : S ≤ normalizer (F : Set K) := le_sup_left.trans hNF
  have hinv : ∀ a ∈ F, t * a * t⁻¹ = a⁻¹ := inv_t h hF hNF hb
  have hiS : i ∈ S := h.RR_le hi
  have hjS : j ∈ S := h.RR_le hj
  have hrS : r ∈ S := h.RR_le hr
  have hsS : s ∈ S := h.RR_le hs
  have htS : t ∈ S := h.RR_le h.shape.t_mem
  have hiN : i ∈ normalizer (F : Set K) := hSN hiS
  have hjN : j ∈ normalizer (F : Set K) := hSN hjS
  have hrN : r ∈ normalizer (F : Set K) := hSN hrS
  have hsN : s ∈ normalizer (F : Set K) := hSN hsS
  have htN : t ∈ normalizer (F : Set K) := hSN htS
  have htcomm : t * s = s * t := (h.t_comm_S s hsS).symm
  have hsq : Nat.card F = Nat.card ↥(F ⊓ centralizer ({s} : Set K)) ^ 2 :=
    (hF.card_eq_sq_of_swap hsN hrN htN hs2 hinv htcomm hrs).1
  have hFne : 1 < Nat.card F := (Subgroup.one_lt_card_iff_ne_bot F).mpr hF.ne
  have h1F : 1 < Nat.card ↥(F ⊓ centralizer ({s} : Set K)) := by
    by_contra hcon
    have hle : Nat.card ↥(F ⊓ centralizer ({s} : Set K)) ^ 2 ≤ 1 ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    rw [one_pow, ← hsq] at hle
    omega
  have hF₁ : FData f (F ⊓ centralizer ({s} : Set K)) := fiveCard_fData_inf hF h1F
  have hx : i ∈ normalizer ((F ⊓ centralizer ({s} : Set K) : Subgroup K) : Set K) :=
    fiveCard_normalizer_inf hiN his
  have hy : j ∈ normalizer ((F ⊓ centralizer ({s} : Set K) : Subgroup K) : Set K) :=
    fiveCard_normalizer_inf hjN hjs
  have hii : i * i = t := (sq i).symm.trans hi2
  have hjj : j * j = t := (sq j).symm.trans hj2
  have hx2 : ∀ a ∈ (F ⊓ centralizer ({s} : Set K)), i * i * a * (i * i)⁻¹ = a⁻¹ := by
    intro a ha
    rw [hii]
    exact hinv a (Subgroup.mem_inf.mp ha).1
  have hy2 : ∀ a ∈ (F ⊓ centralizer ({s} : Set K)), j * j * a * (j * j)⁻¹ = a⁻¹ := by
    intro a ha
    rw [hjj]
    exact hinv a (Subgroup.mem_inf.mp ha).1
  have hxy : ∀ a ∈ (F ⊓ centralizer ({s} : Set K)),
      j * i * j⁻¹ * a * (j * i * j⁻¹)⁻¹ = (i * a * i⁻¹)⁻¹ := by
    intro a ha
    have hbF : i * a * i⁻¹ ∈ F :=
      (Subgroup.mem_set_normalizer_iff.mp hiN a).mp (Subgroup.mem_inf.mp ha).1
    rw [hji]
    calc t * i * a * (t * i)⁻¹ = t * (i * a * i⁻¹) * t⁻¹ := by group
      _ = (i * a * i⁻¹)⁻¹ := hinv _ hbF
  have hle : Nat.card ↥(F ⊓ centralizer ({s} : Set K)) ≤ f ^ 3 :=
    card_le_of_pRank_le hF.prime hF₁.comm hF₁.exp (hrank s hsS hs2 hs1)
  obtain ⟨k, hk⟩ := hF₁.even_card_exponent hx hy hx2 hy2 hxy
  have hF2 : Nat.card ↥(F ⊓ centralizer ({s} : Set K)) = f ^ 2 :=
    fiveCard_card_sq hF.prime.two_le hk h1F hle
  rw [hsq, hF2]
  ring
end

section
open Subgroup
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K] {p d f : ℕ} {S F : Subgroup K} {z t : K}

theorem fiveCyc_conj_iff {g a s : K} (hgs : g * s = s * g) :
    a * s = s * a ↔ g * a * g⁻¹ * s = s * (g * a * g⁻¹) := by
  have hgi : g⁻¹ * s = s * g⁻¹ := by
    calc g⁻¹ * s = g⁻¹ * (s * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * s) * g⁻¹ := by rw [hgs]
      _ = s * g⁻¹ := by group
  have h1 : g * a * g⁻¹ * s = g * (a * s) * g⁻¹ := by
    calc g * a * g⁻¹ * s = g * a * (g⁻¹ * s) := by group
      _ = g * a * (s * g⁻¹) := by rw [hgi]
      _ = g * (a * s) * g⁻¹ := by group
  have h2 : s * (g * a * g⁻¹) = g * (s * a) * g⁻¹ := by
    calc s * (g * a * g⁻¹) = (s * g) * a * g⁻¹ := by group
      _ = (g * s) * a * g⁻¹ := by rw [hgs]
      _ = g * (s * a) * g⁻¹ := by group
  rw [h1, h2]
  constructor
  · intro h
    rw [h]
  · intro h
    exact mul_left_cancel (mul_right_cancel h)

theorem fiveCyc_mem_normalizer_inf {s g : K} (hg : g ∈ normalizer (F : Set K))
    (hgs : g * s = s * g) :
    g ∈ normalizer ((F ⊓ centralizer ({s} : Set K) : Subgroup K) : Set K) := by
  refine mem_normalizer_iff.mpr fun a => ?_
  have hF' : a ∈ F ↔ g * a * g⁻¹ ∈ F := mem_normalizer_iff.mp hg a
  have hC' : a * s = s * a ↔ g * a * g⁻¹ * s = s * (g * a * g⁻¹) := fiveCyc_conj_iff hgs
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  exact and_congr hF' hC'

theorem fiveCyc_FData_inf {s : K} (hF : FData f F)
    (hcard : Nat.card ↥(F ⊓ centralizer ({s} : Set K)) = f ^ 2) :
    FData f (F ⊓ centralizer ({s} : Set K)) := by
  refine ⟨hF.prime, hF.odd, fun a ha b hb => ?_, fun a ha => ?_, ?_⟩
  · exact hF.comm a (Subgroup.mem_inf.mp ha).1 b (Subgroup.mem_inf.mp hb).1
  · exact hF.exp a (Subgroup.mem_inf.mp ha).1
  · refine (Subgroup.one_lt_card_iff_ne_bot _).mp ?_
    rw [hcard]
    have := hF.prime.two_le
    nlinarith

theorem fiveCyc_comm_conj {c i a : K} (hci : c * i = i * c) :
    c * (i * a * i⁻¹) * c⁻¹ = i * (c * a * c⁻¹) * i⁻¹ := by
  calc c * (i * a * i⁻¹) * c⁻¹ = (c * i) * a * (c * i)⁻¹ := by group
    _ = (i * c) * a * (i * c)⁻¹ := by rw [hci]
    _ = i * (c * a * c⁻¹) * i⁻¹ := by group

theorem fiveCyc_act {F₁ : Subgroup K} {r c : K} {n : ℕ} (hF : FData f F)
    (hrN : r ∈ normalizer (F : Set K)) (hcr : c * r = r * c) (hF₁F : F₁ ≤ F)
    (hn : ∀ b ∈ F₁, c * b * c⁻¹ = b ^ n)
    (hdec : ∀ a ∈ F, ∃ b ∈ F₁, ∃ b' ∈ F₁, a = b * (r * b' * r⁻¹)) :
    ∀ a ∈ F, c * a * c⁻¹ = a ^ n := by
  intro a ha
  obtain ⟨b, hb, b', hb', hab⟩ := hdec a ha
  have hbF : b ∈ F := hF₁F hb
  have hb'F : b' ∈ F := hF₁F hb'
  have hrb' : r * b' * r⁻¹ ∈ F := (mem_normalizer_iff.mp hrN b').mp hb'F
  have hcomm : Commute b (r * b' * r⁻¹) := hF.comm b hbF _ hrb'
  have hconjr : c * (r * b' * r⁻¹) * c⁻¹ = r * (c * b' * c⁻¹) * r⁻¹ := by
    calc c * (r * b' * r⁻¹) * c⁻¹ = (c * r) * b' * (c * r)⁻¹ := by group
      _ = (r * c) * b' * (r * c)⁻¹ := by rw [hcr]
      _ = r * (c * b' * c⁻¹) * r⁻¹ := by group
  rw [hab]
  calc c * (b * (r * b' * r⁻¹)) * c⁻¹ = (c * b * c⁻¹) * (c * (r * b' * r⁻¹) * c⁻¹) := by group
    _ = (c * b * c⁻¹) * (r * (c * b' * c⁻¹) * r⁻¹) := by rw [hconjr]
    _ = b ^ n * (r * b' ^ n * r⁻¹) := by rw [hn b hb, hn b' hb']
    _ = b ^ n * (r * b' * r⁻¹) ^ n := by rw [conj_pow]
    _ = (b * (r * b' * r⁻¹)) ^ n := (hcomm.mul_pow n).symm

theorem five_cyclic (h : Setup 5 4 S z t) (hF : FData f F)
    (hNF : S ⊔ zpowers z ≤ normalizer (F : Set K))
    (hb : ∀ S₀ : Subgroup K, S₀ ≤ S → S₀ ≠ ⊥ → zpowers z ≤ normalizer (S₀ : Set K) →
      F ⊓ centralizer (S₀ : Set K) = ⊥)
    (hrank : ∀ y ∈ S, y ^ 2 = 1 → y ≠ 1 → CFSG.Open.pRank f (F ⊓ centralizer ({y} : Set K)) ≤ 3)
    {i j r s : K} (hi : i ∈ RR S z) (hj : j ∈ RR S z) (hr : r ∈ RR S z) (hs : s ∈ RR S z)
    (hi2 : i ^ 2 = t) (hj2 : j ^ 2 = t) (hji : j * i * j⁻¹ = t * i)
    (hr2 : r ^ 2 = t) (hs2 : s ^ 2 = 1) (hs1 : s ≠ 1) (hrs : r * s * r⁻¹ = t * s)
    (his : i * s = s * i) (hjs : j * s = s * j) : IsCyclic (CC S z) := by
  have hSN : S ≤ normalizer (F : Set K) := le_sup_left.trans hNF
  have hzF : zpowers z ≤ normalizer (F : Set K) := le_sup_right.trans hNF
  have hRS : RR S z ≤ S := h.RR_le
  have hinv : ∀ a ∈ F, t * a * t⁻¹ = a⁻¹ := inv_t h hF hNF hb
  have hcard : Nat.card F = f ^ 4 :=
    five_card h hF hNF hb hrank hi hj hr hs hi2 hj2 hji hr2 hs2 hs1 hrs his hjs
  have hiS : i ∈ S := hRS hi
  have hjS : j ∈ S := hRS hj
  have hrS : r ∈ S := hRS hr
  have hsS : s ∈ S := hRS hs
  have htS : t ∈ S := hRS h.shape.t_mem
  have hcomm_ts : t * s = s * t := (h.t_comm_S s hsS).symm
  obtain ⟨hsq, hdec⟩ := hF.card_eq_sq_of_swap (g := s) (h := r) (t' := t)
    (hSN hsS) (hSN hrS) (hSN htS) hs2 hinv hcomm_ts hrs
  have hsq' : Nat.card ↥(F ⊓ centralizer ({s} : Set K)) ^ 2 = (f ^ 2) ^ 2 := by
    rw [← hsq, hcard]
    ring
  have hF₁card : Nat.card ↥(F ⊓ centralizer ({s} : Set K)) = f ^ 2 :=
    Nat.pow_left_injective (by norm_num) hsq'
  have hF₁ : FData f (F ⊓ centralizer ({s} : Set K)) := fiveCyc_FData_inf hF hF₁card
  have hCS : ∀ c ∈ CC S z, c ∈ S := fun c hc => (Subgroup.mem_inf.mp hc).1
  have hCR : ∀ c ∈ CC S z, ∀ x ∈ RR S z, x * c = c * x := fun c hc x hx =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 x hx
  have hCN : CC S z ≤ normalizer (F : Set K) := fun c hc => hSN (hCS c hc)
  have hscalar : ∀ c ∈ CC S z, ∃ n : ℕ, ∀ a ∈ F, c * a * c⁻¹ = a ^ n := by
    intro c hc
    have hcs : c * s = s * c := (hCR c hc s hs).symm
    have hci : c * i = i * c := (hCR c hc i hi).symm
    have hcj : c * j = j * c := (hCR c hc j hj).symm
    have hcr : c * r = r * c := (hCR c hc r hr).symm
    have hii : i * i = t := (pow_two i).symm.trans hi2
    have hjj : j * j = t := (pow_two j).symm.trans hj2
    have hx2 : ∀ a ∈ F ⊓ centralizer ({s} : Set K), i * i * a * (i * i)⁻¹ = a⁻¹ := by
      intro a ha
      rw [hii]
      exact hinv a (Subgroup.mem_inf.mp ha).1
    have hy2 : ∀ a ∈ F ⊓ centralizer ({s} : Set K), j * j * a * (j * j)⁻¹ = a⁻¹ := by
      intro a ha
      rw [hjj]
      exact hinv a (Subgroup.mem_inf.mp ha).1
    have hxy : ∀ a ∈ F ⊓ centralizer ({s} : Set K),
        j * i * j⁻¹ * a * (j * i * j⁻¹)⁻¹ = (i * a * i⁻¹)⁻¹ := by
      intro a ha
      rw [hji]
      have hconj : i * a * i⁻¹ ∈ F :=
        (mem_normalizer_iff.mp (hSN hiS) a).mp (Subgroup.mem_inf.mp ha).1
      calc t * i * a * (t * i)⁻¹ = t * (i * a * i⁻¹) * t⁻¹ := by group
        _ = (i * a * i⁻¹)⁻¹ := hinv _ hconj
    have hcx : ∀ a ∈ F ⊓ centralizer ({s} : Set K),
        c * (i * a * i⁻¹) * c⁻¹ = i * (c * a * c⁻¹) * i⁻¹ :=
      fun a _ => fiveCyc_comm_conj hci
    have hcy : ∀ a ∈ F ⊓ centralizer ({s} : Set K),
        c * (j * a * j⁻¹) * c⁻¹ = j * (c * a * c⁻¹) * j⁻¹ :=
      fun a _ => fiveCyc_comm_conj hcj
    obtain ⟨n, hn⟩ := hF₁.scalar_of_card_sq hF₁card
      (fiveCyc_mem_normalizer_inf (hSN hiS) his) (fiveCyc_mem_normalizer_inf (hSN hjS) hjs)
      (fiveCyc_mem_normalizer_inf (hSN (hCS c hc)) hcs) hx2 hy2 hxy hcx hcy
    exact ⟨n, fiveCyc_act hF (hSN hrS) hcr (inf_le_left : F ⊓ centralizer ({s} : Set K) ≤ F) hn hdec⟩
  have hfaith : ∀ c ∈ CC S z, (∀ a ∈ F, c * a = a * c) → c = 1 := fun c hc hcom =>
    faithful hF.ne hzF h.zS hb c (hCS c hc) hcom
  exact hF.isCyclic_of_scalar hCN hfaith hscalar
end

section
open Subgroup
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K] {p d f : ℕ} {S F : Subgroup K} {z t : K}

theorem threeCard_mem_CC {c : K} (hc : c ∈ CC S z) :
    c ∈ S ∧ ∀ r ∈ RR S z, r * c = c * r := by
  obtain ⟨hcS, hcC⟩ := Subgroup.mem_inf.mp hc
  exact ⟨hcS, fun r hr => Subgroup.mem_centralizer_iff.mp hcC r hr⟩

theorem threeCard_zpow_sq {u : K} (hu : u ^ 2 = 1) (k : ℤ) : (u ^ k) ^ 2 = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu, one_zpow]

theorem threeCard_exp_le {q m n : ℕ} (hq : 2 ≤ q) (h : q ^ m ≤ q ^ n) : m ≤ n := by
  by_contra hmn
  exact absurd h (not_le.mpr (Nat.pow_lt_pow_right (by omega) (not_le.mp hmn)))

theorem three_card (h : Setup 3 2 S z t) (hF : FData f F)
    (hNF : S ⊔ zpowers z ≤ normalizer (F : Set K))
    (hb : ∀ S₀ : Subgroup K, S₀ ≤ S → S₀ ≠ ⊥ → zpowers z ≤ normalizer (S₀ : Set K) →
      F ⊓ centralizer (S₀ : Set K) = ⊥)
    (hrank : ∀ y ∈ S, y ^ 2 = 1 → y ≠ 1 → CFSG.Open.pRank f (F ⊓ centralizer ({y} : Set K)) ≤ 2)
    (hnc : ¬ IsCyclic (CC S z)) {i j : K} (hi : i ∈ RR S z) (hj : j ∈ RR S z)
    (hi2 : i ^ 2 = t) (hj2 : j ^ 2 = t) (hji : j * i * j⁻¹ = t * i) : Nat.card F = f ^ 4 := by
  have hSN : S ≤ normalizer (F : Set K) := le_sup_left.trans hNF
  have hzF : zpowers z ≤ normalizer (F : Set K) := le_sup_right.trans hNF
  have hzS : zpowers z ≤ normalizer (S : Set K) := h.zS
  have hiS : i ∈ S := Setup.RR_le h hi
  have hjS : j ∈ S := Setup.RR_le h hj
  have htS : t ∈ S := Setup.RR_le h h.shape.t_mem
  have hiN : i ∈ normalizer (F : Set K) := hSN hiS
  have hjN : j ∈ normalizer (F : Set K) := hSN hjS
  have htN : t ∈ normalizer (F : Set K) := hSN htS
  have hinv : ∀ a ∈ F, t * a * t⁻¹ = a⁻¹ := inv_t h hF hNF hb
  have hconj : ∀ a ∈ F, i * a * i⁻¹ ∈ F := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp hiN a).mp ha
  have hii : i * i = t := (pow_two i).symm.trans hi2
  have hjj : j * j = t := (pow_two j).symm.trans hj2
  have hx2 : ∀ a ∈ F, i * i * a * (i * i)⁻¹ = a⁻¹ := by
    intro a ha
    rw [hii]
    exact hinv a ha
  have hy2 : ∀ a ∈ F, j * j * a * (j * j)⁻¹ = a⁻¹ := by
    intro a ha
    rw [hjj]
    exact hinv a ha
  have hxy : ∀ a ∈ F, j * i * j⁻¹ * a * (j * i * j⁻¹)⁻¹ = (i * a * i⁻¹)⁻¹ := by
    intro a ha
    have h1 := hinv (i * a * i⁻¹) (hconj a ha)
    rw [hji, ← h1]
    group
  obtain ⟨k, hk⟩ := hF.even_card_exponent hiN hjN hx2 hy2 hxy
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have hk0' : k = 0 := by omega
    rw [hk0', mul_zero, pow_zero] at hk
    have hF1 : 1 < Nat.card F := F.one_lt_card_iff_ne_bot.mpr hF.ne
    rw [hk] at hF1
    omega
  obtain ⟨c, hcC, hc2⟩ := exists_sq_eq_of_not_isCyclic (Setup.isPGroup_CC h)
    (Setup.t_mem_CC h) h.shape.t_sq h.shape.t_ne (CC_unique_involution h hF hNF hb) hnc
  obtain ⟨hcS, hcR⟩ := threeCard_mem_CC hcC
  have hic : i * c = c * i := hcR i hi
  have hjc : j * c = c * j := hcR j hj
  have hgS : i * c ∈ S := S.mul_mem hiS hcS
  have hgN : i * c ∈ normalizer (F : Set K) := hSN hgS
  have hg2 : (i * c) ^ 2 = 1 := by
    rw [(show Commute i c from hic).mul_pow, hi2, hc2, ← pow_two]
    exact h.shape.t_sq
  have hg1 : i * c ≠ 1 := by
    intro hic1
    have hiC : i ∈ CC S z := by
      rw [eq_inv_of_mul_eq_one_left hic1]
      exact (CC S z).inv_mem hcC
    have hiT : i ∈ zpowers t := by
      rw [← Setup.RR_inf_CC h]
      exact Subgroup.mem_inf.mpr ⟨hi, hiC⟩
    obtain ⟨k', hk'⟩ := Subgroup.mem_zpowers_iff.mp hiT
    apply h.shape.t_ne
    rw [← hi2, ← hk']
    exact threeCard_zpow_sq h.shape.t_sq k'
  have hcomm : t * (i * c) = i * c * t := (Setup.t_comm_S h (i * c) hgS).symm
  have hjcconj : j * c * j⁻¹ = c := by
    rw [hjc, mul_inv_cancel_right]
  have hswap : j * (i * c) * j⁻¹ = t * (i * c) := by
    calc j * (i * c) * j⁻¹ = (j * i * j⁻¹) * (j * c * j⁻¹) := by group
      _ = t * (i * c) := by rw [hji, hjcconj, mul_assoc]
  obtain ⟨hsplit, -⟩ := hF.card_eq_sq_of_swap hgN hjN htN hg2 hinv hcomm hswap
  have hE := hrank (i * c) hgS hg2 hg1
  have hEcomm : ∀ a ∈ F ⊓ centralizer ({i * c} : Set K), ∀ b ∈ F ⊓ centralizer ({i * c} : Set K),
      a * b = b * a := fun a ha b hb' =>
    hF.comm a (Subgroup.mem_inf.mp ha).1 b (Subgroup.mem_inf.mp hb').1
  have hEexp : ∀ a ∈ F ⊓ centralizer ({i * c} : Set K), a ^ f = 1 := fun a ha =>
    hF.exp a (Subgroup.mem_inf.mp ha).1
  have hle := card_le_of_pRank_le hF.prime hEcomm hEexp hE
  have hup : Nat.card F ≤ f ^ 4 := by
    rw [hsplit]
    calc Nat.card ↥(F ⊓ centralizer ({i * c} : Set K)) ^ 2 ≤ (f ^ 2) ^ 2 :=
          Nat.pow_le_pow_left hle 2
      _ = f ^ 4 := by ring
  have hk2 : 2 * k ≤ 4 := by
    have hpow : f ^ (2 * k) ≤ f ^ 4 := by
      rw [← hk]
      exact hup
    exact threeCard_exp_le hF.prime.two_le hpow
  rcases (show k = 1 ∨ k = 2 by omega) with rfl | rfl
  ·
    exfalso
    have hcard : Nat.card F = f ^ 2 := hk.trans (by norm_num)
    have hscalar : ∀ c' ∈ CC S z, ∃ n : ℕ, ∀ a ∈ F, c' * a * c'⁻¹ = a ^ n := by
      intro c' hc'
      obtain ⟨hc'S, hc'R⟩ := threeCard_mem_CC hc'
      have hci : c' * i = i * c' := (hc'R i hi).symm
      have hcj : c' * j = j * c' := (hc'R j hj).symm
      have hcx : ∀ a ∈ F, c' * (i * a * i⁻¹) * c'⁻¹ = i * (c' * a * c'⁻¹) * i⁻¹ := by
        intro a _
        calc c' * (i * a * i⁻¹) * c'⁻¹ = (c' * i) * a * (c' * i)⁻¹ := by group
          _ = (i * c') * a * (i * c')⁻¹ := by rw [hci]
          _ = i * (c' * a * c'⁻¹) * i⁻¹ := by group
      have hcy : ∀ a ∈ F, c' * (j * a * j⁻¹) * c'⁻¹ = j * (c' * a * c'⁻¹) * j⁻¹ := by
        intro a _
        calc c' * (j * a * j⁻¹) * c'⁻¹ = (c' * j) * a * (c' * j)⁻¹ := by group
          _ = (j * c') * a * (j * c')⁻¹ := by rw [hcj]
          _ = j * (c' * a * c'⁻¹) * j⁻¹ := by group
      exact hF.scalar_of_card_sq hcard hiN hjN (hSN hc'S) hx2 hy2 hxy hcx hcy
    have hfaith : ∀ c' ∈ CC S z, (∀ a ∈ F, c' * a = a * c') → c' = 1 := fun c' hc' hcm =>
      faithful hF.ne hzF hzS hb c' (threeCard_mem_CC hc').1 hcm
    have hCF : CC S z ≤ normalizer (F : Set K) := fun c' hc' => hSN (threeCard_mem_CC hc').1
    exact hnc (hF.isCyclic_of_scalar hCF hfaith hscalar)
  ·
    exact hk.trans (by norm_num)
end

section
open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K] {p d f : ℕ} {S F : Subgroup K} {z t : K}

theorem threeShape_comm_of_mem_CC {c r : K} (hc : c ∈ CC S z) (hr : r ∈ RR S z) : r * c = c * r :=
  Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 r hr

theorem Setup.rankThreeIsQ8CentralCyclic_of_cyclic (h : Setup 3 2 S z t)
    (e : ↥(RR S z) ≃* QuaternionGroup 2) (hc : IsCyclic ↥(CC S z)) :
    ∃ n : ℕ, rankThreeIsQ8CentralCyclic S n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (Setup.isPGroup_CC h).exists_card_eq
  refine ⟨n, ?_⟩
  unfold rankThreeIsQ8CentralCyclic
  exact ⟨RR S z, CC S z, ⟨e⟩, hc, hn, fun a ha b hb => threeShape_comm_of_mem_CC hb ha,
    Setup.CC_sup h, Setup.card_RR_inf_CC h⟩

theorem three_shape (h : Setup 3 2 S z t) (e : ↥(RR S z) ≃* QuaternionGroup 2) (hF : FData f F)
    (hNF : S ⊔ zpowers z ≤ normalizer (F : Set K))
    (hb : ∀ S₀ : Subgroup K, S₀ ≤ S → S₀ ≠ ⊥ → zpowers z ≤ normalizer (S₀ : Set K) →
      F ⊓ centralizer (S₀ : Set K) = ⊥)
    (hnc : ¬ IsCyclic ↥(CC S z)) : ∃ n : ℕ, smallRankIsQ8Quaternion S n := by
  obtain ⟨n, hn3, _, hquat⟩ := quaternion_of_unique_involution (Setup.isPGroup_CC h)
    (Setup.t_mem_CC h) h.shape.t_sq h.shape.t_ne (CC_unique_involution h hF hNF hb) hnc
  refine ⟨n, ?_⟩
  unfold smallRankIsQ8Quaternion
  exact ⟨RR S z, CC S z, ⟨e⟩, hn3, hquat, fun a ha b hbC => threeShape_comm_of_mem_CC hbC ha,
    Setup.CC_sup h, Setup.card_RR_inf_CC h⟩
end

section
open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K] {p d f : ℕ} {S F : Subgroup K} {z t : K}

theorem five_shape (h : Setup 5 4 S z t) {A B : Subgroup K} (eA : ↥A ≃* QuaternionGroup 2)
    (eB : ↥B ≃* DihedralGroup 4) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hR : A ⊔ B = RR S z) (hcard : Nat.card ↥(A ⊓ B : Subgroup K) = 2)
    (hcyc : IsCyclic ↥(CC S z)) : ∃ n : ℕ, smallRankIsQ8D8CentralCyclic S n := by
  obtain ⟨n, hn⟩ := (h.isPGroup_CC).exists_card_eq
  refine ⟨n, A, B, CC S z, ⟨eA⟩, ⟨eB⟩, hcyc, hn, hAB, ?_, ?_, hcard, ?_, ?_⟩
  · intro a ha c hc
    have haR : a ∈ RR S z := by
      rw [← hR]
      exact Subgroup.mem_sup_left ha
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 a haR
  · intro b hb c hc
    have hbR : b ∈ RR S z := by
      rw [← hR]
      exact Subgroup.mem_sup_right hb
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 b hbR
  · rw [hR]
    exact h.card_RR_inf_CC
  · rw [hR]
    exact h.CC_sup
end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
