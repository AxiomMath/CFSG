module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbGold
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbType
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveEpsS1

public section

open Subgroup CFSG.Open CFSG.Blueprint CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.GH74.GLS.Bg.Thompson
open scoped commutatorElement

namespace CFSG.ComponentClassification.RankTwoAltFive

namespace Setting310

variable {G : Type} [Group G] [Finite G] {A R T V₀ : Subgroup G} {g : G}
  (h : Setting310 A R g T V₀)
include h

section PStructure

variable {P : Subgroup G} (hP : IsSylowOf 2 P (transvGroup (R ⊔ T) V₀))
  (hPC : P ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) = R ⊔ T)
include hP hPC

omit hP hPC in
theorem mem_normalizer_Vprime {V' : Subgroup G} (hV' : IsVprime (R ⊔ T) V₀ P V') {u : G}
    (huP : u ∈ normalizer (P : Set G)) (huV : u ∈ normalizer ((R ⊔ T : Subgroup G) : Set G)) :
    u ∈ normalizer (V' : Set G) := by
  have hV₀V' : V₀ ≤ V' := hV'.inf ▸ inf_le_right
  have key : ∀ {w : G}, w ∈ normalizer (P : Set G) →
      w ∈ normalizer ((R ⊔ T : Subgroup G) : Set G) → ∀ v ∈ V', w * v * w⁻¹ ∈ V' := by
    intro w hwP hwV v hv
    by_cases hvV : v ∈ R ⊔ T
    · have hv0 : v ∈ V₀ := hV'.inf ▸ mem_inf.mpr ⟨hvV, hv⟩
      exact hV₀V' ((mem_normalizer_iff.mp (h.normalizer_le_normalizer_V₀ hwV) v).mp hv0)
    · have hv2 : v * v = 1 := by rw [← sq]; exact hV'.elem.2 v hv
      refine hV'.inv _ ((mem_normalizer_iff.mp hwP v).mp (hV'.le hv)) ?_ ?_
      · calc w * v * w⁻¹ * (w * v * w⁻¹) = w * (v * v) * w⁻¹ := by group
          _ = 1 := by rw [hv2]; group
      · exact fun he => hvV ((mem_normalizer_iff.mp hwV v).mpr he)
  rw [mem_normalizer_iff]
  intro v
  refine ⟨key huP huV v, fun hv => ?_⟩
  have := key (inv_mem huP) (inv_mem huV) _ hv
  rwa [show u⁻¹ * (u * v * u⁻¹) * u⁻¹⁻¹ = v by group] at this

theorem inv_mul_b_sq_conj_not_mem {b₀ b : G} (hb₀N : b₀ ∈ normalizer (V₀ : Set G))
    (hb₀3 : orderOf b₀ = 3)
    (hb₀tr : ∀ c ∈ V₀, ∀ d ∈ V₀, c ≠ 1 → d ≠ 1 → ∃ k : ℕ, (b₀ ^ k)⁻¹ * c * b₀ ^ k = d)
    (hbP : b ∈ normalizer (P : Set G))
    (hbc : ∀ y ∈ P, ∀ r ∈ R, ⁅b * y * b⁻¹, r⁆ = b₀ * ⁅y, r⁆ * b₀⁻¹)
    {c : G} (hc : c ∈ P) (hcV : c ∉ R ⊔ T) : c⁻¹ * (b * b * c * (b * b)⁻¹) ∉ R ⊔ T := by
  intro hv
  have hR2 : ∀ x ∈ R, x * x = 1 := fun x hx => h.mul_self (mem_sup_left hx)
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  obtain ⟨r, hr, hr1, -⟩ := exists_ne_one_ne h.cardR hR2 (one_mem R)
  have hrP : r ∈ P := hVP (mem_sup_left hr)
  have hbcP : b * c * b⁻¹ ∈ P := (mem_normalizer_iff.mp hbP c).mp hc
  have hbbc : b * b * c * (b * b)⁻¹ = b * (b * c * b⁻¹) * b⁻¹ := by group
  have hbbcP : b * b * c * (b * b)⁻¹ ∈ P := by
    rw [hbbc]
    exact (mem_normalizer_iff.mp hbP _).mp hbcP
  have hvP : c⁻¹ * (b * b * c * (b * b)⁻¹) ∈ P := mul_mem (inv_mem hc) hbbcP
  have h1 : ⁅b * b * c * (b * b)⁻¹, r⁆ = ⁅c, r⁆ := by
    have e : b * b * c * (b * b)⁻¹ = c * (c⁻¹ * (b * b * c * (b * b)⁻¹)) := by group
    rw [e, h.commP_mul_left hP hPC hc hvP hrP]
    have hvr : ⁅c⁻¹ * (b * b * c * (b * b)⁻¹), r⁆ = 1 := by
      rw [commutatorElement_def, h.comm hv (mem_sup_left hr)]
      group
    rw [hvr, mul_one]
  rw [hbbc, hbc _ hbcP r hr, hbc c hc r hr] at h1
  have hcr := h.commP_mem hP hPC hc hrP
  have hcr1 : ⁅c, r⁆ ≠ 1 := fun he => hr1 (by
    have := h.mem_V₀_of_commP_eq_one hP hPC hc hcV (mem_sup_left hr) he
    have h2 : r ∈ R ⊓ V₀ := mem_inf.mpr ⟨hr, this⟩
    rwa [h.inf_R_V₀, mem_bot] at h2)
  have hb₀3' : b₀ ^ 3 = 1 := by rw [← hb₀3]; exact pow_orderOf_eq_one b₀
  have hfix : b₀ * ⁅c, r⁆ * b₀⁻¹ = ⁅c, r⁆ := by
    have hsq : b₀ * b₀ = b₀⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_three']
      exact hb₀3'
    calc b₀ * ⁅c, r⁆ * b₀⁻¹ = b₀ * (b₀ * (b₀ * ⁅c, r⁆ * b₀⁻¹) * b₀⁻¹) * b₀⁻¹ := by rw [h1]
      _ = (b₀ * b₀) * (b₀ * ⁅c, r⁆ * b₀⁻¹) * (b₀ * b₀)⁻¹ := by group
      _ = b₀⁻¹ * (b₀ * ⁅c, r⁆ * b₀⁻¹) * b₀⁻¹⁻¹ := by rw [hsq]
      _ = ⁅c, r⁆ := by group
  exact (h.b₀_cycle hb₀N hb₀3 hb₀tr hcr hcr1).1 hfix

variable (hIIb : centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G))
include hIIb

theorem mul_self_mod_V₀ (hP64 : Nat.card P = 64) {n : G}
    (hnV : n ∈ normalizer ((R ⊔ T : Subgroup G) : Set G)) {v : G} (hv : v ∈ R ⊔ T) :
    v⁻¹ * (n * n * v * (n * n)⁻¹) ∈ V₀ := by
  obtain ⟨p, hp, hnp⟩ := h.exists_mul_mem_normalizer_R hP hPC hP64 hnV
  have hpV : p ∈ normalizer ((R ⊔ T : Subgroup G) : Set G) := (hP.le hp).1
  set m := n * p with hm
  have hmV : m ∈ normalizer ((R ⊔ T : Subgroup G) : Set G) := mul_mem hnV hpV
  have hnV₀ : n ∈ normalizer (V₀ : Set G) := h.normalizer_le_normalizer_V₀ hnV
  have hmV₀ : m ∈ normalizer (V₀ : Set G) := h.normalizer_le_normalizer_V₀ hmV
  have hconjV : ∀ {u y : G}, u ∈ normalizer ((R ⊔ T : Subgroup G) : Set G) → y ∈ R ⊔ T →
      u * y * u⁻¹ ∈ R ⊔ T := fun hu hy => (mem_normalizer_iff.mp hu _).mp hy
  have hconjV₀ : ∀ {u y : G}, u ∈ normalizer (V₀ : Set G) → y ∈ V₀ → u * y * u⁻¹ ∈ V₀ :=
    fun hu hy => (mem_normalizer_iff.mp hu _).mp hy
  have hnm : ∀ y ∈ R ⊔ T, (m * y * m⁻¹)⁻¹ * (n * y * n⁻¹) ∈ V₀ := by
    intro y hy
    have hw := P_mod hP (inv_mem hp) hy
    have e : (m * y * m⁻¹)⁻¹ * (n * y * n⁻¹) =
        m * (y⁻¹ * (p⁻¹ * y * p⁻¹⁻¹)) * m⁻¹ := by
      rw [hm]; group
    rw [e]
    exact hconjV₀ hmV₀ hw
  have hmm : ∀ y ∈ R ⊔ T, y⁻¹ * (m * m * y * (m * m)⁻¹) ∈ V₀ := by
    intro y hy
    have hmmC := h.mul_self_mem_centralizer_R hIIb hnp
    obtain ⟨r, hr, w, hw, rfl⟩ := h.exists_mul hy
    have hrm : m * m * r * (m * m)⁻¹ = r := by
      rw [← mem_centralizer_iff.mp hmmC r hr]; group
    have e : (r * w)⁻¹ * (m * m * (r * w) * (m * m)⁻¹) = w⁻¹ * (m * m * w * (m * m)⁻¹) := by
      calc (r * w)⁻¹ * (m * m * (r * w) * (m * m)⁻¹) =
          w⁻¹ * r⁻¹ * (m * m * r * (m * m)⁻¹) * (m * m * w * (m * m)⁻¹) := by group
        _ = w⁻¹ * (m * m * w * (m * m)⁻¹) := by rw [hrm]; group
    rw [e]
    exact mul_mem (inv_mem hw) (hconjV₀ (mul_mem hmV₀ hmV₀) hw)
  have hy1 : n * v * n⁻¹ ∈ R ⊔ T := hconjV hnV hv
  have hmy : m * v * m⁻¹ ∈ R ⊔ T := hconjV hmV hv
  have h1 := hnm v hv
  have h2 := hnm _ hmy
  have h3 := hconjV₀ hnV₀ h1
  have h4 := hmm v hv
  have e : v⁻¹ * (n * n * v * (n * n)⁻¹) =
      (v⁻¹ * (m * m * v * (m * m)⁻¹)) *
        ((m * (m * v * m⁻¹) * m⁻¹)⁻¹ * (n * (m * v * m⁻¹) * n⁻¹)) *
          (n * ((m * v * m⁻¹)⁻¹ * (n * v * n⁻¹)) * n⁻¹) := by group
  rw [e]
  exact mul_mem (mul_mem h4 h2) h3

theorem not_conj_Vprime (hP64 : Nat.card P = 64) {V' : Subgroup G}
    (hV' : IsVprime (R ⊔ T) V₀ P V') (y : G) : rightConjugate (R ⊔ T) y ≠ V' := by
  intro hy
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  have hV₀V' : V₀ ≤ V' := hV'.inf ▸ inf_le_right
  have hyV₀ : ∀ w ∈ V₀, y * w * y⁻¹ ∈ V₀ := by
    intro w hw
    have hwV : y * w * y⁻¹ ∈ R ⊔ T := by
      have : w ∈ rightConjugate (R ⊔ T) y := hy ▸ hV₀V' hw
      rwa [mem_rightConjugate_iff] at this
    by_contra hw0
    have hw1 : w ≠ 1 := fun he => hw0 (by rw [he]; group; exact one_mem _)
    exact h.not_isRootInv_of_isConj hw hw1 (isConj_iff.mpr ⟨y, rfl⟩)
      (h.isRootInv_of_mem_V hwV hw0)
  have hyV₀' : ∀ w ∈ V₀, y⁻¹ * w * y ∈ V₀ := by
    have hle : rightConjugate V₀ y⁻¹ ≤ V₀ := by
      intro u hu
      rw [mem_rightConjugate_iff] at hu
      have := hyV₀ _ hu
      rwa [show y * (y⁻¹ * u * y⁻¹⁻¹) * y⁻¹ = u by group] at this
    have heq : rightConjugate V₀ y⁻¹ = V₀ :=
      eq_of_le_of_card_ge hle (le_of_eq (rightConjugate_card V₀ y⁻¹).symm)
    intro w hw
    rw [← heq, mem_rightConjugate_iff] at hw
    simpa using hw
  obtain ⟨b₀, b, hb₀N, hb₀3, hb₀tr, hbP, hbV, -, hbc⟩ := h.exists_b hP hPC
  have hbV' := h.mem_normalizer_Vprime hV' hbP hbV
  have hnV : y * b * y⁻¹ ∈ normalizer ((R ⊔ T : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro v
    have hiff : ∀ u : G, u ∈ R ⊔ T ↔ y⁻¹ * u * y ∈ V' := fun u => by
      rw [← hy, mem_rightConjugate_iff]
      simp only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left]
    rw [hiff, hiff, show y⁻¹ * (y * b * y⁻¹ * v * (y * b * y⁻¹)⁻¹) * y =
      b * (y⁻¹ * v * y) * b⁻¹ by group]
    exact mem_normalizer_iff.mp hbV' _
  obtain ⟨c, hcV', hcV₀⟩ : ∃ c ∈ V', c ∉ V₀ := by
    by_contra hcon
    push Not at hcon
    have := card_le_of_le (show V' ≤ V₀ from hcon)
    rw [hV'.card, h.card_V₀] at this
    omega
  have hcV : c ∉ R ⊔ T := fun he => hcV₀ (hV'.inf ▸ mem_inf.mpr ⟨he, hcV'⟩)
  have hcP : c ∈ P := hV'.le hcV'
  have hv : y * c * y⁻¹ ∈ R ⊔ T := by
    have : c ∈ rightConjugate (R ⊔ T) y := hy ▸ hcV'
    rwa [mem_rightConjugate_iff] at this
  have h1 := h.mul_self_mod_V₀ hP hPC hIIb hP64 hnV hv
  have e : (y * c * y⁻¹)⁻¹ * (y * b * y⁻¹ * (y * b * y⁻¹) * (y * c * y⁻¹) *
      (y * b * y⁻¹ * (y * b * y⁻¹))⁻¹) = y * (c⁻¹ * (b * b * c * (b * b)⁻¹)) * y⁻¹ := by group
  rw [e] at h1
  have h2 := hyV₀' _ h1
  rw [show y⁻¹ * (y * (c⁻¹ * (b * b * c * (b * b)⁻¹)) * y⁻¹) * y =
    c⁻¹ * (b * b * c * (b * b)⁻¹) by group] at h2
  exact h.inv_mul_b_sq_conj_not_mem hP hPC hb₀N hb₀3 hb₀tr hbP hbc hcP hcV (h.V₀_le h2)

section Outer

variable {x z r₁ : G} (hx : OuterInvol R T V₀ P x z r₁) {V' : Subgroup G}
  (hV' : IsVprime (R ⊔ T) V₀ P V')
include hx hV'

theorem isSylowOf_top_of_isVprime (hP64 : Nat.card P = 64) :
    IsSylowOf 2 (P ⊔ zpowers x) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS₁ := h.outer_isSylowOf_sup hP hPC hx hP64
  obtain ⟨S, hS, hS₁S⟩ := exists_isSylowOf_le le_top hS₁.isPGroup
  have hS₁N : P ⊔ zpowers x ≤ normalizer ((R ⊔ T : Subgroup G) : Set G) := hS₁.le
  have hVS₁ : R ⊔ T ≤ P ⊔ zpowers x := (hPC ▸ inf_le_left : R ⊔ T ≤ P).trans le_sup_left
  by_contra hne
  have hlt : P ⊔ zpowers x < S := lt_of_le_of_ne hS₁S fun he => hne (he ▸ hS)
  obtain ⟨n, hn, hnS₁⟩ := IsConcreteLE.exists_of_lt (lt_inf_normalizer hS.isPGroup hlt)
  obtain ⟨hnS, hnN⟩ := mem_inf.mp hn
  have hnV : n ∈ normalizer ((R ⊔ T : Subgroup G) : Set G) := by
    have hS₁n : rightConjugate (P ⊔ zpowers x) n = P ⊔ zpowers x :=
      (rightConjugate_eq_self_iff _ n).mpr hnN
    have hVn : rightConjugate (R ⊔ T) n ≤ P ⊔ zpowers x := by
      rw [← hS₁n]; exact map_mono hVS₁
    rcases h.outer_eq_or_eq_of_elemAbelian_of_isVprime hP hPC hx hV' hVn
      (isElemAbelian_rightConjugate h.loc.elem n) (by rw [rightConjugate_card, h.loc.card])
      with h1 | h1
    · exact (rightConjugate_eq_self_iff _ n).mp h1
    · exact absurd h1 (h.not_conj_Vprime hP hPC hIIb hP64 hV' n)
  have hT2 : IsPGroup 2 ((P ⊔ zpowers x) ⊔ zpowers n : Subgroup G) :=
    hS.isPGroup.to_le (sup_le hS₁S (zpowers_le.mpr hnS))
  have heq := hS₁.eq_of_le le_sup_left (sup_le hS₁N (zpowers_le.mpr hnV)) hT2
  exact hnS₁ (heq ▸ mem_sup_right (mem_zpowers n))

theorem false_of_outer_isVprime (hGold : Asc76X.GoldschmidtTheoremA)
    (hP64 : Nat.card P = 64) : False := by
  have hS₁ := h.isSylowOf_top_of_isVprime hP hPC hIIb hx hV' hP64
  obtain ⟨S, hSS⟩ : ∃ S : Sylow 2 G, (S : Subgroup G) = P ⊔ zpowers x := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hc := hS₁.card_eq
    rw [Subgroup.card_top] at hc
    exact ⟨Sylow.ofCard _ hc, Sylow.coe_ofCard _ _⟩
  have hVP : R ⊔ T ≤ P := hPC ▸ inf_le_left
  have hV₀V' : V₀ ≤ V' := hV'.inf ▸ inf_le_right
  have hzV₀ := hx.z_mem
  have hz1 := hx.z_ne
  have hXn : (rankTwoX A).Normal := normalClosure_normal
  have hV₀X : V₀ ≤ rankTwoX A := h.V₀_le_A.trans le_normalClosure
  by_cases hxz : IsConj z x
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hxX : x ∈ rankTwoX A := by
      obtain ⟨c, hc⟩ := isConj_iff.mp hxz
      rw [← hc]
      exact hXn.conj_mem z (hV₀X hzV₀) c
    have hS₁2 : IsPGroup 2 (P ⊔ zpowers x : Subgroup G) := hS₁.isPGroup
    obtain ⟨k, hkP, hkext, hkC⟩ := h.exists_conj_mem_of_thompson_X hS₁ le_sup_left
      (outer_relIndex_sup hx) (mem_sup_right (mem_zpowers x)) hx.not_mem hxX (fun y n _ => by
        rw [pow_mul, sq, hx.sq, one_pow, mul_one, inv_mul_cancel]
        exact one_mem P)
    have hzS₁ : ∀ t ∈ P ⊔ zpowers x, t * z = z * t := by
      intro t ht
      rcases (outer_mem_sup_iff hx).mp ht with h1 | h1
      · exact P_comm_V₀ hP hzV₀ h1
      · obtain ⟨p, hp, rfl⟩ : ∃ p ∈ P, t = x * p :=
          ⟨x * t, h1, by rw [← mul_assoc, hx.sq, one_mul]⟩
        calc x * p * z = x * (p * z) := mul_assoc _ _ _
          _ = x * (z * p) := by rw [P_comm_V₀ hP hzV₀ hp]
          _ = x * z * p := (mul_assoc _ _ _).symm
          _ = z * x * p := by rw [hx.z_comm]
          _ = z * (x * p) := mul_assoc _ _ _
    have hxy : IsConj x (k⁻¹ * x * k) := isConj_iff.mpr ⟨k⁻¹, by group⟩
    have hS₁y : P ⊔ zpowers x ≤ centralizer ({k⁻¹ * x * k} : Set G) :=
      le_centralizer_of_isExtremalIn hS₁2 hzS₁ (hxz.trans hxy) hkext
    have hcomm : ∀ v ∈ P ⊔ zpowers x, k⁻¹ * x * k * v = v * (k⁻¹ * x * k) := fun v hv =>
      (mem_centralizer_singleton_iff.mp (hS₁y hv)).symm
    have hyz : k⁻¹ * x * k = z := by
      rcases h.outer_eq_of_comm hP hPC hx hV' hkP
        (fun v hv => hcomm v (mem_sup_left (hVP hv)))
        (fun v hv => hcomm v (mem_sup_left (hV'.le hv)))
        (hcomm x (mem_sup_right (mem_zpowers x))) with h1 | h1
      · exfalso
        apply hx.not_mem
        have hx1 : x = 1 := by
          calc x = k * (k⁻¹ * x * k) * k⁻¹ := by group
            _ = 1 := by rw [h1]; group
        rw [hx1]
        exact one_mem P
      · exact h1
    have hr₁C : r₁ ∈ (P ⊔ zpowers x) ⊓ centralizer ({x} : Set G) :=
      mem_inf.mpr ⟨mem_sup_left (hVP (mem_sup_left hx.r_mem)),
        mem_centralizer_singleton_iff.mpr hx.r_comm.symm⟩
    obtain ⟨hdS, hdC⟩ := mem_inf.mp (hkC r₁ hr₁C)
    rw [hyz] at hdC
    have hdz : k⁻¹ * r₁ * k * z = z * (k⁻¹ * r₁ * k) := mem_centralizer_singleton_iff.mp hdC
    have hd2 : k⁻¹ * r₁ * k * (k⁻¹ * r₁ * k) = 1 := by
      calc k⁻¹ * r₁ * k * (k⁻¹ * r₁ * k) = k⁻¹ * (r₁ * r₁) * k := by group
        _ = 1 := by rw [h.mul_self (mem_sup_left hx.r_mem)]; group
    have hd1 : k⁻¹ * r₁ * k ≠ 1 := by
      intro h1
      apply hx.r_ne
      calc r₁ = k * (k⁻¹ * r₁ * k) * k⁻¹ := by group
        _ = 1 := by rw [h1]; group
    have hdroot : IsRootInv A (k⁻¹ * r₁ * k) := (h.isRootInv_of_mem_R hx.r_mem).conj k
    have hzd : ¬ IsRootInv A (z * (k⁻¹ * r₁ * k)) := by
      apply h.not_isRootInv_of_isConj hzV₀ hz1
      obtain ⟨r, -, hr⟩ := h.outer_exists_conj_mul_r hx
      have e : z * (k⁻¹ * r₁ * k) = k⁻¹ * (x * r₁) * k := by rw [← hyz]; group
      rw [e]
      refine hxz.trans (isConj_iff.mpr ⟨k⁻¹ * r⁻¹, ?_⟩)
      rw [← hr]
      group
    apply hzd
    have hdV₀ : k⁻¹ * r₁ * k ∉ V₀ := fun h0 =>
      h.not_isRootInv_of_isConj h0 hd1 (IsConj.refl _) hdroot
    rcases (outer_mem_sup_iff hx).mp hdS with hdP | hdP
    · by_cases hdV : k⁻¹ * r₁ * k ∈ R ⊔ T
      · refine h.isRootInv_of_mem_V (mul_mem (h.V₀_le hzV₀) hdV) fun h0 => hdV₀ ?_
        have := mul_mem (inv_mem hzV₀) h0
        rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
      · have hzdP : z * (k⁻¹ * r₁ * k) ∈ P := mul_mem (hVP (h.V₀_le hzV₀)) hdP
        have hzdV : z * (k⁻¹ * r₁ * k) ∉ R ⊔ T := fun h0 => hdV (by
          have := mul_mem (inv_mem (h.V₀_le hzV₀)) h0
          rwa [← mul_assoc, inv_mul_cancel, one_mul] at this)
        have hzd2 : z * (k⁻¹ * r₁ * k) * (z * (k⁻¹ * r₁ * k)) = 1 := by
          calc z * (k⁻¹ * r₁ * k) * (z * (k⁻¹ * r₁ * k)) =
              z * (k⁻¹ * r₁ * k * z) * (k⁻¹ * r₁ * k) := by group
            _ = z * (z * (k⁻¹ * r₁ * k)) * (k⁻¹ * r₁ * k) := by rw [hdz]
            _ = z * z * ((k⁻¹ * r₁ * k) * (k⁻¹ * r₁ * k)) := by group
            _ = 1 := by rw [h.mul_self (h.V₀_le hzV₀), hd2, one_mul]
        obtain ⟨c, hc⟩ := h.P_invol_conj hP hPC hdP hdV hd2 hzdP hzdV hzd2
        exact hdroot.of_isConj (isConj_iff.mpr ⟨c⁻¹, by rw [inv_inv]; exact hc⟩)
    · obtain ⟨w, -, hw⟩ := h.outer_exists_conj_mul_z hP hx hdP hd2
      rw [← hdz]
      exact hdroot.of_isConj (isConj_iff.mpr ⟨w⁻¹, by rw [inv_inv]; exact hw⟩)
  ·
    have hconjP : ∀ a ∈ V₀, a ≠ 1 → ∀ y : G, y⁻¹ * a * y ∈ P ⊔ zpowers x →
        y⁻¹ * a * y ∈ P := by
      intro a ha ha1 y hy
      rcases (outer_mem_sup_iff hx).mp hy with h1 | h1
      · exact h1
      · exfalso
        have ha2 : y⁻¹ * a * y * (y⁻¹ * a * y) = 1 := by
          calc y⁻¹ * a * y * (y⁻¹ * a * y) = y⁻¹ * (a * a) * y := by group
            _ = 1 := by rw [h.mul_self (h.V₀_le ha)]; group
        obtain ⟨q, -, hq⟩ := h.outer_exists_conj_eq hP hPC hx hP64 h1 ha2
        apply hxz
        refine (h.isConj_of_mem_V₀ hzV₀ hz1 ha ha1).trans (isConj_iff.mpr ⟨q * y⁻¹, ?_⟩)
        calc q * y⁻¹ * a * (q * y⁻¹)⁻¹ = q * (y⁻¹ * a * y) * q⁻¹ := by group
          _ = q * (q⁻¹ * x * q) * q⁻¹ := by rw [hq]
          _ = x := by group
    have hV₀1 : V₀ ≠ ⊥ := fun he => by
      have := h.card_V₀
      rw [he, card_bot] at this
      omega
    have hr₁S : r₁ ∈ (S : Subgroup G) := by
      rw [hSS]
      exact mem_sup_left (hVP (mem_sup_left hx.r_mem))
    have hr₁X := h.outer_r_mem_X hx
    have hr₁2 : r₁ ^ 2 = 1 := by rw [sq]; exact h.mul_self (mem_sup_left hx.r_mem)
    have hr₁V₀ : r₁ ∉ V₀ := fun h0 => hx.r_ne (by
      have h2 : r₁ ∈ R ⊓ V₀ := mem_inf.mpr ⟨hx.r_mem, h0⟩
      rwa [h.inf_R_V₀, mem_bot] at h2)
    by_cases hcase : ∃ c ∈ P, c ∉ R ⊔ T ∧ c * c = 1 ∧
        ∃ w ∈ V₀, w ≠ 1 ∧ ∃ y : G, y⁻¹ * w * y = c
    ·
      obtain ⟨c, hcP, hcV, hc2, w, hw, hw1, y₀, hy₀⟩ := hcase
      have hcl : ∀ a ∈ V', ∀ y : G, y⁻¹ * a * y ∈ (S : Subgroup G) → y⁻¹ * a * y ∈ V' := by
        intro a ha y hy
        by_cases ha1 : a = 1
        · rw [ha1]
          simp
        have ha2 : a * a = 1 := by rw [← sq]; exact hV'.elem.2 a ha
        obtain ⟨w', hw', hw'1, y', hy'⟩ : ∃ w' ∈ V₀, w' ≠ 1 ∧ ∃ y' : G, y'⁻¹ * w' * y' = a := by
          by_cases haV : a ∈ R ⊔ T
          · exact ⟨a, hV'.inf ▸ mem_inf.mpr ⟨haV, ha⟩, ha1, 1, by group⟩
          · obtain ⟨u, hu⟩ := h.P_invol_conj hP hPC hcP hcV hc2 (hV'.le ha) haV ha2
            exact ⟨w, hw, hw1, y₀ * u, by rw [← hu, ← hy₀]; group⟩
        have hb : y⁻¹ * a * y = (y' * y)⁻¹ * w' * (y' * y) := by rw [← hy']; group
        rw [hSS] at hy
        rw [hb] at hy ⊢
        have hbP := hconjP w' hw' hw'1 (y' * y) hy
        by_cases hbV : (y' * y)⁻¹ * w' * (y' * y) ∈ R ⊔ T
        · by_cases hb0 : (y' * y)⁻¹ * w' * (y' * y) ∈ V₀
          · exact hV₀V' hb0
          · exact absurd rfl (h.conj_V₀_ne hw' hw'1 hbV hb0 (y' * y))
        · refine hV'.inv _ hbP ?_ hbV
          calc (y' * y)⁻¹ * w' * (y' * y) * ((y' * y)⁻¹ * w' * (y' * y)) =
              (y' * y)⁻¹ * (w' * w') * (y' * y) := by group
            _ = 1 := by rw [h.mul_self (h.V₀_le hw')]; group
      have hr₁W := (h.goldschmidt_X hGold S (by rw [hSS]; exact hV'.le.trans le_sup_left)
        hV'.elem.1 hcl (fun he => hV₀1 (le_bot_iff.mp (he ▸ hV₀V')))).2 r₁ hr₁S hr₁X hr₁2
      exact hr₁V₀ (hV'.inf ▸ mem_inf.mpr ⟨mem_sup_left hx.r_mem, hr₁W⟩)
    ·
      push Not at hcase
      have hcl : ∀ a ∈ V₀, ∀ y : G, y⁻¹ * a * y ∈ (S : Subgroup G) → y⁻¹ * a * y ∈ V₀ := by
        intro a ha y hy
        by_cases ha1 : a = 1
        · rw [ha1]
          simp
        rw [hSS] at hy
        have hyP := hconjP a ha ha1 y hy
        by_cases hbV : y⁻¹ * a * y ∈ R ⊔ T
        · by_contra hb0
          exact h.conj_V₀_ne ha ha1 hbV hb0 y rfl
        · exfalso
          refine hcase _ hyP hbV ?_ a ha ha1 y rfl
          calc y⁻¹ * a * y * (y⁻¹ * a * y) = y⁻¹ * (a * a) * y := by group
            _ = 1 := by rw [h.mul_self (h.V₀_le ha)]; group
      have hab : IsMulCommutative V₀ :=
        ⟨⟨fun a b => Subtype.ext (h.comm (h.V₀_le a.2) (h.V₀_le b.2))⟩⟩
      have hVS : V₀ ≤ (S : Subgroup G) := by
        rw [hSS]
        exact (h.V₀_le.trans hVP).trans le_sup_left
      exact hr₁V₀ ((h.goldschmidt_X hGold S hVS hab hcl hV₀1).2 r₁ hr₁S hr₁X hr₁2)

end Outer

end PStructure

end Setting310

end CFSG.ComponentClassification.RankTwoAltFive
