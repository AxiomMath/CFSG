module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011S4aId
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93ModelJ
public import CFSG.GH74.GLS.Stage2.Local.Lemma23e

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK.Proofs2 CFSG.GH74.GLS.Stage2.Local

section Fused

variable {K : Type} [Group K] [Finite K]

theorem exists_order_four {L Q : Subgroup K} {q : ℕ} (hodd : Odd q) (hq3 : 3 < q)
    (hsl : HasSL2Model ↥L (fun r => r = q)) (hQ : CFSG.ABGLocalTools.IsSylowOf 2 Q L) {z : K}
    (hzL : z ∈ L) (hz2 : orderOf z = 2) : ∃ a ∈ Q, orderOf a = 4 ∧ a ^ 2 = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, huniq⟩ := sl2_model_center_inv hodd hsl
  have hcardL : Nat.card ↥L = q * (q ^ 2 - 1) := card_of_hasSL2Model hsl
  have h8 : 8 ∣ q ^ 2 - 1 := by
    obtain ⟨k, hk⟩ := hodd
    subst hk
    have : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by
      have h1 : 1 ≤ (2 * k + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      zify [h1]
      ring
    rw [this]
    obtain ⟨m, hm⟩ := Nat.even_mul_succ_self k
    exact ⟨m, by rw [hm]; ring⟩
  have hne : Nat.card ↥L ≠ 0 := Nat.card_pos.ne'
  have hf : 3 ≤ (Nat.card ↥L).factorization 2 := by
    rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne, hcardL]
    exact Dvd.dvd.mul_left (by simpa using h8) q
  have hQcard := hQ.card_eq
  have hQgt : 2 < Nat.card ↥Q := by
    rw [hQcard]
    calc 2 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (Nat.card ↥L).factorization 2 := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨x, hxQ, hxz⟩ : ∃ x ∈ Q, x ∉ zpowers z := by
    by_contra h
    push Not at h
    have hle : Q ≤ zpowers z := h
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hz2] at this
    omega
  have hQL : Q ≤ L := hQ.le
  obtain ⟨k, hk⟩ : ∃ k, orderOf x = 2 ^ k := by
    obtain ⟨j, hj⟩ := hQ.isPGroup ⟨x, hxQ⟩
    have h1 : orderOf x ∣ 2 ^ j := by
      apply orderOf_dvd_of_pow_eq_one
      exact congrArg Subtype.val hj
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    exact ⟨k, hk⟩
  have hk2 : 2 ≤ k := by
    by_contra hlt
    push Not at hlt
    interval_cases k
    · apply hxz
      have : x = 1 := orderOf_eq_one_iff.1 (by simpa using hk)
      rw [this]; exact one_mem _
    · apply hxz
      have h2 : orderOf x = 2 := by simpa using hk
      have := huniq x (hQL hxQ) z hzL h2 hz2
      rw [this]; exact mem_zpowers z
  obtain ⟨a, ha⟩ : ∃ a, a = x ^ (2 ^ (k - 2)) := ⟨_, rfl⟩
  have hdvd : 2 ^ (k - 2) ∣ orderOf x := by
    rw [hk]; exact Nat.pow_dvd_pow 2 (by omega)
  have hord4 : orderOf a = 4 := by
    rw [ha, orderOf_pow_of_dvd (by positivity) hdvd, hk]
    have : 2 ^ k = 2 ^ (k - 2) * 4 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
      congr 1; omega
    rw [this, Nat.mul_div_cancel_left _ (by positivity)]
  have haQ : a ∈ Q := by rw [ha]; exact Subgroup.pow_mem _ hxQ _
  refine ⟨a, haQ, hord4, ?_⟩
  have hsq : orderOf (a ^ 2) = 2 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hord4]; norm_num), hord4]
  exact huniq _ (Subgroup.pow_mem _ (hQL haQ) 2) z hzL hsq hz2


omit [Finite K] in
theorem mem_normalizer_of_commute {I₁ I₂ : Subgroup K} (hcomm : ∀ a ∈ I₁, ∀ b ∈ I₂, a * b = b * a)
    {a b : K} (ha : a ∈ I₁) (hb : b ∈ I₂) :
    a * b ∈ normalizer (I₁ : Set K) ∧ a * b ∈ normalizer (I₂ : Set K) := by
  have h₁ : ∀ g ∈ I₂, g ∈ normalizer (I₁ : Set K) := fun g hg => by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hc : ∀ x ∈ I₁, g * x * g⁻¹ = x := fun x hx => by
      calc g * x * g⁻¹ = (x * g) * g⁻¹ := by rw [hcomm x hx g hg]
        _ = x := by group
    constructor
    · intro hh; rw [hc h hh]; exact hh
    · intro hh
      have hc' : g⁻¹ * (g * h * g⁻¹) = (g * h * g⁻¹) * g⁻¹ :=
        (hcomm _ hh g⁻¹ (I₂.inv_mem hg)).symm
      have e : h = g * h * g⁻¹ := by
        calc h = g⁻¹ * (g * h * g⁻¹) * g := by group
          _ = (g * h * g⁻¹) * g⁻¹ * g := by rw [hc']
          _ = g * h * g⁻¹ := by group
      rw [e]; exact hh
  have h₂ : ∀ g ∈ I₁, g ∈ normalizer (I₂ : Set K) := fun g hg => by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hc : ∀ x ∈ I₂, g * x * g⁻¹ = x := fun x hx => by
      calc g * x * g⁻¹ = (x * g) * g⁻¹ := by rw [hcomm g hg x hx]
        _ = x := by group
    constructor
    · intro hh; rw [hc h hh]; exact hh
    · intro hh
      have hc' : g⁻¹ * (g * h * g⁻¹) = (g * h * g⁻¹) * g⁻¹ := hcomm g⁻¹ (I₁.inv_mem hg) _ hh
      have e : h = g * h * g⁻¹ := by
        calc h = g⁻¹ * (g * h * g⁻¹) * g := by group
          _ = (g * h * g⁻¹) * g⁻¹ * g := by rw [hc']
          _ = g * h * g⁻¹ := by group
      rw [e]; exact hh
  exact ⟨(normalizer (I₁ : Set K)).mul_mem (Subgroup.le_normalizer ha) (h₁ b hb),
    (normalizer (I₂ : Set K)).mul_mem (h₂ a ha) (Subgroup.le_normalizer hb)⟩


omit [Finite K] in
theorem le_normalizer_of_commute' {I₁ I₂ : Subgroup K} (hcomm : ∀ a ∈ I₁, ∀ b ∈ I₂, a * b = b * a) :
    I₂ ≤ normalizer (I₁ : Set K) := fun g hg => by
  have := mem_normalizer_of_commute hcomm (I₁.one_mem) hg
  simpa using this.1

theorem s4a_fused {q : ℕ} (hodd : Odd q) (hq3 : 3 < q) (P : Sylow 2 K) {z : K}
    (hzc : ∀ x ∈ (P : Subgroup K), x * z = z * x) (hz2 : orderOf z = 2) {I₁ I₂ : Subgroup K}
    (hI : I₁ ⊔ I₂ = IVK.Ez z) (hcomm : ∀ a ∈ I₁, ∀ b ∈ I₂, a * b = b * a) (hinter : I₁ ⊓ I₂ = zpowers z)
    (hsl₁ : HasSL2Model ↥I₁ (fun r => r = q)) (hsl₂ : HasSL2Model ↥I₂ (fun r => r = q))
    (hone : ∀ x y : K, orderOf x = 2 → orderOf y = 2 → IsConj x y) :
    ∃ y ∈ (P : Subgroup K), orderOf y = 2 ∧ y ≠ z ∧ IsConj z y ∧ y ∈ normalizer (I₁ : Set K) ∧
      y ∈ normalizer (I₂ : Set K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPtop : CFSG.ABGLocalTools.IsSylowOf 2 (P : Subgroup K) ⊤ :=
    ⟨P.subtype le_top, by rw [Sylow.coe_subtype, subgroupOf_map_subtype, inf_of_le_left le_top]⟩
  have hPC : (P : Subgroup K) ≤ centralizer ({z} : Set K) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (hzc x hx)
  have hSC : CFSG.ABGLocalTools.IsSylowOf 2 (P : Subgroup K) (centralizer ({z} : Set K)) :=
    hPtop.of_le hPC le_top
  have hEC : IVK.Ez z ≤ centralizer ({z} : Set K) := Ivk93Adapt.jm_Ez_le_centralizer z
  have hCE : centralizer ({z} : Set K) ≤ normalizer ((IVK.Ez z : Subgroup K) : Set K) :=
    Ivk93Adapt.jm_centralizer_le_normalizer_Ez z
  have hSE : CFSG.ABGLocalTools.IsSylowOf 2 ((P : Subgroup K) ⊓ IVK.Ez z) (IVK.Ez z) :=
    hSC.inf_of_le_normalizer hEC hCE
  have hzI : z ∈ I₁ ⊓ I₂ := by rw [hinter]; exact mem_zpowers z
  have hI₁E : I₁ ≤ IVK.Ez z := hI ▸ le_sup_left
  have hI₂E : I₂ ≤ IVK.Ez z := hI ▸ le_sup_right
  have hcomm' : ∀ a ∈ I₂, ∀ b ∈ I₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  have hEn₁ : IVK.Ez z ≤ normalizer (I₁ : Set K) := by
    rw [← hI]; exact sup_le Subgroup.le_normalizer (le_normalizer_of_commute' hcomm)
  have hEn₂ : IVK.Ez z ≤ normalizer (I₂ : Set K) := by
    rw [← hI]; exact sup_le (le_normalizer_of_commute' hcomm') Subgroup.le_normalizer
  have hS₁ := hSE.inf_of_le_normalizer hI₁E hEn₁
  have hS₂ := hSE.inf_of_le_normalizer hI₂E hEn₂
  obtain ⟨a, haQ, ha4, ha2⟩ := exists_order_four hodd hq3 hsl₁ hS₁ hzI.1 hz2
  obtain ⟨b, hbQ, hb4, hb2⟩ := exists_order_four hodd hq3 hsl₂ hS₂ hzI.2 hz2
  have haP : a ∈ (P : Subgroup K) := haQ.1.1
  have hbP : b ∈ (P : Subgroup K) := hbQ.1.1
  have haI : a ∈ I₁ := haQ.2
  have hbI : b ∈ I₂ := hbQ.2
  have hab : a * b = b * a := hcomm a haI b hbI
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, sq] at this
  have hsq : a * b * (a * b) = 1 := by
    have ha2' : a * a = z := by rw [← sq]; exact ha2
    have hb2' : b * b = z := by rw [← sq]; exact hb2
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2', hb2', hzz]
  have hnot : ∀ {c : K}, c ∈ I₁ → c ∈ I₂ → orderOf c = 4 → False := by
    intro c hc1 hc2 hc4
    have : c ∈ zpowers z := hinter ▸ ⟨hc1, hc2⟩
    have := orderOf_dvd_of_mem_zpowers this
    rw [hc4, hz2] at this
    omega
  have hy1 : a * b ≠ 1 := by
    intro h
    have : a = b⁻¹ := eq_inv_of_mul_eq_one_left h
    exact hnot haI (by rw [this]; exact I₂.inv_mem hbI) ha4
  have hyz : a * b ≠ z := by
    intro h
    have : a = z * b⁻¹ := by rw [← h]; group
    exact hnot haI (by rw [this]; exact I₂.mul_mem hzI.2 (I₂.inv_mem hbI)) ha4
  have hy2 : orderOf (a * b) = 2 := orderOf_eq_prime (by rwa [sq]) hy1
  exact ⟨a * b, (P : Subgroup K).mul_mem haP hbP, hy2, hyz, hone z (a * b) hz2 hy2,
    (mem_normalizer_of_commute hcomm haI hbI).1, (mem_normalizer_of_commute hcomm haI hbI).2⟩


end Fused

section NonFused

variable {K : Type} [Group K] [Finite K]

theorem hasSL2Model_of_equiv {A B : Type} [Group A] [Group B] {q : ℕ}
    (h : HasSL2Model A (fun r => r = q)) (e : A ≃* B) : HasSL2Model B (fun r => r = q) := by
  obtain ⟨F, iF, fF, hq, ⟨e'⟩⟩ := h
  exact ⟨F, iF, fF, hq, ⟨e.symm.trans e'⟩⟩

theorem s4a_nonfused {q : ℕ} (hodd : Odd q) (h5 : 5 ≤ q)
    (hK : (q % 4 = 3 ∧ IVK.IsLnEps 4 K 1 q) ∨ (q % 4 = 1 ∧ IVK.IsLnEps 4 K (-1) q))
    (P : Sylow 2 K) {z : K} (hzP : z ∈ (P : Subgroup K)) (hz2 : orderOf z = 2)
    (hzc : ∀ x ∈ (P : Subgroup K), x * z = z * x) {I₁ I₂ : Subgroup K}
    (hI : I₁ ⊔ I₂ = IVK.Ez z) (hcomm : ∀ a ∈ I₁, ∀ b ∈ I₂, a * b = b * a)
    (hsl₁ : HasSL2Model ↥I₁ (fun r => r = q)) (hsl₂ : HasSL2Model ↥I₂ (fun r => r = q)) :
    ∃ y ∈ (P : Subgroup K), orderOf y = 2 ∧ y ≠ z ∧ IsConj z y ∧ y ∈ normalizer (I₁ : Set K) ∧
      y ∈ normalizer (I₂ : Set K) := by
  obtain ⟨t, w, E₁, E₂, htP, hwP, ht2, hw2, htw, hprod, hinterE, htconj, hEz, hE₂, hsl, hE₁₂, hcommE,
    hnorm, hw1iff, hclasses, hnotconj, hEfus, hpgl, hwfus, hcen⟩ :=
    CFSG.GH74.GLS.Stage2.Final.ivk_4_10 K q hodd h5 (Or.inr hK) P z hzP hz2 hzc
  have hw1 : w ≠ 1 := by
    intro h
    have hpsp := hw1iff.1 h
    rcases hK with ⟨-, hl⟩ | ⟨-, hl⟩
    · exact (CFSG.GH74.GLS.Stage2.Final.ivk_PSp4_ne_LU K q hpsp).1 hl
    · exact (CFSG.GH74.GLS.Stage2.Final.ivk_PSp4_ne_LU K q hpsp).2 hl
  have hwo : orderOf w = 2 := hw2.resolve_left hw1
  have hwz : IsConj z w := by
    have := (hwfus hw1).2 1 ⟨(P : Subgroup K).one_mem, (IVK.Ez z).one_mem⟩ (by simpa using hwo)
    simpa using this
  have hwE : w ∉ IVK.Ez z := by
    intro h
    have : w ∈ IVK.Ez z ⊓ (zpowers t ⊔ zpowers w) := ⟨h, Subgroup.mem_sup_right (mem_zpowers w)⟩
    rw [hinterE, Subgroup.mem_bot] at this
    exact hw1 this
  have hzE : z ∈ IVK.Ez z := by
    rw [hEz]
    have : z ∈ E₁ ⊓ E₂ := by rw [hE₁₂]; exact mem_zpowers z
    exact Subgroup.mem_sup_left this.1
  have hwz' : w ≠ z := fun h => hwE (h ▸ hzE)
  have hwN₁ : w ∈ normalizer (E₁ : Set K) := by
    have : w ∈ (P : Subgroup K) ⊓ IVK.Ez z ⊔ zpowers w := Subgroup.mem_sup_right (mem_zpowers w)
    rw [← hnorm] at this
    exact this.1
  have hsE₂ : HasSL2Model ↥E₂ (fun r => r = q) := by
    refine hasSL2Model_of_equiv hsl ?_
    rw [hE₂]
    exact E₁.equivMapOfInjective _ (MulAut.conj t).injective
  have hwN₂ : w ∈ normalizer (E₂ : Set K) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hmem : ∀ y, y ∈ E₂ ↔ t⁻¹ * y * t ∈ E₁ := fun y => by
      rw [hE₂]
      exact Lemma31g.mem_conj_iff E₁ t y
    have hc : t⁻¹ * (w * x * w⁻¹) * t = w * (t⁻¹ * x * t) * w⁻¹ := by
      have h1 : t⁻¹ * w = w * t⁻¹ := htw.inv_left.eq
      have h2 : w⁻¹ * t = t * w⁻¹ := htw.symm.inv_left.eq
      calc t⁻¹ * (w * x * w⁻¹) * t = (t⁻¹ * w) * x * (w⁻¹ * t) := by group
        _ = (w * t⁻¹) * x * (t * w⁻¹) := by rw [h1, h2]
        _ = w * (t⁻¹ * x * t) * w⁻¹ := by group
    rw [hmem, hmem, hc]
    exact Subgroup.mem_normalizer_iff.1 hwN₁ (t⁻¹ * x * t)
  have hdec := decomp_eq_of_sl2 (z := z) (by omega : 3 < q) hz2 (E₁ := E₁) (E₂ := E₂) (I₁ := I₁) (I₂ := I₂)
    (by rw [← hEz, hI]) hcommE hE₁₂ hsl hsE₂ hcomm hsl₁ hsl₂
  refine ⟨w, hwP, hwo, hwz', hwz, ?_, ?_⟩
  · rcases hdec.1 with h | h <;> rw [h]
    · exact hwN₁
    · exact hwN₂
  · rcases hdec.2 with h | h <;> rw [h]
    · exact hwN₁
    · exact hwN₂

end NonFused

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011
