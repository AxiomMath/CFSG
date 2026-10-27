module

public import CFSG.GroupTheory.ABGLocalTools.Constraint
import CFSG.GroupTheory.ABGLocalTools.RelativeStability
import CFSG.GroupTheory.ABGLocalTools.PStabilitySignalizer
import CFSG.GroupTheory.FrattiniQuotient

public section

open Subgroup
open scoped commutatorElement

namespace CFSG.ABGLocalTools

variable {H : Type*} [Group H] {p : ℕ}

@[expose] def IsChiefFactorUnder (p : ℕ) (N W₁ W₂ : Subgroup H) : Prop :=
  W₂ < W₁ ∧ N ≤ normalizer (W₁ : Set H) ∧ N ≤ normalizer (W₂ : Set H) ∧
    (∀ x ∈ W₁, ∀ y ∈ W₂, x * y * x⁻¹ ∈ W₂) ∧ (∀ x ∈ W₁, ∀ y ∈ W₁, ⁅x, y⁆ ∈ W₂) ∧
    (∀ x ∈ W₁, x ^ p ∈ W₂) ∧
    ∀ X : Subgroup H, W₂ ≤ X → X ≤ W₁ → N ≤ normalizer (X : Set H) → X = W₂ ∨ X = W₁

@[expose] def chiefKernel (p : ℕ) (P : Subgroup H) : Subgroup H where
  carrier := {n | n ∈ normalizer (P : Set H) ∧ ∀ W₁ W₂ : Subgroup H, W₁ ≤ P →
    IsChiefFactorUnder p (normalizer (P : Set H)) W₁ W₂ → ∀ w ∈ W₁, ⁅w, n⁆ ∈ W₂}
  one_mem' := ⟨one_mem _, fun _ W₂ _ _ w _ => by rw [commutatorElement_one_right]; exact one_mem _⟩
  mul_mem' := by
    rintro n m ⟨hn, hn'⟩ ⟨hm, hm'⟩
    refine ⟨mul_mem hn hm, fun W₁ W₂ hW hc w hw => ?_⟩
    have h1 := hn' W₁ W₂ hW hc w hw
    have h2 := hm' W₁ W₂ hW hc w hw
    have h3 : n * ⁅w, m⁆ * n⁻¹ ∈ W₂ := (mem_normalizer_iff.mp (hc.2.2.1 hn) _).mp h2
    have : ⁅w, n * m⁆ = ⁅w, n⁆ * (n * ⁅w, m⁆ * n⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [this]
    exact mul_mem h1 h3
  inv_mem' := by
    rintro n ⟨hn, hn'⟩
    refine ⟨inv_mem hn, fun W₁ W₂ hW hc w hw => ?_⟩
    have hw' : n⁻¹ * w * n ∈ W₁ := by
      have := (mem_normalizer_iff.mp (hc.2.1 (inv_mem hn)) w).mp hw
      simpa using this
    have h1 := hn' W₁ W₂ hW hc _ hw'
    have : ⁅w, n⁻¹⁆ = ⁅n⁻¹ * w * n, n⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [this]
    exact inv_mem h1

theorem mem_chiefKernel_iff {P : Subgroup H} {n : H} :
    n ∈ chiefKernel p P ↔ n ∈ normalizer (P : Set H) ∧ ∀ W₁ W₂ : Subgroup H, W₁ ≤ P →
      IsChiefFactorUnder p (normalizer (P : Set H)) W₁ W₂ → ∀ w ∈ W₁, ⁅w, n⁆ ∈ W₂ :=
  Iff.rfl

theorem pow_conj_eq_of_commute {m q : H} (hc : Commute m (q⁻¹ * m * q * m⁻¹)) (j : ℕ) :
    m ^ j * q * (m ^ j)⁻¹ = q * (q⁻¹ * m * q * m⁻¹) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 : m * q * m⁻¹ = q * (q⁻¹ * m * q * m⁻¹) := by group
    have h2 : m * (q⁻¹ * m * q * m⁻¹) ^ j * m⁻¹ = (q⁻¹ * m * q * m⁻¹) ^ j := by
      rw [(hc.pow_right j).eq, mul_inv_cancel_right]
    calc m ^ (j + 1) * q * (m ^ (j + 1))⁻¹ = m * (m ^ j * q * (m ^ j)⁻¹) * m⁻¹ := by group
      _ = m * (q * (q⁻¹ * m * q * m⁻¹) ^ j) * m⁻¹ := by rw [ih]
      _ = (m * q * m⁻¹) * (m * (q⁻¹ * m * q * m⁻¹) ^ j * m⁻¹) := by group
      _ = q * (q⁻¹ * m * q * m⁻¹) * (q⁻¹ * m * q * m⁻¹) ^ j := by rw [h1, h2]
      _ = q * (q⁻¹ * m * q * m⁻¹) ^ (j + 1) := by rw [pow_succ', mul_assoc]

variable [Finite H] [Fact p.Prime]

theorem exists_pow_centralizes_of_mem_chiefKernel {P : Subgroup H} (hP : IsPGroup p P) :
    ∀ n : ℕ, ∀ Q : Subgroup H, Nat.card Q = n → Q ≤ P →
      normalizer (P : Set H) ≤ normalizer (Q : Set H) →
      ∀ k ∈ chiefKernel p P, ∃ e : ℕ, ∀ q ∈ Q, k ^ (p ^ e) * q * (k ^ (p ^ e))⁻¹ = q := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Q hn hQP hQN k hk
  by_cases hQ : Q = ⊥
  · refine ⟨0, fun q hq => ?_⟩
    rw [hQ, mem_bot] at hq
    rw [hq, mul_one, mul_inv_cancel]
  have hQp : IsPGroup p Q := hP.to_le hQP
  set F := (frattini Q).map Q.subtype with hF
  obtain ⟨-, hcommQ, hpowQ, -, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hQp
  have hFQ : F ≤ Q := map_subtype_le _
  have hFne : F ≠ Q := by
    intro hFQ'
    apply hQ
    have htop : frattini Q = ⊤ := by
      apply map_injective Q.subtype_injective
      have h1 : (⊤ : Subgroup Q).map Q.subtype = Q := by
        rw [← MonoidHom.range_eq_map, range_subtype]
      rw [h1, ← hF, hFQ']
    have h := frattini_nongenerating (K := (⊥ : Subgroup Q)) (by rw [htop, sup_top_eq])
    rw [eq_bot_iff]
    intro q hq
    have : (⟨q, hq⟩ : Q) ∈ (⊥ : Subgroup Q) := by rw [h]; exact mem_top _
    rw [mem_bot] at this
    rw [mem_bot]
    exact congrArg Subtype.val this
  have hFN : normalizer (P : Set H) ≤ normalizer (F : Set H) := fun g hg =>
    mem_normalizer_map_subtype_of_characteristic (hQN hg)
  have hcommF : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ F := by
    intro x hx y hy
    refine ⟨⁅(⟨x, hx⟩ : Q), ⟨y, hy⟩⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, ← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (frattini Q) ⁅_, _⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact hcommQ.is_comm.comm _ _
  have hpowF : ∀ x ∈ Q, x ^ p ∈ F := by
    intro x hx
    refine ⟨(⟨x, hx⟩ : Q) ^ p, ?_, rfl⟩
    rw [SetLike.mem_coe, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hpowQ _
  obtain ⟨Q₁, hFQ₁, hmax⟩ := Finite.exists_le_maximal
    (p := fun Y : Subgroup H => F ≤ Y ∧ Y ≤ Q ∧ Y ≠ Q ∧
      normalizer (P : Set H) ≤ normalizer (Y : Set H)) ⟨le_rfl, hFQ, hFne, hFN⟩
  obtain ⟨-, hQ₁Q, hQ₁ne, hQ₁N⟩ := hmax.prop
  have hlt : Q₁ < Q := lt_of_le_of_ne hQ₁Q hQ₁ne
  have hchief : IsChiefFactorUnder p (normalizer (P : Set H)) Q Q₁ := by
    refine ⟨hlt, hQN, hQ₁N, fun x hx y hy => ?_, fun x hx y hy => hFQ₁ (hcommF x hx y hy),
      fun x hx => hFQ₁ (hpowF x hx), fun X hQ₁X hXQ hXN => ?_⟩
    · have : x * y * x⁻¹ = ⁅x, y⁆ * y := by
        simp only [commutatorElement_def]
        group
      rw [this]
      exact mul_mem (hFQ₁ (hcommF x hx y (hQ₁Q hy))) hy
    · by_cases hXQ' : X = Q
      · exact Or.inr hXQ'
      · exact Or.inl (hmax.eq_of_le ⟨hFQ₁.trans hQ₁X, hXQ, hXQ', hXN⟩ hQ₁X).symm
  have hkQ := (mem_chiefKernel_iff.mp hk).2 Q Q₁ hQP hchief
  obtain ⟨e₁, he₁⟩ := ih (Nat.card Q₁) (hn ▸ card_lt_of_lt hlt) Q₁ rfl (hQ₁Q.trans hQP) hQ₁N k
    hk
  set m := k ^ (p ^ e₁) with hm
  have hmK : m ∈ chiefKernel p P := pow_mem hk _
  have hmQ := (mem_chiefKernel_iff.mp hmK).2 Q Q₁ hQP hchief
  obtain ⟨a, ha⟩ := (hQp.to_le hQ₁Q).exists_card_eq
  refine ⟨e₁ + a, fun q hq => ?_⟩
  have hc : q⁻¹ * m * q * m⁻¹ ∈ Q₁ := by
    have := hmQ q⁻¹ (inv_mem hq)
    simpa [commutatorElement_def] using this
  have hcomm : Commute m (q⁻¹ * m * q * m⁻¹) := by
    have h := he₁ _ hc
    exact (mul_inv_eq_iff_eq_mul.mp h)
  have hcpow : (q⁻¹ * m * q * m⁻¹) ^ (p ^ a) = 1 := by
    have h := pow_card_eq_one' (G := Q₁) (x := ⟨_, hc⟩)
    rw [ha] at h
    exact congrArg Subtype.val h
  rw [pow_add, pow_mul, ← hm, pow_conj_eq_of_commute hcomm, hcpow, mul_one]

theorem le_normalizerPCoreModCentralizer_of_chief {P A : Subgroup H} (hP : IsPGroup p P)
    (hAN : A ≤ normalizer (P : Set H))
    (hchief : ∀ W₁ W₂ : Subgroup H, W₁ ≤ P →
      IsChiefFactorUnder p (normalizer (P : Set H)) W₁ W₂ → ⁅W₁, A⁆ ≤ W₂) :
    A ≤ normalizerPCoreModCentralizer p P := by
  set N := normalizer (P : Set H) with hN
  set Cn := (centralizer (P : Set H)).subgroupOf N with hCn
  set K := (chiefKernel p P).subgroupOf N with hK
  have hKn : K.Normal := by
    constructor
    intro k hk g
    rw [hK, mem_subgroupOf] at hk ⊢
    refine ⟨mul_mem (mul_mem g.2 (mem_chiefKernel_iff.mp hk).1) (inv_mem g.2),
      fun W₁ W₂ hW hc w hw => ?_⟩
    have hw' : (g : H)⁻¹ * w * g ∈ W₁ := by
      have := (mem_normalizer_iff.mp (hc.2.1 (inv_mem g.2)) w).mp hw
      simpa using this
    have h1 := (mem_chiefKernel_iff.mp hk).2 W₁ W₂ hW hc _ hw'
    have h2 := (mem_normalizer_iff.mp (hc.2.2.1 g.2) _).mp h1
    have : ⁅w, ((g * k * g⁻¹ : N) : H)⁆ = (g : H) * ⁅(g : H)⁻¹ * w * g, (k : H)⁆ * (g : H)⁻¹ := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [this]
    exact h2
  have himg : K.map (QuotientGroup.mk' Cn) ≤ pCore p (N ⧸ Cn) := by
    apply le_sSup
    refine ⟨hKn.map _ (QuotientGroup.mk'_surjective _), ?_⟩
    rintro ⟨x, k, hk, rfl⟩
    obtain ⟨e, he⟩ := exists_pow_centralizes_of_mem_chiefKernel hP _ P rfl le_rfl le_rfl k hk
    refine ⟨e, Subtype.ext ?_⟩
    change QuotientGroup.mk' Cn k ^ (p ^ e) = 1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hCn, mem_subgroupOf,
      mem_centralizer_iff]
    intro q hq
    have h := he q hq
    rw [Subgroup.coe_pow]
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  intro a ha
  have haK : a ∈ chiefKernel p P :=
    ⟨hAN ha, fun W₁ W₂ hW hc w hw => hchief W₁ W₂ hW hc (commutator_mem_commutator hw ha)⟩
  rw [mem_normalizerPCoreModCentralizer_iff]
  exact ⟨hAN ha, himg ⟨⟨a, hAN ha⟩, haK, rfl⟩⟩

end CFSG.ABGLocalTools
