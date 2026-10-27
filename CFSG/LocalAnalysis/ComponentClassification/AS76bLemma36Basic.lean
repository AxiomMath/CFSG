module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75Lemma31
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma35
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.ComponentClassification

open Subgroup CFSG.Open CFSG.Goldschmidt CFSG.Goldschmidt.G2
open scoped Pointwise commutatorElement

namespace Asc75Lemma31.Hyp

variable {G : Type} [Group G] {V X : Subgroup G} {y : G} (h : Hyp V X y)
include h

omit h in
theorem le_fixGrp_of_inf_eq_bot {M : Subgroup G} (hMV : M ≤ V)
    (hMy : y ∈ normalizer (M : Set G)) (hMW : M ⊓ comGrp V y = ⊥) : M ≤ fixGrp V y := by
  intro m hm
  refine mem_inf.mpr ⟨hMV hm, ?_⟩
  by_contra hmy
  have hmem : ⁅m, y⁆ ∈ M ⊓ comGrp V y := by
    refine mem_inf.mpr ⟨?_, commutator_mem_commutator (hMV hm) (mem_zpowers y)⟩
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    refine mul_mem hm ?_
    rw [← mul_assoc]
    exact (mem_normalizer_iff.mp hMy m⁻¹).mp (inv_mem hm)
  rw [hMW, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact hmy (mem_centralizer_singleton_iff.mpr hmem)

theorem comGrp_le_of_inf_ne_bot {M : Subgroup G} (hMy : y ∈ normalizer (M : Set G))
    (hMW : M ⊓ comGrp V y ≠ ⊥) : comGrp V y ≤ M := by
  obtain ⟨⟨w₀, hw₀⟩, hw₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hMW
  have hw₀1' : w₀ ≠ 1 := fun h1 => hw₀1 (Subtype.ext h1)
  intro w hw
  by_cases hw1 : w = 1
  · rw [hw1]
    exact one_mem M
  obtain ⟨k, hk⟩ := h.trans w₀ (mem_inf.mp hw₀).2 w hw hw₀1' hw1
  have := (mem_normalizer_iff.mp (inv_mem (pow_mem hMy k)) w₀).mp (mem_inf.mp hw₀).1
  rwa [inv_inv, hk] at this

theorem comGrp_le_of_ne_bot {x₀ : G} (hx₀ : x₀ ∈ X) (hU : conjSub x₀ (fixGrp V y) ≠ fixGrp V y)
    {M : Subgroup G} (hMV : M ≤ V) (hMX : X ≤ normalizer (M : Set G)) (hM : M ≠ ⊥) :
    comGrp V y ≤ M :=
  h.comGrp_le_of_inf_ne_bot (hMX h.mem) (h.inf_comGrp_ne_bot hx₀ hU hMV hMX hM)

end Asc75Lemma31.Hyp

namespace AS76b.Lemma36

open Asc75Lemma31

variable {G : Type} [Group G] [Finite G]

structure ConjData (V Q B : Subgroup G) (y : G) : Prop where
  elem : IsElemAbelian 2 V
  le : Q ≤ V
  sup_eq : Q ⊔ (V ⊓ B) = V
  le_centralizer : Q ≤ centralizer (B : Set G)
  mem : y ∈ B
  mem_normalizer : y ∈ normalizer (V : Set G)
  odd : Odd (orderOf y)
  trans : ∀ b ∈ V ⊓ B, ∀ c ∈ V ⊓ B, b ≠ 1 → c ≠ 1 → ∃ k : ℕ, (y ^ k)⁻¹ * b * y ^ k = c
  four_le : 4 ≤ Nat.card Q
  card_lt : 2 * Nat.card Q < Nat.card V

namespace ConjData

variable {V Q B : Subgroup G} {y : G} (d : ConjData V Q B y)
include d

omit [Finite G] in
theorem commute_of_mem {q : G} (hq : q ∈ Q) : q * y = y * q :=
  (mem_centralizer_iff.mp (d.le_centralizer hq) y d.mem).symm

omit [Finite G] in
theorem le_normalizer : V ⊓ B ≤ normalizer (Q : Set G) :=
  le_normalizer_of_le d.elem d.le inf_le_left

theorem card_le : Nat.card V ≤ Nat.card Q * Nat.card (V ⊓ B : Subgroup G) := by
  conv_lhs => rw [← d.sup_eq]
  exact AS76b.card_sup_le_mul d.le_normalizer

omit [Finite G] in
theorem ne_bot : Q ≠ ⊥ := by
  intro h0
  have := d.four_le
  rw [h0, card_bot] at this
  omega

theorem eq_one_of_commute {z : G} (hz : z ∈ V ⊓ B) (hzy : z * y = y * z) : z = 1 := by
  by_contra hz1
  have hle : V ⊓ B ≤ zpowers z := by
    intro e he
    by_cases he1 : e = 1
    · rw [he1]
      exact one_mem _
    obtain ⟨k, hk⟩ := d.trans z hz e he hz1 he1
    have hc : (y ^ k)⁻¹ * z * y ^ k = z := by
      rw [mul_assoc, (Commute.pow_right hzy k).eq, inv_mul_cancel_left]
    rw [← hk, hc]
    exact mem_zpowers z
  have h2 : Nat.card (zpowers z) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one two_pos (d.elem.2 z (mem_inf.mp hz).1)
  have h3 : Nat.card V ≤ Nat.card Q * 2 :=
    d.card_le.trans (Nat.mul_le_mul_left _ ((card_le_of_le hle).trans h2))
  have := d.card_lt
  omega

theorem inf_eq_bot : Q ⊓ (V ⊓ B) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [mem_bot]
  exact d.eq_one_of_commute (mem_inf.mp hz).2 (d.commute_of_mem (mem_inf.mp hz).1)

theorem card_eq : Nat.card V = Nat.card Q * Nat.card (V ⊓ B : Subgroup G) := by
  conv_lhs => rw [← d.sup_eq]
  exact AS76b.card_sup_eq_mul d.le_normalizer d.inf_eq_bot

theorem inf_ne_bot : V ⊓ B ≠ ⊥ := by
  intro h0
  have h1 := d.card_eq
  rw [h0, card_bot, mul_one] at h1
  have := d.card_lt
  omega

theorem fixGrp_eq : fixGrp V y = Q := by
  refine le_antisymm (fun v hv => ?_)
    (le_inf d.le fun q hq => mem_centralizer_singleton_iff.mpr (d.commute_of_mem hq))
  obtain ⟨hvV, hvy⟩ := mem_inf.mp hv
  have hv' : v ∈ Q ⊔ (V ⊓ B) := by
    rw [d.sup_eq]
    exact hvV
  obtain ⟨q, hq, w, hw, rfl⟩ := AS76b.exists_mul_of_mem_sup_of_le_normalizer d.le_normalizer hv'
  have h1 : q * w * y = y * (q * w) := mem_centralizer_singleton_iff.mp hvy
  have h2 : q * y = y * q := d.commute_of_mem hq
  have hwy : w * y = y * w := by
    apply mul_left_cancel (a := q)
    rw [← mul_assoc, h1, ← mul_assoc, ← h2, mul_assoc]
  rw [d.eq_one_of_commute hw hwy, mul_one]
  exact hq

omit [Finite G] in
theorem commutatorElement_mem {v a : G} (hv : v ∈ V) (haB : a ∈ B)
    (haV : a ∈ normalizer (V : Set G)) : ⁅v, a⁆ ∈ V ⊓ B := by
  have hv' : v ∈ Q ⊔ (V ⊓ B) := by
    rw [d.sup_eq]
    exact hv
  refine mem_inf.mpr ⟨?_, ?_⟩
  · rw [commutatorElement_def]
    have h1 : a * v⁻¹ * a⁻¹ ∈ V := (mem_normalizer_iff.mp haV _).mp (inv_mem hv)
    simpa [mul_assoc] using mul_mem hv h1
  obtain ⟨q, hq, w, hw, rfl⟩ := AS76b.exists_mul_of_mem_sup_of_le_normalizer d.le_normalizer hv'
  have hwB : w ∈ B := (mem_inf.mp hw).2
  have hc : q * (w * a * w⁻¹) = (w * a * w⁻¹) * q :=
    (mem_centralizer_iff.mp (d.le_centralizer hq) _ (mul_mem (mul_mem hwB haB) (inv_mem hwB))).symm
  have heq : ⁅q * w, a⁆ = w * a * w⁻¹ * a⁻¹ := by
    rw [commutatorElement_def]
    calc q * w * a * (q * w)⁻¹ * a⁻¹ = q * (w * a * w⁻¹) * q⁻¹ * a⁻¹ := by group
      _ = (w * a * w⁻¹) * q * q⁻¹ * a⁻¹ := by rw [hc]
      _ = w * a * w⁻¹ * a⁻¹ := by group
  rw [heq]
  exact mul_mem (mul_mem (mul_mem hwB haB) (inv_mem hwB)) (inv_mem haB)

omit [Finite G] in
theorem comGrp_le : comGrp V y ≤ V ⊓ B := by
  rw [comGrp, commutator_le]
  intro v hv z hz
  exact d.commutatorElement_mem hv ((zpowers_le.mpr d.mem) hz)
    ((zpowers_le.mpr d.mem_normalizer) hz)

theorem not_mem_centralizer : y ∉ centralizer (V : Set G) := by
  intro hy
  apply d.inf_ne_bot
  rw [eq_bot_iff]
  intro z hz
  rw [mem_bot]
  exact d.eq_one_of_commute hz (mem_centralizer_iff.mp hy z (mem_inf.mp hz).1)

theorem hyp {X : Subgroup G} (hX : X ≤ normalizer (V : Set G)) (hyX : y ∈ X)
    (hti : ∀ x ∈ X, conjSub x Q ≠ Q → Q ⊓ conjSub x Q = ⊥) : Hyp V X y where
  elem := d.elem
  le := hX
  mem := hyX
  odd := d.odd
  not_mem := d.not_mem_centralizer
  ne_bot := by
    change fixGrp V y ≠ ⊥
    rw [d.fixGrp_eq]
    exact d.ne_bot
  trans := fun b hb c hc hb1 hc1 => d.trans b (d.comGrp_le hb) c (d.comGrp_le hc) hb1 hc1
  ti := by
    intro x hx hne
    change conjSub x (fixGrp V y) ≠ fixGrp V y at hne
    change fixGrp V y ⊓ conjSub x (fixGrp V y) = ⊥
    rw [d.fixGrp_eq] at hne ⊢
    exact hti x hx hne

theorem comGrp_eq : comGrp V y = V ⊓ B := by
  have h0 : Hyp V (zpowers y) y := d.hyp (zpowers_le.mpr d.mem_normalizer) (mem_zpowers y)
    fun x hx hne => absurd (by rw [← d.fixGrp_eq]; exact Hyp.conjSub_fixGrp hx) hne
  refine eq_of_le_of_card_ge d.comGrp_le ?_
  have h1 := h0.card_eq
  rw [d.fixGrp_eq] at h1
  have h2 := d.card_eq
  have hQ : 0 < Nat.card Q := Nat.card_pos
  exact (Nat.eq_of_mul_eq_mul_left hQ (h1.symm.trans h2)).ge

theorem commutator_eq : ⁅B ⊓ normalizer (V : Set G), V⁆ = V ⊓ B := by
  apply le_antisymm
  · rw [commutator_comm, commutator_le]
    intro v hv a ha
    exact d.commutatorElement_mem hv (mem_inf.mp ha).1 (mem_inf.mp ha).2
  · rw [← d.comGrp_eq, comGrp, commutator_comm]
    exact commutator_mono (zpowers_le.mpr (mem_inf.mpr ⟨d.mem, d.mem_normalizer⟩)) le_rfl

end ConjData

@[expose] def pairGroup (V B₁ B₂ : Subgroup G) : Subgroup G :=
  AS76b.oUpperTwo (B₁ ⊓ normalizer (V : Set G)) ⊔ AS76b.oUpperTwo (B₂ ⊓ normalizer (V : Set G))

section PairGroup

variable {V B₁ B₂ : Subgroup G}

omit [Finite G] in
theorem oUpperTwo_le (H : Subgroup G) : AS76b.oUpperTwo H ≤ H :=
  (closure_le _).mpr fun _ hx => hx.1

omit [Finite G] in
theorem pairGroup_comm : pairGroup V B₁ B₂ = pairGroup V B₂ B₁ :=
  sup_comm _ _

omit [Finite G] in
theorem pairGroup_le : pairGroup V B₁ B₂ ≤ normalizer (V : Set G) :=
  sup_le ((oUpperTwo_le _).trans inf_le_right) ((oUpperTwo_le _).trans inf_le_right)

omit [Finite G] in
theorem mem_pairGroup_left {y : G} (hyB : y ∈ B₁) (hyV : y ∈ normalizer (V : Set G))
    (hy : Odd (orderOf y)) : y ∈ pairGroup V B₁ B₂ :=
  mem_sup_left (subset_closure ⟨mem_inf.mpr ⟨hyB, hyV⟩, hy⟩)

omit [Finite G] in
theorem mem_pairGroup_right {y : G} (hyB : y ∈ B₂) (hyV : y ∈ normalizer (V : Set G))
    (hy : Odd (orderOf y)) : y ∈ pairGroup V B₁ B₂ :=
  mem_sup_right (subset_closure ⟨mem_inf.mpr ⟨hyB, hyV⟩, hy⟩)

omit [Finite G] in
theorem index_pairGroup_ne_two {X₀ : Subgroup G} :
    (X₀.subgroupOf (pairGroup V B₁ B₂)).index ≠ 2 := by
  intro h2
  have hodd : ∀ z ∈ pairGroup V B₁ B₂, Odd (orderOf z) → z ∈ X₀ := by
    intro z hz hzo
    have hsq : z * z ∈ X₀ := mem_subgroupOf.mp (Subgroup.mul_self_mem_of_index_two h2 ⟨z, hz⟩)
    obtain ⟨m, hm⟩ := hzo
    have hz' : z = (z * z) ^ (m + 1) := by
      rw [← sq, ← pow_mul, show 2 * (m + 1) = orderOf z + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    rw [hz']
    exact pow_mem hsq _
  have hle : pairGroup V B₁ B₂ ≤ X₀ := sup_le
    ((closure_le _).mpr fun z hz => hodd z (mem_sup_left (subset_closure hz)) hz.2)
    ((closure_le _).mpr fun z hz => hodd z (mem_sup_right (subset_closure hz)) hz.2)
  have htop : X₀.subgroupOf (pairGroup V B₁ B₂) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    exact mem_subgroupOf.mpr (hle z.2)
  rw [htop, index_top] at h2
  exact absurd h2 (by norm_num)

end PairGroup

structure PairData (V Q₁ B₁ Q₂ B₂ : Subgroup G) (y₁ y₂ : G) : Prop where
  d₁ : ConjData V Q₁ B₁ y₁
  d₂ : ConjData V Q₂ B₂ y₂
  inf_eq_bot : Q₁ ⊓ Q₂ = ⊥
  ti₁ : ∀ x ∈ pairGroup V B₁ B₂, conjSub x Q₁ ≠ Q₁ → Q₁ ⊓ conjSub x Q₁ = ⊥
  ti₂ : ∀ x ∈ pairGroup V B₁ B₂, conjSub x Q₂ ≠ Q₂ → Q₂ ⊓ conjSub x Q₂ = ⊥
  norm₁ : ∀ x ∈ pairGroup V B₁ B₂, conjSub x Q₁ = Q₁ →
    x⁻¹ * y₁ * x ∈ zpowers y₁ ⊔ centralizer (V : Set G)
  norm₂ : ∀ x ∈ pairGroup V B₁ B₂, conjSub x Q₂ = Q₂ →
    x⁻¹ * y₂ * x ∈ zpowers y₂ ⊔ centralizer (V : Set G)

namespace PairData

variable {V Q₁ B₁ Q₂ B₂ : Subgroup G} {y₁ y₂ : G} (hp : PairData V Q₁ B₁ Q₂ B₂ y₁ y₂)
include hp

omit [Finite G] in
theorem symm : PairData V Q₂ B₂ Q₁ B₁ y₂ y₁ where
  d₁ := hp.d₂
  d₂ := hp.d₁
  inf_eq_bot := by rw [inf_comm]; exact hp.inf_eq_bot
  ti₁ := fun x hx => hp.ti₂ x (by rwa [pairGroup_comm])
  ti₂ := fun x hx => hp.ti₁ x (by rwa [pairGroup_comm])
  norm₁ := fun x hx => hp.norm₂ x (by rwa [pairGroup_comm])
  norm₂ := fun x hx => hp.norm₁ x (by rwa [pairGroup_comm])

omit [Finite G] in
theorem mem₁ : y₁ ∈ pairGroup V B₁ B₂ :=
  mem_pairGroup_left hp.d₁.mem hp.d₁.mem_normalizer hp.d₁.odd

theorem hyp₁ : Hyp V (pairGroup V B₁ B₂) y₁ :=
  hp.d₁.hyp pairGroup_le hp.mem₁ hp.ti₁

theorem lemma31₁ :
    (∀ x ∈ pairGroup V B₁ B₂, conjSub x (V ⊓ B₁) = V ⊓ B₁ ∧ conjSub x Q₁ = Q₁) ∨
      ((∀ x ∈ pairGroup V B₁ B₂, conjSub x (V ⊓ B₁) = V ⊓ B₁) ∧
        (∀ x ∈ pairGroup V B₁ B₂, ∀ x' ∈ pairGroup V B₁ B₂, conjSub x Q₁ ≠ Q₁ →
          conjSub x' Q₁ ≠ Q₁ → ∃ k : ℕ, conjSub (y₁ ^ k) (conjSub x Q₁) = conjSub x' Q₁) ∧
        ∀ v ∈ V, v ∉ V ⊓ B₁ ↔ ∃ x ∈ pairGroup V B₁ B₂, v ∈ conjSub x Q₁ ∧ v ≠ 1) := by
  have hN : ∀ x ∈ pairGroup V B₁ B₂, conjSub x (fixGrp V y₁) = fixGrp V y₁ →
      x⁻¹ * y₁ * x ∈ zpowers y₁ ⊔ centralizer (V : Set G) := by
    intro x hx hxU
    rw [hp.d₁.fixGrp_eq] at hxU
    exact hp.norm₁ x hx hxU
  have h := lemma31 hp.hyp₁ (fun _ _ _ => index_pairGroup_ne_two) hN
  rw [hp.d₁.fixGrp_eq, hp.d₁.comGrp_eq] at h
  rcases h with ⟨h1, -⟩ | h2 | ⟨hW, htr, -, hcov⟩
  · have := hp.d₁.four_le
    omega
  · exact Or.inl h2
  · exact Or.inr ⟨hW, htr, hcov⟩

theorem normalizes₁ : ∀ x ∈ pairGroup V B₁ B₂, conjSub x (V ⊓ B₁) = V ⊓ B₁ := by
  rcases hp.lemma31₁ with h | ⟨h, -⟩
  · exact fun x hx => (h x hx).1
  · exact h

theorem normalizes₂ : ∀ x ∈ pairGroup V B₁ B₂, conjSub x (V ⊓ B₂) = V ⊓ B₂ := by
  intro x hx
  exact hp.symm.normalizes₁ x (by rwa [pairGroup_comm])

theorem case_three₁ {x₀ : G} (hx₀ : x₀ ∈ pairGroup V B₁ B₂) (hU : conjSub x₀ Q₁ ≠ Q₁) :
    (∀ x ∈ pairGroup V B₁ B₂, ∀ x' ∈ pairGroup V B₁ B₂, conjSub x Q₁ ≠ Q₁ →
      conjSub x' Q₁ ≠ Q₁ → ∃ k : ℕ, conjSub (y₁ ^ k) (conjSub x Q₁) = conjSub x' Q₁) ∧
    ∀ v ∈ V, v ∉ V ⊓ B₁ ↔ ∃ x ∈ pairGroup V B₁ B₂, v ∈ conjSub x Q₁ ∧ v ≠ 1 := by
  rcases hp.lemma31₁ with h | ⟨-, htr, hcov⟩
  · exact absurd (h x₀ hx₀).2 hU
  · exact ⟨htr, hcov⟩

theorem le_of_ne_bot₁ {x₀ : G} (hx₀ : x₀ ∈ pairGroup V B₁ B₂) (hU : conjSub x₀ Q₁ ≠ Q₁)
    {M : Subgroup G} (hMV : M ≤ V) (hMX : ∀ x ∈ pairGroup V B₁ B₂, conjSub x M = M)
    (hM : M ≠ ⊥) : V ⊓ B₁ ≤ M := by
  rw [← hp.d₁.comGrp_eq]
  refine hp.hyp₁.comGrp_le_of_ne_bot hx₀ (by rwa [hp.d₁.fixGrp_eq]) hMV
    (fun x hx => mem_normalizer_of_conjSub_eq (hMX x hx)) hM

theorem eq_of_normalizes₂ (hX₂ : ∀ x ∈ pairGroup V B₁ B₂, conjSub x Q₂ = Q₂) :
    Q₂ = V ⊓ B₁ := by
  have hy₁ : y₁ ∈ normalizer (Q₂ : Set G) := mem_normalizer_of_conjSub_eq (hX₂ y₁ hp.mem₁)
  have hne : Q₂ ⊓ comGrp V y₁ ≠ ⊥ := by
    intro h0
    have h1 := Hyp.le_fixGrp_of_inf_eq_bot hp.d₂.le hy₁ h0
    rw [hp.d₁.fixGrp_eq] at h1
    apply hp.d₂.ne_bot
    rw [eq_bot_iff, ← hp.inf_eq_bot]
    exact le_inf h1 le_rfl
  have hle := hp.hyp₁.comGrp_le_of_inf_ne_bot hy₁ hne
  rw [hp.d₁.comGrp_eq] at hle
  refine (eq_of_le_of_card_ge hle ?_).symm
  have h1 : Nat.card (Q₁ ⊔ Q₂ : Subgroup G) = Nat.card Q₁ * Nat.card Q₂ :=
    AS76b.card_sup_eq_mul (le_normalizer_of_le hp.d₁.elem hp.d₁.le hp.d₂.le) hp.inf_eq_bot
  have h2 : Nat.card (Q₁ ⊔ Q₂ : Subgroup G) ≤ Nat.card V :=
    card_le_of_le (sup_le hp.d₁.le hp.d₂.le)
  have h4 : Nat.card Q₁ * Nat.card Q₂ ≤ Nat.card Q₁ * Nat.card (V ⊓ B₁ : Subgroup G) := by
    rw [← h1, ← hp.d₁.card_eq]
    exact h2
  exact Nat.le_of_mul_le_mul_left h4 Nat.card_pos

theorem eq_of_normalizes (hX : ∀ x ∈ pairGroup V B₁ B₂, conjSub x Q₁ = Q₁) :
    Q₂ = V ⊓ B₁ ∧ Q₁ = V ⊓ B₂ ∧ ∀ x ∈ pairGroup V B₁ B₂, conjSub x Q₂ = Q₂ := by
  have hX₂ : ∀ x ∈ pairGroup V B₁ B₂, conjSub x Q₂ = Q₂ := by
    by_contra hne
    push Not at hne
    obtain ⟨x₀, hx₀, hx₀Q⟩ := hne
    have hx₀' : x₀ ∈ pairGroup V B₂ B₁ := by rwa [pairGroup_comm]
    have hX' : ∀ x ∈ pairGroup V B₂ B₁, conjSub x Q₁ = Q₁ := fun x hx =>
      hX x (by rwa [pairGroup_comm])
    have hW' : ∀ x ∈ pairGroup V B₂ B₁, conjSub x (V ⊓ B₁) = V ⊓ B₁ := fun x hx =>
      hp.normalizes₁ x (by rwa [pairGroup_comm])
    have h1 : V ⊓ B₂ ≤ Q₁ := hp.symm.le_of_ne_bot₁ hx₀' hx₀Q hp.d₁.le hX' hp.d₁.ne_bot
    have h2 : V ⊓ B₂ ≤ V ⊓ B₁ :=
      hp.symm.le_of_ne_bot₁ hx₀' hx₀Q inf_le_left hW' hp.d₁.inf_ne_bot
    apply hp.d₂.inf_ne_bot
    rw [eq_bot_iff, ← hp.d₁.inf_eq_bot]
    exact le_inf h1 h2
  refine ⟨hp.eq_of_normalizes₂ hX₂, hp.symm.eq_of_normalizes₂ fun x hx =>
    hX x (by rwa [pairGroup_comm]), hX₂⟩

theorem normalizes_of_le (hQ : Q₂ ≤ V ⊓ B₁) : ∀ x ∈ pairGroup V B₁ B₂, conjSub x Q₁ = Q₁ := by
  by_contra hne
  push Not at hne
  obtain ⟨x₀, hx₀, hx₀Q⟩ := hne
  have h1 : V ⊓ B₁ ≤ V ⊓ B₂ :=
    hp.le_of_ne_bot₁ hx₀ hx₀Q inf_le_left hp.normalizes₂ hp.d₂.inf_ne_bot
  apply hp.d₂.ne_bot
  rw [eq_bot_iff, ← hp.d₂.inf_eq_bot]
  exact le_inf le_rfl (hQ.trans h1)

end PairData

end AS76b.Lemma36

end CFSG.ComponentClassification
