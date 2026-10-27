module

public import Mathlib.GroupTheory.Frattini
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core

public section

namespace CFSG.GH74

open Subgroup
open scoped commutatorElement

theorem exists_finset_closure_sup_eq {G : Type*} [Group G] [Finite G] {H A : Subgroup G}
    (hHA : H ≤ A) {k : ℕ} (hk : Nat.card A ≤ 2 ^ k * Nat.card H) :
    ∃ R : Finset G, (R : Set G) ⊆ A ∧ R.card ≤ k ∧ closure (R : Set G) ⊔ H = A := by
  classical
  induction k generalizing H with
  | zero =>
    refine ⟨∅, by simp, by simp, ?_⟩
    rw [Finset.coe_empty, closure_empty, bot_sup_eq]
    exact eq_of_le_of_card_ge hHA (by simpa using hk)
  | succ k ih =>
    by_cases hH : H = A
    · exact ⟨∅, by simp, by simp, by rw [Finset.coe_empty, closure_empty, bot_sup_eq, hH]⟩
    obtain ⟨g, hgA, hgH⟩ : ∃ g ∈ A, g ∉ H := by
      by_contra hcon
      push Not at hcon
      exact hH (le_antisymm hHA hcon)
    have hH'A : H ⊔ closure {g} ≤ A :=
      sup_le hHA ((closure_le _).2 (Set.singleton_subset_iff.2 hgA))
    have hlt : H < H ⊔ closure {g} :=
      lt_of_le_of_ne le_sup_left fun h => hgH (h ▸ mem_sup_right (subset_closure rfl))
    have h2 : 2 * Nat.card H ≤ Nat.card ↥(H ⊔ closure {g}) := by
      obtain ⟨c, hc⟩ := card_dvd_of_le hlt.le
      have hlt' := card_lt_of_lt hlt
      have hpos : 0 < Nat.card ↥(H ⊔ closure {g}) := Nat.card_pos
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [hc, mul_zero] at hpos
        exact lt_irrefl 0 hpos
      have hc1 : c ≠ 1 := by
        rintro rfl
        rw [hc, mul_one] at hlt'
        exact lt_irrefl _ hlt'
      have hc2 : 2 ≤ c := by omega
      calc 2 * Nat.card H ≤ c * Nat.card H := Nat.mul_le_mul_right _ hc2
        _ = Nat.card ↥(H ⊔ closure {g}) := by rw [hc, mul_comm]
    obtain ⟨R, hRA, hRk, hR⟩ := ih hH'A (by
      calc Nat.card A ≤ 2 ^ (k + 1) * Nat.card H := hk
        _ = 2 ^ k * (2 * Nat.card H) := by ring
        _ ≤ 2 ^ k * Nat.card ↥(H ⊔ closure {g}) := Nat.mul_le_mul_left _ h2)
    refine ⟨insert g R, ?_, (Finset.card_insert_le _ _).trans (by omega), ?_⟩
    · rw [Finset.coe_insert]
      exact Set.insert_subset hgA hRA
    · rw [Finset.coe_insert, Set.insert_eq, closure_union, ← hR]
      rw [sup_assoc, sup_comm (closure {g}) _, sup_assoc]

theorem exists_finset_closure_eq_top_of_coinvariant {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (A : Subgroup P) [A.Normal] (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (t : P) {m k : ℕ} (hs : ∃ s : Finset P, s.card ≤ m ∧ closure (s : Set P) ⊔ A = ⊤)
    (hC : Nat.card ↥(A ⊓ centralizer {t}) ≤ 2 ^ k) :
    ∃ s : Finset P, s.card ≤ m + k ∧ closure (s : Set P) = ⊤ := by
  classical
  haveI : Fact (IsPGroup 2 P) := ⟨hP⟩
  obtain ⟨s, hsm, hsA⟩ := hs
  have hconj : ∀ a ∈ A, t * a * t⁻¹ ∈ A := fun a ha => ‹A.Normal›.conj_mem a ha t
  let φ : A →* A :=
    { toFun := fun a => ⟨(a : P)⁻¹ * (t * a * t⁻¹), mul_mem (inv_mem a.2) (hconj a a.2)⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        change ((a : P) * b)⁻¹ * (t * (a * b) * t⁻¹) =
          ((a : P)⁻¹ * (t * a * t⁻¹)) * ((b : P)⁻¹ * (t * b * t⁻¹))
        have hc : (t * a * t⁻¹) * (b : P)⁻¹ = (b : P)⁻¹ * (t * a * t⁻¹) :=
          hA _ (hconj a a.2) _ (inv_mem b.2)
        calc ((a : P) * b)⁻¹ * (t * (a * b) * t⁻¹)
            = (b : P)⁻¹ * (a : P)⁻¹ * ((t * a * t⁻¹) * (t * b * t⁻¹)) := by group
          _ = (a : P)⁻¹ * (b : P)⁻¹ * ((t * a * t⁻¹) * (t * b * t⁻¹)) := by
              rw [hA _ (inv_mem b.2) _ (inv_mem a.2)]
          _ = (a : P)⁻¹ * ((b : P)⁻¹ * (t * a * t⁻¹)) * (t * b * t⁻¹) := by group
          _ = (a : P)⁻¹ * ((t * a * t⁻¹) * (b : P)⁻¹) * (t * b * t⁻¹) := by rw [hc]
          _ = ((a : P)⁻¹ * (t * a * t⁻¹)) * ((b : P)⁻¹ * (t * b * t⁻¹)) := by group }
  have hφ : ∀ a : A, ((φ a : A) : P) = (a : P)⁻¹ * (t * a * t⁻¹) := fun _ => rfl
  have hker : φ.ker.map A.subtype = A ⊓ centralizer {t} := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      have h1 : (a : P)⁻¹ * (t * a * t⁻¹) = 1 := by
        rw [← hφ, MonoidHom.mem_ker.1 ha, OneMemClass.coe_one]
      have h2 : (a : P) = t * a * t⁻¹ := inv_mul_eq_one.1 h1
      refine mem_inf.2 ⟨a.2, mem_centralizer_singleton_iff.2 ?_⟩
      calc (a : P) * t = (t * a * t⁻¹) * t := by rw [← h2]
        _ = t * a := by group
    · rintro hx
      obtain ⟨hxA, hxc⟩ := mem_inf.1 hx
      have hxt : x * t = t * x := mem_centralizer_singleton_iff.1 hxc
      refine ⟨⟨x, hxA⟩, MonoidHom.mem_ker.2 (Subtype.ext ?_), rfl⟩
      change x⁻¹ * (t * x * t⁻¹) = 1
      rw [← hxt, mul_inv_cancel_right, inv_mul_cancel]
  have hkercard : Nat.card φ.ker = Nat.card ↥(A ⊓ centralizer {t}) := by
    rw [← hker, card_map_of_injective A.subtype_injective]
  set I : Subgroup P := φ.range.map A.subtype with hIdef
  have hIA : I ≤ A := map_subtype_le _
  have hAI : Nat.card A ≤ 2 ^ k * Nat.card I := by
    rw [hIdef, card_map_of_injective A.subtype_injective, ← card_ker_mul_card_range φ, hkercard]
    exact Nat.mul_le_mul_right _ hC
  obtain ⟨R, -, hRk, hR⟩ := exists_finset_closure_sup_eq hIA hAI
  have hIΦ : I ≤ frattini P := by
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    apply CFSG.commutator_le_frattini_of_isPGroup (p := 2)
    have e : A.subtype (φ a) = ⁅(a : P)⁻¹, t⁆ := by
      rw [commutatorElement_def, inv_inv]
      change (a : P)⁻¹ * (t * a * t⁻¹) = _
      group
    rw [e]
    exact commutator_mem_commutator (mem_top _) (mem_top _)
  refine ⟨s ∪ R, (Finset.card_union_le _ _).trans (by omega), ?_⟩
  apply CFSG.lemma_1_7_a (p := 2)
  rw [eq_top_iff, ← hsA]
  have hcl : closure (s : Set P) ⊔ closure (R : Set P) ≤ closure ((s ∪ R : Finset P) : Set P) := by
    rw [Finset.coe_union, closure_union]
  refine sup_le ((le_sup_left.trans hcl).trans le_sup_left) ?_
  rw [← hR]
  exact sup_le ((le_sup_right.trans hcl).trans le_sup_left) (hIΦ.trans le_sup_right)

theorem exists_finset_closure_eq_of_coinvariant {X P : Type*} [Group X] [Finite X] [Group P]
    (φ : X →* P) {Q : Subgroup X} (hQ : IsPGroup 2 Q)
    (hA : ∀ a ∈ Q ⊓ φ.ker, ∀ b ∈ Q ⊓ φ.ker, a * b = b * a) {t : X} (ht : t ∈ Q) {m k : ℕ}
    (hm : ∃ s : Finset P, s.card ≤ m ∧ Subgroup.closure (s : Set P) = Q.map φ)
    (hk : Nat.card ↥(Q ⊓ φ.ker ⊓ Subgroup.centralizer ({t} : Set X)) ≤ 2 ^ k) :
    ∃ s : Finset X, s.card ≤ m + k ∧ Subgroup.closure (s : Set X) = Q := by
  classical
  obtain ⟨s, hsm, hsQ⟩ := hm
  set ψ : Q →* P := φ.comp Q.subtype with hψ
  set A : Subgroup Q := ψ.ker with hAdef
  have hAX : ∀ a : Q, a ∈ A → (a : X) ∈ Q ⊓ φ.ker := fun a ha => mem_inf.2 ⟨a.2, ha⟩
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    Subtype.ext (hA _ (hAX a ha) _ (hAX b hb))
  let lift : P → Q := fun p =>
    if h : p ∈ Q.map φ then ⟨Classical.choose (mem_map.1 h), (Classical.choose_spec
      (mem_map.1 h)).1⟩ else 1
  have hlift : ∀ p ∈ Q.map φ, ψ (lift p) = p := fun p hp => by
    simp only [hψ, lift, dif_pos hp, MonoidHom.comp_apply, coe_subtype]
    exact (Classical.choose_spec (mem_map.1 hp)).2
  have hsmap : ∀ p ∈ s, p ∈ Q.map φ := fun p hp => hsQ ▸ subset_closure hp
  have himage : ψ '' ((s.image lift : Finset Q) : Set Q) = s := by
    rw [Finset.coe_image, Set.image_image]
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      change ψ (lift q) ∈ (s : Set P)
      rw [hlift q (hsmap q hq)]
      exact hq
    · intro hp
      exact ⟨p, hp, hlift p (hsmap p hp)⟩
  have hgen : closure ((s.image lift : Finset Q) : Set Q) ⊔ A = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : ψ x ∈ (closure ((s.image lift : Finset Q) : Set Q)).map ψ := by
      rw [MonoidHom.map_closure, himage, hsQ]
      exact mem_map_of_mem φ x.2
    obtain ⟨y, hy, hyx⟩ := mem_map.1 hx
    have hyA : y⁻¹ * x ∈ A := by
      rw [hAdef, MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
    simpa only [mul_inv_cancel_left] using mul_mem_sup hy hyA
  have hC : Nat.card ↥(A ⊓ centralizer {(⟨t, ht⟩ : Q)}) ≤ 2 ^ k := by
    refine le_trans ?_ hk
    rw [← card_map_of_injective Q.subtype_injective]
    refine card_le_of_le ?_
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨haA, hat⟩ := mem_inf.1 ha
    refine mem_inf.2 ⟨hAX a haA, mem_centralizer_singleton_iff.2 ?_⟩
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.1 hat)
  obtain ⟨s', hs'k, hs'⟩ := exists_finset_closure_eq_top_of_coinvariant hQ A hAab ⟨t, ht⟩
    ⟨s.image lift, Finset.card_image_le.trans hsm, hgen⟩ hC
  refine ⟨s'.image Q.subtype, Finset.card_image_le.trans hs'k, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hs', ← MonoidHom.range_eq_map, range_subtype]

end CFSG.GH74
