module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Comp

public section

namespace CFSG.ComponentClassification.GSThmB.CorC

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {X : Type} [Group X]

@[expose] def wCore (E : Subgroup X) : Subgroup X :=
  ⨅ (e : X) (_ : e ∈ E) (_ : e ≠ 1),
    (pPrimeCore 2 (centralizer ({e} : Set X))).map (centralizer ({e} : Set X)).subtype

theorem wCore_le {E : Subgroup X} {e : X} (heE : e ∈ E) (he1 : e ≠ 1) :
    wCore E ≤ (pPrimeCore 2 (centralizer ({e} : Set X))).map (centralizer ({e} : Set X)).subtype :=
  (iInf_le _ e).trans ((iInf_le _ heE).trans (iInf_le _ he1))

structure Config (a : X) (J E : Subgroup X) : Prop where
  orderOf_eq : orderOf a = 2
  le_centralizer : J ≤ centralizer ({a} : Set X)
  isPComponent : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set X)))
  equiv : Nonempty (J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 7))
  le_H : E ≤ centralizer ({a} : Set X) ⊓ normalizer (J : Set X)
  four : Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
  commutator_eq : ⁅J, centralizer ({a} : Set X) ⊓ wCore E⁆ = J

@[expose] noncomputable def twoPart (a : X) (J : Subgroup X) : ℕ :=
  2 ^ (Nat.card ↥(centralizer ({a} : Set X) ⊓ normalizer (J : Set X))).factorization 2

namespace Config

variable {a : X} {J E : Subgroup X}

theorem card_eq (h : Config a J E) : Nat.card E = 4 := by
  obtain ⟨φ⟩ := h.four
  rw [Nat.card_congr φ.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card]
  rfl

theorem mul_self_eq (h : Config a J E) {e : X} (he : e ∈ E) : e * e = 1 := by
  obtain ⟨φ⟩ := h.four
  have hm : ∀ y : Multiplicative (ZMod 2) × Multiplicative (ZMod 2), y * y = 1 := by decide
  have : (⟨e, he⟩ : E) * ⟨e, he⟩ = 1 := φ.injective (by rw [map_mul, map_one, hm])
  exact congrArg Subtype.val this

theorem exists_involution (h : Config a J E) : ∃ e ∈ E, e ≠ 1 ∧ orderOf e = 2 := by
  obtain ⟨e, heE, he1⟩ : ∃ e ∈ E, e ≠ 1 := by
    by_contra hne
    push Not at hne
    have hbot : E = ⊥ := eq_bot_iff.mpr fun g hg => (mem_bot).mpr (hne g hg)
    have h4 := h.card_eq
    rw [hbot, card_bot] at h4
    omega
  exact ⟨e, heE, he1, orderOf_eq_prime (by rw [pow_two]; exact h.mul_self_eq heE) he1⟩

theorem le_normalizer (h : Config a J E) :
    centralizer ({a} : Set X) ⊓ wCore E ≤ normalizer (J : Set X) := by
  have h1 := le_normalizer_commutator (centralizer ({a} : Set X) ⊓ wCore E) J
  rwa [commutator_comm, h.commutator_eq] at h1

variable [Finite X]

theorem odd_card_wCore (h : Config a J E) : Odd (Nat.card (wCore E)) := by
  obtain ⟨e, heE, he1, -⟩ := h.exists_involution
  have hodd : Odd (Nat.card ((pPrimeCore 2 (centralizer ({e} : Set X))).map
      (centralizer ({e} : Set X)).subtype)) := by
    rw [card_map_of_injective (centralizer ({e} : Set X)).subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  exact hodd.of_dvd_nat (card_dvd_of_le (wCore_le heE he1))

theorem not_le_oddIn (h : Config a J E) : ¬ J ≤ (pPrimeCore 2 J).map J.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J _ h.le_centralizer).mp
      h.isPComponent).2.2
  intro hle
  obtain ⟨-, -, u, v, huv⟩ := hJq
  apply huv
  have h1 : ∀ q : J ⧸ pPrimeCore 2 J, q = 1 := by
    intro q
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
    rw [QuotientGroup.eq_one_iff]
    exact (mem_map_iff_mem J.subtype_injective).mp (hle j.2)
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
  rw [h1 u, h1 v]

theorem gsUnbalancingTriple (hSol : GrSLit.SolomonCommutingCoreInput) (h : Config a J E) {e : X}
    (heE : e ∈ E) (he1 : e ≠ 1) : GSUnbalancingTriple a e J := by
  have he : orderOf e = 2 := orderOf_eq_prime (by rw [pow_two]; exact h.mul_self_eq heE) he1
  have hea : e * a = a * e := mem_centralizer_singleton_iff.mp (mem_inf.mp (h.le_H heE)).1
  refine GrSLit.GrS5.gsUnbalancingTriple_of_not_le hSol he h.orderOf_eq hea h.le_centralizer
    h.isPComponent (Y := centralizer ({a} : Set X) ⊓ wCore E) (fun y hy => ?_) ?_
  · exact mem_inf.mpr ⟨wCore_le heE he1 (mem_inf.mp hy).2, (mem_inf.mp hy).1⟩
  · intro hle
    rw [h.commutator_eq] at hle
    exact h.not_le_oddIn hle

end Config

variable [Finite X]

end CFSG.ComponentClassification.GSThmB.CorC
