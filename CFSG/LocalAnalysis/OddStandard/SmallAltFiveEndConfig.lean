module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.OddStandard

open Subgroup

structure FiveConfig {X : Type*} [Group X] (t : X) : Prop where
  orderOf_eq : orderOf t = 2
  exists_comp : ∃ L : Subgroup X, L ≤ centralizer ({t} : Set X) ∧
    (∀ c ∈ centralizer ({t} : Set X), ∀ l ∈ L, c * l * c⁻¹ ∈ L) ∧
    Nonempty (L ≃* alternatingGroup (Fin 5))
  card_eq : Nat.card (centralizer ({t} : Set X)) = 120 ∨
    Nat.card (centralizer ({t} : Set X)) = 240

namespace FiveConfig

variable {X : Type*} [Group X] {t : X}

theorem map_centralizer_singleton {Y : Type*} [Group Y] (e : X ≃* Y) (t : X) :
    (centralizer ({t} : Set X)).map e.toMonoidHom = centralizer ({e t} : Set Y) := by
  ext y
  rw [Subgroup.mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro hc
    have := congrArg e hc
    simpa using this
  · intro hc
    have := congrArg e.symm hc
    simpa using this

theorem of_mulEquiv {Y : Type*} [Group Y] (e : X ≃* Y) (h : FiveConfig t) : FiveConfig (e t) := by
  obtain ⟨L, hLC, hLn, ⟨f⟩⟩ := h.exists_comp
  refine ⟨(MulEquiv.orderOf_eq e t).trans h.orderOf_eq, ⟨L.map e.toMonoidHom, ?_, ?_, ?_⟩, ?_⟩
  · rw [← map_centralizer_singleton e t]
    exact Subgroup.map_mono hLC
  · intro c hc l hl
    obtain ⟨l₀, hl₀, rfl⟩ := hl
    have hc' : e.symm c ∈ centralizer ({t} : Set X) := by
      have h1 : c ∈ (centralizer ({t} : Set X)).map e.toMonoidHom := by
        rw [map_centralizer_singleton]
        exact hc
      obtain ⟨c₀, hc₀, rfl⟩ := h1
      simpa using hc₀
    refine ⟨e.symm c * l₀ * (e.symm c)⁻¹, hLn _ hc' _ hl₀, ?_⟩
    simp
  · exact ⟨((L.equivMapOfInjective e.toMonoidHom e.injective).symm.trans f)⟩
  · have h1 := Subgroup.card_map_of_injective (K := centralizer ({t} : Set X))
      (show Function.Injective e.toMonoidHom from e.injective)
    rw [map_centralizer_singleton] at h1
    rw [h1]
    exact h.card_eq

theorem isPerfect_alternatingGroup_five : Group.IsPerfect (alternatingGroup (Fin 5)) :=
  ⟨commutator_alternatingGroup_eq_top (α := Fin 5) (by simp)⟩

theorem card_alternatingGroup_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.card_eq_fintype_card, Nat.factorial]

theorem false_of_isSolvable (h : FiveConfig t)
    (hs : Group.IsSolvable (centralizer ({t} : Set X))) : False := by
  obtain ⟨L, hLC, -, ⟨e⟩⟩ := h.exists_comp
  have h1 : Group.IsSolvable L :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLC)
  have h2 : Group.IsSolvable (alternatingGroup (Fin 5)) :=
    Group.isSolvable_of_isSolvable_injective
      (show Function.Injective e.symm.toMonoidHom from e.symm.injective)
  have : Group.IsPerfect (alternatingGroup (Fin 5)) := isPerfect_alternatingGroup_five
  have : Nontrivial (alternatingGroup (Fin 5)) := inferInstance
  exact Group.IsPerfect.not_isSolvable (G := alternatingGroup (Fin 5)) h2

theorem false_of_twoConstrained (h : FiveConfig t) {Q : Subgroup X}
    (hQC : Q ≤ centralizer ({t} : Set X)) (hQ : IsPGroup 2 Q)
    (hQn : centralizer ({t} : Set X) ≤ normalizer (Q : Set X))
    (hcon : centralizer ({t} : Set X) ⊓ centralizer (Q : Set X) ≤ Q) : False := by
  obtain ⟨L, hLC, hLn, ⟨e⟩⟩ := h.exists_comp
  have hQc : ∀ c ∈ centralizer ({t} : Set X), ∀ q ∈ Q, c * q * c⁻¹ ∈ Q :=
    fun c hc q hq => (mem_normalizer_iff.1 (hQn hc) q).1 hq
  have : IsSimpleGroup L := e.isSimpleGroup
  have hnorm : ((L ⊓ Q).subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : X) ∈ L ⊓ Q := hn
    show ((g * n * g⁻¹ : L) : X) ∈ L ⊓ Q
    exact ⟨(g * n * g⁻¹ : L).2, hQc g (hLC g.2) n hn'.2⟩
  have hLQ : L ≤ Q := by
    have := hnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((L ⊓ Q).subgroupOf L) with hbot | htop
    · intro l hl
      have hcomm : ∀ q ∈ Q, l * q = q * l := by
        intro q hq
        have h1 : l * q * l⁻¹ * q⁻¹ ∈ L ⊓ Q := by
          refine ⟨?_, ?_⟩
          · have h2 : q * l⁻¹ * q⁻¹ ∈ L := hLn q (hQC hq) l⁻¹ (L.inv_mem hl)
            have := L.mul_mem hl h2
            simpa [mul_assoc] using this
          · have h2 : l * q * l⁻¹ ∈ Q := hQc l (hLC hl) q hq
            exact Q.mul_mem h2 (Q.inv_mem hq)
        have h3 : (⟨l * q * l⁻¹ * q⁻¹, h1.1⟩ : L) ∈ (L ⊓ Q).subgroupOf L := h1
        rw [hbot, Subgroup.mem_bot] at h3
        have h4 : l * q * l⁻¹ * q⁻¹ = 1 := congrArg Subtype.val h3
        calc l * q = (l * q * l⁻¹ * q⁻¹) * (q * l) := by group
          _ = q * l := by rw [h4, one_mul]
      exact hcon ⟨hLC hl, mem_centralizer_iff.2 fun q hq => (hcomm q hq).symm⟩
    · intro l hl
      have h3 : (⟨l, hl⟩ : L) ∈ (L ⊓ Q).subgroupOf L := by rw [htop]; exact mem_top _
      exact h3.2
  have hL2 : IsPGroup 2 L := hQ.to_le hLQ
  have : Finite L := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨n, hn⟩ := hL2.exists_card_eq
  have h60 : Nat.card L = 60 := by rw [Nat.card_congr e.toEquiv, card_alternatingGroup_five]
  have h3 : 3 ∣ 2 ^ n := by rw [← hn, h60]; norm_num
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

theorem five_dvd_card (h : FiveConfig t) : 5 ∣ Nat.card (centralizer ({t} : Set X)) := by
  rcases h.card_eq with h1 | h1 <;> rw [h1] <;> norm_num

theorem false_of_card_ne (h : FiveConfig t) (h1 : Nat.card (centralizer ({t} : Set X)) ≠ 120)
    (h2 : Nat.card (centralizer ({t} : Set X)) ≠ 240) : False := by
  rcases h.card_eq with h3 | h3
  · exact h1 h3
  · exact h2 h3

end FiveConfig

end CFSG.OddStandard
