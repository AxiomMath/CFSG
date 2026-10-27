module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbDefs

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

section Z4Z4E4

variable {G : Type} [Group G]

theorem card_sq_one_Z4Z4Z2Z2 :
    Nat.card {a : Outside.Z4Z4Z2Z2 // a ^ 2 = 1} = 16 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem IsZ4Z4E4.comm {Q : Subgroup G} (h : IsZ4Z4E4 Q) {a b : G} (ha : a ∈ Q) (hb : b ∈ Q) :
    a * b = b * a := by
  obtain ⟨e⟩ := h
  have h' : e ⟨a, ha⟩ * e ⟨b, hb⟩ = e ⟨b, hb⟩ * e ⟨a, ha⟩ := mul_comm _ _
  have h2 : (⟨a, ha⟩ : Q) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ :=
    e.injective (by rw [map_mul, map_mul, h'])
  exact congrArg Subtype.val h2

theorem IsZ4Z4E4.card {Q : Subgroup G} (h : IsZ4Z4E4 Q) : Nat.card Q = 64 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
  decide +kernel

theorem IsZ4Z4E4.pow_four {Q : Subgroup G} (h : IsZ4Z4E4 Q) {a : G} (ha : a ∈ Q) : a ^ 4 = 1 := by
  obtain ⟨e⟩ := h
  have hx : ∀ x : Outside.Z4Z4Z2Z2, x ^ 4 = 1 := by decide +kernel
  have hxa : e ⟨a, ha⟩ ^ 4 = 1 := hx _
  have h1 : (⟨a, ha⟩ : Q) ^ 4 = 1 :=
    e.injective (by rw [map_pow, hxa, map_one])
  simpa using congrArg Subtype.val h1

theorem IsZ4Z4E4.exists_sq_ne_one {Q : Subgroup G} (h : IsZ4Z4E4 Q) : ∃ a ∈ Q, a ^ 2 ≠ 1 := by
  obtain ⟨e⟩ := h
  let x : Outside.Z4Z4Z2Z2 := Multiplicative.ofAdd ((1 : ZMod 4), 0, 0, 0)
  have hx : x ^ 2 ≠ 1 := by decide +kernel
  refine ⟨((e.symm x : Q) : G), (e.symm x : Q).2, fun hsq => hx ?_⟩
  have hQ : (e.symm x : Q) ^ 2 = 1 := Subtype.ext (by simpa using hsq)
  have h2 := congrArg e hQ
  simpa using h2

private theorem z4z4_sq_one_iff {Q : Subgroup G} (e : Q ≃* Outside.Z4Z4Z2Z2) (q : Q) :
    ((q : G) ^ 2 = 1) ↔ (e q) ^ 2 = 1 := by
  constructor
  · intro h
    have hq : q ^ 2 = 1 := Subtype.ext (by simpa using h)
    rw [← map_pow, hq, map_one]
  · intro h
    have hq : q ^ 2 = 1 := e.injective (by rw [map_pow, h, map_one])
    simpa using congrArg Subtype.val hq

theorem IsZ4Z4E4.card_sq_one {Q : Subgroup G} (h : IsZ4Z4E4 Q) :
    Nat.card {a : G // a ∈ Q ∧ a ^ 2 = 1} = 16 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr ?_]
  · exact card_sq_one_Z4Z4Z2Z2
  · exact (Equiv.subtypeSubtypeEquivSubtypeInter (fun a : G => a ∈ Q)
        (fun a => a ^ 2 = 1)).symm.trans
      (e.toEquiv.subtypeEquiv (z4z4_sq_one_iff e))

end Z4Z4E4

section Yq

variable {G : Type} [Group G] {t tau x₁ x₂ rho : G}

theorem mem_closure_sq_one_iff {Q : Subgroup G} (hcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) (x : G) :
    x ∈ closure {g : G | g ∈ Q ∧ g ^ 2 = 1} ↔ x ∈ Q ∧ x ^ 2 = 1 := by
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem g hg => exact hg
    | one => exact ⟨one_mem _, by simp⟩
    | mul y z hy hz ihy ihz =>
        exact ⟨mul_mem ihy.1 ihz.1,
          by rw [Commute.mul_pow (hcomm y ihy.1 z ihz.1) 2, ihy.2, ihz.2, one_mul]⟩
    | inv y hy ihy => exact ⟨inv_mem ihy.1, by rw [inv_pow, ihy.2, inv_one]⟩
  · rintro ⟨hQ, h2⟩
    exact subset_closure ⟨hQ, h2⟩

theorem ctxYq_le_ctxQ : ctxYq t tau x₁ x₂ rho ≤ ctxQ t tau x₁ x₂ rho := by
  rw [ctxYq, Subgroup.closure_le]
  rintro g ⟨hg, _⟩
  exact hg

theorem mem_ctxYq_iff (hQ : IsZ4Z4E4 (ctxQ t tau x₁ x₂ rho)) (a : G) :
    a ∈ ctxYq t tau x₁ x₂ rho ↔ a ∈ ctxQ t tau x₁ x₂ rho ∧ a ^ 2 = 1 := by
  unfold ctxYq
  exact mem_closure_sq_one_iff (fun a ha b hb => IsZ4Z4E4.comm hQ ha hb) a

theorem card_ctxYq (hQ : IsZ4Z4E4 (ctxQ t tau x₁ x₂ rho)) :
    Nat.card (ctxYq t tau x₁ x₂ rho) = 16 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun a => mem_ctxYq_iff hQ a))]
  exact IsZ4Z4E4.card_sq_one hQ

end Yq

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
