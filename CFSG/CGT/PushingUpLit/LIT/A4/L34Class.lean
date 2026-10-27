module

public import CFSG.CGT.PushingUpLit.LIT.A4.L34Cfg

public section

namespace CFSG.CGT.PushingUpLit.A4.L34

open CFSG CFSG.Assembly CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.SolK
  CFSG.RankThree.PartOne.SolD3 CFSG.CGT.PushingUpLit.A4

variable {G : Type} [Group G]

@[expose] def conjOrbit (N : Subgroup G) (v : G) : Set G := {x | ∃ n ∈ N, x = n * v * n⁻¹}

theorem card_eq_card_conjOrbit_mul [Finite G] (N : Subgroup G) (v : G) :
    Nat.card N = Nat.card ↥(conjOrbit N v) * Nat.card ↥(N ⊓ Subgroup.centralizer {v}) := by
  let K : Subgroup N := (N ⊓ Subgroup.centralizer {v}).subgroupOf N
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup K
  have h2 : Nat.card K = Nat.card ↥(N ⊓ Subgroup.centralizer {v}) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  let f : (↥N ⧸ K) → G := Quotient.lift (fun n : ↥N => (n : G) * v * (n : G)⁻¹) (by
    intro a b hab
    have hab' : a⁻¹ * b ∈ K := QuotientGroup.leftRel_apply.1 hab
    have hc : ((a⁻¹ * b : ↥N) : G) ∈ N ⊓ Subgroup.centralizer {v} := Subgroup.mem_subgroupOf.1 hab'
    have hc2 := (Subgroup.mem_inf.1 hc).2
    have hc3 : ((a⁻¹ * b : ↥N) : G) * v = v * ((a⁻¹ * b : ↥N) : G) :=
      Subgroup.mem_centralizer_singleton_iff.1 hc2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hc3
    have hc4 : ((a : G)⁻¹ * b) * v * ((a : G)⁻¹ * b)⁻¹ = v := mul_inv_eq_iff_eq_mul.2 hc3
    show (a : G) * v * (a : G)⁻¹ = (b : G) * v * (b : G)⁻¹
    calc (a : G) * v * (a : G)⁻¹
        = (a : G) * (((a : G)⁻¹ * b) * v * ((a : G)⁻¹ * b)⁻¹) * (a : G)⁻¹ := by rw [hc4]
      _ = (b : G) * v * (b : G)⁻¹ := by group)
  have hinj : Function.Injective f := by
    intro x y hxy
    induction x using Quotient.inductionOn with
    | h a =>
    induction y using Quotient.inductionOn with
    | h b =>
    refine Quotient.sound (QuotientGroup.leftRel_apply.2 ?_)
    have e : (a : G) * v * (a : G)⁻¹ = (b : G) * v * (b : G)⁻¹ := hxy
    refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨(a⁻¹ * b).2, ?_⟩)
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (a : G)⁻¹ * (b : G) * v = (a : G)⁻¹ * ((b : G) * v * (b : G)⁻¹) * (b : G) := by group
      _ = (a : G)⁻¹ * ((a : G) * v * (a : G)⁻¹) * (b : G) := by rw [e]
      _ = v * ((a : G)⁻¹ * (b : G)) := by group
  have hrange : Set.range f = conjOrbit N v := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      induction q using Quotient.inductionOn with
      | h a => exact ⟨a, a.2, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨Quotient.mk _ ⟨n, hn⟩, rfl⟩
  have h3 : Nat.card (↥N ⧸ K) = Nat.card ↥(conjOrbit N v) := by
    rw [← hrange]
    exact (Nat.card_congr (Equiv.ofInjective f hinj))
  rw [h1, h3, h2]

@[expose] def nineSet (t : Two G) : Set G :=
  {x | ∃ p ∈ t.V₁, p ≠ 1 ∧ ∃ q ∈ t.V₂, q ≠ 1 ∧ x = p * q}

namespace Two.Cfg

variable {t : Two G} (h : t.Cfg)
include h

theorem card_nineSet [Finite G] : Nat.card ↥(nineSet t) = 9 := by
  let f : Wn t.X₁ × Wn t.X₂ → ↥(nineSet t) := fun pq =>
    ⟨pq.1.1 * pq.2.1, pq.1.1, pq.1.2.1, pq.1.2.2, pq.2.1, pq.2.2.1, pq.2.2.2, rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨p, hp, hp1⟩, ⟨q, hq, hq1⟩⟩ ⟨⟨p', hp', hp1'⟩, ⟨q', hq', hq1'⟩⟩ e
      have e' : p * q = p' * q' := congrArg Subtype.val e
      obtain ⟨rfl, rfl⟩ := h.mul_inj hp hp' hq hq' e'
      rfl
    · rintro ⟨x, p, hp, hp1, q, hq, hq1, rfl⟩
      exact ⟨(⟨p, hp, hp1⟩, ⟨q, hq, hq1⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, card_Wn h.blk₁, card_Wn h.blk₂]

theorem conjOrbit_eq [Finite G] {w₁ w₂ : G} (hw₁ : w₁ ∈ t.V₁) (hw₁1 : w₁ ≠ 1) (hw₂ : w₂ ∈ t.V₂)
    (hw₂1 : w₂ ≠ 1) : conjOrbit t.M (w₁ * w₂) = nineSet t := by
  ext x
  constructor
  · rintro ⟨n, hn, rfl⟩
    have hsplit : n * (w₁ * w₂) * n⁻¹ = (n * w₁ * n⁻¹) * (n * w₂ * n⁻¹) := by group
    rw [hsplit]
    have n1 : n * w₁ * n⁻¹ ≠ 1 := fun e => hw₁1 (conj_eq_one_iff.1 e)
    have n2 : n * w₂ * n⁻¹ ≠ 1 := fun e => hw₂1 (conj_eq_one_iff.1 e)
    rcases h.perm n hn with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact ⟨_, conj_mem_pCoreOf e1 hw₁, n1, _, conj_mem_pCoreOf e2 hw₂, n2, rfl⟩
    · have m1 : n * w₁ * n⁻¹ ∈ t.V₂ := by
        have h1 : n * w₁ * n⁻¹ ∈ conjSub n t.V₁ := conj_mem_conjSub hw₁
        have e : conjSub n t.V₁ = t.V₂ := by
          show conjSub n (pCoreOf 2 t.X₁) = pCoreOf 2 t.X₂
          rw [← pCoreOf_conjSub, e1]
        rwa [e] at h1
      have m2 : n * w₂ * n⁻¹ ∈ t.V₁ := by
        have h1 : n * w₂ * n⁻¹ ∈ conjSub n t.V₂ := conj_mem_conjSub hw₂
        have e : conjSub n t.V₂ = t.V₁ := by
          show conjSub n (pCoreOf 2 t.X₂) = pCoreOf 2 t.X₁
          rw [← pCoreOf_conjSub, e2]
        rwa [e] at h1
      exact ⟨_, m2, n2, _, m1, n1, (h.comm_V m2 m1).symm⟩
  · rintro ⟨p, hp, hp1, q, hq, hq1, rfl⟩
    obtain ⟨y₁, hy₁, e₁⟩ := Blk3.exists_conj_of_ne_one h.blk₁ hw₁ hw₁1 hp hp1
    obtain ⟨y₂, hy₂, e₂⟩ := Blk3.exists_conj_of_ne_one h.blk₂ hw₂ hw₂1 hq hq1
    refine ⟨y₁ * y₂, t.M.mul_mem (h.le₁ hy₁) (h.le₂ hy₂), ?_⟩
    have c1 : y₂ * w₁ = w₁ * y₂ := (h.comm w₁ (t.V₁_le hw₁) y₂ hy₂).symm
    have hz : y₂ * w₂ * y₂⁻¹ ∈ t.X₂ :=
      t.X₂.mul_mem (t.X₂.mul_mem hy₂ (t.V₂_le hw₂)) (t.X₂.inv_mem hy₂)
    have c2 : y₁ * (y₂ * w₂ * y₂⁻¹) = (y₂ * w₂ * y₂⁻¹) * y₁ := h.comm y₁ hy₁ _ hz
    have e3 : y₁ * (y₂ * w₂ * y₂⁻¹) * y₁⁻¹ = y₂ * w₂ * y₂⁻¹ := by rw [c2]; group
    calc p * q = (y₁ * w₁ * y₁⁻¹) * (y₂ * w₂ * y₂⁻¹) := by rw [e₁, e₂]
      _ = (y₁ * w₁ * y₁⁻¹) * (y₁ * (y₂ * w₂ * y₂⁻¹) * y₁⁻¹) := by rw [e3]
      _ = y₁ * (w₁ * y₂) * w₂ * y₂⁻¹ * y₁⁻¹ := by group
      _ = y₁ * (y₂ * w₁) * w₂ * y₂⁻¹ * y₁⁻¹ := by rw [c1]
      _ = (y₁ * y₂) * (w₁ * w₂) * (y₁ * y₂)⁻¹ := by group

theorem class_nine [Finite G] {w₁ w₂ : G} (hw₁ : w₁ ∈ t.V₁) (hw₁1 : w₁ ≠ 1) (hw₂ : w₂ ∈ t.V₂)
    (hw₂1 : w₂ ≠ 1) :
    Nat.card t.M = 9 * Nat.card ↥(t.M ⊓ Subgroup.centralizer {w₁ * w₂}) := by
  rw [card_eq_card_conjOrbit_mul t.M (w₁ * w₂), h.conjOrbit_eq hw₁ hw₁1 hw₂ hw₂1, h.card_nineSet]

theorem relIndex_normalizer : (Subgroup.normalizer (t.X₁ : Set G)).relIndex t.M = 2 := by
  obtain ⟨k₀, hk₀, e₀⟩ := h.swap
  have hdvd : (Subgroup.normalizer (t.X₁ : Set G)).relIndex t.M ∣ 2 := by
    rw [Subgroup.relIndex_dvd_two_iff]
    refine ⟨k₀, hk₀, fun b hb => ?_⟩
    rcases h.perm b hb with ⟨e1, -⟩ | ⟨-, e2⟩
    · exact Or.inr (mem_normalizer_iff_conjSub.2 e1)
    · left
      refine mem_normalizer_iff_conjSub.2 ?_
      rw [← conjSub_conjSub, e₀, e2]
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
  · exfalso
    rw [Subgroup.relIndex_eq_one] at h1
    have := mem_normalizer_iff_conjSub.1 (h1 hk₀)
    exact h.X_ne (this.symm.trans e₀)
  · exact h2

end Two.Cfg

end CFSG.CGT.PushingUpLit.A4.L34
