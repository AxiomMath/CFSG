module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_14Diag
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpComp
public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoI1Basic
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_14Pair

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.ResD

open Subgroup CFSG
open CFSG.GH74.GLS.Stage2.Final.Thm6.L20 (PairShape)
open scoped commutatorElement

section Basic

variable {G : Type*} [Group G]

theorem mem_zpowers_mul_self_of_odd {x : G} (hx : Odd (orderOf x)) : x ∈ zpowers (x * x) := by
  obtain ⟨m, hm⟩ := hx
  refine Subgroup.mem_zpowers_iff.mpr ⟨((m + 1 : ℕ) : ℤ), ?_⟩
  rw [zpow_natCast, ← sq, ← pow_mul]
  calc x ^ (2 * (m + 1)) = x ^ (2 * m + 1) * x := by
        rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, pow_succ]
    _ = x := by rw [← hm, pow_orderOf_eq_one, one_mul]

variable {L₁ L₂ : Subgroup G}

@[expose] def projOne (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (N : Subgroup G) : Subgroup G where
  carrier := {a | a ∈ L₁ ∧ ∃ b ∈ L₂, a * b ∈ N}
  one_mem' := ⟨L₁.one_mem, 1, L₂.one_mem, by rw [mul_one]; exact N.one_mem⟩
  mul_mem' := by
    rintro a a' ⟨ha, b, hb, hab⟩ ⟨ha', b', hb', hab'⟩
    refine ⟨L₁.mul_mem ha ha', b * b', L₂.mul_mem hb hb', ?_⟩
    have e : b * a' = a' * b := (hc a' ha' b hb).symm
    have : a * a' * (b * b') = (a * b) * (a' * b') := by
      calc a * a' * (b * b') = a * (a' * b) * b' := by group
        _ = a * (b * a') * b' := by rw [e]
        _ = (a * b) * (a' * b') := by group
    rw [this]
    exact N.mul_mem hab hab'
  inv_mem' := by
    rintro a ⟨ha, b, hb, hab⟩
    refine ⟨L₁.inv_mem ha, b⁻¹, L₂.inv_mem hb, ?_⟩
    have e : a * b = b * a := hc a ha b hb
    have : a⁻¹ * b⁻¹ = (a * b)⁻¹ := by rw [e, mul_inv_rev]
    rw [this]
    exact N.inv_mem hab

theorem mem_projOne {hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a} {N : Subgroup G} {a : G} :
    a ∈ projOne hc N ↔ a ∈ L₁ ∧ ∃ b ∈ L₂, a * b ∈ N :=
  Iff.rfl

end Basic

variable {Q : Type} [Group Q] [Finite Q] {L₁ L₂ : Subgroup Q} {s : Q}

theorem projOne_normal (h : PairShape L₁ L₂) (hs₁ : ∀ a ∈ L₁, s * a * s⁻¹ ∈ L₂)
    {N : Subgroup Q}
    (hΔN : ∀ a ∈ L₁, ∀ n ∈ N, (a * (s * a * s⁻¹)) * n * (a * (s * a * s⁻¹))⁻¹ ∈ N) :
    ((projOne h.comm N).subgroupOf L₁).Normal := by
  refine ⟨fun x hx l => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨-, b, hb, hxb⟩ := hx
  have hl : (l : Q) ∈ L₁ := l.2
  have hx1 : (x : Q) ∈ L₁ := x.2
  set a' : Q := s * (l : Q) * s⁻¹ with ha'
  have ha'2 : a' ∈ L₂ := hs₁ _ hl
  refine ⟨(l * x * l⁻¹).2, a' * b * a'⁻¹, L₂.mul_mem (L₂.mul_mem ha'2 hb) (L₂.inv_mem ha'2), ?_⟩
  have key := hΔN _ hl _ hxb
  have c1 : a' * (x : Q) = (x : Q) * a' := (h.comm _ hx1 _ ha'2).symm
  have hb' : a' * b * a'⁻¹ ∈ L₂ := L₂.mul_mem (L₂.mul_mem ha'2 hb) (L₂.inv_mem ha'2)
  have c2 : (l : Q)⁻¹ * (a' * b * a'⁻¹) = (a' * b * a'⁻¹) * (l : Q)⁻¹ :=
    h.comm _ (L₁.inv_mem hl) _ hb'
  have e : ((l : Q) * a') * ((x : Q) * b) * ((l : Q) * a')⁻¹ =
      ((l * x * l⁻¹ : ↥L₁) : Q) * (a' * b * a'⁻¹) := by
    calc ((l : Q) * a') * ((x : Q) * b) * ((l : Q) * a')⁻¹
        = (l : Q) * (a' * (x : Q)) * b * a'⁻¹ * (l : Q)⁻¹ := by group
      _ = (l : Q) * ((x : Q) * a') * b * a'⁻¹ * (l : Q)⁻¹ := by rw [c1]
      _ = (l : Q) * (x : Q) * ((a' * b * a'⁻¹) * (l : Q)⁻¹) := by group
      _ = (l : Q) * (x : Q) * ((l : Q)⁻¹ * (a' * b * a'⁻¹)) := by rw [c2]
      _ = ((l * x * l⁻¹ : ↥L₁) : Q) * (a' * b * a'⁻¹) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
  rw [← e]
  exact key

theorem not_le_right (h : PairShape L₁ L₂) : ¬ L₁ ≤ L₂ := by
  intro hle
  have hq := h.c₁.1
  have hperf : ⁅L₁, L₁⁆ = L₁ := Subgroup.isPerfect_iff.mp hq.1
  have hab : ⁅L₁, L₁⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact h.comm b hb a (hle ha)
  have hbot : L₁ = ⊥ := hperf.symm.trans hab
  have : Nontrivial ↥L₁ := CFSG.LocalCores.isQuasisimple_nontrivial hq
  obtain ⟨x, hx⟩ := exists_ne (1 : ↥L₁)
  apply hx
  have hx' : (x : Q) ∈ (⊥ : Subgroup Q) := hbot ▸ x.2
  exact Subtype.ext (Subgroup.mem_bot.mp hx')

theorem le_right_of_odd (h : PairShape L₁ L₂) (hs₁ : ∀ a ∈ L₁, s * a * s⁻¹ ∈ L₂)
    {N : Subgroup Q} (hNK : N ≤ L₁ ⊔ L₂) (hodd : Odd (Nat.card ↥N))
    (hΔN : ∀ a ∈ L₁, ∀ n ∈ N, (a * (s * a * s⁻¹)) * n * (a * (s * a * s⁻¹))⁻¹ ∈ N) :
    N ≤ L₂ := by
  have hq₁ : IsQuasisimple ↥L₁ := h.c₁.1
  rcases CFSG.GH74.GLS.Stage2.Signalizer.Odd87.quasisimple_normal_le_center_or_eq hq₁
      (fun x hx => (mem_projOne.mp hx).1) (projOne_normal h hs₁ hΔN) with hc | heq
  · intro n hn
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      CFSG.GH74.GLS.Stage2.Final.L26.exists_mul_of_mem_sup_of_commute h.comm (hNK hn)
    have haA : a ∈ projOne h.comm N := ⟨ha, b, hb, hn⟩
    have hac := (hc haA).2
    have ha2 : a * a = 1 :=
      h.center₁ a ha fun l hl => (Subgroup.mem_centralizer_iff.mp hac l hl).symm
    have hab : a * b = b * a := h.comm a ha b hb
    have hsq : (a * b) * (a * b) = b * b := by
      calc (a * b) * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hab]
        _ = (a * a) * (b * b) := by group
        _ = b * b := by rw [ha2, one_mul]
    have hord : Odd (orderOf (a * b)) := by
      have h1 := orderOf_dvd_natCard (⟨a * b, hn⟩ : ↥N)
      rw [Subgroup.orderOf_mk] at h1
      exact Odd.of_dvd_nat hodd h1
    have hmem := mem_zpowers_mul_self_of_odd hord
    rw [hsq] at hmem
    exact Subgroup.zpowers_le.mpr (L₂.mul_mem hb hb) hmem
  · exfalso
    have hL₂K : L₂ ≤ L₁ ⊔ L₂ := le_sup_right
    have hL₁K : L₁ ≤ L₁ ⊔ L₂ := le_sup_left
    have hKn : L₁ ⊔ L₂ ≤ normalizer (L₂ : Set Q) := by
      refine sup_le (fun a ha => ?_) Subgroup.le_normalizer
      rw [Subgroup.mem_normalizer_iff]
      intro b
      constructor
      · intro hb
        rw [h.comm a ha b hb, mul_inv_cancel_right]
        exact hb
      · intro hb
        have e := h.comm a⁻¹ (L₁.inv_mem ha) _ hb
        have hb' : b = a * b * a⁻¹ := by
          calc b = a⁻¹ * (a * b * a⁻¹) * a := by group
            _ = (a * b * a⁻¹) * a⁻¹ * a := by rw [e]
            _ = a * b * a⁻¹ := by group
        rw [hb']
        exact hb
    have : (L₂.subgroupOf (L₁ ⊔ L₂)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hL₂K).mpr hKn
    have hperf : ⁅L₁.subgroupOf (L₁ ⊔ L₂), L₁.subgroupOf (L₁ ⊔ L₂)⁆ =
        L₁.subgroupOf (L₁ ⊔ L₂) := by
      apply Subgroup.map_injective (L₁ ⊔ L₂).subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hL₁K]
      exact Subgroup.isPerfect_iff.mp hq₁.1
    have hoddK : Odd (Nat.card ↥(N.subgroupOf (L₁ ⊔ L₂))) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv]
      exact hodd
    have hle : L₁.subgroupOf (L₁ ⊔ L₂) ≤
        L₂.subgroupOf (L₁ ⊔ L₂) ⊔ N.subgroupOf (L₁ ⊔ L₂) := by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      have hxA : (x : Q) ∈ projOne h.comm N := by rw [heq]; exact hx
      obtain ⟨-, b, hb, hxb⟩ := hxA
      have hbK : b ∈ L₁ ⊔ L₂ := hL₂K hb
      have hn : (⟨(x : Q) * b, (L₁ ⊔ L₂).mul_mem x.2 hbK⟩ : ↥(L₁ ⊔ L₂)) ∈
          N.subgroupOf (L₁ ⊔ L₂) := hxb
      have he : (⟨b⁻¹, (L₁ ⊔ L₂).inv_mem hbK⟩ : ↥(L₁ ⊔ L₂)) ∈ L₂.subgroupOf (L₁ ⊔ L₂) :=
        L₂.inv_mem hb
      have hx' : x = (⟨(x : Q) * b, (L₁ ⊔ L₂).mul_mem x.2 hbK⟩ : ↥(L₁ ⊔ L₂)) *
          ⟨b⁻¹, (L₁ ⊔ L₂).inv_mem hbK⟩ := by
        apply Subtype.ext
        simp
      have hmem := Subgroup.mul_mem_sup hn he
      rw [← hx'] at hmem
      exact (sup_comm (N.subgroupOf (L₁ ⊔ L₂)) (L₂.subgroupOf (L₁ ⊔ L₂))).le hmem
    have h12 :=
      CFSG.GH74.GLS.Stage2.Signalizer.L52Two.I1.le_of_perfect_of_le_sup_odd hperf hoddK hle
    apply not_le_right h
    intro a ha
    exact h12 (show (⟨a, hL₁K ha⟩ : ↥(L₁ ⊔ L₂)) ∈ L₁.subgroupOf (L₁ ⊔ L₂) from ha)

theorem eq_bot_of_odd (h : PairShape L₁ L₂) (hs2 : s * s = 1) (hs₁ : ∀ a ∈ L₁, s * a * s⁻¹ ∈ L₂)
    (hs₂ : ∀ b ∈ L₂, s * b * s⁻¹ ∈ L₁) {N : Subgroup Q} (hNK : N ≤ L₁ ⊔ L₂)
    (hodd : Odd (Nat.card ↥N))
    (hΔN : ∀ a ∈ L₁, ∀ n ∈ N, (a * (s * a * s⁻¹)) * n * (a * (s * a * s⁻¹))⁻¹ ∈ N) :
    N = ⊥ := by
  have h2 : N ≤ L₂ := le_right_of_odd h hs₁ hNK hodd hΔN
  have hΔN' : ∀ b ∈ L₂, ∀ n ∈ N, (b * (s * b * s⁻¹)) * n * (b * (s * b * s⁻¹))⁻¹ ∈ N := by
    intro b hb n hn
    have ha : s * b * s⁻¹ ∈ L₁ := hs₂ b hb
    have e : (s * b * s⁻¹) * (s * (s * b * s⁻¹) * s⁻¹) = b * (s * b * s⁻¹) := by
      rw [CFSG.GH74.GLS.Stage2.Final.Thm6.L20.swap_swap hs2]
      exact h.comm _ ha b hb
    rw [← e]
    exact hΔN _ ha n hn
  have h1 : N ≤ L₁ := le_right_of_odd h.symm hs₂ (by rw [sup_comm]; exact hNK) hodd hΔN'
  rw [eq_bot_iff]
  intro n hn
  have hsq : n * n = 1 := h.center₁ n (h1 hn) fun l hl => (h.comm l hl n (h2 hn)).symm
  have hord : Odd (orderOf n) := by
    have h3 := orderOf_dvd_natCard (⟨n, hn⟩ : ↥N)
    rw [Subgroup.orderOf_mk] at h3
    exact Odd.of_dvd_nat hodd h3
  rw [Subgroup.mem_bot]
  have hdvd : orderOf n ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hsq)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1' | h2'
  · exact orderOf_eq_one_iff.mp h1'
  · rw [h2'] at hord
    exact absurd hord (by decide)

theorem comm_diag_of_odd (h : PairShape L₁ L₂) (hs2 : s * s = 1)
    (hs₁ : ∀ a ∈ L₁, s * a * s⁻¹ ∈ L₂) (hs₂ : ∀ b ∈ L₂, s * b * s⁻¹ ∈ L₁) {x : Q}
    (hx : x ∈ normalizer ((L₁ ⊔ L₂ : Subgroup Q) : Set Q)) {O : Subgroup Q}
    (hodd : Odd (Nat.card ↥O))
    (hΔO : ∀ a ∈ L₁, ∀ o ∈ O, (a * (s * a * s⁻¹)) * o * (a * (s * a * s⁻¹))⁻¹ ∈ O)
    (hxO : ∀ a ∈ L₁, ⁅x, a * (s * a * s⁻¹)⁆ ∈ O) :
    ∀ a ∈ L₁, x * (a * (s * a * s⁻¹)) = (a * (s * a * s⁻¹)) * x := by
  have hδ : ∀ a ∈ L₁, a * (s * a * s⁻¹) ∈ L₁ ⊔ L₂ := fun a ha =>
    (L₁ ⊔ L₂).mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right (hs₁ a ha))
  have hoddN : Odd (Nat.card ↥(O ⊓ (L₁ ⊔ L₂))) :=
    Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_left)
  have hΔN : ∀ a ∈ L₁, ∀ n ∈ O ⊓ (L₁ ⊔ L₂),
      (a * (s * a * s⁻¹)) * n * (a * (s * a * s⁻¹))⁻¹ ∈ O ⊓ (L₁ ⊔ L₂) := fun a ha n hn =>
    ⟨hΔO a ha n hn.1, (L₁ ⊔ L₂).mul_mem ((L₁ ⊔ L₂).mul_mem (hδ a ha) hn.2)
      ((L₁ ⊔ L₂).inv_mem (hδ a ha))⟩
  have hbot := eq_bot_of_odd h hs2 hs₁ hs₂ inf_le_right hoddN hΔN
  intro a ha
  have hcK : ⁅x, a * (s * a * s⁻¹)⁆ ∈ L₁ ⊔ L₂ := by
    rw [commutatorElement_def]
    exact (L₁ ⊔ L₂).mul_mem ((Subgroup.mem_normalizer_iff.mp hx _).mp (hδ a ha))
      ((L₁ ⊔ L₂).inv_mem (hδ a ha))
  have hmem : ⁅x, a * (s * a * s⁻¹)⁆ ∈ O ⊓ (L₁ ⊔ L₂) := ⟨hxO a ha, hcK⟩
  rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact hmem

theorem centralizes_of_comm_diag (h : PairShape L₁ L₂) (hs2 : s * s = 1)
    (hs₁ : ∀ a ∈ L₁, s * a * s⁻¹ ∈ L₂) (hs₂ : ∀ b ∈ L₂, s * b * s⁻¹ ∈ L₁) {x : Q}
    (hx₁ : ∀ a ∈ L₁, x * a * x⁻¹ ∈ L₁) (hx₂ : ∀ b ∈ L₂, x * b * x⁻¹ ∈ L₂)
    (hxΔ : ∀ a ∈ L₁, x * (a * (s * a * s⁻¹)) = (a * (s * a * s⁻¹)) * x) :
    (∀ a ∈ L₁, x * a = a * x) ∧ (∀ b ∈ L₂, x * b = b * x) :=
  CFSG.GH74.GLS.Stage2.Final.Thm6.L20.diag_centralizes (Subgroup.isPerfect_iff.mp h.c₁.1.1)
    h.comm hs2 hs₁ hs₂ (I := centralizer ({x} : Set Q))
    (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hxΔ a ha).symm) hx₁ hx₂
    (fun _ hi => (Subgroup.mem_centralizer_singleton_iff.mp hi).symm)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.ResD
