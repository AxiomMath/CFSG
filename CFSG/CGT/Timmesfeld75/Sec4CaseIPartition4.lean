module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIPartition3
public import CFSG.CGT.Timmesfeld75.Sec4CaseIConj
public import CFSG.CGT.Timmesfeld75.Sec4CaseIPartition2

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

section Partition

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a w : G}

omit [Finite G] in
theorem inf_conjSubgroup_eq_bot_of_ne (hT : IsWC T) {y y' : G}
    (hne : conjSubgroup y T ≠ conjSubgroup y' T) :
    conjSubgroup y T ⊓ conjSubgroup y' T = ⊥ := by
  have e : conjSubgroup y' T = conjSubgroup (y' * y⁻¹) (conjSubgroup y T) := by
    rw [conjSubgroup_conjSubgroup]
    congr 1
    group
  rw [e] at hne ⊢
  exact (hT.conj y).inf_conj_eq_bot fun h => hne (h.symm)

theorem Sec4Hyp.commute_sec4N_of_actsTriv
    (hAsc : AschbacherNoPolarInput) (h : Sec4Hyp T T₁ a T₂)
    (hq : 2 * Nat.card (normIn T T₁) < Nat.card T) (hw : Sec4ActsTriv T T₁ T₂ w)
    (hwT : w ∈ Subgroup.normalizer (T : Set G))
    (hC : Nat.card (normIn T T₁) ≤ Nat.card ↥(T ⊓ Subgroup.centralizer ({w} : Set G))) :
    ∀ m ∈ sec4N T T₁ T₂, w * m * w⁻¹ = m := by
  obtain ⟨f, hf2, hcardT, hcount⟩ := h.card_conj_gt hAsc hq
  have hfin : {U : Subgroup G | ∃ y ∈ sec4Y T T₁ T₂, U = conjSubgroup y T}.Finite :=
    Set.toFinite _
  set c := Nat.card ↥(sec4Psi h hw T) with hc
  have hcle : c ≤ 2 ^ f := h.card_sec4Psi_le hw hwT hcardT hC
  have hcpos : 0 < c := Nat.card_pos
  have hnorm : ∀ U ∈ hfin.toFinset, conjSubgroup w U = U := by
    intro U hU
    obtain ⟨y, hy, rfl⟩ := hfin.mem_toFinset.1 hU
    exact h.conjSubgroup_eq_of_actsTriv hw hy
  have hdisj : ∀ U ∈ hfin.toFinset, ∀ U' ∈ hfin.toFinset, U ≠ U' →
      sec4Psi h hw U ⊓ sec4Psi h hw U' = ⊥ := by
    intro U hU U' hU' hne
    obtain ⟨y, hy, rfl⟩ := hfin.mem_toFinset.1 hU
    obtain ⟨y', hy', rfl⟩ := hfin.mem_toFinset.1 hU'
    exact sec4Psi_inf_eq_bot h hw (hnorm _ hU) (hnorm _ hU')
      (inf_conjSubgroup_eq_bot_of_ne h.pair.wc hne)
  have hcards : ∀ U ∈ hfin.toFinset, Nat.card ↥(sec4Psi h hw U) = c := by
    intro U hU
    obtain ⟨y, hy, rfl⟩ := hfin.mem_toFinset.1 hU
    exact h.card_sec4Psi_conj hw hy
  have hge := card_ge_of_pairwise_inf_eq_bot (sec4Nu h hw).range hfin.toFinset (sec4Psi h hw)
    (fun U _ => Subgroup.map_le_range _ _) hdisj hcards
  have hscard : hfin.toFinset.card =
      Set.ncard {U : Subgroup G | ∃ y ∈ sec4Y T T₁ T₂, U = conjSubgroup y T} :=
    (Set.ncard_eq_toFinset_card _ hfin).symm
  have hNab : ∀ m ∈ sec4N T T₁ T₂, ∀ m' ∈ sec4N T T₁ T₂, m * m' = m' * m :=
    fun _ hm _ hm' => elemAbelian_mul_comm h.isElemAbelian_sec4N hm hm'
  obtain ⟨y₁, hy₁, hT₁⟩ := h.exists_mem_sec4Y_conj₁
  obtain ⟨y₂, hy₂, hT₂⟩ := h.exists_mem_sec4Y_conj₂
  have hc₁ : Nat.card ↥(sec4Psi h hw T₁) = c := by
    have := h.card_sec4Psi_conj hw hy₁
    rwa [← hT₁] at this
  have hc₂ : Nat.card ↥(sec4Psi h hw T₂) = c := by
    have := h.card_sec4Psi_conj hw hy₂
    rwa [← hT₂] at this
  have hdec : ∀ m : ↥(sec4N T T₁ T₂), ∃ m₀ ∈ (T ⊓ sec4N T T₁ T₂).subgroupOf (sec4N T T₁ T₂),
      ∃ m₁ ∈ (T₁ ⊓ sec4N T T₁ T₂).subgroupOf (sec4N T T₁ T₂),
        ∃ m₂ ∈ (T₂ ⊓ sec4N T T₁ T₂).subgroupOf (sec4N T T₁ T₂), m = m₀ * m₁ * m₂ := by
    intro m
    obtain ⟨l₀, hl₀, l₁, hl₁, l₂, hl₂, hm⟩ := exists_mul_mul_of_mem_sup
      (A := normIn T T₁) (B := normIn T₁ T) (C := normIn T₂ T)
      (fun x hx y hy => hNab x (normIn_le_sec4N_left hx) y (normIn_le_sec4N_mid hy))
      (fun x hx z hz => hNab x (normIn_le_sec4N_left hx) z (normIn_le_sec4N_right hz))
      (fun y hy z hz => hNab y (normIn_le_sec4N_mid hy) z (normIn_le_sec4N_right hz)) m.2
    exact ⟨⟨l₀, normIn_le_sec4N_left hl₀⟩,
      Subgroup.mem_subgroupOf.2 ⟨normIn_le _ _ hl₀, normIn_le_sec4N_left hl₀⟩,
      ⟨l₁, normIn_le_sec4N_mid hl₁⟩,
      Subgroup.mem_subgroupOf.2 ⟨normIn_le _ _ hl₁, normIn_le_sec4N_mid hl₁⟩,
      ⟨l₂, normIn_le_sec4N_right hl₂⟩,
      Subgroup.mem_subgroupOf.2 ⟨normIn_le _ _ hl₂, normIn_le_sec4N_right hl₂⟩, Subtype.ext hm⟩
  have hup : Nat.card ↥(sec4Nu h hw).range ≤ c * c * c := by
    let F : ↥(sec4Psi h hw T) × ↥(sec4Psi h hw T₁) × ↥(sec4Psi h hw T₂) →
        ↥(sec4Nu h hw).range := fun p =>
      ⟨p.1 * p.2.1 * p.2.2, (sec4Nu h hw).range.mul_mem ((sec4Nu h hw).range.mul_mem
        (Subgroup.map_le_range _ _ p.1.2) (Subgroup.map_le_range _ _ p.2.1.2))
        (Subgroup.map_le_range _ _ p.2.2.2)⟩
    have hF : Function.Surjective F := by
      rintro ⟨_, m, rfl⟩
      obtain ⟨m₀, hm₀, m₁, hm₁, m₂, hm₂, rfl⟩ := hdec m
      refine ⟨(⟨sec4Nu h hw m₀, m₀, hm₀, rfl⟩, ⟨sec4Nu h hw m₁, m₁, hm₁, rfl⟩,
        ⟨sec4Nu h hw m₂, m₂, hm₂, rfl⟩), ?_⟩
      apply Subtype.ext
      simp only [F, map_mul]
    calc Nat.card ↥(sec4Nu h hw).range
        ≤ Nat.card (↥(sec4Psi h hw T) × ↥(sec4Psi h hw T₁) × ↥(sec4Psi h hw T₂)) :=
          Nat.card_le_card_of_surjective F hF
      _ = c * c * c := by
          rw [Nat.card_prod, Nat.card_prod, hc₁, hc₂, mul_assoc]
  have hc1 : c = 1 := by
    by_contra hne
    have h2 : 2 ≤ c := by omega
    have h3 : c ^ 3 ≤ (2 ^ f) ^ 3 := Nat.pow_le_pow_left hcle 3
    have h4 : hfin.toFinset.card ≤ hfin.toFinset.card * (c - 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    have h5 : c * c * c = c ^ 3 := by ring
    rw [hscard] at hge h4
    omega
  have hb₀ : sec4Psi h hw T = ⊥ := Subgroup.eq_bot_of_card_eq _ (hc.symm.trans hc1)
  have hb₁ : sec4Psi h hw T₁ = ⊥ := Subgroup.eq_bot_of_card_eq _ (hc₁.trans hc1)
  have hb₂ : sec4Psi h hw T₂ = ⊥ := Subgroup.eq_bot_of_card_eq _ (hc₂.trans hc1)
  intro m hm
  obtain ⟨m₀, hm₀, m₁, hm₁, m₂, hm₂, hmm⟩ := hdec ⟨m, hm⟩
  have h1 : sec4Nu h hw m₀ = 1 := by
    have : sec4Nu h hw m₀ ∈ sec4Psi h hw T := ⟨m₀, hm₀, rfl⟩
    rw [hb₀] at this
    exact Subgroup.mem_bot.1 this
  have h2 : sec4Nu h hw m₁ = 1 := by
    have : sec4Nu h hw m₁ ∈ sec4Psi h hw T₁ := ⟨m₁, hm₁, rfl⟩
    rw [hb₁] at this
    exact Subgroup.mem_bot.1 this
  have h3 : sec4Nu h hw m₂ = 1 := by
    have : sec4Nu h hw m₂ ∈ sec4Psi h hw T₂ := ⟨m₂, hm₂, rfl⟩
    rw [hb₂] at this
    exact Subgroup.mem_bot.1 this
  have hν : sec4Nu h hw ⟨m, hm⟩ = 1 := by
    rw [hmm, map_mul, map_mul, h1, h2, h3, mul_one, mul_one]
  have h4 := congrArg Subtype.val hν
  rw [coe_sec4Nu] at h4
  have h5 : w * m * w⁻¹ * m⁻¹ = 1 := h4
  rwa [mul_inv_eq_one] at h5

end Partition

end CFSG.CGT.Timmesfeld75
