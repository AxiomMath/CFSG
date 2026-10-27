module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S7I

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {d : Data G} {K₀ : Subgroup G}

theorem sylow_prod_decomp {G : Type*} [Group G] [Finite G] {A B P : Subgroup G} {m n : ℕ}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hi : A ⊓ B = ⊥) (hP : P ≤ A ⊔ B)
    (hcardP : Nat.card P = 2 ^ n) (hcardAB : Nat.card ↥(A ⊔ B) = 2 ^ n * m) (hm : Odd m) :
    ∀ x ∈ P, ∃ a ∈ P ⊓ A, ∃ b ∈ P ⊓ B, x = a * b := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P' : Subgroup ↥(A ⊔ B) := P.subgroupOf (A ⊔ B) with hP'
  have hP'card : Nat.card P' = 2 ^ n :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv).trans hcardP
  have hP'p : IsPGroup 2 ↥P' := IsPGroup.of_card hP'card
  set QA : Subgroup G := (P'.map (KProd.projA A B hc hi)).map A.subtype with hQA
  set QB : Subgroup G := (P'.map (KProd.projB A B hc hi)).map B.subtype with hQB
  have hQAp : IsPGroup 2 ↥QA := (hP'p.map (KProd.projA A B hc hi)).map A.subtype
  have hQBp : IsPGroup 2 ↥QB := (hP'p.map (KProd.projB A B hc hi)).map B.subtype
  have hQAA : QA ≤ A := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hQBB : QB ≤ B := by
    rintro _ ⟨b, -, rfl⟩
    exact b.2
  have hcomm : ∀ a ∈ QA, ∀ b ∈ QB, a * b = b * a := fun a ha b hb => hc a (hQAA ha) b (hQBB hb)
  have hPle : P ≤ QA ⊔ QB := by
    intro x hx
    set x' : ↥(A ⊔ B) := ⟨x, hP hx⟩ with hx'
    have hx'P : x' ∈ P' := hx
    have hxe := KProd.exists_eq_mul A B hc hi x'
    have h1 : ((KProd.projA A B hc hi x' : ↥A) : G) ∈ QA :=
      ⟨_, ⟨x', hx'P, rfl⟩, rfl⟩
    have h2 : ((KProd.projB A B hc hi x' : ↥B) : G) ∈ QB :=
      ⟨_, ⟨x', hx'P, rfl⟩, rfl⟩
    have : x = ((KProd.projA A B hc hi x' : ↥A) : G) * ((KProd.projB A B hc hi x' : ↥B) : G) := hxe
    rw [this]
    exact mul_mem (mem_sup_left h1) (mem_sup_right h2)
  have hQp : IsPGroup 2 ↥(QA ⊔ QB) := ModSplit.isPGroup_sup_of_comm hQAp hQBp hcomm
  have hQle : QA ⊔ QB ≤ A ⊔ B := sup_le_sup hQAA hQBB
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 hQp
  have hdvd : 2 ^ j ∣ 2 ^ n * m := hj ▸ hcardAB ▸ Subgroup.card_dvd_of_le hQle
  have hjn : j ≤ n := by
    by_contra hlt
    push Not at hlt
    have h2 : 2 ^ (n + 1) ∣ 2 ^ n * m :=
      (pow_dvd_pow 2 (by omega : n + 1 ≤ j)).trans hdvd
    rw [pow_succ] at h2
    have h3 : 2 ∣ m := Nat.dvd_of_mul_dvd_mul_left (by positivity) h2
    exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 h3)
  have hPQ : P = QA ⊔ QB := by
    have hcard' : Nat.card ↥(QA ⊔ QB) ≤ Nat.card ↥P := by
      rw [hj, hcardP]
      exact Nat.pow_le_pow_right (by norm_num) hjn
    exact Subgroup.eq_of_le_of_card_ge hPle hcard'
  intro x hx
  have hx' : x ∈ QA ⊔ QB := hPQ ▸ hx
  obtain ⟨a, ha, b, hb, rfl⟩ := KProd.exists_mul_of_mem_sup_of_comm hcomm hx'
  exact ⟨a, ⟨hPQ ▸ mem_sup_left ha, hQAA ha⟩, b, ⟨hPQ ▸ mem_sup_right hb, hQBB hb⟩, rfl⟩

section PQ

variable (h : d.Hyp) (hKU : d.KUnitary) (hf : d.IsUnitaryFactor K₀)

include h hKU in
theorem Data.Hyp.card_P_u : Nat.card d.P = 2 ^ 20 :=
  h.card_P (h.comm_M_V₂_mem_W hKU) (fun m hm => h.M_le_normalizer_Y hKU hm)

include h hKU in
theorem Data.Hyp.P_inf_H_u : d.P ⊓ d.H = d.S :=
  h.P_inf_H (h.comm_M_V₂_mem_W hKU) (fun m hm => h.M_le_normalizer_Y hKU hm)

include h hKU in
theorem Data.Hyp.exists_Q_mul_Qt {x : G} (hx : x ∈ d.P) :
    ∃ q ∈ d.P ⊓ Data.Nn h hKU hf, ∃ q' ∈ d.P ⊓ d.tc (Data.Nn h hKU hf), x = q * q' :=
  sylow_prod_decomp (A := Data.Nn h hKU hf) (B := d.tc (Data.Nn h hKU hf)) (m := 225)
    (fun _ ha _ hb => h.comm_Nn_tcNn hKU hf ha hb) (h.Nn_inf_tcNn hKU hf) (h.P_le_N₂ hKU hf)
    (h.card_P_u hKU) (by
      have := h.card_N₂ hKU hf
      rw [Data.N₂] at this
      rw [this]
      norm_num) (by decide) x hx

include h hKU in
theorem Data.Hyp.delta_mem_S_of_mem_Q {q : G} (hq : q ∈ d.P ⊓ Data.Nn h hKU hf) :
    q * (d.t * q * d.t) ∈ d.S := by
  rw [← h.P_inf_H_u hKU]
  refine ⟨d.P.mul_mem hq.1 (h.t_conj_mem_P hq.1), ?_⟩
  have hc : q * (d.t * q * d.t) = (d.t * q * d.t) * q :=
    h.comm_Nn_tcNn hKU hf hq.2 (h.t_conj_mem_tcNn hKU hf hq.2)
  refine mem_centralizer_singleton_iff.2 ?_
  show q * (d.t * q * d.t) * d.t = d.t * (q * (d.t * q * d.t))
  have e : d.t * (q * (d.t * q * d.t)) * d.t = q * (d.t * q * d.t) := by
    calc d.t * (q * (d.t * q * d.t)) * d.t
        = (d.t * q * d.t) * q * (d.t * d.t) := by group
      _ = (d.t * q * d.t) * q := by rw [h.t_mul_t, mul_one]
      _ = q * (d.t * q * d.t) := hc.symm
  calc q * (d.t * q * d.t) * d.t
      = (d.t * (q * (d.t * q * d.t)) * d.t) * d.t := by rw [e]
    _ = d.t * (q * (d.t * q * d.t)) := by rw [mul_assoc _ d.t d.t, h.t_mul_t, mul_one]

include h hKU in
theorem Data.Hyp.exists_mem_Q_delta_eq {s : G} (hs : s ∈ d.S) :
    ∃ q ∈ d.P ⊓ Data.Nn h hKU hf, s = q * (d.t * q * d.t) := by
  have hsPH : s ∈ d.P ⊓ d.H := by rw [h.P_inf_H_u hKU]; exact hs
  have hsr : s ∈ (Data.delta h hKU hf).range := by
    rw [h.range_delta hKU hf]
    exact ⟨h.P_le_N₂ hKU hf hsPH.1, hsPH.2⟩
  obtain ⟨n, hn⟩ := hsr
  have hsn : s = (n : G) * (d.t * (n : G) * d.t) := hn.symm
  obtain ⟨q, hq, q', hq', hqq'⟩ := h.exists_Q_mul_Qt hKU hf hsPH.1
  have htn : d.t * (n : G) * d.t ∈ d.tc (Data.Nn h hKU hf) := h.t_conj_mem_tcNn hKU hf n.2
  obtain ⟨hnq, -⟩ := eq_of_mul_eq_mul_of_inf_eq_bot (h.Nn_inf_tcNn hKU hf) n.2 hq.2 htn hq'.2
    (by rw [← hsn, hqq'])
  refine ⟨(n : G), ?_, hsn⟩
  rw [hnq]
  exact hq

end PQ

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
