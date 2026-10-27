module

public import CFSG.Foundations.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
public import CFSG.GH74.GLS.IVK.Proofs2.ConjComponent
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011CentCoreZ

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.CFT

open Subgroup CFSG CFSG.GH74.GLS.IVK.Proofs2
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem gwComponent {K : Subgroup Y} (h : CFSG.IsComponent K) :
    CFSG.GorensteinWalter.IsComponentOf K ⊤ := by
  obtain ⟨⟨hperf, hsimple, a, b, hab⟩, hsub⟩ := h
  refine ⟨le_top, hsub.subgroupOf, ?_, hperf.commutator_eq_top, hsimple⟩
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨⟨a', b', fun h => hab (by rw [h])⟩⟩

theorem eq_of_le_sup_of_perfect {I B E : Subgroup Y} (hB : CFSG.IsComponent B)
    (hcomm : ∀ a ∈ I, ∀ b ∈ B, a * b = b * a) (hIE : I ≤ E) (hEle : E ≤ I ⊔ B)
    (hEsub : E.IsSubnormal) (hEperf : ⁅E, E⁆ = E) (hne : E ≠ I ⊔ B) : E = I := by
  rcases CFSG.GorensteinWalter.component_le_or_commutator_eq_bot (gwComponent hB) hEsub with hBE | hBE
  · exact absurd (le_antisymm hEle (sup_le hIE hBE)) hne
  ·
    have hBc : ∀ b ∈ B, ∀ e ∈ E, b * e = e * b := by
      intro b hb e he
      have : ⁅b, e⁆ ∈ (⊥ : Subgroup Y) := hBE ▸ commutator_mem_commutator hb he
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    apply le_antisymm _ hIE
    calc E = ⁅E, E⁆ := hEperf.symm
      _ ≤ I := by
        rw [Subgroup.commutator_le]
        intro g₁ hg₁ g₂ hg₂
        obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := ConjComponent.exists_mul_of_mem_sup hcomm (hEle hg₁)
        obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := ConjComponent.exists_mul_of_mem_sup hcomm (hEle hg₂)
        have hb₂E : b₂ ∈ E := by
          have : b₂ = a₂⁻¹ * (a₂ * b₂) := by group
          rw [this]; exact E.mul_mem (E.inv_mem (hIE ha₂)) hg₂
        have e : ⁅a₁ * b₁, a₂ * b₂⁆ = ⁅a₁, a₂⁆ := by
          rw [hcomm a₁ ha₁ b₁ hb₁, hcomm a₂ ha₂ b₂ hb₂]
          exact ConjComponent.commutatorElement_mul_mul (hcomm a₁ ha₁ b₁ hb₁).symm
            (hcomm a₂ ha₂ b₁ hb₁).symm (hBc b₁ hb₁ b₂ hb₂E) (hcomm a₁ ha₁ b₂ hb₂).symm
            (hcomm a₂ ha₂ b₂ hb₂).symm
        rw [e]
        exact Subgroup.commutator_le_self I (commutator_mem_commutator ha₁ ha₂)

theorem eq_or_eq_of_perfect_subnormal {I₁ I₂ E : Subgroup Y} {q : ℕ} (hq : Odd q)
    (hc₁ : CFSG.IsComponent I₁) (hc₂ : CFSG.IsComponent I₂)
    (hcomm : ∀ a ∈ I₁, ∀ b ∈ I₂, a * b = b * a) (hinf : Nat.card ↥(I₁ ⊓ I₂) = 2)
    (hcard₁ : Nat.card ↥I₁ = q * (q ^ 2 - 1)) (hcard₂ : Nat.card ↥I₂ = q * (q ^ 2 - 1))
    (hEle : E ≤ I₁ ⊔ I₂) (hEsub : E.IsSubnormal) (hEperf : ⁅E, E⁆ = E) (hEne : E ≠ ⊥)
    (hEcard : ∃ m : ℕ, Odd m ∧ Nat.card ↥E = q * (q ^ 2 - 1) * m) : E = I₁ ∨ E = I₂ := by
  have hcomm' : ∀ a ∈ I₂, ∀ b ∈ I₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  have hneE : E ≠ I₁ ⊔ I₂ := by
    intro hE
    obtain ⟨m, hm, hcardE⟩ := hEcard
    have hB : I₂ ≤ normalizer (I₁ : Set Y) := fun b hb =>
      Subgroup.mem_normalizer_iff.2 fun h => by
        constructor
        · intro hh
          have := hcomm h hh b hb
          have e : b * h * b⁻¹ = h := by
            calc b * h * b⁻¹ = (b * h) * b⁻¹ := rfl
              _ = (h * b) * b⁻¹ := by rw [this]
              _ = h := by group
          rw [e]; exact hh
        · intro hh
          have hc := hcomm _ hh b hb
          have e : h = b * h * b⁻¹ := by
            calc h = b⁻¹ * ((b * h * b⁻¹) * b) := by group
              _ = b⁻¹ * (b * (b * h * b⁻¹)) := by rw [hc]
              _ = b * h * b⁻¹ := by group
          rwa [← e] at hh
    have hprod := CentCore.card_sup_mul_card_inf_of_le_normalizer hB
    rw [← hE, hcardE, hinf, hcard₁, hcard₂] at hprod
    have hpos : 0 < q * (q ^ 2 - 1) := by
      by_contra h0
      have h0' : q * (q ^ 2 - 1) = 0 := by omega
      rw [h0'] at hcard₁
      have : Nat.card ↥I₁ = 0 := hcard₁
      exact absurd this Nat.card_pos.ne'
    have h2m : m * 2 = q * (q ^ 2 - 1) := by
      have : q * (q ^ 2 - 1) * (m * 2) = q * (q ^ 2 - 1) * (q * (q ^ 2 - 1)) := by
        rw [← hprod]; ring
      exact Nat.eq_of_mul_eq_mul_left hpos this
    obtain ⟨k, rfl⟩ := hq
    obtain ⟨j, hj⟩ := Nat.even_mul_succ_self k
    have hsq : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by
      have : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
      omega
    rw [hsq, hj] at h2m
    have : m = (2 * k + 1) * 4 * j := by nlinarith
    exact (Nat.not_even_iff_odd.2 hm) ⟨(2 * k + 1) * 2 * j, by rw [this]; ring⟩
  rcases CFSG.GorensteinWalter.component_le_or_commutator_eq_bot (gwComponent hc₁) hEsub with h1 | h1
  · exact Or.inl (eq_of_le_sup_of_perfect hc₂ hcomm h1 hEle hEsub hEperf hneE)
  rcases CFSG.GorensteinWalter.component_le_or_commutator_eq_bot (gwComponent hc₂) hEsub with h2 | h2
  · refine Or.inr (eq_of_le_sup_of_perfect hc₁ hcomm' h2 (by rwa [sup_comm]) hEsub hEperf ?_)
    rwa [sup_comm]
  ·
    exfalso
    apply hEne
    rw [← hEperf, eq_bot_iff, Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have hcc : ∀ (I : Subgroup Y), ⁅I, E⁆ = ⊥ → ∀ a ∈ I, ∀ e ∈ E, a * e = e * a := by
      intro I hI a ha e he
      have : ⁅a, e⁆ ∈ (⊥ : Subgroup Y) := hI ▸ commutator_mem_commutator ha he
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    obtain ⟨a, ha, b, hb, rfl⟩ := ConjComponent.exists_mul_of_mem_sup hcomm (hEle hg₁)
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    have e1 := hcc I₁ h1 a ha g₂ hg₂
    have e2 := hcc I₂ h2 b hb g₂ hg₂
    calc a * b * g₂ = a * (b * g₂) := by group
      _ = a * (g₂ * b) := by rw [e2]
      _ = (a * g₂) * b := by group
      _ = (g₂ * a) * b := by rw [e1]
      _ = g₂ * (a * b) := by group

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.CFT
