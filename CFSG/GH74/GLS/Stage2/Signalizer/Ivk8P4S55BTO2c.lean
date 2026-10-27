module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTO2s
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTStmt

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG
open scoped commutatorElement

variable {M : Type} [Group M] [Finite M]

omit [Finite M] in
theorem le_centralizer_of_commutator_eq_bot {A B : Subgroup M} (h : ⁅A, B⁆ = ⊥) :
    A ≤ centralizer (B : Set M) := by
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have : ⁅a, b⁆ ∈ (⊥ : Subgroup M) := h ▸ Subgroup.commutator_mem_commutator ha hb
  exact (commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp this)).symm

theorem step_out {N X : Subgroup M} [N.Normal] [hXn : X.Normal] (hNX : N ≤ X)
    (hX2 : ∀ x ∈ X, ∃ n : ℕ, x ^ 2 ^ n ∈ N)
    (h3 : ∀ J₁ J₂ J₃ : Subgroup M, IsComponent J₁ → IsComponent J₂ → IsComponent J₃ →
      J₁ ≠ J₂ → J₁ ≠ J₃ → J₂ ≠ J₃ → False)
    (hOut : ∀ J : Subgroup M, IsComponent J → J ≤ N → OutTwoNilp (↥J ⧸ center ↥J))
    {g : M} {m : ℕ} (hm : Odd m) (hgm : g ^ m = 1) :
    ∀ x ∈ X, ∃ c ∈ centralizer (layer M : Set M), c ∈ X ∧ x⁻¹ * (g * x * g⁻¹) * c⁻¹ ∈ N := by
  intro x hx
  set w := x⁻¹ * (g * x * g⁻¹) with hw
  have hwX : w ∈ X := X.mul_mem (X.inv_mem hx) (hXn.conj_mem x hx g)
  suffices key : ∃ n ∈ N, n⁻¹ * w ∈ centralizer (layer M : Set M) by
    obtain ⟨n, hnN, hc⟩ := key
    refine ⟨n⁻¹ * w, hc, X.mul_mem (X.inv_mem (hNX hnN)) hwX, ?_⟩
    have e : w * (n⁻¹ * w)⁻¹ = n := by group
    rw [e]
    exact hnN
  have hout : ∀ J : Subgroup M, IsComponent J → ¬ J ≤ N → X ≤ centralizer (J : Set M) :=
    fun J hJ hJN => le_centralizer_of_not_le hX2 hJ hJN
  by_cases hex : ∃ J₁ : Subgroup M, IsComponent J₁ ∧ J₁ ≤ N
  · obtain ⟨J₁, hJ₁, hJ₁N⟩ := hex
    obtain ⟨O₁, -, -, hodd₁, h2₁⟩ := hOut J₁ hJ₁ hJ₁N
    obtain ⟨hwN₁, hwO₁⟩ := w_facts (x := x) h3 hJ₁ h2₁ hm hgm
    obtain ⟨k, hk⟩ := hX2 w hwX
    obtain ⟨n₁, hn₁N, hn₁J, hc₁⟩ := exists_pc hJ₁.1.1 hJ₁N hodd₁ hwN₁ hwO₁ hk
    set w₁ := n₁⁻¹ * w with hw₁def
    have hw₁X : w₁ ∈ X := X.mul_mem (X.inv_mem (hNX hn₁N)) hwX
    by_cases hex2 : ∃ J₂ : Subgroup M, IsComponent J₂ ∧ J₂ ≤ N ∧ J₂ ≠ J₁
    · obtain ⟨J₂, hJ₂, hJ₂N, hne⟩ := hex2
      obtain ⟨O₂, -, -, hodd₂, h2₂⟩ := hOut J₂ hJ₂ hJ₂N
      have hcomm : ⁅J₁, J₂⁆ = ⊥ := by
        rcases LocalCores.distinct_components_commute hJ₁ hJ₂ with h | h
        · exact absurd h.symm hne
        · exact h
      have hJ₁₂ : J₁ ≤ centralizer (J₂ : Set M) := le_centralizer_of_commutator_eq_bot hcomm
      have hJ₂₁ : J₂ ≤ centralizer (J₁ : Set M) :=
        le_centralizer_of_commutator_eq_bot (by rw [Subgroup.commutator_comm]; exact hcomm)
      obtain ⟨hwN₂, hwO₂⟩ := w_facts (x := x) h3 hJ₂ h2₂ hm hgm
      set S₂ : Subgroup M := (O₂.comap (actJ J₂)).map (normalizer (J₂ : Set M)).subtype
        with hS₂
      have hJ₁S : J₁ ≤ S₂ := by
        intro j hj
        refine ⟨⟨j, mem_normalizer_of_mem_centralizer (hJ₁₂ hj)⟩, ?_, rfl⟩
        show actJ J₂ _ ∈ O₂
        rw [actJ_eq_one_of_mem_centralizer (hJ₁₂ hj)]
        exact O₂.one_mem
      have hwS : w ∈ S₂ := ⟨⟨w, hwN₂⟩, hwO₂, rfl⟩
      have hsupS : J₁ ⊔ zpowers w ≤ S₂ := sup_le hJ₁S (zpowers_le.mpr hwS)
      obtain ⟨n₁', hn₁'O, hn₁'e⟩ := hsupS hn₁J
      have hw₁N₂ : w₁ ∈ normalizer (J₂ : Set M) := by
        have : w₁ = (n₁' : M)⁻¹ * w := by rw [hw₁def, ← hn₁'e]; rfl
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ n₁'.2) hwN₂
      have hw₁O₂ : actJ J₂ ⟨w₁, hw₁N₂⟩ ∈ O₂ := by
        have e : (⟨w₁, hw₁N₂⟩ : ↥(normalizer (J₂ : Set M))) = n₁'⁻¹ * ⟨w, hwN₂⟩ :=
          Subtype.ext (by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]
            rw [hw₁def, ← hn₁'e]
            rfl)
        rw [e, map_mul, map_inv]
        exact O₂.mul_mem (O₂.inv_mem hn₁'O) hwO₂
      obtain ⟨k₂, hk₂⟩ := hX2 w₁ hw₁X
      obtain ⟨n₂, hn₂N, hn₂J, hc₂⟩ := exists_pc hJ₂.1.1 hJ₂N hodd₂ hw₁N₂ hw₁O₂ hk₂
      refine ⟨n₁ * n₂, N.mul_mem hn₁N hn₂N, ?_⟩
      have he : (n₁ * n₂)⁻¹ * w = n₂⁻¹ * w₁ := by rw [hw₁def]; group
      rw [he]
      apply mem_centralizer_layer
      intro J hJ
      by_cases h1 : J = J₁
      · subst h1
        have hsup : J₂ ⊔ zpowers w₁ ≤ centralizer (J : Set M) :=
          sup_le hJ₂₁ (zpowers_le.mpr hc₁)
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hsup hn₂J)) hc₁
      · by_cases h2 : J = J₂
        · subst h2
          exact hc₂
        · exact (h3 J J₁ J₂ hJ hJ₁ hJ₂ h1 h2 hne.symm).elim
    · refine ⟨n₁, hn₁N, ?_⟩
      apply mem_centralizer_layer
      intro J hJ
      by_cases h1 : J = J₁
      · subst h1
        exact hc₁
      · have hJN : ¬ J ≤ N := fun hJN => hex2 ⟨J, hJ, hJN, h1⟩
        exact hout J hJ hJN hw₁X
  · refine ⟨1, N.one_mem, ?_⟩
    rw [inv_one, one_mul]
    apply mem_centralizer_layer
    intro J hJ
    exact hout J hJ (fun hJN => hex ⟨J, hJ, hJN⟩) hwX

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
