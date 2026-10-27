module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Kind
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTNP

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG
open scoped commutatorElement

variable {M : Type*} [Group M] [Finite M]

omit [Finite M] in
theorem eq_bot_of_perfect_of_le_centralizer {L : Subgroup M} (hL : ⁅L, L⁆ = L)
    (hc : L ≤ centralizer (L : Set M)) : L = ⊥ := by
  rw [← hL, eq_bot_iff, Subgroup.commutator_le]
  intro a ha b hb
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact (Subgroup.mem_centralizer_iff.mp (hc hb)) a ha

omit [Finite M] in
theorem commutatorElement_mul_central {c₁ c₂ j₁ j₂ : M}
    (h₁ : ∀ y, c₁ * y = y * c₁) (h₂ : ∀ y, c₂ * y = y * c₂) :
    ⁅c₁ * j₁, c₂ * j₂⁆ = ⁅j₁, j₂⁆ := by
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev, mul_inv_rev]
  have e1 : c₁ * j₁ * (c₂ * j₂) * (j₁⁻¹ * c₁⁻¹) * (j₂⁻¹ * c₂⁻¹) =
      c₁ * (j₁ * (c₂ * j₂) * j₁⁻¹ * c₁⁻¹ * j₂⁻¹ * c₂⁻¹) := by group
  rw [e1]
  have hc₁i : ∀ y, c₁⁻¹ * y = y * c₁⁻¹ := fun y => by
    calc c₁⁻¹ * y = c₁⁻¹ * (y * c₁) * c₁⁻¹ := by group
      _ = c₁⁻¹ * (c₁ * y) * c₁⁻¹ := by rw [h₁ y]
      _ = y * c₁⁻¹ := by group
  have hc₂i : ∀ y, c₂⁻¹ * y = y * c₂⁻¹ := fun y => by
    calc c₂⁻¹ * y = c₂⁻¹ * (y * c₂) * c₂⁻¹ := by group
      _ = c₂⁻¹ * (c₂ * y) * c₂⁻¹ := by rw [h₂ y]
      _ = y * c₂⁻¹ := by group
  calc c₁ * (j₁ * (c₂ * j₂) * j₁⁻¹ * c₁⁻¹ * j₂⁻¹ * c₂⁻¹)
      = c₁ * c₁⁻¹ * (j₁ * (c₂ * j₂) * j₁⁻¹ * j₂⁻¹ * c₂⁻¹) := by
        rw [show j₁ * (c₂ * j₂) * j₁⁻¹ * c₁⁻¹ * j₂⁻¹ * c₂⁻¹ =
          j₁ * (c₂ * j₂) * j₁⁻¹ * (c₁⁻¹ * j₂⁻¹) * c₂⁻¹ by group, hc₁i]
        rw [show j₁ * (c₂ * j₂) * j₁⁻¹ * (j₂⁻¹ * c₁⁻¹) * c₂⁻¹ =
          (j₁ * (c₂ * j₂) * j₁⁻¹ * j₂⁻¹) * (c₁⁻¹ * c₂⁻¹) by group]
        rw [show c₁⁻¹ * c₂⁻¹ = c₂⁻¹ * c₁⁻¹ from hc₁i _]
        have := hc₁i (j₁ * (c₂ * j₂) * j₁⁻¹ * j₂⁻¹ * c₂⁻¹)
        rw [show c₁ * (j₁ * (c₂ * j₂) * j₁⁻¹ * j₂⁻¹ * (c₂⁻¹ * c₁⁻¹)) =
          c₁ * ((j₁ * (c₂ * j₂) * j₁⁻¹ * j₂⁻¹ * c₂⁻¹) * c₁⁻¹) by group, ← this]
        group
    _ = j₁ * j₂ * j₁⁻¹ * j₂⁻¹ := by
        rw [mul_inv_cancel, one_mul]
        rw [show j₁ * (c₂ * j₂) = c₂ * (j₁ * j₂) by rw [← mul_assoc, ← h₂ j₁, mul_assoc]]
        rw [show c₂ * (j₁ * j₂) * j₁⁻¹ * j₂⁻¹ * c₂⁻¹ = c₂ * ((j₁ * j₂ * j₁⁻¹ * j₂⁻¹) * c₂⁻¹)
          by group, ← hc₂i]
        group

theorem exists_partner
    (h3 : ∀ J₁ J₂ J₃ : Subgroup M, IsComponent J₁ → IsComponent J₂ → IsComponent J₃ →
      J₁ ≠ J₂ → J₁ ≠ J₃ → J₂ ≠ J₃ → False)
    {J : Subgroup M} (hJ : IsComponent J) {L : Subgroup M} (hLp : ⁅L, L⁆ = L) (hL1 : L ≠ ⊥)
    (hLE : L ≤ layer M) (hLJ : L ≤ centralizer (J : Set M)) :
    ∃ J' : Subgroup M, IsComponent J' ∧ J' ≠ J ∧
      (∀ K : Subgroup M, IsComponent K → K = J ∨ K = J') ∧ L ≤ J' := by
  by_cases hex : ∃ J' : Subgroup M, IsComponent J' ∧ J' ≠ J
  · obtain ⟨J', hJ', hne⟩ := hex
    have huniq : ∀ K : Subgroup M, IsComponent K → K = J ∨ K = J' := by
      intro K hK
      by_contra hc
      push Not at hc
      exact h3 J J' K hJ hJ' hK hne.symm (Ne.symm hc.1) (Ne.symm hc.2)
    refine ⟨J', hJ', hne, huniq, ?_⟩
    have hcomm : ∀ a ∈ J, ∀ b ∈ J', a * b = b * a := by
      have h0 : ⁅J, J'⁆ = ⊥ := (LocalCores.distinct_components_commute hJ hJ').resolve_left
        (Ne.symm hne)
      intro a ha b hb
      have : ⁅a, b⁆ ∈ (⊥ : Subgroup M) := h0 ▸ Subgroup.commutator_mem_commutator ha hb
      exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp this)
    have hlay : layer M ≤ J ⊔ J' := sSup_le fun K hK =>
      (huniq K hK).elim (fun h => h ▸ le_sup_left) (fun h => h ▸ le_sup_right)
    set N : Subgroup M := J ⊔ J' with hN
    have hcen : ∀ c ∈ J, c ∈ centralizer (J : Set M) → ∀ y ∈ N, c * y = y * c := by
      intro c hcJ hcC y hy
      have hle : N ≤ centralizer ({c} : Set M) := sup_le
        (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp hcC) x hx))
        (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hcomm c hcJ x hx).symm)
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy)).symm
    have hdec : ∀ x ∈ L, ∃ c ∈ J, c ∈ centralizer (J : Set M) ∧ ∃ j' ∈ J', x = c * j' := by
      intro x hx
      obtain ⟨c, hc, j', hj', rfl⟩ := Odd87.exists_mul_of_mem_sup' hcomm (hlay (hLE hx))
      refine ⟨c, hc, ?_, j', hj', rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hx' := (Subgroup.mem_centralizer_iff.mp (hLJ hx)) y hy
      have hj'y : y * j' = j' * y := hcomm y hy j' hj'
      calc y * c = y * (c * j') * j'⁻¹ := by group
        _ = c * j' * y * j'⁻¹ := by rw [hx']
        _ = c * (j' * y) * j'⁻¹ := by group
        _ = c * (y * j') * j'⁻¹ := by rw [hj'y]
        _ = c * y := by group
    rw [← hLp, Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨c₁, hc₁J, hc₁C, j₁, hj₁, rfl⟩ := hdec a ha
    obtain ⟨c₂, hc₂J, hc₂C, j₂, hj₂, rfl⟩ := hdec b hb
    have hmem : ∀ {y : M}, y ∈ J ∨ y ∈ J' → y ∈ N := fun h =>
      h.elim (fun h => Subgroup.mem_sup_left h) (fun h => Subgroup.mem_sup_right h)
    have key := commutatorElement_mul_central (M := ↥N) (c₁ := ⟨c₁, hmem (Or.inl hc₁J)⟩)
      (c₂ := ⟨c₂, hmem (Or.inl hc₂J)⟩) (j₁ := ⟨j₁, hmem (Or.inr hj₁)⟩)
      (j₂ := ⟨j₂, hmem (Or.inr hj₂)⟩)
      (fun y => Subtype.ext (hcen c₁ hc₁J hc₁C y y.2))
      (fun y => Subtype.ext (hcen c₂ hc₂J hc₂C y y.2))
    have key' := congrArg Subtype.val key
    simp only [Subgroup.coe_mul, commutatorElement_def, Subgroup.coe_inv] at key'
    rw [commutatorElement_def, key']
    exact J'.mul_mem (J'.mul_mem (J'.mul_mem hj₁ hj₂) (J'.inv_mem hj₁)) (J'.inv_mem hj₂)
  · exfalso
    push Not at hex
    have hlay : layer M ≤ J := sSup_le fun K hK => (hex K hK).le
    apply hL1
    apply eq_bot_of_perfect_of_le_centralizer hLp
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hLJ hx)) y (hlay (hLE hy))

theorem mem_normalizer_of_partner {J J' : Subgroup M} (hJ : IsComponent J)
    (hJ' : IsComponent J') (hne : J' ≠ J) (huniq : ∀ K : Subgroup M, IsComponent K → K = J ∨ K = J')
    {L : Subgroup M} (hLp : ⁅L, L⁆ = L) (hL1 : L ≠ ⊥) (hLJ' : L ≤ J') {x : M}
    (hx : x ∈ normalizer (L : Set M)) :
    x ∈ normalizer (J : Set M) ∧ x ∈ normalizer (J' : Set M) := by
  have hcomp : ∀ K : Subgroup M, IsComponent K → IsComponent (K.map (MulAut.conj x).toMonoidHom) :=
    fun K hK => LocalCores.isComponent_map_mulEquiv (MulAut.conj x) hK
  have hLx : L.map (MulAut.conj x).toMonoidHom = L := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (mem_normalizer_iff.mp hx w).mp hw
    · intro hy
      refine ⟨x⁻¹ * y * x, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      have := (mem_normalizer_iff.mp ((normalizer (L : Set M)).inv_mem hx) y).mp hy
      simpa [mul_assoc] using this
  have hJ'x : J'.map (MulAut.conj x).toMonoidHom = J' := by
    rcases huniq _ (hcomp J' hJ') with h | h
    · exfalso
      have hLJ : L ≤ J := by
        rw [← h, ← hLx]
        exact Subgroup.map_mono hLJ'
      apply hL1
      apply eq_bot_of_perfect_of_le_centralizer hLp
      have hcomm : ⁅J, J'⁆ = ⊥ := (LocalCores.distinct_components_commute hJ hJ').resolve_left
        (Ne.symm hne)
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have : ⁅a, b⁆ ∈ (⊥ : Subgroup M) :=
        hcomm ▸ Subgroup.commutator_mem_commutator (hLJ ha) (hLJ' hb)
      exact (commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp this)).symm
    · exact h
  refine ⟨?_, mem_normalizer_of_map_conj_eq hJ'x⟩
  rcases huniq _ (hcomp J hJ) with h | h
  · exact mem_normalizer_of_map_conj_eq h
  · exfalso
    apply hne
    apply Subgroup.map_injective (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective
    rw [hJ'x]
    exact h.symm

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
