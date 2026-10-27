module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open Equiv Equiv.Perm

@[expose] def sixASigma : Sym 7 := Equiv.swap 0 1

@[expose] def sixAEps : Z 2 := Multiplicative.ofAdd 1

theorem sixA_Z2_cases : ∀ ε : Z 2, ε = 1 ∨ ε = sixAEps := by decide

@[expose] def sixAEmb : Fin 5 ≃ {x : Fin 7 // 2 ≤ x.val} where
  toFun i := ⟨⟨i.val + 2, by omega⟩, by simp⟩
  invFun x := ⟨x.1.val - 2, by omega⟩
  left_inv i := by ext; simp
  right_inv x := by
    apply Subtype.ext; apply Fin.ext; simp; omega

@[expose] def sixAExt : Sym 5 →* Sym 7 := Equiv.Perm.extendDomainHom sixAEmb

@[expose] def sixAFlip : Z 2 →* Sym 7 where
  toFun ε := if ε = 1 then 1 else sixASigma
  map_one' := by simp
  map_mul' := by decide

theorem sixAFlip_one : sixAFlip 1 = 1 := by simp [sixAFlip]

theorem sixAFlip_eps : sixAFlip sixAEps = sixASigma := by
  simp [sixAFlip, sixAEps]

theorem sixAExt_apply_of_lt (ρ : Sym 5) (x : Fin 7) (hx : x.val < 2) : sixAExt ρ x = x := by
  simp only [sixAExt, Equiv.Perm.extendDomainHom_apply]
  exact Equiv.Perm.extendDomain_apply_not_subtype ρ sixAEmb (by simpa using hx)

theorem sixAExt_disjoint (ρ : Sym 5) : Equiv.Perm.Disjoint sixASigma (sixAExt ρ) := by
  intro x
  by_cases hx : x.val < 2
  · right; exact sixAExt_apply_of_lt ρ x hx
  · left
    have h0 : x ≠ 0 := by intro h; apply hx; simp [h]
    have h1 : x ≠ 1 := by intro h; apply hx; simp [h]
    simp [sixASigma, Equiv.swap_apply_of_ne_of_ne h0 h1]

theorem sixA_commute (ε : Z 2) (ρ : Sym 5) : Commute (sixAFlip ε) (sixAExt ρ) := by
  rcases sixA_Z2_cases ε with rfl | rfl
  · rw [sixAFlip_one]; exact Commute.one_left _
  · rw [sixAFlip_eps]; exact (sixAExt_disjoint ρ).commute

@[expose] def sixATheta : Z 2 × Sym 5 →* Sym 7 :=
  MonoidHom.noncommCoprod sixAFlip sixAExt sixA_commute

theorem sixATheta_apply (ε : Z 2) (ρ : Sym 5) : sixATheta (ε, ρ) = sixAFlip ε * sixAExt ρ := by
  simp [sixATheta, MonoidHom.noncommCoprod_apply]

@[expose] def sixAIsA (t : Sym 7) : Prop :=
  t.cycleType = {2} ∧ (sixASigma * t).cycleType = {2, 2}

@[expose] def sixAIsB (t : Sym 7) : Prop :=
  t.cycleType = {2, 2} ∧ (sixASigma * t).cycleType = {2, 2, 2}

@[expose] def sixAIsC (t : Sym 7) : Prop :=
  t.cycleType = {2, 2} ∧ (sixASigma * t).cycleType = {2}

@[expose] def sixAIsD (t : Sym 7) : Prop :=
  t.cycleType = {2, 2, 2} ∧ (sixASigma * t).cycleType = {2, 2}

end CFSG.EvenSporadicStandard.HNRecog.Section3
