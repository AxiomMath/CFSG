module

public import CFSG.Foundations.Basic
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG

theorem pRank_congr_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (p : ℕ) :
    pRank p X = pRank p Y := by
  unfold pRank
  congr 1
  ext r
  constructor
  · rintro ⟨A, hA, hc⟩
    exact ⟨A.map e.toMonoidHom,
      IsElementaryAbelian.of_mulEquiv (A.equivMapOfInjective _ e.injective) hA,
      by rw [Subgroup.card_map_of_injective e.injective, hc]⟩
  · rintro ⟨A, hA, hc⟩
    exact ⟨A.map e.symm.toMonoidHom,
      IsElementaryAbelian.of_mulEquiv (A.equivMapOfInjective _ e.symm.injective) hA,
      by rw [Subgroup.card_map_of_injective e.symm.injective, hc]⟩

open Subgroup in
theorem two_le_pRank_of_commute_independent {P : Type*} [Group P] [Finite P] {p : ℕ}
    (hp : p.Prime) {e₁ e₂ : P} (hc : Commute e₁ e₂) (h₁ : e₁ ^ p = 1) (h₂ : e₂ ^ p = 1)
    (hi : ∀ i j : ℤ, e₁ ^ i * e₂ ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j) :
    2 ≤ pRank p P := by
  have : Fact p.Prime := ⟨hp⟩
  have hne1 : e₁ ≠ 1 := by
    intro h
    have h' := (hi 1 0 (by rw [h]; simp)).1
    have : p ∣ 1 := by exact_mod_cast h'
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have hne2 : e₂ ≠ 1 := by
    intro h
    have h' := (hi 0 1 (by rw [h]; simp)).2
    have : p ∣ 1 := by exact_mod_cast h'
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have ho₁ : orderOf e₁ = p := orderOf_eq_prime h₁ hne1
  have ho₂ : orderOf e₂ = p := orderOf_eq_prime h₂ hne2
  have hcomm : ∀ (a : ↥(zpowers e₁)) (b : ↥(zpowers e₂)),
      Commute ((zpowers e₁).subtype a) ((zpowers e₂).subtype b) := by
    intro a b
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp b.2
    change Commute (a : P) (b : P)
    rw [← hk, ← hl]
    exact hc.zpow_zpow k l
  let f : ↥(zpowers e₁) × ↥(zpowers e₂) →* P :=
    MonoidHom.noncommCoprod (zpowers e₁).subtype (zpowers e₂).subtype hcomm
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨a, b⟩ hab
    have hab' : (a : P) * b = 1 := hab
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp b.2
    rw [← hk, ← hl] at hab'
    obtain ⟨hpk, hpl⟩ := hi k l hab'
    have ha : a = 1 := by
      apply Subtype.ext
      rw [← hk]
      obtain ⟨m, rfl⟩ := hpk
      rw [zpow_mul, zpow_natCast, h₁, one_zpow]
      rfl
    have hb : b = 1 := by
      apply Subtype.ext
      rw [← hl]
      obtain ⟨m, rfl⟩ := hpl
      rw [zpow_mul, zpow_natCast, h₂, one_zpow]
      rfl
    rw [ha, hb]
    rfl
  have hcard : Nat.card (↥(zpowers e₁) × ↥(zpowers e₂)) = p ^ 2 := by
    rw [Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, ho₁, ho₂]
    ring
  have hrank := CFSG.SectionRank.le_pRank_of_injective hp.one_lt
    (A := ↥(zpowers e₁) × ↥(zpowers e₂))
    (fun a b => Prod.ext (mul_comm' a.1 b.1) (mul_comm' a.2 b.2))
    (fun a => Prod.ext (by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.1.2
        apply Subtype.ext
        change (a.1 : P) ^ p = 1
        rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h₁, one_zpow])
      (by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2.2
        apply Subtype.ext
        change (a.2 : P) ^ p = 1
        rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h₂, one_zpow]))
    hcard f hf (H := ⊤) le_top
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact hrank

end CFSG
