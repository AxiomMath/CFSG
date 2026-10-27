module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L58B
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XLemma25
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L56J

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem frattini_ne_bot_of_mul_self_ne {P : Subgroup G} (hP : IsPGroup 2 P) {x : G}
    (hx : x ∈ P) (hxx : x * x ≠ 1) : frattini P ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 P) := ⟨hP⟩
  intro h
  have h1 := CFSG.pth_power_mem_frattini_of_isPGroup (R := P) (p := 2) ⟨x, hx⟩
  rw [h, mem_bot] at h1
  apply hxx
  have := congrArg Subtype.val h1
  simpa [pow_two] using this

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
include h

theorem exists_mul_self_ne_one_Q (hQ : 4 < Nat.card Q) : ∃ q ∈ Q, q * q ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hsq
  push Not at hsq
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.isPGroup_Q
  have hk3 : 3 ≤ k := by
    by_contra hk3
    push Not at hk3
    have h1 : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hk] at h1
    omega
  have hE : CFSG.Open.IsElemAbelian 2 (⊤ : Subgroup Q) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun a _ => Subtype.ext ?_⟩
    · exact commute_of_sq_eq_one hsq (a : Q).2 (b : Q).2
    · rw [SubgroupClass.coe_pow, OneMemClass.coe_one, sq]
      exact hsq _ a.2
  have h1 := SectionRank.le_pRank one_lt_two (le_refl (⊤ : Subgroup Q)) hE
    (by rw [Subgroup.card_top, hk])
  rw [← SectionRank.pRank_eq_open_pRank_top, h.pRank_Q] at h1
  omega

theorem lemma58 (hQ : 4 < Nat.card Q) {g g' : G} (hg : g ∈ T) (hg' : g' ∈ T)
    (hne : conjugate Q g ≠ conjugate Q g') :
    conjugate Q g ⊓ conjugate Q g' = ⊥ ∧
      ∀ a ∈ conjugate Q g, ∀ b ∈ conjugate Q g', a * b = b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hconjT : ∀ x ∈ T, conjugate Q x ≤ T := fun x hx y hy => by
    have h1 := h.ST (h.QS (mem_conjugate_iff.mp hy))
    rw [show y = x⁻¹ * (x * y * x⁻¹) * x by group]
    exact mul_mem (mul_mem (inv_mem hx) h1) hx
  have hcc : ∀ x y : G, conjugate (conjugate Q x) y = conjugate Q (x * y) := fun x y => by
    ext a
    rw [mem_conjugate_iff, mem_conjugate_iff, mem_conjugate_iff,
      show x * y * a * (x * y)⁻¹ = x * (y * a * y⁻¹) * x⁻¹ by group]
  have hTI : ∀ x ∈ T, ∀ y ∈ T, conjugate Q x ≠ conjugate Q y →
      conjugate Q x ⊓ conjugate Q y = ⊥ := by
    intro x hx y hy hxy
    have hne' : conjugate Q (y * x⁻¹) ≠ Q := fun h1 => hxy (by
      have h2 : conjugate Q y = conjugate Q x := by
        rw [show y = y * x⁻¹ * x by group, ← hcc, h1]
      exact h2.symm)
    have h1 := h.inf_conjugate_Q_eq_bot_of_ne (mul_mem hy (inv_mem hx)) hne'
    rw [eq_bot_iff]
    intro a ha
    have h2 : x * a * x⁻¹ ∈ Q ⊓ conjugate Q (y * x⁻¹) := by
      refine mem_inf.mpr ⟨mem_conjugate_iff.mp (mem_inf.mp ha).1, ?_⟩
      rw [mem_conjugate_iff, show y * x⁻¹ * (x * a * x⁻¹) * (y * x⁻¹)⁻¹ = y * a * y⁻¹ by group]
      exact mem_conjugate_iff.mp (mem_inf.mp ha).2
    rw [h1, mem_bot] at h2
    rw [mem_bot]
    calc a = x⁻¹ * (x * a * x⁻¹) * x := by group
      _ = 1 := by rw [h2]; group
  refine ⟨hTI g hg g' hg' hne, ?_⟩
  set Δ : Set (Subgroup G) := {R | ∃ x ∈ T, R = conjugate Q x} with hΔ
  have hcomm := Asc76X.lemma25 (S := T) (Δ := Δ) h.sylT.isPGroup
    (fun R hR => by
      obtain ⟨x, hx, rfl⟩ := hR
      exact hconjT x hx)
    (fun R hR s hs => by
      obtain ⟨x, hx, rfl⟩ := hR
      exact ⟨x * s, mul_mem hx hs, hcc x s⟩)
    (fun R hR R' hR' => by
      obtain ⟨x, -, rfl⟩ := hR
      obtain ⟨y, -, rfl⟩ := hR'
      rw [card_conjugate_eq_card, card_conjugate_eq_card])
    (fun R hR => by
      obtain ⟨x, hx, rfl⟩ := hR
      obtain ⟨q, hq, hqq⟩ := h.exists_mul_self_ne_one_Q hQ
      refine frattini_ne_bot_of_mul_self_ne (h.sylT.isPGroup.to_le (hconjT x hx))
        (x := x⁻¹ * q * x) (by rw [mem_conjugate_iff]; group; exact hq) fun h1 => hqq ?_
      calc q * q = x * (x⁻¹ * q * x * (x⁻¹ * q * x)) * x⁻¹ := by group
        _ = 1 := by rw [h1]; group)
    (fun R hR R' hR' hRR' => by
      obtain ⟨x, hx, rfl⟩ := hR
      obtain ⟨y, hy, rfl⟩ := hR'
      exact hTI x hx y hy hRR')
    _ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩ hne
  intro a ha b hb
  have h1 : ⁅a, b⁆ ∈ ⁅conjugate Q g, conjugate Q g'⁆ := commutator_mem_commutator ha hb
  rw [hcomm, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

end Sec5

end CFSG.ComponentClassification.Foote5
