module

public import CFSG.CGT.PushingUpLit.LIT.Foote.L53A
public import CFSG.CGT.PushingUpLit.LIT.Foote.TheoremADef
public import CFSG.CGT.PushingUpLit.LIT.Foote.Top

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace CE

variable {M J : Subgroup G} (c : CE G M J)
include c

theorem endgame (hA : FooteTheoremA) {x z : G} {Ω Zg : Subgroup G}
    (hxne : rightConjugate J x ≠ J) (hxM : x ∈ M)
    (hzJ : z ∈ Subgroup.normalizer (J : Set G)) (hzx : z * x = x * z)
    (hZΩ : Ω ≤ Subgroup.normalizer (Zg : Set G)) (hzZ : z ∈ Zg) (hz1 : z ≠ 1)
    (hCΩ : ∀ u ∈ Zg, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ Ω)
    (hΔ : ∀ j ∈ J, j * (x⁻¹ * j * x) ∈ Ω) : J ≤ Ω := by
  classical
  have hJ := c.block
  have hcom : ∀ a ∈ J, ∀ b ∈ J, a * (x⁻¹ * b * x) = (x⁻¹ * b * x) * a := by
    intro a ha b hb
    have hcm := c.commutator_conj_eq_bot hxM hxne
    have hb' : x⁻¹ * b * x ∈ rightConjugate J x := by
      rw [mem_rightConjugate_iff]
      have e : x * (x⁻¹ * b * x) * x⁻¹ = b := by group
      rw [e]
      exact hb
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcm ha
    exact (Subgroup.mem_centralizer_iff.1 this _ hb').symm
  have hδmul : ∀ a ∈ J, ∀ b ∈ J,
      (a * b) * (x⁻¹ * (a * b) * x) = (a * (x⁻¹ * a * x)) * (b * (x⁻¹ * b * x)) := by
    intro a ha b hb
    have h1 := hcom b hb a ha
    calc a * b * (x⁻¹ * (a * b) * x) = a * (b * (x⁻¹ * a * x)) * (x⁻¹ * b * x) := by group
      _ = a * ((x⁻¹ * a * x) * b) * (x⁻¹ * b * x) := by rw [h1]
      _ = (a * (x⁻¹ * a * x)) * (b * (x⁻¹ * b * x)) := by group
  have hδinv : ∀ a ∈ J, a⁻¹ * (x⁻¹ * a⁻¹ * x) = (a * (x⁻¹ * a * x))⁻¹ := by
    intro a ha
    have hc : Commute a (x⁻¹ * a * x) := hcom a ha a ha
    calc a⁻¹ * (x⁻¹ * a⁻¹ * x) = a⁻¹ * (x⁻¹ * a * x)⁻¹ := by group
      _ = (x⁻¹ * a * x)⁻¹ * a⁻¹ := hc.inv_inv.eq
      _ = (a * (x⁻¹ * a * x))⁻¹ := (mul_inv_rev a (x⁻¹ * a * x)).symm
  have hconj : ∀ w : G, w * x = x * w → ∀ y : G,
      x⁻¹ * (w * y * w⁻¹) * x = w * (x⁻¹ * y * x) * w⁻¹ := by
    intro w hwx y
    have hc : Commute w x := hwx
    have h1 : x⁻¹ * w = w * x⁻¹ := hc.inv_right.eq.symm
    have h2 : w⁻¹ * x = x * w⁻¹ := hc.inv_left.eq
    calc x⁻¹ * (w * y * w⁻¹) * x = (x⁻¹ * w) * y * (w⁻¹ * x) := by group
      _ = (w * x⁻¹) * y * (x * w⁻¹) := by rw [h1, h2]
      _ = w * (x⁻¹ * y * x) * w⁻¹ := by group
  by_cases hcase : ∀ j ∈ J, z * (j * (x⁻¹ * j * x)) = (j * (x⁻¹ * j * x)) * z
  ·
    have hcent : ∀ j ∈ J, ∃ t ∈ J, (∀ k ∈ J, t * k = k * t) ∧ z * j * z⁻¹ = j * t := by
      intro j hj
      set a := z * j * z⁻¹ with ha
      have haJ : a ∈ J := (Subgroup.mem_normalizer_iff.1 hzJ j).1 hj
      have hδ : a * (x⁻¹ * a * x) = j * (x⁻¹ * j * x) := by
        have e1 : x⁻¹ * a * x = z * (x⁻¹ * j * x) * z⁻¹ := hconj z hzx j
        have e2 : a * (x⁻¹ * a * x) = z * (j * (x⁻¹ * j * x)) * z⁻¹ := by
          rw [e1, ha]
          group
        rw [e2, hcase j hj]
        group
      have hjt : j⁻¹ * a = x⁻¹ * (j * a⁻¹) * x := by
        calc j⁻¹ * a = j⁻¹ * (a * (x⁻¹ * a * x)) * (x⁻¹ * a * x)⁻¹ := by group
          _ = j⁻¹ * (j * (x⁻¹ * j * x)) * (x⁻¹ * a * x)⁻¹ := by rw [hδ]
          _ = x⁻¹ * (j * a⁻¹) * x := by group
      refine ⟨j⁻¹ * a, J.mul_mem (J.inv_mem hj) haJ, fun k hk => ?_, by rw [ha]; group⟩
      rw [hjt]
      exact (hcom k hk (j * a⁻¹) (J.mul_mem hj (J.inv_mem haJ))).symm
    have hfix : ∀ a ∈ J, ∀ b ∈ J, ⁅a, b⁆ * z = z * ⁅a, b⁆ := by
      intro a ha b hb
      obtain ⟨ta, haJ, hta, hza⟩ := hcent a ha
      obtain ⟨tb, hbJ, htb, hzb⟩ := hcent b hb
      have e : z * ⁅a, b⁆ * z⁻¹ = ⁅z * a * z⁻¹, z * b * z⁻¹⁆ := conjugate_commutatorElement a b z
      rw [hza, hzb, commutator_mul_central (hta b hb) (hta tb hbJ) (htb a ha)] at e
      calc ⁅a, b⁆ * z = (z * ⁅a, b⁆ * z⁻¹) * z := by rw [e]
        _ = z * ⁅a, b⁆ := by group
    have hJC : J ≤ Subgroup.centralizer ({z} : Set G) := by
      calc J = ⁅J, J⁆ := hJ.perfect.symm
        _ = Subgroup.closure {g | ∃ h₁ ∈ J, ∃ h₂ ∈ J, ⁅h₁, h₂⁆ = g} := Subgroup.commutator_def J J
        _ ≤ Subgroup.centralizer ({z} : Set G) := by
          rw [Subgroup.closure_le]
          rintro _ ⟨a, ha, b, hb, rfl⟩
          rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
          exact hfix a ha b hb
    exact hJC.trans (hCΩ z hzZ hz1)
  ·
    push Not at hcase
    obtain ⟨j₀, hj₀, hj₀ne⟩ := hcase
    have hzp : Subgroup.zpowers z ≤ Zg := Subgroup.zpowers_le.2 hzZ
    have hzpN : Subgroup.zpowers z ≤ Subgroup.normalizer (J : Set G) := Subgroup.zpowers_le.2 hzJ
    set A : Subgroup G := ⁅Subgroup.zpowers z, J⁆ with hAdef
    have hAJ : A ≤ J := by
      rw [hAdef, Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_left.1 hzpN
    have hJA : J ≤ Subgroup.normalizer (A : Set G) :=
      Subgroup.normalizer_commutator_ge_right (Subgroup.zpowers z) J
    have hAnc : ¬ A ≤ Subgroup.centralizer (J : Set G) := by
      intro hAc
      have h1 : ⁅A, J⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hAc
      have h2 : ⁅⁅J, Subgroup.zpowers z⁆, J⁆ = ⊥ := by
        rw [Subgroup.commutator_comm J (Subgroup.zpowers z)]
        exact h1
      have h3 : ⁅⁅J, J⁆, Subgroup.zpowers z⁆ = ⊥ :=
        Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := J) (H₂ := J)
          (H₃ := Subgroup.zpowers z) h2 h1
      rw [hJ.perfect] at h3
      have h4 : J ≤ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.1 h3
      have hzc : ∀ k ∈ J, z * k = k * z := fun k hk =>
        (Subgroup.mem_centralizer_iff.1 (h4 hk) z (Subgroup.mem_zpowers z))
      apply hj₀ne
      have hc1 := hzc j₀ hj₀
      have hc2 : z * (x⁻¹ * j₀ * x) = (x⁻¹ * j₀ * x) * z := by
        have hcz : Commute z x := hzx
        calc z * (x⁻¹ * j₀ * x) = (z * x⁻¹) * j₀ * x := by group
          _ = (x⁻¹ * z) * j₀ * x := by rw [hcz.inv_right.eq]
          _ = x⁻¹ * (z * j₀) * x := by group
          _ = x⁻¹ * (j₀ * z) * x := by rw [hc1]
          _ = x⁻¹ * j₀ * (z * x) := by group
          _ = x⁻¹ * j₀ * (x * z) := by rw [hzx]
          _ = (x⁻¹ * j₀ * x) * z := by group
      calc z * (j₀ * (x⁻¹ * j₀ * x)) = (z * j₀) * (x⁻¹ * j₀ * x) := by group
        _ = (j₀ * z) * (x⁻¹ * j₀ * x) := by rw [hc1]
        _ = j₀ * (z * (x⁻¹ * j₀ * x)) := by group
        _ = j₀ * ((x⁻¹ * j₀ * x) * z) := by rw [hc2]
        _ = (j₀ * (x⁻¹ * j₀ * x)) * z := by group
    have hVA : blockU J ≤ A := hJ.blockU_le_of_normal hAJ hJA hAnc
    have hδZ' : ∀ a, a ∈ Subgroup.closure {g | ∃ h₁ ∈ Subgroup.zpowers z, ∃ h₂ ∈ J, ⁅h₁, h₂⁆ = g} →
        a ∈ J ∧ a * (x⁻¹ * a * x) ∈ Zg := by
      intro a ha'
      induction ha' using Subgroup.closure_induction with
      | mem g hg =>
        obtain ⟨w, hw, j, hj, rfl⟩ := hg
        have hwJ : w * j * w⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 (hzpN hw) j).1 hj
        have hgJ : ⁅w, j⁆ ∈ J := by
          rw [commutatorElement_def]
          exact J.mul_mem hwJ (J.inv_mem hj)
        refine ⟨hgJ, ?_⟩
        have hwx : w * x = x * w := by
          obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
          exact ((Commute.zpow_left (show Commute z x from hzx) i).eq)
        have hδj : j * (x⁻¹ * j * x) ∈ Ω := hΔ j hj
        have e : ⁅w, j⁆ * (x⁻¹ * ⁅w, j⁆ * x) = ⁅w, j * (x⁻¹ * j * x)⁆ := by
          have e1 := hδmul (w * j * w⁻¹) hwJ j⁻¹ (J.inv_mem hj)
          have e2 := hδinv j hj
          have e3 := hconj w hwx j
          rw [commutatorElement_def, commutatorElement_def, e1, e2, e3]
          group
        rw [e, commutatorElement_def]
        have hy : (j * (x⁻¹ * j * x)) * w⁻¹ * (j * (x⁻¹ * j * x))⁻¹ ∈ Zg :=
          (Subgroup.mem_normalizer_iff.1 (hZΩ hδj) w⁻¹).1 (Zg.inv_mem (hzp hw))
        have := Zg.mul_mem (hzp hw) hy
        simpa [mul_assoc] using this
      | one => exact ⟨J.one_mem, by simp⟩
      | mul a b _ _ haI hbI =>
        obtain ⟨haJ, haZ⟩ := haI
        obtain ⟨hbJ, hbZ⟩ := hbI
        refine ⟨J.mul_mem haJ hbJ, ?_⟩
        rw [hδmul a haJ b hbJ]
        exact Zg.mul_mem haZ hbZ
      | inv a _ haI =>
        obtain ⟨haJ, haZ⟩ := haI
        refine ⟨J.inv_mem haJ, ?_⟩
        rw [hδinv a haJ]
        exact Zg.inv_mem haZ
    have hδZ : ∀ a ∈ A, a ∈ J ∧ a * (x⁻¹ * a * x) ∈ Zg := fun a ha => hδZ' a (by
      rw [hAdef, Subgroup.commutator_def] at ha
      exact ha)
    have hgen : ∀ j ∈ J, (∃ n : ℕ, j ^ 2 ^ n = 1) →
        j * j ∈ Subgroup.centralizer (blockU J : Set G) → j ∈ Ω := by
      intro j hj hj2 hjj
      obtain ⟨a', ha'V, ha'j, k, hk, hak⟩ := hA G J hJ j (Subgroup.le_normalizer hj) hj2 hjj
      have ha'A : a' ∈ A := hVA ha'V
      have ha'J : a' ∈ J := hAJ ha'A
      obtain ⟨-, hu⟩ := hδZ a' ha'A
      have hu1 : a' * (x⁻¹ * a' * x) ≠ 1 := by
        intro h1
        apply hak
        have h2 : a' = x⁻¹ * a'⁻¹ * x := by
          calc a' = (x⁻¹ * a' * x)⁻¹ := by
                rw [← mul_eq_one_iff_eq_inv] at *
                exact by simpa using h1.symm ▸ rfl
            _ = x⁻¹ * a'⁻¹ * x := by group
        rw [h2]
        have := hcom k hk a'⁻¹ (J.inv_mem ha'J)
        exact this.symm
      have hjc : j ∈ Subgroup.centralizer ({a' * (x⁻¹ * a' * x)} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 := hcom j hj a' ha'J
        calc j * (a' * (x⁻¹ * a' * x)) = (j * a') * (x⁻¹ * a' * x) := by group
          _ = (a' * j) * (x⁻¹ * a' * x) := by rw [ha'j]
          _ = a' * (j * (x⁻¹ * a' * x)) := by group
          _ = a' * ((x⁻¹ * a' * x) * j) := by rw [h1]
          _ = (a' * (x⁻¹ * a' * x)) * j := by group
      exact hCΩ _ hu hu1 hjc
    calc J ≤ Subgroup.closure {j | j ∈ J ∧ (∃ n : ℕ, j ^ 2 ^ n = 1) ∧
          j * j ∈ Subgroup.centralizer (blockU J : Set G)} := hJ.le_closure_twoElements
      _ ≤ Ω := (Subgroup.closure_le Ω).2 fun j hj => hgen j hj.1 hj.2.1 hj.2.2

end CE

end CFSG.CGT.PushingUpLit.LIT.Foote
