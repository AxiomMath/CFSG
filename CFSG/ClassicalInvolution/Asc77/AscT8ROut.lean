module

public import CFSG.ClassicalInvolution.Asc77.AscE187Conj
public import CFSG.ClassicalInvolution.Asc77.AscT8RX

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.AscP1Nine3 CFSG.ClassicalInvolution.Asc77.T8
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

namespace T8R

section Pure

variable {G : Type} [Group G]

theorem exists_fourGroup {z t : G} (hz : z * z = 1) (ht : t * t = 1) (hz1 : z ≠ 1) (ht1 : t ≠ 1)
    (hzt : z ≠ t) (hc : z * t = t * z) :
    ∃ U : Subgroup G, IsElemAbelian2 U 2 ∧ z ∈ U ∧ t ∈ U ∧
      ∀ y ∈ U, y = 1 ∨ y = z ∨ y = t ∨ y = z * t := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have htz : t * z = z * t := hc.symm
  have hztz : z * t * z = t := by
    calc z * t * z = z * (t * z) := by rw [mul_assoc]
      _ = z * (z * t) := by rw [htz]
      _ = (z * z) * t := by rw [mul_assoc]
      _ = t := by rw [hz, one_mul]
  have hztt : z * t * t = z := by rw [mul_assoc, ht, mul_one]
  have hzzt : z * (z * t) = t := by rw [← mul_assoc, hz, one_mul]
  have htzt : t * (z * t) = z := by
    calc t * (z * t) = (t * z) * t := by rw [mul_assoc]
      _ = (z * t) * t := by rw [htz]
      _ = z := hztt
  have hzt2 : z * t * (z * t) = 1 := by
    calc z * t * (z * t) = (z * t * z) * t := by rw [mul_assoc (z * t) z t]
      _ = t * t := by rw [hztz]
      _ = 1 := ht
  have hzti : (z * t)⁻¹ = z * t := inv_eq_of_mul_eq_one_right hzt2
  have hzt1 : z * t ≠ 1 := by
    intro h
    have h' : z = t⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [hti] at h'
    exact hzt h'
  have hzzt' : z ≠ z * t := by
    intro h
    apply ht1
    exact (mul_left_cancel (a := z) (by rw [mul_one]; exact h)).symm
  have htzt' : t ≠ z * t := by
    intro h
    apply hz1
    exact (mul_right_cancel (b := t) (by rw [one_mul]; exact h)).symm
  let U : Subgroup G :=
    { carrier := {y | y = 1 ∨ y = z ∨ y = t ∨ y = z * t}
      mul_mem' := by
        intro a b ha hb
        rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
          simp only [Set.mem_ofPred_eq, one_mul, mul_one, hz, ht, hzt2, hztz, hztt, hzzt, htzt, htz,
            true_or, or_true]
      one_mem' := Or.inl rfl
      inv_mem' := by
        intro a ha
        rcases ha with rfl | rfl | rfl | rfl
        · simp
        · simp [hzi]
        · simp [hti]
        · simp [hzti] }
  have hset : (U : Set G) = {1, z, t, z * t} := by
    ext y
    simp [U]
  refine ⟨U, ⟨?_, ?_⟩, Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inl rfl)), fun y hy => hy⟩
  · show Nat.card ↥(U : Set G) = 2 ^ 2
    have h1 : (1 : G) ∉ ({z, t, z * t} : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hz1.symm, ht1.symm, hzt1.symm⟩
    have h2 : z ∉ ({t, z * t} : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hzt, hzzt'⟩
    rw [Nat.card_coe_set_eq, hset, Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
      Set.ncard_pair htzt']
    norm_num
  · intro x hx
    rcases hx with rfl | rfl | rfl | rfl
    · simp
    · exact hz
    · exact ht
    · exact hzt2

end Pure

section Cert

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem eq_one_of_mem_inf {P₁ P₂ : Subgroup G} {z₁ z₂ : G} (h₁ : IsUniqueInvolution P₁ z₁)
    (h₂ : IsUniqueInvolution P₂ z₂) (hne : z₁ ≠ z₂) (hP : IsPGroup 2 ↥P₁) {e : G} (he₁ : e ∈ P₁)
    (he₂ : e ∈ P₂) : e = 1 := by
  by_contra he1
  have hA2 : IsPGroup 2 ↥(P₁ ⊓ P₂) := hP.to_inf_left
  have hAne : P₁ ⊓ P₂ ≠ ⊥ := fun h => he1 (by
    have : e ∈ P₁ ⊓ P₂ := ⟨he₁, he₂⟩
    rw [h] at this
    exact Subgroup.mem_bot.mp this)
  have hcard : 2 ≤ Nat.card ↥(P₁ ⊓ P₂) := by
    have h1 : 1 ≤ Nat.card ↥(P₁ ⊓ P₂) := Nat.card_pos
    have h2 : Nat.card ↥(P₁ ⊓ P₂) ≠ 1 := fun h => hAne (Subgroup.card_eq_one.mp h)
    omega
  have hz₁A : z₁ ∈ P₁ ⊓ P₂ := T3.mem_of_isPGroup h₁ inf_le_left hA2 hcard
  rcases h₂.unique z₁ hz₁A.2 h₁.sq with h | h
  · exact h₁.ne_one h
  · exact hne h


theorem Std8.conj (hs : Std8 p f Ω K J S R T W z t) (n : G) :
    Std8 p f Ω (conjSub n K) (conjSub n J) (conjSylow n S) (conjSub n R) (conjSub n T)
      (conjSub n W) (n * z * n⁻¹) (n * t * n⁻¹) := by
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hcl := hΩ.conjInvariant
  have hmem : conjSub n K ∈ Ω := hcl n K hs.stand.mem
  refine ⟨⟨hs.stand.odd, hs.stand.five, hΩ, hs.stand.below, hs.stand.ih, hs.stand.aEmpty, hmem, ?_,
    hs.stand.gen⟩, ?_, hs.hz.conj n, omegaNbr_conj hcl hs.hJ n, hs.ht.conj n, ?_, ?_, ?_⟩
  · intro L hL
    obtain ⟨g, hg⟩ := hs.stand.trans L hL
    refine ⟨g * n⁻¹, ?_⟩
    rw [← conjSub_mul, inv_mul_cancel_right, hg]
  · exact fun K' hK' => T8.noTwins_of_mem hcl hs.stand.trans hs.noTwins hmem K' hK'
  · obtain ⟨hR, hRK, hRS⟩ := hs.hR
    refine ⟨RSet.conj hcl hR n, conjSub_mono hRK, ?_⟩
    rw [coe_conjSylow]
    exact conjSub_mono hRS
  · obtain ⟨hT, hTJ, hTS⟩ := hs.hT
    refine ⟨RSet.conj hcl hT n, conjSub_mono hTJ, ?_⟩
    rw [coe_conjSylow]
    exact conjSub_mono hTS
  · obtain ⟨hW, hWS, hWn⟩ := hs.hW
    refine ⟨WSet.conj hcl hW n, ?_, ?_⟩
    · rw [coe_conjSylow]
      exact conjSub_mono hWS
    · intro s hs'
      rw [coe_conjSylow, mem_conjSub_iff] at hs'
      have := hWn _ hs'
      calc conjSub s (conjSub n W) = conjSub n (conjSub (n⁻¹ * s * n) W) := by
            rw [← conjSub_mul, ← conjSub_mul]
            congr 1
            group
        _ = conjSub n W := by rw [this]

theorem eq_sup_oddCoreOf_conj (hΩ : HypOmegaMod p f Ω)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) (n : G) :
    omegaNbrGen Ω (conjSub n K) = conjSub n J ⊔ oddCoreOf (omegaNbrGen Ω (conjSub n K)) := by
  rw [omegaNbrGen_conjSub hΩ, oddCoreOf_conjSub_eq]
  conv_lhs => rw [hX]
  exact conjSub_sup n _ _

end Cert

end T8R

end CFSG.ClassicalInvolution.Asc77
