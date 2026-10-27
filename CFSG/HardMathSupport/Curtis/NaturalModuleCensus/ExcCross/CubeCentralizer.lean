module

public import CFSG.HardMathSupport.Malle.Proving.E27FixedCube
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

open CFSG.HardMathSupport.Malle.Proving

theorem dvd81_card_inf_centralizer_of_cube {G : Type} [Group G] [Finite G] {P V : Subgroup G}
    (hP : IsPGroup 3 P) (hVP : V ≤ P)
    (hVn : ∀ p ∈ P, ∀ v ∈ V, p * v * p⁻¹ ∈ V)
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hV3 : ∀ a ∈ V, a ^ 3 = 1)
    (hcard : 3 ^ 7 ≤ Nat.card V) {s : G} (hsP : s ∈ P) (hs : s ^ 3 = 1) :
    81 ∣ Nat.card (P ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C : Subgroup G := Subgroup.centralizer ({s} : Set G) with hC
  have hmemC : ∀ g, g ∈ C ↔ g * s = s * g := fun g => by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
  have hcube : 3 ^ 7 ≤ Nat.card (V ⊓ C : Subgroup G) ^ 3 := by
    refine hcard.trans ?_
    have hAc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := hVc
    exact card_le_card_inf_centralizer_cube hAc hV3 hs (fun a ha => hVn s hsP a ha)
  have hAP : IsPGroup 3 (V ⊓ C : Subgroup G) := hP.to_le (inf_le_left.trans hVP)
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp hAP
  have ha3 : 3 ≤ a := by
    by_contra hlt
    rw [not_le] at hlt
    rw [ha, ← pow_mul] at hcube
    have : 3 ^ (a * 3) ≤ 3 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h7 : 3 ^ 7 ≤ 3 ^ 6 := hcube.trans this
    omega
  have hVP' : IsPGroup 3 V := hP.to_le hVP
  by_cases hsV : s ∈ V
  · have hle : V ≤ P ⊓ C := fun v hv => ⟨hVP hv, (hmemC v).mpr (hVc v hv s hsV)⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hVP'
    have hn7 : 7 ≤ n := by
      by_contra hlt
      rw [not_le] at hlt
      rw [hn] at hcard
      have : 3 ^ n ≤ 3 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h7 : 3 ^ 7 ≤ 3 ^ 6 := hcard.trans this
      omega
    have h81 : 81 ∣ Nat.card V := by
      rw [hn]
      have : (3 : ℕ) ^ 4 ∣ 3 ^ n := pow_dvd_pow 3 (by omega)
      simpa using this
    exact h81.trans (Subgroup.card_dvd_of_le hle)
  · set B : Subgroup G := (V ⊓ C) ⊔ Subgroup.zpowers s with hB
    have hzC : Subgroup.zpowers s ≤ C := by
      rw [Subgroup.zpowers_le]
      exact (hmemC s).mpr rfl
    have hzP : Subgroup.zpowers s ≤ P := by
      rw [Subgroup.zpowers_le]
      exact hsP
    have hBle : B ≤ P ⊓ C :=
      sup_le (fun g hg => ⟨hVP hg.1, hg.2⟩) (fun g hg => ⟨hzP hg, hzC hg⟩)
    have hAB : (V ⊓ C : Subgroup G) ≤ B := le_sup_left
    have hsB : s ∈ B := Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
    have hBP : IsPGroup 3 B := hP.to_le (hBle.trans inf_le_left)
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card).mp hBP
    have hdvd : Nat.card (V ⊓ C : Subgroup G) ∣ Nat.card B := Subgroup.card_dvd_of_le hAB
    rw [ha, hb] at hdvd
    have hab : a ≤ b := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
    have hne : a ≠ b := by
      intro hab'
      subst hab'
      have hcardeq : Nat.card (V ⊓ C : Subgroup G) = Nat.card B := by rw [ha, hb]
      have heq : (V ⊓ C : Subgroup G) = B :=
        Subgroup.eq_of_le_of_card_ge hAB (le_of_eq hcardeq.symm)
      have : s ∈ (V ⊓ C : Subgroup G) := heq ▸ hsB
      exact hsV this.1
    have hb4 : 4 ≤ b := by omega
    have h81 : 81 ∣ Nat.card B := by
      rw [hb]
      have : (3 : ℕ) ^ 4 ∣ 3 ^ b := pow_dvd_pow 3 hb4
      simpa using this
    exact h81.trans (Subgroup.card_dvd_of_le hBle)

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross
