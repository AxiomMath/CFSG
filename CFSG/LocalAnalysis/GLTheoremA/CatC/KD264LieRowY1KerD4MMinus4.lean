module

public import CFSG.GH74.Generic.S1.Exo.HermOddStructure
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusExtraction

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KD4

open Module QuadraticMap CFSG.GroupTheory.WeirSylow CFSG.GH74.Generic.S1.Exo
open scoped commutatorElement

noncomputable section

section Arith

theorem three_not_dvd_card {K : Type} [Field K] [Finite K] (h3 : (3 : K) ≠ 0) :
    ¬ 3 ∣ Nat.card K := by
  intro hdvd
  haveI := Fintype.ofFinite K
  haveI : Fact (Nat.Prime (ringChar K)) := ⟨CharP.char_is_prime K (ringChar K)⟩
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K (ringChar K)
  rw [Nat.card_eq_fintype_card, hcard] at hdvd
  have h3p : 3 ∣ ringChar K := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  have heq : 3 = ringChar K := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h3p
  apply h3
  have hc : ((3 : ℕ) : K) = 0 := by
    rw [heq]
    exact CharP.cast_eq_zero K (ringChar K)
  simpa using hc

theorem three_dvd_card_pow_four_sub_one {K : Type} [Field K] [Finite K] (h3 : (3 : K) ≠ 0) :
    3 ∣ Nat.card K ^ 4 - 1 := by
  have hq : ¬ 3 ∣ Nat.card K := three_not_dvd_card h3
  have h4 : Nat.card K ^ 4 % 3 = 1 := by
    have h1 : Nat.card K % 3 = 1 ∨ Nat.card K % 3 = 2 := by omega
    rw [Nat.pow_mod]
    rcases h1 with h1 | h1 <;> rw [h1]
  have : 1 ≤ Nat.card K ^ 4 := Nat.one_le_pow _ _ Nat.card_pos
  omega

end Arith

section Comm

theorem conj_mem_commutator {G : Type*} [Group G] {O : Subgroup G} {g : G} (hg : g ∈ O) {n : G}
    (hn : n ∈ ⁅O, O⁆) : g * n * g⁻¹ ∈ ⁅O, O⁆ := by
  set ψ : G →* G := (MulAut.conj g).toMonoidHom with hψ
  have hle : O.map ψ ≤ O := by
    rintro _ ⟨h, hh, rfl⟩
    exact O.mul_mem (O.mul_mem hg hh) (O.inv_mem hg)
  have hmap := Subgroup.map_commutator O O ψ
  have : ψ n ∈ ⁅O.map ψ, O.map ψ⁆ := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem ψ hn
  exact Subgroup.commutator_mono hle hle this

theorem commutator_le_self {G : Type*} [Group G] (O : Subgroup G) : ⁅O, O⁆ ≤ O := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact O.mul_mem (O.mul_mem (O.mul_mem ha hb) (O.inv_mem ha)) (O.inv_mem hb)

theorem mem_commutator_of_perfect {G : Type*} [Group G] {H : Subgroup G}
    (hp : Group.IsPerfect H) {n : G} (hn : n ∈ H) : n ∈ ⁅H, H⁆ := by
  rw [Subgroup.isPerfect_iff.1 hp]
  exact hn

theorem not_comm_of_perfect {H : Type*} [Group H] [Nontrivial H] (hp : Group.IsPerfect H) :
    ¬ ∀ x y : H, x * y = y * x := by
  intro hc
  haveI : IsMulCommutative H := ⟨⟨hc⟩⟩
  exact Group.IsPerfect.not_isMulCommutative H inferInstance

end Comm

section Minus4

variable {K : Type} [Field K] [Finite K] {U : Type} [AddCommGroup U] [Module K U]

theorem minus4_char2 [CharP K 2] (h3 : (3 : K) ≠ 0) (hdim : finrank K U = 4)
    (Q : QuadraticForm K U) (hnd : (polarBilin Q).Nondegenerate) (hnp : ¬ IsPlusType Q) :
    ∃ N : Subgroup (U ≃ₗ[K] U), N ≤ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      (∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, ∀ n ∈ N, g * n * g⁻¹ ∈ N) ∧
      IsSimpleGroup N ∧ Group.IsPerfect N ∧ (¬ ∀ x y : N, x * y = y * x) ∧ 3 ∣ Nat.card N := by
  haveI : FiniteDimensional K U := Module.finite_of_finrank_eq_succ hdim
  have hts : ∀ U' : Submodule K U, finrank K U' = finrank K U / 2 → ∃ u ∈ U', Q u ≠ 0 := by
    intro U' hU'
    by_contra hcon
    push Not at hcon
    exact hnp ⟨U', by omega, fun x hx => hcon x hx⟩
  obtain ⟨hs, hp, hna, -, -, h4, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction Q hnd (Or.inl hdim) hts
  obtain ⟨E, _, _, D, ψ, ρ, -, -, -, hrange, hcard⟩ := h4 hdim
  refine ⟨⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆,
    commutator_le_self _, fun g hg n hn => conj_mem_commutator hg hn, hs, hp, hna, ?_⟩
  have hc : Nat.card ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ = Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) := by
    rw [← hrange]
    exact hcard
  rw [hc]
  exact Dvd.dvd.mul_left (three_dvd_card_pow_four_sub_one h3) _

theorem minus4_odd (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (hdim : finrank K U = 4)
    (Q : QuadraticForm K U) (hnd : (polarBilin Q).Nondegenerate) (hnp : ¬ IsPlusType Q) :
    ∃ N : Subgroup (U ≃ₗ[K] U), N ≤ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      (∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, ∀ n ∈ N, g * n * g⁻¹ ∈ N) ∧
      IsSimpleGroup N ∧ Group.IsPerfect N ∧ (¬ ∀ x y : N, x * y = y * x) ∧ 3 ∣ Nat.card N := by
  obtain ⟨E, _, _, hcardE, Ω, hΩle, hΩs, hΩp, hΩcard, -, hneg, hnegΩ, hdec⟩ :=
    soForm_minus_four_structure h2 hdim Q hnd hnp
  have hΩO : Ω ≤ TauCeti.QuadraticMap.orthogonalGroup Q := fun x hx => (hΩle hx).1
  have hcen : ∀ g : U ≃ₗ[K] U, LinearEquiv.neg K * g = g * LinearEquiv.neg K := by
    intro g
    ext v
    simp
  have hcommute : ∀ g : U ≃ₗ[K] U, Commute (LinearEquiv.neg K) g := fun g => hcen g
  have key1 : ∀ (x y : U ≃ₗ[K] U), ⁅LinearEquiv.neg K * x, y⁆ = ⁅x, y⁆ := by
    intro x y
    have h1 : ⁅LinearEquiv.neg K * x, y⁆ =
        (LinearEquiv.neg K * (x * y * x⁻¹) * (LinearEquiv.neg K)⁻¹) * y⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [h1, (hcommute (x * y * x⁻¹)).mul_inv_cancel, commutatorElement_def]
  have key2 : ∀ (x y : U ≃ₗ[K] U), ⁅x, LinearEquiv.neg K * y⁆ = ⁅x, y⁆ := by
    intro x y
    have h1 : ⁅x, LinearEquiv.neg K * y⁆ =
        (x * LinearEquiv.neg K * x⁻¹) * (x * y * x⁻¹ * y⁻¹) * (LinearEquiv.neg K)⁻¹ := by
      rw [commutatorElement_def]
      group
    have h2 : x * LinearEquiv.neg K * x⁻¹ = LinearEquiv.neg K := by
      rw [← hcen x, mul_assoc, mul_inv_cancel, mul_one]
    rw [h1, h2, (hcommute (x * y * x⁻¹ * y⁻¹)).mul_inv_cancel, commutatorElement_def]
  have hcommΩ : ⁅soForm Q, soForm Q⁆ ≤ Ω := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rcases hdec a ha with h | h <;> rcases hdec b hb with h' | h'
    · exact Ω.mul_mem (Ω.mul_mem (Ω.mul_mem h h') (Ω.inv_mem h)) (Ω.inv_mem h')
    · rw [← key2 a b]
      exact Ω.mul_mem (Ω.mul_mem (Ω.mul_mem h h') (Ω.inv_mem h)) (Ω.inv_mem h')
    · rw [← key1 a b]
      exact Ω.mul_mem (Ω.mul_mem (Ω.mul_mem h h') (Ω.inv_mem h)) (Ω.inv_mem h')
    · rw [← key1 a b, ← key2 (LinearEquiv.neg K * a) b]
      exact Ω.mul_mem (Ω.mul_mem (Ω.mul_mem h h') (Ω.inv_mem h)) (Ω.inv_mem h')
  refine ⟨Ω, hΩO, fun g hg n hn => ?_, hΩs, hΩp, ?_, ?_⟩
  · set ψ : (U ≃ₗ[K] U) →* (U ≃ₗ[K] U) := (MulAut.conj g).toMonoidHom with hψ
    have hle : Ω.map ψ ≤ soForm Q := by
      rintro _ ⟨m, hm, rfl⟩
      have hmS := hΩle hm
      rw [mem_soForm_iff] at hmS
      show g * m * g⁻¹ ∈ soForm Q
      rw [mem_soForm_iff]
      refine ⟨fun v => ?_, ?_⟩
      · have e1 : (g * m * g⁻¹) v = g (m (g⁻¹ v)) := rfl
        rw [e1, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg,
          hmS.1, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (inv_mem hg)]
      · rw [map_mul, map_mul, hmS.2, mul_one, map_inv, mul_inv_cancel]
    have hmem : ψ n ∈ ⁅Ω.map ψ, Ω.map ψ⁆ := by
      rw [← Subgroup.map_commutator]
      exact Subgroup.mem_map_of_mem ψ (mem_commutator_of_perfect hΩp hn)
    exact hcommΩ (Subgroup.commutator_mono hle hle hmem)
  · haveI := hΩs.toNontrivial
    exact not_comm_of_perfect hΩp
  · have h3d : 3 ∣ Nat.card Ω * 2 := by
      rw [hΩcard]
      exact Dvd.dvd.mul_left (three_dvd_card_pow_four_sub_one h3) _
    exact (Nat.Coprime.dvd_of_dvd_mul_right (by norm_num : Nat.Coprime 3 2) h3d)

theorem minus4_component (h3 : (3 : K) ≠ 0) (hdim : finrank K U = 4) (Q : QuadraticForm K U)
    (hnd : (polarBilin Q).Nondegenerate) (hnp : ¬ IsPlusType Q) :
    ∃ N : Subgroup (U ≃ₗ[K] U), N ≤ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      (∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, ∀ n ∈ N, g * n * g⁻¹ ∈ N) ∧
      IsSimpleGroup N ∧ Group.IsPerfect N ∧ (¬ ∀ x y : N, x * y = y * x) ∧ 3 ∣ Nat.card N := by
  by_cases h2 : (2 : K) = 0
  · haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    exact minus4_char2 h3 hdim Q hnd hnp
  · exact minus4_odd h2 h3 hdim Q hnd hnp

end Minus4

end


end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KD4

end
