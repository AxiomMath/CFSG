module

public import CFSG.LieType.BorelTits.LeviQuotient
public import CFSG.LieType.BorelTits.LeviBound
public import CFSG.LieType.BorelTits.LeviOrder
public import CFSG.LieType.BorelTits.UnitaryForm

public section

namespace CFSG.LieType.BorelTits

open CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Curtis.UnitaryLevi

theorem map_parabolic_clauses {G G' : Type*} [Group G] [Group G'] [Finite G] (π : G →* G')
    (hπ : Function.Surjective π) {p : ℕ} {A₀ P₀ O₀ : Subgroup G} {A : Subgroup G'}
    (hA : A₀.map π = A)
    (hN : Subgroup.normalizer (A₀ : Set G) = (Subgroup.normalizer (A : Set G')).comap π)
    (hOP : O₀ ≤ P₀) (hAO : A₀ ≤ O₀) (hO : IsPGroup p O₀)
    (hPO : P₀ ≤ Subgroup.normalizer (O₀ : Set G))
    (hNP : Subgroup.normalizer (A₀ : Set G) ≤ P₀) :
    O₀.map π ≤ P₀.map π ∧ A ≤ O₀.map π ∧ IsPGroup p (O₀.map π) ∧
      (∀ x ∈ P₀.map π, ∀ o ∈ O₀.map π, x * o * x⁻¹ ∈ O₀.map π) ∧
      ∀ g : G', (∀ a ∈ A, g * a * g⁻¹ ∈ A) → g ∈ P₀.map π := by
  haveI : Finite G' := Finite.of_surjective π hπ
  refine ⟨Subgroup.map_mono hOP, ?_, IsPGroup.map hO π, ?_, ?_⟩
  · rw [← hA]
    exact Subgroup.map_mono hAO
  · rintro x hx o ho
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
    have hxN : π g ∈ Subgroup.normalizer (O₀.map π : Set G') :=
      Subgroup.le_normalizer_map (H := O₀) π (Subgroup.mem_map_of_mem π (hPO hg))
    exact (Subgroup.mem_normalizer_iff.mp hxN o).1 ho
  · intro g hg
    have hgN : g ∈ Subgroup.normalizer (A : Set G') :=
      Subgroup.mem_normalizer_fintype fun a ha => hg a ha
    obtain ⟨g₀, rfl⟩ := hπ g
    have hg₀N : g₀ ∈ Subgroup.normalizer (A₀ : Set G) := by
      rw [hN, Subgroup.mem_comap]
      exact hgN
    exact Subgroup.mem_map_of_mem π (hNP hg₀N)

theorem card_dvd_of_le_map {G G' : Type*} [Group G] [Group G'] [Finite G] (π : G →* G')
    {P₀ O₀ : Subgroup G} {X : ℕ}
    (hX : ∀ T ≤ P₀, Nat.card ↥⁅T, T⁆ ∣ Nat.card ↥(⁅T, T⁆ ⊓ O₀) * X)
    {S : Subgroup G'} (hSP : S ≤ P₀.map π) (hS : commutator ↥S = ⊤) :
    Nat.card S ∣ Nat.card ↥(S ⊓ O₀.map π) * X := by
  let T : Subgroup G := S.comap π ⊓ P₀
  have hT : T ≤ P₀ := inf_le_right
  have hmap : T.map π = S := by
    ext y
    constructor
    · rintro ⟨x, ⟨hxS, hxP⟩, rfl⟩
      exact hxS
    · intro hy
      obtain ⟨x, hxP, hxy⟩ := Subgroup.mem_map.mp (hSP hy)
      exact Subgroup.mem_map.mpr
        ⟨x, ⟨by simpa [Subgroup.mem_comap, hxy] using hy, hxP⟩, hxy⟩
  have hc : commutator ↥(T.map π) = ⊤ := by
    rw [hmap]
    exact hS
  have h := card_map_dvd_card_inf_map_mul π (hX T hT) hc
  rwa [hmap] at h

theorem unitaryForm_σ_apply {p f : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K]
    [CharP K p] (hUF : UnitaryFieldData p f K) (hK : Nat.card K = (p ^ f) ^ 2) (n : ℕ) (c : K) :
    (unitaryForm p f hK n).σ c = hUF.bar c := by
  change unitaryInvolution K p f c = hUF.bar c
  rw [unitaryInvolution_apply, hUF.bar_apply]

theorem unitaryForm_bar_β {p f : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K]
    [CharP K p] (hUF : UnitaryFieldData p f K) (hK : Nat.card K = (p ^ f) ^ 2) (n : ℕ)
    (u v : Fin n → K) :
    hUF.bar ((unitaryForm p f hK n).β u v) = (unitaryForm p f hK n).β v u := by
  have hbar : ∀ c : K, hUF.bar c = unitaryInvolution K p f c := by
    intro c
    rw [hUF.bar_apply, unitaryInvolution_apply]
  rw [unitaryForm_β, unitaryForm_β, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, hbar, hbar, unitaryInvolution_involutive hK, mul_comm]

theorem one_le_finrank_isoSeq_one_statedSU {p f n : ℕ} [Fact p.Prime] {K : Type} [Field K]
    [Finite K] [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2)
    {A₀ : Subgroup ↥(StatedSU n (p ^ f) K)} (hA₀ : IsPGroup p A₀) (hne : A₀ ≠ ⊥) :
    1 ≤ Module.finrank K
      (isoSeq (unitaryForm p f hK n) (natRep (StatedSU n (p ^ f) K)) A₀ 1) := by
  rw [Submodule.one_le_finrank_iff]
  exact isoSeq_one_ne_bot (unitaryForm p f hK n) (natRep (StatedSU n (p ^ f) K)) p
    (isIsometric_natRep_statedSU hK n) (natRep_injective _) A₀ hA₀ hne

theorem levi_su6_arith_two (q : ℕ) :
    q ^ 2 * ((q ^ 2) ^ 2 - 1) * (q * (q ^ 2 - 1)) =
      q ^ 3 * (q ^ 2 - 1) * (q ^ 4 - 1) := by
  rw [show (q ^ 2) ^ 2 = q ^ 4 by rw [← pow_mul]]
  ring

theorem levi_su6_arith_three (q : ℕ) :
    (q ^ 2) ^ 3 * ((q ^ 2) ^ 2 - 1) * ((q ^ 2) ^ 3 - 1) * 1 =
      q ^ 6 * (q ^ 4 - 1) * (q ^ 6 - 1) := by
  have h2 : (q ^ 2) ^ 2 = q ^ 4 := by rw [← pow_mul]
  have h3 : (q ^ 2) ^ 3 = q ^ 6 := by rw [← pow_mul]
  rw [h2, h3]
  ring

theorem exists_levi_bound_statedSU6 {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hUF : UnitaryFieldData 2 f K) (hK : Nat.card K = (2 ^ f) ^ 2)
    (A₀ : Subgroup ↥(StatedSU 6 (2 ^ f) K)) (hA₀ : IsPGroup 2 A₀) (hne : A₀ ≠ ⊥) :
    ∃ X : ℕ,
      (X = (2 ^ f) ^ 6 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) *
          ((2 ^ f) ^ 4 - 1) ∨
        X = (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1) ∨
        X = (2 ^ f) ^ 6 * ((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 6 - 1)) ∧
      ∀ T ≤ flagStab (natRep (StatedSU 6 (2 ^ f) K))
          (isoFlag (unitaryForm 2 f hK 6) (natRep (StatedSU 6 (2 ^ f) K)) A₀),
        Nat.card ↥⁅T, T⁆ ∣
          Nat.card ↥(⁅T, T⁆ ⊓ flagKernel (natRep (StatedSU 6 (2 ^ f) K))
            (isoFlag (unitaryForm 2 f hK 6) (natRep (StatedSU 6 (2 ^ f) K)) A₀)) * X := by
  let F := unitaryForm 2 f hK 6
  let ρ := natRep (StatedSU 6 (2 ^ f) K)
  have hρ : IsIsometric F ρ := isIsometric_natRep_statedSU hK 6
  have hW : F.IsTotallyIsotropic (isoSeq F ρ A₀ 1) := isoSeq_isTotallyIsotropic F ρ A₀ 1
  have hdim : Module.finrank K (PieceQ (isoSeq F ρ A₀ 1) (F.perp (isoSeq F ρ A₀ 1))) +
      2 * Module.finrank K (isoSeq F ρ A₀ 1) = 6 := by
    rw [finrank_pieceQ_perp F hW, Module.finrank_fin_fun]
  have hj1 : 1 ≤ Module.finrank K (isoSeq F ρ A₀ 1) :=
    one_le_finrank_isoSeq_one_statedSU hK hA₀ hne
  have hj3 : Module.finrank K (isoSeq F ρ A₀ 1) ≤ 3 := by omega
  have hB : (perpForm F hUF.bar (unitaryForm_σ_apply hUF hK 6)
      (isoSeq F ρ A₀ 1) hW).IsSymm :=
    perpForm_isSymm F hUF.bar (unitaryForm_σ_apply hUF hK 6) hW
      (unitaryForm_bar_β hUF hK 6)
  have hBl : (perpForm F hUF.bar (unitaryForm_σ_apply hUF hK 6)
      (isoSeq F ρ A₀ 1) hW).SeparatingLeft :=
    perpForm_separatingLeft F hUF.bar (unitaryForm_σ_apply hUF hK 6) hW
  have hjmem : Module.finrank K (isoSeq F ρ A₀ 1) = 1 ∨
      Module.finrank K (isoSeq F ρ A₀ 1) = 2 ∨
      Module.finrank K (isoSeq F ρ A₀ 1) = 3 := by omega
  rcases hjmem with hj | hj | hj
  · have hn : Module.finrank K (PieceQ (isoSeq F ρ A₀ 1)
        (F.perp (isoSeq F ρ A₀ 1))) = 4 := by omega
    refine ⟨_, Or.inl rfl, ?_⟩
    intro T hT
    have hlevi := card_commutator_dvd_levi F ρ hρ A₀ hUF.bar
      (unitaryForm_σ_apply hUF hK 6) hT
    rw [card_ker_det_eq (N := PieceQ ⊥ (isoSeq F ρ A₀ 1)), finrank_pieceQ_bot, hj,
      card_specialLinearGroup_fin_one, card_sesqSpecialUnitaryGroup_four hUF hB hBl hn,
      one_mul] at hlevi
    exact hlevi
  · have hn : Module.finrank K (PieceQ (isoSeq F ρ A₀ 1)
        (F.perp (isoSeq F ρ A₀ 1))) = 2 := by omega
    refine ⟨_, Or.inr (Or.inl rfl), ?_⟩
    intro T hT
    have hlevi := card_commutator_dvd_levi F ρ hρ A₀ hUF.bar
      (unitaryForm_σ_apply hUF hK 6) hT
    rw [card_ker_det_eq (N := PieceQ ⊥ (isoSeq F ρ A₀ 1)), finrank_pieceQ_bot, hj,
      card_specialLinearGroup_fin_two hK, card_sesqSpecialUnitaryGroup_two hUF hB hBl hn,
      levi_su6_arith_two (2 ^ f)] at hlevi
    exact hlevi
  · have hn : Module.finrank K (PieceQ (isoSeq F ρ A₀ 1)
        (F.perp (isoSeq F ρ A₀ 1))) = 0 := by omega
    refine ⟨_, Or.inr (Or.inr rfl), ?_⟩
    intro T hT
    have hlevi := card_commutator_dvd_levi F ρ hρ A₀ hUF.bar
      (unitaryForm_σ_apply hUF hK 6) hT
    rw [card_ker_det_eq (N := PieceQ ⊥ (isoSeq F ρ A₀ 1)), finrank_pieceQ_bot, hj,
      card_specialLinearGroup_fin_three hK,
      card_sesqSpecialUnitaryGroup_of_finrank_eq_zero
        (perpForm F hUF.bar (unitaryForm_σ_apply hUF hK 6) (isoSeq F ρ A₀ 1) hW) hn,
      levi_su6_arith_three (2 ^ f)] at hlevi
    exact hlevi

theorem exists_levi_statedProj_su6_of_bound {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2)
    (hX : ∀ A₀ : Subgroup ↥(StatedSU 6 (2 ^ f) K), IsPGroup 2 A₀ → A₀ ≠ ⊥ →
      ∃ X : ℕ,
        (X = (2 ^ f) ^ 6 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) *
            ((2 ^ f) ^ 4 - 1) ∨
          X = (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1) ∨
          X = (2 ^ f) ^ 6 * ((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 6 - 1)) ∧
        ∀ T ≤ flagStab (natRep (StatedSU 6 (2 ^ f) K))
            (isoFlag (unitaryForm 2 f hK 6) (natRep (StatedSU 6 (2 ^ f) K)) A₀),
          Nat.card ↥⁅T, T⁆ ∣
            Nat.card ↥(⁅T, T⁆ ⊓ flagKernel (natRep (StatedSU 6 (2 ^ f) K))
              (isoFlag (unitaryForm 2 f hK 6) (natRep (StatedSU 6 (2 ^ f) K)) A₀)) * X)
    {A : Subgroup (StatedProj (StatedSU 6 (2 ^ f) K))} (hA : A ≠ ⊥) (hA2 : IsPGroup 2 A) :
    ∃ P O : Subgroup (StatedProj (StatedSU 6 (2 ^ f) K)), O ≤ P ∧ A ≤ O ∧ IsPGroup 2 O ∧
      (∀ p ∈ P, ∀ o ∈ O, p * o * p⁻¹ ∈ O) ∧
      (∀ g, (∀ a ∈ A, g * a * g⁻¹ ∈ A) → g ∈ P) ∧
      ∀ S : Subgroup (StatedProj (StatedSU 6 (2 ^ f) K)), S ≤ P → commutator ↥S = ⊤ →
        Nat.card S ∣ Nat.card ↥(S ⊓ O) *
            ((2 ^ f) ^ 6 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) * ((2 ^ f) ^ 4 - 1)) ∨
        Nat.card S ∣ Nat.card ↥(S ⊓ O) *
            ((2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1)) ∨
        Nat.card S ∣ Nat.card ↥(S ⊓ O) *
            ((2 ^ f) ^ 6 * ((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 6 - 1)) := by
  let H := StatedSU 6 (2 ^ f) K
  let F := unitaryForm 2 f hK 6
  let ρ := natRep H
  let π : ↥H →* StatedProj H :=
    QuotientGroup.mk' ((StatedScalars (Fin 6) K).subgroupOf H)
  obtain ⟨A₀, hA₀2, hA₀map, hA₀N⟩ := exists_isPGroup_map_eq_statedProj H hA2
  have hA₀ne : A₀ ≠ ⊥ := by
    intro h
    apply hA
    rw [← hA₀map, h, Subgroup.map_bot]
  obtain ⟨X, hXdisj, hXbound⟩ := hX A₀ hA₀2 hA₀ne
  let P₀ : Subgroup ↥H := flagStab ρ (isoFlag F ρ A₀)
  let O₀ : Subgroup ↥H := flagKernel ρ (isoFlag F ρ A₀)
  have hρ : IsIsometric F ρ := isIsometric_natRep_statedSU hK 6
  obtain ⟨hOP, hAO, hO, hnorm, hNP⟩ :=
    map_parabolic_clauses π (QuotientGroup.mk'_surjective _) hA₀map hA₀N
      (flagKernel_le_flagStab ρ (isoFlag F ρ A₀))
      (le_flagKernel_isoFlag F ρ 2 hρ A₀ hA₀2)
      (isPGroup_flagKernel ρ 2 (natRep_injective H) (isoFlag_zero F ρ A₀)
        (isoFlag_top F ρ A₀))
      (flagStab_le_normalizer_flagKernel ρ (isoFlag F ρ A₀))
      (normalizer_le_flagStab_isoFlag F ρ hρ A₀)
  refine ⟨P₀.map π, O₀.map π, hOP, hAO, hO, hnorm, hNP, ?_⟩
  intro S hSP hS
  have hdvd := card_dvd_of_le_map π (fun T hT => hXbound T hT) hSP hS
  rcases hXdisj with rfl | rfl | rfl
  · exact Or.inl hdvd
  · exact Or.inr (Or.inl hdvd)
  · exact Or.inr (Or.inr hdvd)

theorem exists_levi_statedProj_su6 {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2)
    {A : Subgroup (StatedProj (StatedSU 6 (2 ^ f) K))} (hA : A ≠ ⊥) (hA2 : IsPGroup 2 A) :
    ∃ P O : Subgroup (StatedProj (StatedSU 6 (2 ^ f) K)), O ≤ P ∧ A ≤ O ∧ IsPGroup 2 O ∧
      (∀ p ∈ P, ∀ o ∈ O, p * o * p⁻¹ ∈ O) ∧
      (∀ g, (∀ a ∈ A, g * a * g⁻¹ ∈ A) → g ∈ P) ∧
      ∀ S : Subgroup (StatedProj (StatedSU 6 (2 ^ f) K)), S ≤ P → commutator ↥S = ⊤ →
        Nat.card S ∣ Nat.card ↥(S ⊓ O) *
            ((2 ^ f) ^ 6 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) * ((2 ^ f) ^ 4 - 1)) ∨
        Nat.card S ∣ Nat.card ↥(S ⊓ O) *
            ((2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1)) ∨
        Nat.card S ∣ Nat.card ↥(S ⊓ O) *
            ((2 ^ f) ^ 6 * ((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 6 - 1)) := by
  have hUF : UnitaryFieldData 2 f K :=
    ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, Nat.mul_comm f 2]⟩
  haveI : CharP K 2 := hUF.charP
  exact exists_levi_statedProj_su6_of_bound hK
    (fun A₀ hA₀ hne => exists_levi_bound_statedSU6 hUF hK A₀ hA₀ hne) hA hA2

end CFSG.LieType.BorelTits
