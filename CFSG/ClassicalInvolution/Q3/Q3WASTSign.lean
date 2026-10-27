module

public import CFSG.ClassicalInvolution.Asc77.AscR10E24
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.RouteD
  CFSG.LieType.Universal CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups commutatorElement



section Types

theorem false_of_linear_of_unitary3 {X : Type} [Group X] {U V : Subgroup X}
    (hl : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W U V)
    (hu : ∃ W, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W U V) : False := by
  obtain ⟨W₀, hl⟩ := hl
  obtain ⟨W₁, hu⟩ := hu
  have hodd : Odd (Nat.card (GaloisField 3 1)) := by
    rw [GaloisField.card 3 1 (by norm_num)]; decide
  have hc : Nat.card (GaloisField 3 1) = 3 ^ 1 := GaloisField.card 3 1 (by norm_num)
  have hc' : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := card_galoisField_two_mul 3 1 le_rfl
  have hq2 : 3 ^ 1 ≠ 2 := by norm_num
  have e1 := RouteD.Gaps.linear_eq_sup hl
  have e2 := RouteD.Gaps.unitary_eq_sup hc' hq2 hu
  rw [e1] at hl
  rw [e2] at hu
  exact RouteD.Gaps.not_linear_and_unitary hc hc' hodd hl hu

end Types

section Pairs

theorem linear_pair_psl3 {n : ℕ} (hadm : StatedLieAdmissible .PSL n 3 1)
    {R₁ R₂ : Subgroup (Generic.modelUniv .PSL n 3 1 Nat.prime_three).K}
    (hR₁ : R₁ ∈ longestFundamental (Generic.modelUniv .PSL n 3 1 Nat.prime_three).D)
    (hR₂ : R₂ ∈ longestFundamental (Generic.modelUniv .PSL n 3 1 Nat.prime_three).D)
    {c₁ c₂ : (Generic.modelUniv .PSL n 3 1 Nat.prime_three).K} (hc₁ : c₁ ∈ R₁) (hc₂ : c₂ ∈ R₂)
    (ho₁ : orderOf c₁ = 2) (ho₂ : orderOf c₂ = 2) (hc : c₁ * c₂ = c₂ * c₁) (hne : R₁ ≠ R₂)
    (hnc : ¬ Commutes R₁ R₂) : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₁ R₂ := by
  have hn : 2 ≤ n := hadm.2.2.1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hodd : Odd (Nat.card (GaloisField 3 1)) := by
    rw [GaloisField.card 3 1 (by norm_num)]; decide
  have h2 : (2 : GaloisField 3 1) ≠ 0 := ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  obtain ⟨i₁, hi₁⟩ : R₁ ∈ longRootSet (K := GaloisField 3 1) hn :=
    fundamentalSubgroups_psl_subset hn (longestFundamental_subset .PSL _ hR₁)
  obtain ⟨i₂, hi₂⟩ : R₂ ∈ longRootSet (K := GaloisField 3 1) hn :=
    fundamentalSubgroups_psl_subset hn (longestFundamental_subset .PSL _ hR₂)
  have e₁ : c₁ = i₁ := (hi₁.isClassicalSL2 h2).eq_of_orderOf_eq_two hodd hc₁ ho₁
  have e₂ : c₂ = i₂ := (hi₂.isClassicalSL2 h2).eq_of_orderOf_eq_two hodd hc₂ ho₂
  subst e₁ e₂
  by_cases hn3 : 3 ≤ m + 1
  · by_cases hne' : c₁ = c₂
    · exact absurd (by rw [hi₁.eq_longRootGroup h2, hi₂.eq_longRootGroup h2, hne']) hne
    · rcases commute_or_linearBlockStandardPair h2 hn3 hi₁ hi₂ hc hne' with h | ⟨-, h⟩
      · exact absurd h hnc
      · exact ⟨_, h⟩
  · obtain rfl : m = 1 := by omega
    have k₁ := longRootSet_two_subset (F := GaloisField 3 1) hn ⟨_, hi₁⟩
    have k₂ := longRootSet_two_subset (F := GaloisField 3 1) hn ⟨_, hi₂⟩
    exact absurd ((Set.mem_singleton_iff.mp k₁).trans (Set.mem_singleton_iff.mp k₂).symm) hne

private theorem map_equiv_symm_map3 {G H : Type} [Group G] [Group H] (φ : G ≃* H)
    (R : Subgroup G) : (R.map φ.toMonoidHom).map φ.symm.toMonoidHom = R := by
  rw [Subgroup.map_map]
  have : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rw [this, Subgroup.map_id]

theorem unitary_pair_psu3 {n : ℕ} (hadm : StatedLieAdmissible .PSU n 3 1)
    {R₁ R₂ : Subgroup (Generic.modelUniv .PSU n 3 1 Nat.prime_three).K}
    (hR₁ : R₁ ∈ longestFundamental (Generic.modelUniv .PSU n 3 1 Nat.prime_three).D)
    (hR₂ : R₂ ∈ longestFundamental (Generic.modelUniv .PSU n 3 1 Nat.prime_three).D)
    {c₁ c₂ : (Generic.modelUniv .PSU n 3 1 Nat.prime_three).K} (hc₁ : c₁ ∈ R₁) (hc₂ : c₂ ∈ R₂)
    (ho₁ : orderOf c₁ = 2) (ho₂ : orderOf c₂ = 2) (hc : c₁ * c₂ = c₂ * c₁) (hne : R₁ ≠ R₂)
    (hnc : ¬ Commutes R₁ R₂) :
    ∃ W, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W R₁ R₂ := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hn3 : 3 ≤ n := hadm.2.2.1
  have hn : 2 ≤ n := by omega
  have hF : Nat.card (GaloisField 3 2) = (3 ^ 1) ^ 2 := card_galoisField_two_mul 3 1 le_rfl
  obtain ⟨φ, hφ⟩ := psu_model_equiv hp2 hadm
  obtain ⟨i₁, hi₁⟩ : R₁.map φ.toMonoidHom ∈ longRootSetU (K := GaloisField 3 2) (p := 3)
      (f := 1) hn := (hφ R₁).mp (longestFundamental_subset .PSU _ hR₁)
  obtain ⟨i₂, hi₂⟩ : R₂.map φ.toMonoidHom ∈ longRootSetU (K := GaloisField 3 2) (p := 3)
      (f := 1) hn := (hφ R₂).mp (longestFundamental_subset .PSU _ hR₂)
  have e₁ : φ c₁ = i₁ := hi₁.eq_of_orderOf_eq_two hF hp2 ⟨c₁, hc₁, rfl⟩
    (by rw [MulEquiv.orderOf_eq]; exact ho₁)
  have e₂ : φ c₂ = i₂ := hi₂.eq_of_orderOf_eq_two hF hp2 ⟨c₂, hc₂, rfl⟩
    (by rw [MulEquiv.orderOf_eq]; exact ho₂)
  have hcφ : Commute i₁ i₂ := by
    show i₁ * i₂ = i₂ * i₁
    rw [← e₁, ← e₂, ← map_mul, ← map_mul, hc]
  by_cases hne' : i₁ = i₂
  · exfalso
    apply hne
    have h12 : R₁.map φ.toMonoidHom = R₂.map φ.toMonoidHom := by
      rw [hi₁.eq_longRootGroupSU (two_ne_zero_of_charP_ne_two hp2),
        hi₂.eq_longRootGroupSU (two_ne_zero_of_charP_ne_two hp2), hne']
    exact Subgroup.map_injective φ.injective h12
  · rcases commute_or_unitaryBlockStandardPair hF hp2 hn3 hi₁ hi₂ hcφ hne' with h | ⟨-, h⟩
    · exact absurd (fun x hx y hy => φ.injective (by
        rw [map_mul, map_mul]
        exact h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩)) hnc
    · have h' := unitaryBlockStandardPair_map h φ.symm.toMonoidHom φ.symm.injective
      rw [map_equiv_symm_map3, map_equiv_symm_map3] at h'
      exact ⟨_, h'⟩

open CFSG.ClassicalInvolution.Models.SymplecticPairs (IsHyperbolicPlane planeGroup IsLongRootSp2
  exists_isLongRootSp2_iff) in
theorem false_of_pair_psp3 {n : ℕ} (hadm : StatedLieAdmissible .PSp n 3 1)
    {R₁ R₂ : Subgroup (Generic.modelUniv .PSp n 3 1 Nat.prime_three).K}
    (hR₁ : R₁ ∈ longestFundamental (Generic.modelUniv .PSp n 3 1 Nat.prime_three).D)
    (hR₂ : R₂ ∈ longestFundamental (Generic.modelUniv .PSp n 3 1 Nat.prime_three).D)
    {c₁ c₂ : (Generic.modelUniv .PSp n 3 1 Nat.prime_three).K} (hc₁ : c₁ ∈ R₁) (hc₂ : c₂ ∈ R₂)
    (ho₁ : orderOf c₁ = 2) (ho₂ : orderOf c₂ = 2) (hc : c₁ * c₂ = c₂ * c₁) (hne : R₁ ≠ R₂)
    (hnc : ¬ Commutes R₁ R₂) : False := by
  have hodd : Odd (Nat.card (GaloisField 3 1)) := by
    rw [GaloisField.card 3 1 (by norm_num)]; decide
  have h2 : (2 : GaloisField 3 1) ≠ 0 := ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  have hmem : ∀ R ∈ longestFundamental (Generic.modelUniv .PSp n 3 1 Nat.prime_three).D,
      ∃ P, IsHyperbolicPlane P ∧ R = planeGroup P := fun R hR => by
    have := longestFundamental_subset .PSp _ hR
    rw [fundamentalSubgroups_psp_eq hadm] at this
    exact this
  obtain ⟨P₁, hP₁, rfl⟩ := hmem R₁ hR₁
  obtain ⟨P₂, hP₂, rfl⟩ := hmem R₂ hR₂
  obtain ⟨i₁, hi₁⟩ := (exists_isLongRootSp2_iff h2 _).mpr ⟨P₁, hP₁, rfl⟩
  obtain ⟨i₂, hi₂⟩ := (exists_isLongRootSp2_iff h2 _).mpr ⟨P₂, hP₂, rfl⟩
  have e₁ : c₁ = i₁ := hi₁.eq_of_orderOf_eq_two h2 hc₁ ho₁
  have e₂ : c₂ = i₂ := hi₂.eq_of_orderOf_eq_two h2 hc₂ ho₂
  subst e₁ e₂
  by_cases hne' : c₁ = c₂
  · exact hne (by rw [hi₁.eq_longRootGroup h2, hi₂.eq_longRootGroup h2, hne'])
  · exact hnc (hi₁.commute_of_commute h2 hi₂ hc hne')

end Pairs

section Orth

variable {p e : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (GaloisField p e) V]
  [FiniteDimensional (GaloisField p e) V] {Q : QuadraticForm (GaloisField p e) V}

theorem spinCtx3_sign {𝔉 : Set (Subgroup (spinGroup Q))} (S : SpinCtx3 p e Q 𝔉)
    {R₁ R₂ R₃ : Subgroup (spinGroup Q)} (h₁ : R₁ ∈ 𝔉) (h₂ : R₂ ∈ 𝔉) (h₃ : R₃ ∈ 𝔉)
    {c₁ c₂ c₃ : spinGroup Q} (hc₁ : c₁ ∈ R₁) (hc₂ : c₂ ∈ R₂) (hc₃ : c₃ ∈ R₃)
    (ho₁ : orderOf c₁ = 2) (ho₂ : orderOf c₂ = 2) (ho₃ : orderOf c₃ = 2)
    (h₁₂ : c₁ * c₂ = c₂ * c₁) (h₃₂ : c₃ * c₂ = c₂ * c₃) (h₁₃ : c₁ * c₃ = c₃ * c₁)
    (hR₁₃ : Commutes R₁ R₃) (hne₁₂ : R₁ ≠ R₂) (hne₃₂ : R₃ ≠ R₂) (hnc₁₂ : ¬ Commutes R₁ R₂)
    (hnc₃₂ : ¬ Commutes R₃ R₂) :
    ((∃ W, LinearBlockStandardPair (GaloisField p e) W R₁ R₂) ∧
        ∃ W, LinearBlockStandardPair (GaloisField p e) W R₂ R₃) ∨
      ((∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W R₁ R₂) ∧
        ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W R₂ R₃) := by
  have hodd := S.odd_card
  obtain ⟨i₁, hI₁⟩ := S.map R₁ h₁
  obtain ⟨i₂, hI₂⟩ := S.map R₂ h₂
  obtain ⟨i₃, hI₃⟩ := S.map R₃ h₃
  have e₁ := S.map_eq_of_orderOf h₁ hc₁ ho₁ hI₁
  have e₂ := S.map_eq_of_orderOf h₂ hc₂ ho₂ hI₂
  have e₃ := S.map_eq_of_orderOf h₃ hc₃ ho₃ hI₃
  have k₁₂ : i₁ * i₂ = i₂ * i₁ := by rw [← e₁, ← e₂, ← map_mul, ← map_mul, h₁₂]
  have k₃₂ : i₃ * i₂ = i₂ * i₃ := by rw [← e₃, ← e₂, ← map_mul, ← map_mul, h₃₂]
  have k₁₃ : i₁ * i₃ = i₃ * i₁ := by rw [← e₁, ← e₃, ← map_mul, ← map_mul, h₁₃]
  have hL : ∀ x ∈ R₁.map (spinAction Q), ∀ y ∈ R₃.map (spinAction Q), x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hR₁₃ x hx y hy]
  have hN₁ := S.mem_normalizer ho₁ ho₂ h₁₂ hI₁ hI₂ e₁ e₂ k₁₂
  have hN₃ := S.mem_normalizer ho₃ ho₂ h₃₂ hI₃ hI₂ e₃ e₂ k₃₂
  have hL₁₂ : R₁.map (spinAction Q) ≠ R₂.map (spinAction Q) := fun h =>
    hne₁₂ (S.eq_of_map_eq h₁ h₂ h)
  have hL₃₂ : R₃.map (spinAction Q) ≠ R₂.map (spinAction Q) := fun h =>
    hne₃₂ (S.eq_of_map_eq h₃ h₂ h)
  have hC₁ : i₂ ∉ Subgroup.centralizer ((R₁.map (spinAction Q) : Subgroup _) : Set _) :=
    fun hc => hnc₁₂ (S.commutes_of_map h₁
      ((IsFundamental.commute_iff hodd hI₁ hI₂ k₁₂ hL₁₂).mpr hc))
  have hC₃ : i₂ ∉ Subgroup.centralizer ((R₃.map (spinAction Q) : Subgroup _) : Set _) :=
    fun hc => hnc₃₂ (S.commutes_of_map h₃
      ((IsFundamental.commute_iff hodd hI₃ hI₂ k₃₂ hL₃₂).mpr hc))
  rcases lemma_6_11_signs S.card_eq S.card_eq' hodd hI₁ hI₂ hI₃ k₁₂ k₃₂ k₁₃ hL hN₁ hN₃ hC₁ hC₃ with
    ⟨-, -, hl₁, hl₃⟩ | ⟨-, -, hu₁, hu₃⟩
  · exact Or.inl ⟨S.linear_of_map h₁ h₂ ⟨_, hl₁⟩, S.linear_of_map h₂ h₃ ⟨_, hl₃⟩⟩
  · exact Or.inr ⟨S.unitary_of_map h₁ h₂ ⟨_, hu₁⟩, S.unitary_of_map h₂ h₃ ⟨_, hu₃⟩⟩

end Orth

section Tags

@[expose] def ChainSign3Gen (p : ℕ) [Fact p.Prime] (t : StatedLieTag) (n e : ℕ) : Prop :=
  p ^ e = 3 →
    ∀ R₁ ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D,
    ∀ R₂ ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D,
    ∀ R₃ ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D,
    ∀ c₁ c₂ c₃ : (Generic.modelUniv t n p e Fact.out).K, c₁ ∈ R₁ → c₂ ∈ R₂ → c₃ ∈ R₃ →
      orderOf c₁ = 2 → orderOf c₂ = 2 → orderOf c₃ = 2 →
      c₁ * c₂ = c₂ * c₁ → c₃ * c₂ = c₂ * c₃ → c₁ * c₃ = c₃ * c₁ →
      Commutes R₁ R₃ → R₁ ≠ R₂ → R₃ ≠ R₂ → ¬ Commutes R₁ R₂ → ¬ Commutes R₃ R₂ →
      ((∃ W, LinearBlockStandardPair (GaloisField p e) W R₁ R₂) ∧
          ∃ W, LinearBlockStandardPair (GaloisField p e) W R₂ R₃) ∨
        ((∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W R₁ R₂) ∧
          ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W R₂ R₃)

@[expose] def ChainSign3 (t : StatedLieTag) (n : ℕ) : Prop := ChainSign3Gen 3 t n 1

theorem chainSign3_psl {n : ℕ} (hadm : StatedLieAdmissible .PSL n 3 1) : ChainSign3 .PSL n := by
  intro _ R₁ h₁ R₂ h₂ R₃ h₃ c₁ c₂ c₃ hc₁ hc₂ hc₃ ho₁ ho₂ ho₃ h₁₂ h₃₂ _ _ hne₁₂ hne₃₂ hnc₁₂ hnc₃₂
  exact Or.inl ⟨linear_pair_psl3 hadm h₁ h₂ hc₁ hc₂ ho₁ ho₂ h₁₂ hne₁₂ hnc₁₂,
    linear_pair_psl3 hadm h₂ h₃ hc₂ hc₃ ho₂ ho₃ h₃₂.symm (Ne.symm hne₃₂)
      (fun h => hnc₃₂ h.symm)⟩

theorem chainSign3_psu {n : ℕ} (hadm : StatedLieAdmissible .PSU n 3 1) : ChainSign3 .PSU n := by
  intro _ R₁ h₁ R₂ h₂ R₃ h₃ c₁ c₂ c₃ hc₁ hc₂ hc₃ ho₁ ho₂ ho₃ h₁₂ h₃₂ _ _ hne₁₂ hne₃₂ hnc₁₂ hnc₃₂
  exact Or.inr ⟨unitary_pair_psu3 hadm h₁ h₂ hc₁ hc₂ ho₁ ho₂ h₁₂ hne₁₂ hnc₁₂,
    unitary_pair_psu3 hadm h₂ h₃ hc₂ hc₃ ho₂ ho₃ h₃₂.symm (Ne.symm hne₃₂)
      (fun h => hnc₃₂ h.symm)⟩

theorem chainSign3_psp {n : ℕ} (hadm : StatedLieAdmissible .PSp n 3 1) : ChainSign3 .PSp n := by
  intro _ R₁ h₁ R₂ h₂ R₃ h₃ c₁ c₂ c₃ hc₁ hc₂ hc₃ ho₁ ho₂ ho₃ h₁₂ h₃₂ _ _ hne₁₂ hne₃₂ hnc₁₂ hnc₃₂
  exact (false_of_pair_psp3 hadm h₁ h₂ hc₁ hc₂ ho₁ ho₂ h₁₂ hne₁₂ hnc₁₂).elim

variable {p : ℕ} [Fact p.Prime]

theorem chainSign3Gen_pOmegaPlus {n e : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n p e) :
    ChainSign3Gen p .POmegaPlus n e := by
  have hn : 4 ≤ n := hadm.2.2
  unfold ChainSign3Gen
  rw [RouteD.modelUniv_POmegaPlus_eq (p := p) (f := e) (by omega : 3 ≤ n)]
  intro h3 R₁ h₁ R₂ h₂ R₃ h₃ c₁ c₂ c₃ hc₁ hc₂ hc₃ ho₁ ho₂ ho₃ h₁₂ h₃₂ h₁₃ hR₁₃ hne₁₂ hne₃₂
    hnc₁₂ hnc₃₂
  exact spinCtx3_sign (spinCtx3_pOmegaPlus hn h3) h₁ h₂ h₃ hc₁ hc₂ hc₃ ho₁ ho₂ ho₃ h₁₂ h₃₂ h₁₃
    hR₁₃ hne₁₂ hne₃₂ hnc₁₂ hnc₃₂

theorem chainSign3Gen_pOmegaOdd {n e : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n p e) :
    ChainSign3Gen p .POmegaOdd n e := by
  intro h3 R₁ h₁ R₂ h₂ R₃ h₃ c₁ c₂ c₃ hc₁ hc₂ hc₃ ho₁ ho₂ ho₃ h₁₂ h₃₂ h₁₃ hR₁₃ hne₁₂ hne₃₂
    hnc₁₂ hnc₃₂
  exact spinCtx3_sign (spinCtx3_pOmegaOdd hadm h3) h₁ h₂ h₃ hc₁ hc₂ hc₃ ho₁ ho₂ ho₃ h₁₂ h₃₂ h₁₃
    hR₁₃ hne₁₂ hne₃₂ hnc₁₂ hnc₃₂

theorem chainSign3Gen_pOmegaMinus {n e : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n p e) :
    ChainSign3Gen p .POmegaMinus n e := by
  intro h3 R₁ h₁ R₂ h₂ R₃ h₃ c₁ c₂ c₃ hc₁ hc₂ hc₃ ho₁ ho₂ ho₃ h₁₂ h₃₂ h₁₃ hR₁₃ hne₁₂ hne₃₂
    hnc₁₂ hnc₃₂
  exact spinCtx3_sign (spinCtx3_pOmegaMinus hadm h3) h₁ h₂ h₃ hc₁ hc₂ hc₃ ho₁ ho₂ ho₃ h₁₂ h₃₂ h₁₃
    hR₁₃ hne₁₂ hne₃₂ hnc₁₂ hnc₃₂

theorem chainSign3_of_classical {t : StatedLieTag} {n : ℕ}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (hadm : StatedLieAdmissible t n 3 1) : ChainSign3 t n := by
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [chainSign3_psl hadm, chainSign3_psu hadm, chainSign3_psp hadm,
    chainSign3Gen_pOmegaOdd hadm, chainSign3Gen_pOmegaPlus hadm, chainSign3Gen_pOmegaMinus hadm]

end Tags

end CFSG.ClassicalInvolution.Q3.Q3W
