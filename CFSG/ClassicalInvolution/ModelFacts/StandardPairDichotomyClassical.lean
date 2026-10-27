module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomy
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalToralBasic
public import CFSG.ClassicalInvolution.RouteD.TypeCRecognition

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)
open scoped MatrixGroups

section Types

@[expose] def StandardPairDichotomyTypes (p : ℕ) [Fact p.Prime] (t : StatedLieTag) (n e : ℕ)
    (lin uni : Prop) : Prop :=
  p ≠ 2 → 5 ≤ p ^ e →
    ∀ R₁ ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D,
    ∀ R₂ ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D,
    ∀ c₁ c₂ : (Generic.modelUniv t n p e Fact.out).K, c₁ ∈ R₁ → c₂ ∈ R₂ →
      orderOf c₁ = 2 → orderOf c₂ = 2 → c₁ * c₂ = c₂ * c₁ →
      R₁ = R₂ ∨ Commutes R₁ R₂ ∨
        (lin ∧ ∃ W, LinearBlockStandardPair (GaloisField p e) W R₁ R₂) ∨
        (uni ∧ ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W R₁ R₂)

variable {p : ℕ} [Fact p.Prime] {t : StatedLieTag} {n e : ℕ} {lin uni : Prop}

theorem StandardPairDichotomyTypes.dichotomy (h : StandardPairDichotomyTypes p t n e lin uni) :
    StandardPairDichotomy p t n e := by
  intro hp2 hq R₁ h₁ R₂ h₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ hc
  rcases h hp2 hq R₁ h₁ R₂ h₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ hc with h | h | ⟨-, h⟩ | ⟨-, h⟩
  exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h)), Or.inr (Or.inr (Or.inr h))]

theorem StandardPairDichotomyTypes.map_of_commute
    (h : StandardPairDichotomyTypes p t n e lin uni) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {X : Type}
    [Group X] (ψ : (Generic.modelUniv t n p e Fact.out).K →* X)
    (hker : ψ.ker ≤ Subgroup.center (Generic.modelUniv t n p e Fact.out).K)
    {R₁ R₂ : Subgroup (Generic.modelUniv t n p e Fact.out).K}
    (h₁ : R₁ ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D)
    (h₂ : R₂ ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D)
    {c₁ c₂ : (Generic.modelUniv t n p e Fact.out).K} (hc₁ : c₁ ∈ R₁) (hc₂ : c₂ ∈ R₂)
    (ho₁ : orderOf c₁ = 2) (ho₂ : orderOf c₂ = 2) (hcomm : c₁ * c₂ = c₂ * c₁) :
    R₁.map ψ = R₂.map ψ ∨ Commutes (R₁.map ψ) (R₂.map ψ) ∨
      (lin ∧ ∃ W, LinearBlockStandardPair (GaloisField p e) W (R₁.map ψ) (R₂.map ψ)) ∨
      (uni ∧ ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W (R₁.map ψ)
        (R₂.map ψ)) := by
  have hf : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | h
    · simp at hq
    · exact h
  rcases h hp2 hq R₁ h₁ R₂ h₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ hcomm with rfl | hcm | ⟨hl, W, hW⟩ |
    ⟨hu, W, hW⟩
  · exact Or.inl rfl
  · refine Or.inr (Or.inl ?_)
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcm x hx y hy]
  · exact Or.inr (Or.inr (Or.inl ⟨hl, _,
      Balance.linearBlockStandardPair_map_of_ker_le_center hW ψ hker⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hu, _,
      Balance.unitaryBlockStandardPair_map_of_ker_le_center (K₀ := GaloisField p (2 * e))
        (card_galoisField_two_mul p e hf) hq hW ψ hker⟩))

end Types

section Linear

variable {p : ℕ} [Fact p.Prime]

theorem standardPairDichotomyTypes_psl {n e : ℕ} (hadm : StatedLieAdmissible .PSL n p e) :
    StandardPairDichotomyTypes p .PSL n e True False := by
  intro hp2 hq R₁ hR₁ R₂ hR₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ hc
  have hn : 2 ≤ n := hadm.2.2.1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hF := odd_and_five_le_card_galoisField hp2 hq
  have h2 : (2 : GaloisField p e) ≠ 0 := two_ne_zero_of_odd_natCard hF.1
  obtain ⟨i₁, hi₁⟩ : R₁ ∈ longRootSet (K := GaloisField p e) hn :=
    fundamentalSubgroups_psl_subset hn (longestFundamental_subset .PSL _ hR₁)
  obtain ⟨i₂, hi₂⟩ : R₂ ∈ longRootSet (K := GaloisField p e) hn :=
    fundamentalSubgroups_psl_subset hn (longestFundamental_subset .PSL _ hR₂)
  have e₁ : c₁ = i₁ := (hi₁.isClassicalSL2 h2).eq_of_orderOf_eq_two hF.1 hc₁ ho₁
  have e₂ : c₂ = i₂ := (hi₂.isClassicalSL2 h2).eq_of_orderOf_eq_two hF.1 hc₂ ho₂
  subst e₁ e₂
  by_cases hn3 : 3 ≤ m + 1
  · by_cases hne : c₁ = c₂
    · exact Or.inl (by rw [hi₁.eq_longRootGroup h2, hi₂.eq_longRootGroup h2, hne])
    · rcases commute_or_linearBlockStandardPair h2 hn3 hi₁ hi₂ hc hne with h | ⟨-, h⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl ⟨trivial, _, h⟩))
  · obtain rfl : m = 1 := by omega
    have k₁ := longRootSet_two_subset (F := GaloisField p e) hn ⟨_, hi₁⟩
    have k₂ := longRootSet_two_subset (F := GaloisField p e) hn ⟨_, hi₂⟩
    exact Or.inl ((Set.mem_singleton_iff.mp k₁).trans (Set.mem_singleton_iff.mp k₂).symm)

theorem standardPairDichotomy_psl {n e : ℕ} (hadm : StatedLieAdmissible .PSL n p e) :
    StandardPairDichotomy p .PSL n e :=
  (standardPairDichotomyTypes_psl hadm).dichotomy

end Linear

section Unitary

variable {p : ℕ} [Fact p.Prime]

private theorem map_equiv_symm_map {G H : Type} [Group G] [Group H] (φ : G ≃* H)
    (R : Subgroup G) : (R.map φ.toMonoidHom).map φ.symm.toMonoidHom = R := by
  rw [Subgroup.map_map]
  have : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rw [this, Subgroup.map_id]

theorem standardPairDichotomyTypes_psu {n e : ℕ} (hadm : StatedLieAdmissible .PSU n p e) :
    StandardPairDichotomyTypes p .PSU n e False True := by
  intro hp2 hq R₁ hR₁ R₂ hR₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ hc
  have hf : 1 ≤ e := hadm.2.1
  have hn3 : 3 ≤ n := hadm.2.2.1
  have hn : 2 ≤ n := by omega
  have hF : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := card_galoisField_two_mul p e hf
  obtain ⟨φ, hφ⟩ := psu_model_equiv hp2 hadm
  obtain ⟨i₁, hi₁⟩ : R₁.map φ.toMonoidHom ∈ longRootSetU (K := GaloisField p (2 * e)) (p := p)
      (f := e) hn := (hφ R₁).mp (longestFundamental_subset .PSU _ hR₁)
  obtain ⟨i₂, hi₂⟩ : R₂.map φ.toMonoidHom ∈ longRootSetU (K := GaloisField p (2 * e)) (p := p)
      (f := e) hn := (hφ R₂).mp (longestFundamental_subset .PSU _ hR₂)
  have e₁ : φ c₁ = i₁ := hi₁.eq_of_orderOf_eq_two hF hp2 ⟨c₁, hc₁, rfl⟩
    (by rw [MulEquiv.orderOf_eq]; exact ho₁)
  have e₂ : φ c₂ = i₂ := hi₂.eq_of_orderOf_eq_two hF hp2 ⟨c₂, hc₂, rfl⟩
    (by rw [MulEquiv.orderOf_eq]; exact ho₂)
  have hcφ : Commute i₁ i₂ := by
    show i₁ * i₂ = i₂ * i₁
    rw [← e₁, ← e₂, ← map_mul, ← map_mul, hc]
  by_cases hne : i₁ = i₂
  · left
    have h12 : R₁.map φ.toMonoidHom = R₂.map φ.toMonoidHom := by
      rw [hi₁.eq_longRootGroupSU (two_ne_zero_of_charP_ne_two hp2),
        hi₂.eq_longRootGroupSU (two_ne_zero_of_charP_ne_two hp2), hne]
    exact Subgroup.map_injective φ.injective h12
  · rcases commute_or_unitaryBlockStandardPair hF hp2 hn3 hi₁ hi₂ hcφ hne with h | ⟨-, h⟩
    · refine Or.inr (Or.inl fun x hx y hy => φ.injective ?_)
      rw [map_mul, map_mul]
      exact h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    · have h' := unitaryBlockStandardPair_map h φ.symm.toMonoidHom φ.symm.injective
      rw [map_equiv_symm_map, map_equiv_symm_map] at h'
      exact Or.inr (Or.inr (Or.inr ⟨trivial, _, h'⟩))

theorem standardPairDichotomy_psu {n e : ℕ} (hadm : StatedLieAdmissible .PSU n p e) :
    StandardPairDichotomy p .PSU n e :=
  (standardPairDichotomyTypes_psu hadm).dichotomy

end Unitary

section Symplectic

variable {p : ℕ} [Fact p.Prime]

open CFSG.ClassicalInvolution.Models.SymplecticPairs (IsHyperbolicPlane planeGroup IsLongRootSp2
  exists_isLongRootSp2_iff)

theorem standardPairDichotomyTypes_psp {n e : ℕ} (hadm : StatedLieAdmissible .PSp n p e) :
    StandardPairDichotomyTypes p .PSp n e False False := by
  intro hp2 hq R₁ hR₁ R₂ hR₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ hc
  have hF := odd_and_five_le_card_galoisField hp2 hq
  have h2 : (2 : GaloisField p e) ≠ 0 := two_ne_zero_of_odd_natCard hF.1
  have hmem : ∀ R ∈ longestFundamental (Generic.modelUniv .PSp n p e Fact.out).D,
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
  by_cases hne : c₁ = c₂
  · exact Or.inl (by rw [hi₁.eq_longRootGroup h2, hi₂.eq_longRootGroup h2, hne])
  · exact Or.inr (Or.inl (hi₁.commute_of_commute h2 hi₂ hc hne))

theorem standardPairDichotomy_psp {n e : ℕ} (hadm : StatedLieAdmissible .PSp n p e) :
    StandardPairDichotomy p .PSp n e :=
  (standardPairDichotomyTypes_psp hadm).dichotomy

end Symplectic

end CFSG.ClassicalInvolution.ModelFacts
