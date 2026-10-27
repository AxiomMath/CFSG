module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieLift
public import CFSG.ClassicalInvolution.SmallCases.Constrained

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.CGT.PushingUpLit.SolKAb (STSetting sylowImg)
open CFSG.ComponentClassification.AschbacherTheorem3 (IsQuaternionTwoGroup)
open CFSG.Assembly (pCoreOf)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Generic
open CFSG.LieType.BorelTits

theorem false_of_component {X : Type} [Group X] [Finite X] {C E : Subgroup X}
    (hC : C ⊓ Subgroup.centralizer (pCoreOf 2 C : Set X) ≤ pCoreOf 2 C)
    (hE : CFSG.Open.IsSubnormal E C)
    (hq : CFSG.Open.IsQuasisimple (E ⧸ CFSG.Open.classicalInvolutionOddCore E)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcent : E ≤ Subgroup.centralizer (pCoreOf 2 C : Set X) :=
    le_centralizer_of_isSubnormal_of_isQuasisimple hE (pCoreOf_le 2 C)
      (le_normalizer_pCoreOf 2 C) (pCoreOf_isPGroup 2 C) hq
  have hEC : E ≤ C := isSubnormal_le hE
  have hEQ : E ≤ pCoreOf 2 C := fun x hx => hC ⟨hEC hx, hcent hx⟩
  have hE2 : IsPGroup 2 E := (pCoreOf_isPGroup 2 C).to_le hEQ
  have hq2 : IsPGroup 2 (E ⧸ CFSG.Open.classicalInvolutionOddCore E) := hE2.to_quotient _
  have hnil : Group.IsNilpotent (E ⧸ CFSG.Open.classicalInvolutionOddCore E) := hq2.isNilpotent
  have hnt : Nontrivial (E ⧸ CFSG.Open.classicalInvolutionOddCore E) := by
    have h1 : IsSimpleGroup ((E ⧸ CFSG.Open.classicalInvolutionOddCore E) ⧸
        Subgroup.center (E ⧸ CFSG.Open.classicalInvolutionOddCore E)) := hq.2
    have h2 := h1.toNontrivial
    exact (QuotientGroup.mk_surjective (s := Subgroup.center
      (E ⧸ CFSG.Open.classicalInvolutionOddCore E))).nontrivial
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial
    (E ⧸ CFSG.Open.classicalInvolutionOddCore E)).ne hq.1

theorem false_of_commuting_conj {X : Type} [Group X] {t w : X} {J P : Subgroup X}
    (hw : w ∈ Subgroup.centralizer ({t} : Set X)) (hPJ : P ≤ J)
    (hcomm : ∀ a ∈ J, ∀ b ∈ J, a * (w * b * w⁻¹) = (w * b * w⁻¹) * a)
    (hPC : P ≤ Subgroup.centralizer ({t} : Set X))
    (hPn : (P.subgroupOf (Subgroup.centralizer ({t} : Set X))).Normal)
    (hnc : ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a) : False := by
  obtain ⟨a, haP, b, hbP, hab⟩ := hnc
  have hwinv : w⁻¹ ∈ Subgroup.centralizer ({t} : Set X) := inv_mem hw
  have hb' : w⁻¹ * b * w⁻¹⁻¹ ∈ P := by
    have := hPn.conj_mem ⟨b, hPC hbP⟩ (Subgroup.mem_subgroupOf.mpr hbP) ⟨w⁻¹, hwinv⟩
    exact Subgroup.mem_subgroupOf.mp this
  have h := hcomm a (hPJ haP) (w⁻¹ * b * w⁻¹⁻¹) (hPJ hb')
  have hsimp : w * (w⁻¹ * b * w⁻¹⁻¹) * w⁻¹ = b := by group
  rw [hsimp] at h
  exact hab h

theorem twin_of_lift {K X : Type} [Group K] [Group X] (ψ : K →* X) {R : Subgroup K} {t : X}
    {w : K} (hw : ψ w ∈ Subgroup.centralizer ({t} : Set X))
    (hcomm : ∀ a ∈ R, ∀ b ∈ R, Commute (ψ (w * a * w⁻¹)) (ψ b)) :
    ∃ w' ∈ Subgroup.centralizer ({t} : Set X), ∀ a ∈ R.map ψ, ∀ b ∈ R.map ψ,
      a * (w' * b * w'⁻¹) = (w' * b * w'⁻¹) * a := by
  refine ⟨ψ w, hw, ?_⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  have h := (hcomm b hb a ha).eq
  simp only [map_mul, map_inv] at h
  exact h.symm

theorem ker_eq_center_of_simple {K X : Type} [Group K] [Group X] [IsSimpleGroup X]
    (hna : ∃ a b : X, a * b ≠ b * a) (ψ : K →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center K) : ψ.ker = Subgroup.center K := by
  refine le_antisymm hker fun z hz => ?_
  have hcen : ψ z ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := hψ g
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Subgroup.mem_center_iff.mp hz k)
  have hbot : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  rw [hbot, Subgroup.mem_bot] at hcen
  exact hcen


@[expose] def Kill3At (τ : StatedLieTag) (n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (ψ : (modelUniv τ n 3 1 Nat.prime_three).K →* X),
    Function.Surjective ψ → ψ.ker = Subgroup.center _ →
    ∀ R ∈ fundamentalSubgroups τ (modelUniv τ n 3 1 Nat.prime_three).D,
    ∀ t : X, t ∈ R.map ψ → orderOf t = 2 → (∀ j ∈ R.map ψ, j * t = t * j) →
      (∃ w ∈ Subgroup.centralizer ({t} : Set X), ∀ a ∈ R.map ψ, ∀ b ∈ R.map ψ,
          a * (w * b * w⁻¹) = (w * b * w⁻¹) * a) ∨
      (∃ E : Subgroup X, CFSG.Open.IsSubnormal E (Subgroup.centralizer ({t} : Set X)) ∧
          CFSG.Open.IsQuasisimple (E ⧸ CFSG.Open.classicalInvolutionOddCore E))

@[expose] def Lie3At (τ : StatedLieTag) (n : ℕ) : Prop :=
  IsFundTag τ → StatedLieAdmissible τ n 3 1 →
    ∀ (X : Type) [Group X] [Finite X] (ψ : (modelUniv τ n 3 1 Nat.prime_three).K →* X),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center _ →
      ∀ (R : Subgroup (modelUniv τ n 3 1 Nat.prime_three).K),
        R ∈ fundamentalSubgroups τ (modelUniv τ n 3 1 Nat.prime_three).D →
      ∀ (K : Subgroup X), STSetting X K → ∀ R₀ : Sylow 2 K, IsQuaternionTwoGroup (sylowImg R₀) →
        pCoreOf 2 K ≤ R.map ψ →
        (τ = .PSL ∧ n = 3) ∨ (τ = .PSU ∧ n = 3) ∨ τ = .G2

theorem lie3Table_of_at (h : ∀ τ n, Lie3At τ n) : Lie3Table := fun τ n => h τ n

theorem lie3At_of_survivor {τ : StatedLieTag} {n : ℕ}
    (h : (τ = .PSL ∧ n = 3) ∨ (τ = .PSU ∧ n = 3) ∨ τ = .G2) : Lie3At τ n := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  exact h

end CFSG.CGT.PushingUpLit.SolKNA
