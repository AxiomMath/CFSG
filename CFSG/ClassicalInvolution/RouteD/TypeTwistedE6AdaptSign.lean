module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6AdaptModel
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Generic QuadraticMap
open CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups

section Spin

variable {p e : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (GaloisField p e) V]
  [FiniteDimensional (GaloisField p e) V] {Q : QuadraticForm (GaloisField p e) V}
  {𝔉 : Set (Subgroup (spinGroup Q))}

theorem exists_involution_of_fam (S : SpinCtx p e Q 𝔉) {R : Subgroup (spinGroup Q)} (hR : R ∈ 𝔉) :
    ∃ c ∈ R, orderOf c = 2 := by
  have hodd := S.odd_card
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨i, hI⟩ := S.map R hR
  obtain ⟨c, hcR, hc⟩ := hI.mem
  have hcc : c * c = 1 := S.inj R hR (c * c) (R.mul_mem hcR hcR)
    (by rw [map_mul, hc]; exact hI.mul_self)
  have hc1 : c ≠ 1 := fun h => hI.ne_one hodd (by rw [← hc, h, map_one])
  exact ⟨c, hcR, orderOf_eq_prime (by rw [pow_two]; exact hcc) hc1⟩

theorem eq_of_involutions_fam (S : SpinCtx p e Q 𝔉) {R : Subgroup (spinGroup Q)} (hR : R ∈ 𝔉)
    {c c' : spinGroup Q} (hc : c ∈ R) (hc' : c' ∈ R) (ho : orderOf c = 2) (ho' : orderOf c' = 2) :
    c = c' := by
  obtain ⟨i, hI⟩ := S.map R hR
  have e1 := S.map_eq_of_orderOf hR hc ho hI
  have e2 := S.map_eq_of_orderOf hR hc' ho' hI
  have h1 : c * c'⁻¹ = 1 := S.inj R hR _ (R.mul_mem hc (R.inv_mem hc'))
    (by rw [map_mul, map_inv, e1, e2, mul_inv_cancel])
  exact mul_inv_eq_one.mp h1

theorem linear_pair_of_chain (S : SpinCtx p e Q 𝔉) {X : Type} [Group X]
    (ψ : spinGroup Q →* X) (hker : ψ.ker ≤ Subgroup.center (spinGroup Q))
    (hnc : ∀ R ∈ 𝔉, ∀ r ∈ R, (∀ y : spinGroup Q, r * y * r⁻¹ * y⁻¹ ∈
      Subgroup.center (spinGroup Q)) → r = 1)
    {R₁ R₂ R₃ : Subgroup (spinGroup Q)} (h₁ : R₁ ∈ 𝔉) (h₂ : R₂ ∈ 𝔉) (h₃ : R₃ ∈ 𝔉)
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField p e) W (R₁.map ψ) (R₂.map ψ))
    (h13 : Commutes R₁ R₃) (hn32 : ¬ Commutes R₃ R₂) (hne32 : R₃ ≠ R₂) {yb : X}
    (hyb : yb ∈ R₂.map ψ) (hyb2 : orderOf yb = 2)
    (hnorm : ∀ w ∈ R₃.map ψ, yb * w * yb⁻¹ ∈ R₃.map ψ) :
    ∃ W, LinearBlockStandardPair (GaloisField p e) W (R₂.map ψ) (R₃.map ψ) := by
  have hodd := S.odd_card
  have h2 : (2 : GaloisField p e) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := S.fin
  have hlin' : ∃ W, LinearBlockStandardPair (GaloisField p e) W R₁ R₂ :=
    Gaps.exists_lin_of_map S.four_le S.hC ψ hker (S.perf_le h₁) (S.perf_le h₂) hlin
  obtain ⟨W, hW⟩ := hlin'
  obtain ⟨c₁, hc₁, ho₁⟩ := exists_involution_of_fam S h₁
  obtain ⟨c₂, hc₂, ho₂⟩ := exists_involution_of_fam S h₂
  obtain ⟨c₃, hc₃, ho₃⟩ := exists_involution_of_fam S h₃
  obtain ⟨c', hc'R, hc'yb⟩ := hyb
  have hc'1 : c' ≠ 1 := fun h => by
    rw [h, map_one] at hc'yb
    rw [← hc'yb, orderOf_one] at hyb2
    omega
  have hc'c' : c' * c' = 1 := by
    have h1 : c' * c' ∈ R₂ := R₂.mul_mem hc'R hc'R
    refine hnc R₂ h₂ _ h1 fun y => ?_
    have hψ : ψ (c' * c') = 1 := by
      rw [map_mul, hc'yb]
      have := pow_orderOf_eq_one yb
      rwa [hyb2, pow_two] at this
    have hk := hker (MonoidHom.mem_ker.mpr hψ)
    have e := Subgroup.mem_center_iff.mp hk y
    have : c' * c' * y * (c' * c')⁻¹ * y⁻¹ = 1 := by
      rw [← e]
      group
    rw [this]
    exact Subgroup.one_mem _
  have hc'o : orderOf c' = 2 := orderOf_eq_prime (by rw [pow_two]; exact hc'c') hc'1
  have hc'c₂ : c' = c₂ := eq_of_involutions_fam S h₂ hc'R hc₂ hc'o ho₂
  subst hc'c₂
  have hnormR : ∀ x ∈ R₃, c' * x * c'⁻¹ ∈ R₃ := by
    refine conj_mem_of_perfect (S.perf_le h₃).ge c' fun x hx => ?_
    have hmem : ψ (c' * x * c'⁻¹) ∈ R₃.map ψ := by
      rw [map_mul, map_mul, map_inv, hc'yb]
      exact hnorm _ ⟨x, hx, rfl⟩
    obtain ⟨y, hyR, hy⟩ := hmem
    refine ⟨y, hyR, y⁻¹ * (c' * x * c'⁻¹), hker (MonoidHom.mem_ker.mpr ?_), by group⟩
    rw [map_mul, map_inv, hy, inv_mul_cancel]
  have hc₃c : c' * c₃ * c'⁻¹ = c₃ := by
    refine eq_of_involutions_fam S h₃ (hnormR c₃ hc₃) hc₃ ?_ ho₃
    have h := orderOf_injective (MulAut.conj c').toMonoidHom (MulAut.conj c').injective c₃
    simpa [MulAut.conj_apply, ho₃] using h
  have h₃₂ : c₃ * c' = c' * c₃ := by
    have := hc₃c
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  have h₁₂ : c₁ * c' = c' * c₁ :=
    Gaps.standardPair_involutions_commute h2 hW hc₁ hc'R ho₁ hc'o
  have h₁₃ : c₁ * c₃ = c₃ * c₁ := h13 c₁ hc₁ c₃ hc₃
  obtain ⟨W', hW'⟩ := S.sign_linear h₁ h₂ h₃ hc₁ hc'R hc₃ ho₁ hc'o ho₃ h₁₂ h₃₂ h₁₃ h13
    (ne_of_linearBlockStandardPair hW) hne32 (not_commutes_of_linearBlockStandardPair hW) hn32
    ⟨W, hW⟩
  exact ⟨_, Gaps.linearBlockStandardPair_map ψ hker hW'⟩

end Spin

section Model

variable {p f : ℕ} [Fact p.Prime]

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

@[expose] def SignLinear (p f : ℕ) [Fact p.Prime] (t : StatedLieTag) (n e : ℕ) : Prop :=
  ∀ {X : Type} [Group X] (ψ : (Generic.modelUniv t n p e Fact.out).K →* X),
    ψ.ker ≤ Subgroup.center (Generic.modelUniv t n p e Fact.out).K →
    ∀ R₁ ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n p e Fact.out).D,
      ∀ R₂ ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n p e Fact.out).D,
        ∀ R₃ ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n p e Fact.out).D,
          (∃ W, LinearBlockStandardPair (GaloisField p f) W (R₁.map ψ) (R₂.map ψ)) →
            Commutes R₁ R₃ → ¬ Commutes R₃ R₂ → R₃ ≠ R₂ →
              ∀ yb ∈ R₂.map ψ, orderOf yb = 2 → (∀ w ∈ R₃.map ψ, yb * w * yb⁻¹ ∈ R₃.map ψ) →
                ∃ W, LinearBlockStandardPair (GaloisField p f) W (R₂.map ψ) (R₃.map ψ)

theorem signLinear_pOmegaMinus_five (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    SignLinear p f .POmegaMinus 5 f := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hadm : StatedLieAdmissible .POmegaMinus 5 p f := ⟨Fact.out, hf, by norm_num⟩
  intro X _ ψ hker R₁ hR₁ R₂ hR₂ R₃ hR₃ hlin h13 hn hne yb hyb hyb2 hnorm
  have S := spinCtx_pOmegaMinus hadm hp2 hq
  have hL := fun {R : Subgroup (Generic.modelUniv .POmegaMinus 5 p f Fact.out).K}
    (hR : R ∈ Generic.fundamentalSubgroups .POmegaMinus
      (Generic.modelUniv .POmegaMinus 5 p f Fact.out).D) =>
    fundamentalSubgroups_subset_longest (t := .POmegaMinus) (by decide) (by decide) _ hR
  exact linear_pair_of_chain S ψ hker
    (fun R hR r hr h => Gaps.fundNoncentral p .POmegaMinus 5 f trivial hadm (by decide) R
      (longestFundamental_subset .POmegaMinus _ hR) r hr h)
    (hL hR₁) (hL hR₂) (hL hR₃) hlin h13 hn hne hyb hyb2 hnorm

end Model

end CFSG.ClassicalInvolution.RouteD.NonClassical
