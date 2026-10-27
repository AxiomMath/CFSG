module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyFacts
public import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2Main
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcSigns
public import CFSG.ClassicalInvolution.Balance.BootstrapMember
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPair

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.LieType.Universal
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)
open scoped MatrixGroups commutatorElement

@[expose] def OrthBranch (p : ℕ) [Fact p.Prime] (t : StatedLieTag) (n e : ℕ) : Prop :=
  p ≠ 2 → 5 ≤ p ^ e →
    ∀ R₁ ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D,
    ∀ R₂ ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D,
    ∀ c₁ c₂ : (Generic.modelUniv t n p e Fact.out).K, c₁ ∈ R₁ → c₂ ∈ R₂ →
      orderOf c₁ = 2 → orderOf c₂ = 2 →
      (∀ r ∈ R₁, c₂ * r = r * c₂) → (∀ r ∈ R₂, c₁ * r = r * c₁) →
      R₁ = R₂ ∨ Commutes R₁ R₂

@[expose] def A2Branch (p : ℕ) [Fact p.Prime] (t : StatedLieTag) (n e : ℕ) : Prop :=
  p ≠ 2 → 5 ≤ p ^ e →
    ∀ R₁ ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D,
    ∀ R₂ ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D,
    ∀ c₁ c₂ : (Generic.modelUniv t n p e Fact.out).K, c₁ ∈ R₁ → c₂ ∈ R₂ →
      orderOf c₁ = 2 → orderOf c₂ = 2 → c₁ * c₂ = c₂ * c₁ →
      ¬ ((∀ r ∈ R₁, c₂ * r = r * c₂) ∧ ∀ r ∈ R₂, c₁ * r = r * c₁) →
      (∃ W, LinearBlockStandardPair (GaloisField p e) W R₁ R₂) ∨
        ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W R₁ R₂

@[expose] def A2BranchLeft (p : ℕ) [Fact p.Prime] (t : StatedLieTag) (n e : ℕ) : Prop :=
  p ≠ 2 → 5 ≤ p ^ e →
    ∀ R₁ ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D,
    ∀ R₂ ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D,
    ∀ c₁ c₂ : (Generic.modelUniv t n p e Fact.out).K, c₁ ∈ R₁ → c₂ ∈ R₂ →
      orderOf c₁ = 2 → orderOf c₂ = 2 → c₁ * c₂ = c₂ * c₁ →
      ¬ (∀ r ∈ R₁, c₂ * r = r * c₂) →
      (∃ W, LinearBlockStandardPair (GaloisField p e) W R₁ R₂) ∨
        ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W R₁ R₂

variable {p : ℕ} [Fact p.Prime]

theorem A2BranchLeft.a2Branch {t : StatedLieTag} {n e : ℕ} (h : A2BranchLeft p t n e) :
    A2Branch p t n e := by
  intro hp2 hq R₁ h₁ R₂ h₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ hcomm hn
  by_cases h₂₁ : ∀ r ∈ R₁, c₂ * r = r * c₂
  · have h₁₂ : ¬ ∀ r ∈ R₂, c₁ * r = r * c₁ := fun h' => hn ⟨h₂₁, h'⟩
    rcases h hp2 hq R₂ h₂ R₁ h₁ c₂ c₁ hc₂ hc₁ ho₂ ho₁ hcomm.symm h₁₂ with ⟨W, hW⟩ | ⟨W, hW⟩
    · exact Or.inl ⟨W, linearBlockStandardPair_symm hW⟩
    · exact Or.inr ⟨W, unitaryBlockStandardPair_symm hW⟩
  · exact h hp2 hq R₁ h₁ R₂ h₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ hcomm h₂₁

theorem standardPairDichotomy_of_branches {t : StatedLieTag} {n e : ℕ} (hO : OrthBranch p t n e)
    (hA : A2Branch p t n e) : StandardPairDichotomy p t n e := by
  intro hp2 hq R₁ h₁ R₂ h₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ hcomm
  by_cases h : (∀ r ∈ R₁, c₂ * r = r * c₂) ∧ ∀ r ∈ R₂, c₁ * r = r * c₁
  · rcases hO hp2 hq R₁ h₁ R₂ h₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ h.1 h.2 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases hA hp2 hq R₁ h₁ R₂ h₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ hcomm h with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

theorem standardPairDichotomyFE_of_branches
    (hO : ∀ (t : StatedLieTag) (e : ℕ),
      (t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6) →
        StatedLieAdmissible t 0 p e → OrthBranch p t 0 e)
    (hA : ∀ (t : StatedLieTag) (e : ℕ),
      (t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6) →
        StatedLieAdmissible t 0 p e → A2Branch p t 0 e) : StandardPairDichotomyFE p :=
  fun t e ht hadm => standardPairDichotomy_of_branches (hO t e ht hadm) (hA t e ht hadm)

section Involutions

variable {F : Type} [Field F] [Finite F] {P : Type*} [Group P]

theorem mul_comm_of_orderOf_eq_two_of_equiv_sl2 (hodd : Odd (Nat.card F)) (e : P ≃* SL(2, F))
    {c : P} (hc : orderOf c = 2) (r : P) : c * r = r * c := by
  have h := (orderOf_eq_two_iff_of_equiv_sl2 hodd e c).1 hc
  have hcent : e c ∈ Subgroup.center SL(2, F) := by
    rw [show e c = -1 from e.eq_symm_apply.1 h]
    exact (mem_center_sl2_iff _).2 (Or.inr rfl)
  exact (Subgroup.mem_center_iff.1 ((mem_center_iff_of_equiv_sl2 e c).2 hcent) r).symm

end Involutions

section Fundamental

variable {t : StatedLieTag} {n e : ℕ}

theorem odd_natCard_galoisField_of_five_le (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) :
    Odd (Nat.card (GaloisField p e)) := by
  have hf : e ≠ 0 := by
    rintro rfl
    simp at hq
  rw [GaloisField.card p e hf]
  exact (Fact.out : p.Prime).odd_of_ne_two hp2 |>.pow

theorem mul_comm_of_orderOf_eq_two_of_mem_longestFundamental (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hfund : Generic.IsFundTag t) (hadm : StatedLieAdmissible t n p e) (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4)
    {R : Subgroup (Generic.modelUniv t n p e Fact.out).K}
    (hR : R ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D)
    {c : (Generic.modelUniv t n p e Fact.out).K} (hc : c ∈ R) (ho : orderOf c = 2) :
    ∀ r ∈ R, c * r = r * c := by
  obtain ⟨φ⟩ := nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 hfund hadm hG2 hD4
    (longestFundamental_subset t _ hR)
  intro r hr
  have := mul_comm_of_orderOf_eq_two_of_equiv_sl2 (odd_natCard_galoisField_of_five_le hp2 hq) φ
    (c := ⟨c, hc⟩) ((Subgroup.orderOf_mk c hc).trans ho) ⟨r, hr⟩
  exact congrArg Subtype.val this

theorem commutator_eq_of_mem_longestFundamental (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hfund : Generic.IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    {R : Subgroup (Generic.modelUniv t n p e Fact.out).K}
    (hR : R ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D) : ⁅R, R⁆ = R := by
  refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_)
    (fundPerfect_core t n p e hp2 hfund hadm (le_trans (by norm_num) hq) R
      (longestFundamental_subset t _ hR))
  exact R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb)

end Fundamental

section Frame

variable {K G : Type*} [Group K] [Group G]

theorem orthBranch_of_frame (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K)
    {𝓡 : Set (Subgroup K)} {𝒯 : Subgroup K} (hframe : PairFrame 𝒯 𝓡)
    (hconj : ∀ R ∈ 𝓡, ∀ g : K, conjSub g R ∈ 𝓡) (hperf : ∀ R ∈ 𝓡, ⁅R, R⁆ = R)
    (hcent : ∀ R ∈ 𝓡, ∀ c ∈ R, c * c = 1 → ∀ r ∈ R, c * r = r * c)
    {ι : Type*} (L : ι → Subgroup G) (d : ι → G)
    (hcl : ∀ R ∈ 𝓡, ∀ c ∈ R, c * c = 1 → c ≠ 1 → c ∈ 𝒯 →
      ∃ i, R.map ψ = L i ∧ ψ c = d i)
    (hco : ∀ i j, (∀ y ∈ L j, d i * y = y * d i) → (∀ y ∈ L i, d j * y = y * d j) →
      L i = L j ∨ ∀ x ∈ L i, ∀ y ∈ L j, x * y = y * x)
    {R₁ R₂ : Subgroup K} (h₁ : R₁ ∈ 𝓡) (h₂ : R₂ ∈ 𝓡) {c₁ c₂ : K} (hc₁ : c₁ ∈ R₁) (hc₂ : c₂ ∈ R₂)
    (hsq₁ : c₁ * c₁ = 1) (hne₁ : c₁ ≠ 1) (hsq₂ : c₂ * c₂ = 1) (hne₂ : c₂ ≠ 1)
    (h₂₁ : ∀ r ∈ R₁, c₂ * r = r * c₂) (h₁₂ : ∀ r ∈ R₂, c₁ * r = r * c₁) :
    R₁ = R₂ ∨ Commutes R₁ R₂ := by
  obtain ⟨g, hg₁, hg₂⟩ := hframe R₁ h₁ R₂ h₂ c₁ hc₁ c₂ hc₂ (hcent R₁ h₁ c₁ hc₁ hsq₁)
    (hcent R₂ h₂ c₂ hc₂ hsq₂) h₂₁ h₁₂
  have hmem : ∀ {R : Subgroup K} {x : K}, x ∈ conjSub g⁻¹ R ↔ g * x * g⁻¹ ∈ R := fun {R x} => by
    rw [mem_conjSub_iff, inv_inv]
  have hconjmem : ∀ {R : Subgroup K} {y : K}, y ∈ R → g⁻¹ * y * g ∈ conjSub g⁻¹ R :=
    fun {R y} hy => by rw [hmem]; simpa [mul_assoc] using hy
  have hsqc : ∀ {c : K}, c * c = 1 → (g⁻¹ * c * g) * (g⁻¹ * c * g) = 1 := fun {c} h => by
    calc (g⁻¹ * c * g) * (g⁻¹ * c * g) = g⁻¹ * (c * c) * g := by group
      _ = 1 := by rw [h]; group
  have hnec : ∀ {c : K}, c ≠ 1 → g⁻¹ * c * g ≠ 1 := fun {c} h h' => h (by
    have : c = g * (g⁻¹ * c * g) * g⁻¹ := by group
    rw [this, h']; group)
  obtain ⟨i₁, hi₁, hd₁⟩ := hcl (conjSub g⁻¹ R₁) (hconj R₁ h₁ _) (g⁻¹ * c₁ * g) (hconjmem hc₁)
    (hsqc hsq₁) (hnec hne₁) hg₁
  obtain ⟨i₂, hi₂, hd₂⟩ := hcl (conjSub g⁻¹ R₂) (hconj R₂ h₂ _) (g⁻¹ * c₂ * g) (hconjmem hc₂)
    (hsqc hsq₂) (hnec hne₂) hg₂
  have hcen : ∀ {R : Subgroup K} {c : K}, (∀ r ∈ R, c * r = r * c) →
      ∀ r ∈ conjSub g⁻¹ R, (g⁻¹ * c * g) * r = r * (g⁻¹ * c * g) := fun {R c} h r hr => by
    have h1 := h (g * r * g⁻¹) (hmem.1 hr)
    calc g⁻¹ * c * g * r = g⁻¹ * (c * (g * r * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * r * g⁻¹) * c) * g := by rw [h1]
      _ = r * (g⁻¹ * c * g) := by group
  have hy₁ : ∀ y ∈ L i₁, d i₂ * y = y * d i₂ := fun y hy => by
    rw [← hi₁] at hy
    obtain ⟨r, hr, rfl⟩ := hy
    rw [← hd₂, ← map_mul, ← map_mul, hcen h₂₁ r hr]
  have hy₂ : ∀ y ∈ L i₂, d i₁ * y = y * d i₁ := fun y hy => by
    rw [← hi₂] at hy
    obtain ⟨r, hr, rfl⟩ := hy
    rw [← hd₁, ← map_mul, ← map_mul, hcen h₁₂ r hr]
  have hP₁ := hperf _ (hconj R₁ h₁ g⁻¹)
  have hP₂ := hperf _ (hconj R₂ h₂ g⁻¹)
  rcases hco i₁ i₂ hy₂ hy₁ with heq | hcm
  · left
    have hmap : (conjSub g⁻¹ R₁).map ψ = (conjSub g⁻¹ R₂).map ψ := by rw [hi₁, hi₂, heq]
    have hR := eq_of_map_eq_of_isPerfect ψ hker hP₁ hP₂ hmap
    ext x
    have hx : ∀ {R : Subgroup K}, x ∈ R ↔ g⁻¹ * x * g ∈ conjSub g⁻¹ R := fun {R} => by
      rw [hmem]; simp [mul_assoc]
    rw [hx (R := R₁), hx (R := R₂), hR]
  · right
    have hab : ∀ a ∈ conjSub g⁻¹ R₁, ∀ b ∈ conjSub g⁻¹ R₂, ψ a * ψ b = ψ b * ψ a :=
      fun a ha b hb => by
        have h1 : ψ a ∈ L i₁ := hi₁ ▸ Subgroup.mem_map_of_mem ψ ha
        have h2 : ψ b ∈ L i₂ := hi₂ ▸ Subgroup.mem_map_of_mem ψ hb
        exact hcm _ h1 _ h2
    have hcomm' : Commutes (conjSub g⁻¹ R₁) (conjSub g⁻¹ R₂) := by
      intro a ha b hb
      have hcen' : ∀ r ∈ conjSub g⁻¹ R₁, b * r * b⁻¹ * r⁻¹ ∈ Subgroup.center K := fun r hr => by
        refine hker ?_
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, ← hab r hr b hb]
        group
      exact ((commute_of_commutator_central _ hP₁.ge b hcen') a ha).symm
    intro a ha b hb
    have h1 := hcomm' (g⁻¹ * a * g) (hconjmem ha) (g⁻¹ * b * g) (hconjmem hb)
    calc a * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [h1]
      _ = b * a := by group

end Frame

end CFSG.ClassicalInvolution.ModelFacts
