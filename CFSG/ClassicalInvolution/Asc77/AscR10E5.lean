module

public import CFSG.ClassicalInvolution.Asc77.AscR10E1
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcOrthHull

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)
open CFSG.ClassicalInvolution.Asc77.T3CII (GenSq eq_of_map_eq_of_genSq
  commute_of_map_commute_of_genSq genSq_of_equiv_sl2 ne_two_of_pow_eq_three
  eq_three_of_pow_eq_three neg_one_commutator_sl2_three)
open scoped MatrixGroups commutatorElement



@[expose] def OrthBranch3 (p : ℕ) [Fact p.Prime] (t : StatedLieTag) (n e : ℕ) : Prop :=
  p ^ e = 3 →
    ∀ R₁ ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D,
    ∀ R₂ ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D,
    ∀ c₁ c₂ : (Generic.modelUniv t n p e Fact.out).K, c₁ ∈ R₁ → c₂ ∈ R₂ →
      orderOf c₁ = 2 → orderOf c₂ = 2 →
      (∀ r ∈ R₁, c₂ * r = r * c₂) → (∀ r ∈ R₂, c₁ * r = r * c₁) →
      R₁ = R₂ ∨ Commutes R₁ R₂

section Fundamental

variable {p e : ℕ} [Fact p.Prime] {t : StatedLieTag} {n : ℕ}

theorem odd_natCard_galoisField_of_pow_eq_three (h3 : p ^ e = 3) :
    Odd (Nat.card (GaloisField p e)) := by
  have he : e ≠ 0 := by
    rintro rfl
    simp at h3
  rw [GaloisField.card p e he, h3]
  decide

theorem genSq_of_mem_longestFundamental3 (h3 : p ^ e = 3) (hfund : Generic.IsFundTag t)
    (hadm : StatedLieAdmissible t n p e) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    {R : Subgroup (Generic.modelUniv t n p e Fact.out).K}
    (hR : R ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D) : GenSq R := by
  have hp2 := ne_two_of_pow_eq_three h3
  obtain ⟨φ⟩ := nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 hfund hadm hG2 hD4
    (longestFundamental_subset t _ hR)
  obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
  exact genSq_of_equiv_sl2 φ

theorem mul_comm_of_orderOf_eq_two_of_mem_longestFundamental3 (h3 : p ^ e = 3)
    (hfund : Generic.IsFundTag t) (hadm : StatedLieAdmissible t n p e) (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4) {R : Subgroup (Generic.modelUniv t n p e Fact.out).K}
    (hR : R ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D)
    {c : (Generic.modelUniv t n p e Fact.out).K} (hc : c ∈ R) (ho : orderOf c = 2) :
    ∀ r ∈ R, c * r = r * c := by
  have hp2 := ne_two_of_pow_eq_three h3
  obtain ⟨φ⟩ := nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 hfund hadm hG2 hD4
    (longestFundamental_subset t _ hR)
  intro r hr
  have := mul_comm_of_orderOf_eq_two_of_equiv_sl2 (odd_natCard_galoisField_of_pow_eq_three h3) φ
    (c := ⟨c, hc⟩) ((Subgroup.orderOf_mk c hc).trans ho) ⟨r, hr⟩
  exact congrArg Subtype.val this

theorem mem_commutator_of_orderOf_eq_two_of_mem_longestFundamental3 (h3 : p ^ e = 3)
    (hfund : Generic.IsFundTag t) (hadm : StatedLieAdmissible t n p e) (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4) {R : Subgroup (Generic.modelUniv t n p e Fact.out).K}
    (hR : R ∈ longestFundamental (Generic.modelUniv t n p e Fact.out).D)
    {c : (Generic.modelUniv t n p e Fact.out).K} (hc : c ∈ R) (ho : orderOf c = 2) :
    c ∈ ⁅R, R⁆ := by
  have hp2 := ne_two_of_pow_eq_three h3
  obtain ⟨φ⟩ := nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 hfund hadm hG2 hD4
    (longestFundamental_subset t _ hR)
  have hodd := odd_natCard_galoisField_of_pow_eq_three h3
  have hF : Nat.card (GaloisField p e) = 3 := by
    rw [GaloisField.card p e (by rintro rfl; simp at h3), h3]
  obtain ⟨A, B, hAB⟩ := neg_one_commutator_sl2_three hF
  have h1 := (orderOf_eq_two_iff_of_equiv_sl2 hodd φ ⟨c, hc⟩).1
    ((Subgroup.orderOf_mk c hc).trans ho)
  have h2 : (⟨c, hc⟩ : R) = ⁅φ.symm A, φ.symm B⁆ := by
    rw [h1, ← hAB, map_commutatorElement]
  have h3' : c = ((⁅φ.symm A, φ.symm B⁆ : R) : (Generic.modelUniv t n p e Fact.out).K) := by
    rw [← h2]
  rw [h3']
  rw [commutatorElement_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_carrier.2 (φ.symm A).2)
    (Subgroup.mem_carrier.2 (φ.symm B).2)

end Fundamental

section Frame

variable {K G : Type*} [Group K] [Group G]

theorem orthBranch_of_frame3 (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K)
    (hk2 : ∀ x ∈ ψ.ker, x * x = 1) {𝓡 : Set (Subgroup K)} {𝒯 : Subgroup K} (hframe : PairFrame 𝒯 𝓡)
    (hconj : ∀ R ∈ 𝓡, ∀ g : K, Generic.conjSub g R ∈ 𝓡) (hgs : ∀ R ∈ 𝓡, GenSq R)
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
  have hmem : ∀ {R : Subgroup K} {x : K}, x ∈ Generic.conjSub g⁻¹ R ↔ g * x * g⁻¹ ∈ R :=
    fun {R x} => by
    rw [Generic.mem_conjSub_iff, inv_inv]
  have hconjmem : ∀ {R : Subgroup K} {y : K}, y ∈ R → g⁻¹ * y * g ∈ Generic.conjSub g⁻¹ R :=
    fun {R y} hy => by rw [hmem]; simpa [mul_assoc] using hy
  have hsqc : ∀ {c : K}, c * c = 1 → (g⁻¹ * c * g) * (g⁻¹ * c * g) = 1 := fun {c} h => by
    calc (g⁻¹ * c * g) * (g⁻¹ * c * g) = g⁻¹ * (c * c) * g := by group
      _ = 1 := by rw [h]; group
  have hnec : ∀ {c : K}, c ≠ 1 → g⁻¹ * c * g ≠ 1 := fun {c} h h' => h (by
    have : c = g * (g⁻¹ * c * g) * g⁻¹ := by group
    rw [this, h']; group)
  obtain ⟨i₁, hi₁, hd₁⟩ := hcl (Generic.conjSub g⁻¹ R₁) (hconj R₁ h₁ _) (g⁻¹ * c₁ * g)
    (hconjmem hc₁)
    (hsqc hsq₁) (hnec hne₁) hg₁
  obtain ⟨i₂, hi₂, hd₂⟩ := hcl (Generic.conjSub g⁻¹ R₂) (hconj R₂ h₂ _) (g⁻¹ * c₂ * g)
    (hconjmem hc₂)
    (hsqc hsq₂) (hnec hne₂) hg₂
  have hcen : ∀ {R : Subgroup K} {c : K}, (∀ r ∈ R, c * r = r * c) →
      ∀ r ∈ Generic.conjSub g⁻¹ R, (g⁻¹ * c * g) * r = r * (g⁻¹ * c * g) := fun {R c} h r hr => by
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
  have hP₁ := hgs _ (hconj R₁ h₁ g⁻¹)
  have hP₂ := hgs _ (hconj R₂ h₂ g⁻¹)
  rcases hco i₁ i₂ hy₂ hy₁ with heq | hcm
  · left
    have hmap : (Generic.conjSub g⁻¹ R₁).map ψ = (Generic.conjSub g⁻¹ R₂).map ψ := by
      rw [hi₁, hi₂, heq]
    have hR := eq_of_map_eq_of_genSq ψ hker hk2 hP₁ hP₂ hmap
    ext x
    have hx : ∀ {R : Subgroup K}, x ∈ R ↔ g⁻¹ * x * g ∈ Generic.conjSub g⁻¹ R := fun {R} => by
      rw [hmem]; simp [mul_assoc]
    rw [hx (R := R₁), hx (R := R₂), hR]
  · right
    have hab : ∀ a ∈ Generic.conjSub g⁻¹ R₁, ∀ b ∈ Generic.conjSub g⁻¹ R₂, ψ a * ψ b = ψ b * ψ a :=
      fun a ha b hb => by
        have h1 : ψ a ∈ L i₁ := hi₁ ▸ Subgroup.mem_map_of_mem ψ ha
        have h2 : ψ b ∈ L i₂ := hi₂ ▸ Subgroup.mem_map_of_mem ψ hb
        exact hcm _ h1 _ h2
    have hcomm' : Commutes (Generic.conjSub g⁻¹ R₁) (Generic.conjSub g⁻¹ R₂) := by
      intro a ha b hb
      exact commute_of_map_commute_of_genSq ψ hker hk2 hP₁ (fun a ha => hab a ha b hb) a ha
    intro a ha b hb
    have h1 := hcomm' (g⁻¹ * a * g) (hconjmem ha) (g⁻¹ * b * g) (hconjmem hb)
    calc a * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [h1]
      _ = b * a := by group

end Frame

section Assembly

variable {p e f : ℕ} [Fact p.Prime]

theorem orthBranch_of_hullEmbedding3 {t : StatedLieTag} {τ : Tag} (h3 : p ^ e = 3)
    (hqf : 5 ≤ p ^ f) (hfund : Generic.IsFundTag t) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hne2 : ¬ (t = .PSL ∧ (0 : ℕ) = 2)) (hadm : StatedLieAdmissible t 0 p e)
    (ψ : (Generic.modelUniv t 0 p e Fact.out).K →* ModGL τ (GaloisField p f))
    (hψ : ∀ x, ψ x ∈ adjointGroup τ (GaloisField p f))
    (hker : ψ.ker ≤ Subgroup.center (Generic.modelUniv t 0 p e Fact.out).K)
    (hk2 : ∀ x ∈ ψ.ker, x * x = 1)
    (𝒯 : Subgroup (Generic.modelUniv t 0 p e Fact.out).K)
    (hT : ∀ c ∈ 𝒯, ∃ b : Fin τ.rank → (GaloisField p f)ˣ,
      (∀ i, b i = 1 ∨ b i = -1) ∧ ψ c = rootDiagUnit τ b)
    (hframe : PairFrame 𝒯 (fundamentalSubgroups t (Generic.modelUniv t 0 p e Fact.out).D))
    (hsingle : FundamentalSingleClass t (Generic.modelUniv t 0 p e Fact.out).D)
    {Rθ : Subgroup (Generic.modelUniv t 0 p e Fact.out).K}
    (hRθ𝓡 : Rθ ∈ fundamentalSubgroups t (Generic.modelUniv t 0 p e Fact.out).D)
    {θ : Fin τ.rank → ℤ} (hθ : IsLongRoot τ θ)
    (hhull : Rθ.map ψ ≤ rootRankOneGroup τ (GaloisField p f) θ)
    (hsat : rootRankOneGroup τ (GaloisField p f) θ ⊓ ψ.range ≤ Rθ.map ψ)
    (hlong : ∀ (b : Fin τ.rank → (GaloisField p f)ˣ) (γ : Fin τ.rank → ℤ)
      (hγ : γ ∈ kernelRoots (maskChar (signTupleBits b))),
      componentRootSpan (GaloisField p f) (maskChar (signTupleBits b)) ⟦⟨γ, hγ⟩⟧ =
        rootRankOneGroup τ (GaloisField p f) γ → IsLongRoot τ γ) :
    OrthBranch3 p t 0 e := by
  have hp2 : p ≠ 2 := ne_two_of_pow_eq_three h3
  intro _ R₁ h₁ R₂ h₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ h₂₁ h₁₂
  have hK : ringChar (GaloisField p f) ≠ 2 := by
    rw [ringChar.eq (GaloisField p f) p]
    exact hp2
  have hsq : ∀ {c : (Generic.modelUniv t 0 p e Fact.out).K}, orderOf c = 2 → c * c = 1 :=
    fun {c} h => by
      rw [← pow_two]
      exact h ▸ pow_orderOf_eq_one c
  have hne : ∀ {c : (Generic.modelUniv t 0 p e Fact.out).K}, orderOf c = 2 → c ≠ 1 :=
    fun {c} h h1 => by
      rw [h1, orderOf_one] at h
      omega
  have hcentral : ∀ R ∈ fundamentalSubgroups t (Generic.modelUniv t 0 p e Fact.out).D,
      ∀ x ∈ R, x ∈ Subgroup.center (Generic.modelUniv t 0 p e Fact.out).K → x = 1 :=
    fun R hR x hx hxc =>
      fundNoncentral_generic p t 0 e hfund hadm hne2 R hR x hx fun y => by
        rw [Subgroup.mem_center_iff] at hxc
        have h2 : x * y * x⁻¹ * y⁻¹ = 1 := by
          calc x * y * x⁻¹ * y⁻¹ = (y * x) * x⁻¹ * y⁻¹ := by rw [hxc y]
            _ = 1 := by group
        rw [h2]
        exact Subgroup.one_mem _
  have hinj : ∀ R ∈ fundamentalSubgroups t (Generic.modelUniv t 0 p e Fact.out).D,
      ∀ x ∈ R, ψ x = 1 → x = 1 := fun R hR x hx h1 => hcentral R hR x hx (hker h1)
  refine orthBranch_of_frame3 ψ hker hk2 (𝓡 := longestFundamental _) (𝒯 := 𝒯)
    (fun R₁' h₁' R₂' h₂' => hframe R₁' (longestFundamental_subset t _ h₁') R₂'
      (longestFundamental_subset t _ h₂'))
    (fun R hR g => conjSub_mem_longestFundamental hR g)
    (fun R hR => genSq_of_mem_longestFundamental3 h3 hfund hadm hG2 hD4 hR)
    (fun R hR c hc hcc r hr => ?_)
    (ι := {γ : Fin τ.rank → ℤ // IsLongRoot τ γ ∧
      ∃ x ∈ rootRankOneGroup τ (GaloisField p f) γ ⊓ ψ.range,
        ∃ y ∈ rootRankOneGroup τ (GaloisField p f) γ ⊓ ψ.range, x * y ≠ y * x})
    (fun i => rootRankOneGroup τ (GaloisField p f) i.1 ⊓ ψ.range)
    (fun i => rootTorusSL2 τ (GaloisField p f) i.1 (-1))
    (fun R hR c hc hcc hc1 hc𝒯 => ?_)
    (fun i j h _ => ?_)
    h₁ h₂ hc₁ hc₂ (hsq ho₁) (hne ho₁) (hsq ho₂) (hne ho₂) h₂₁ h₁₂
  · by_cases h1 : c = 1
    · rw [h1]
      simp
    · exact mul_comm_of_orderOf_eq_two_of_mem_longestFundamental3 h3 hfund hadm hG2 hD4 hR hc
        (orderOf_eq_prime (by rwa [pow_two]) h1) r hr
  · obtain ⟨g, hg⟩ := hsingle Rθ hRθ𝓡 R (longestFundamental_subset t _ hR)
    have hRf := longestFundamental_subset t _ hR
    obtain ⟨b, hb, hψc⟩ := hT c hc𝒯
    subst hg
    have hcg : g⁻¹ * c * g ∈ Rθ := Generic.mem_conjSub_iff.1 hc
    obtain ⟨γ, hγ, h1, h2⟩ := exists_rootRankOneGroup_map_conj_eq_hull hp2 hqf ψ hψ hθ hhull hsat
      (hinj Rθ hRθ𝓡) hlong hcg hcc hc1 hb hψc
    refine ⟨⟨γ, hγ, ?_⟩, h1, h2⟩
    by_contra hcomm
    push Not at hcomm
    rw [← h1] at hcomm
    have hle : ⁅Generic.conjSub g Rθ, Generic.conjSub g Rθ⁆ ≤
        Subgroup.center (Generic.modelUniv t 0 p e Fact.out).K := by
      refine Subgroup.commutator_le.2 fun r hr s hs => ?_
      refine hker ?_
      rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
      have := hcomm (ψ r) (Subgroup.mem_map_of_mem ψ hr) (ψ s) (Subgroup.mem_map_of_mem ψ hs)
      rw [this]
      group
    exact hc1 (hcentral _ hRf c hc (hle (mem_commutator_of_orderOf_eq_two_of_mem_longestFundamental3
      h3 hfund hadm hG2 hD4 hR hc (orderOf_eq_prime (by rwa [pow_two]) hc1))))
  · have hev := even_two_mul_iform_div_of_commute_of_nonabelian hK i.2.1.1 j.2.1.1
      (N := rootRankOneGroup τ (GaloisField p f) j.1 ⊓ ψ.range) inf_le_left j.2.2 h
    rcases i.2.1.eq_or_eq_neg_or_iform_eq_zero j.2.1.1 hev with h1 | h1 | h0
    · left
      simp only [h1]
    · left
      simp only [h1]
      rw [rootRankOneGroup_eq_sup i.2.1.1, rootRankOneGroup_eq_sup (IsRoot.neg i.2.1.1), neg_neg,
        sup_comm]
    · right
      exact fun x hx y hy => i.2.1.commute_rootRankOneGroup j.2.1.1 h0 x hx.1 y hy.1

end Assembly

end CFSG.ClassicalInvolution.ModelFacts
