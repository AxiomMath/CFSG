module

public import CFSG.ClassicalInvolution.RouteD.TWT4Trich
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
public import Certificates.Certificate3951
public import Certificates.Certificate3952

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.RouteD.TWT4

open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.G2D4Models.Twin
  CFSG.ClassicalInvolution.RouteD.TWZ CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Models.Transfer
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open CFSG.ClassicalInvolution.RouteD.Exotic (commutes_of_commutator_mem_center)
open scoped MatrixGroups commutatorElement

local notation "GFund" => CFSG.ClassicalInvolution.Generic.fundamentalSubgroups

section D4

variable {p f : ℕ} [Fact p.Prime]


theorem d4FundData (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hadm : StatedLieAdmissible .POmegaPlus 4 p f)
    {S : Subgroup (spinGroup (quadPlus 4 (GaloisField p f)))}
    (hS : S ∈ GFund .POmegaPlus (plusDatum 4 (GaloisField p f) (by norm_num))) :
    S ≤ ⁅S, S⁆ ∧ S.map (spinAction (quadPlus 4 (GaloisField p f))) ∈
        fundSet (quadPlus 4 (GaloisField p f)) ∧
      ∀ r ∈ S, spinAction (quadPlus 4 (GaloisField p f)) r = 1 → r = 1 := by
  have hn3 : 3 ≤ 4 := by norm_num
  have : Group.IsPerfect (spinGroup (quadPlus 4 (GaloisField p f))) :=
    isPerfect_spinGroup_quadPlus hn3
  have hperf : ∀ R ∈ GFund .POmegaPlus (plusDatum 4 (GaloisField p f) hn3), R ≤ ⁅R, R⁆ :=
    Gaps.fundPerfect_modelUniv hp2 (t := .POmegaPlus) (n := 4) (e := f) trivial hadm (by omega)
  have hnc : ∀ R ∈ GFund .POmegaPlus (plusDatum 4 (GaloisField p f) hn3),
      ∀ r ∈ R, r ∈ Subgroup.center (spinGroup (quadPlus 4 (GaloisField p f))) → r = 1 :=
    fund_noncentral_modelUniv (p := p) (e := f) (t := .POmegaPlus) (n := 4) trivial hadm (by simp)
  have hcorr := (Exotic.fundCorr_plus hp2 hq (le_refl 4)).1
  refine ⟨hperf S hS, hcorr S hS, ?_⟩
  exact injOn_of_ker_le_center (ker_spinAction_le_center _) fun r hr hcen =>
    hnc S hS r hr (mem_center_of_commutators_central fun y => by
      have := hcen y
      exact this)

theorem sqTrichotomyOn_plus4_aux (hfl : D4FixLift p f) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .POmegaPlus 4 p f) :
    SqTrichotomyOn .POmegaPlus
      ⟨spinGroup (quadPlus 4 (GaloisField p f)), plusDatum 4 (GaloisField p f) (by norm_num)⟩ := by
  have hn3 : 3 ≤ 4 := by norm_num
  obtain ⟨hodd, h4⟩ := card_galoisField_facts hp2 hq
  obtain ⟨-, hF⟩ := CFSG.ClassicalInvolution.RouteD.card_galoisField_of_four_le
    (p := p) (f := f) (by omega)
  obtain ⟨ρ, hρ⟩ := exists_triality hadm h4 hF
  have : Group.IsPerfect (spinGroup (quadPlus 4 (GaloisField p f))) :=
    isPerfect_spinGroup_quadPlus hn3
  have hdim : Module.finrank (GaloisField p f) (Fin 4 ⊕ Fin 4 → GaloisField p f) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  intro X _ θ hθs hθk R R' R₂ hR hR' hR₂ hne x x' x₂ hx hx2 hx1 hx' hx'2 hx'1 hxx' hx₂ hx₂2 hx₂1
    α hα4 hαR hαR' hαR₂
  have hcK : x * x'⁻¹ ∈ Subgroup.center (spinGroup (quadPlus 4 (GaloisField p f))) :=
    hθk (by rw [MonoidHom.mem_ker, map_mul, map_inv, hxx', mul_inv_cancel])
  have hx'inv : x'⁻¹ = x' := inv_eq_of_mul_eq_one_right hx'2
  have hc2 : (x * x'⁻¹) * (x * x'⁻¹) = 1 := by
    have h1 := Subgroup.mem_center_iff.mp hcK x
    have h2 : x * (x * x'⁻¹) = x'⁻¹ := by rw [← mul_assoc, hx2, one_mul]
    have h3 : x * x'⁻¹ * x = x'⁻¹ := by rw [← h1, h2]
    calc (x * x'⁻¹) * (x * x'⁻¹) = (x * x'⁻¹ * x) * x'⁻¹ := by group
      _ = x'⁻¹ * x'⁻¹ := by rw [h3]
      _ = 1 := by rw [hx'inv, hx'2]
  obtain ⟨σ, hσ, hθ⟩ := exists_aut_ordinary hp2 hadm ρ hρ hcK hc2
  have hord : spinAction (quadPlus 4 (GaloisField p f)) (σ x) =
      spinAction (quadPlus 4 (GaloisField p f)) (σ x') := by
    rw [map_mul, map_inv, map_mul, map_inv] at hθ
    exact mul_inv_eq_one.mp hθ
  set θ' : spinGroup (quadPlus 4 (GaloisField p f)) →* X := θ.comp σ.symm.toMonoidHom with hθ'
  have hθ's : Function.Surjective θ' := hθs.comp σ.symm.surjective
  have hθ'k : θ'.ker ≤ Subgroup.center (spinGroup (quadPlus 4 (GaloisField p f))) := by
    intro s hs
    have h1 : σ.symm s ∈ θ.ker := by
      rw [MonoidHom.mem_ker] at hs ⊢
      exact hs
    have h2 := hθk h1
    have : s = σ (σ.symm s) := by simp
    rw [this]
    rw [Subgroup.mem_center_iff] at h2 ⊢
    intro y
    have := h2 (σ.symm y)
    simpa using congrArg σ this
  have hθ'σ : ∀ s, θ' (σ s) = θ s := fun s => by simp [hθ']
  have hθ'σ' : ∀ s, θ' (σ.toMonoidHom s) = θ s := fun s => by simp [hθ']
  have hlift := liftSimFr_of_d4FixLift hfl hp2 hq θ' hθ'k
  obtain ⟨hRp, hRc, hRi⟩ := d4FundData hp2 hq hadm (hσ R hR)
  obtain ⟨hR'p, hR'c, hR'i⟩ := d4FundData hp2 hq hadm (hσ R' hR')
  obtain ⟨hR₂p, hR₂c, hR₂i⟩ := d4FundData hp2 hq hadm (hσ R₂ hR₂)
  have hne' : R.map σ.toMonoidHom ≠ R'.map σ.toMonoidHom := by
    intro h
    apply hne
    have := congrArg (fun S : Subgroup (spinGroup (quadPlus 4 (GaloisField p f))) =>
      S.map σ.symm.toMonoidHom) h
    simpa [Subgroup.map_map] using this
  have hres := spin_sq_trichotomy_ord (θ := θ') (X := X) hodd (five_le_card_galoisField hq)
    (nondegenerate_polarBilin_quadPlus 4 _) (range_spinAction_quadPlus hn3)
    (centerScalar_quadPlus hn3) hdim hθ's hθ'k hlift hRp hR'p hRc hR'c hRi hR'i hne'
    (Subgroup.mem_map_of_mem _ hx) (by rw [← map_mul, hx2, map_one]) (fun h => hx1
      (σ.injective (by simpa using h)))
    (Subgroup.mem_map_of_mem _ hx') (by rw [← map_mul, hx'2, map_one]) (fun h => hx'1
      (σ.injective (by simpa using h))) hord hR₂p hR₂c hR₂i
    (Subgroup.mem_map_of_mem _ hx₂) (by rw [← map_mul, hx₂2, map_one]) (fun h => hx₂1
      (σ.injective (by simpa using h))) α hα4
    (by rintro _ ⟨r, hr, rfl⟩; rw [hθ'σ']; exact hαR r hr)
    (by rintro _ ⟨r, hr, rfl⟩; rw [hθ'σ']; exact hαR' r hr)
    (by rintro _ ⟨r, hr, rfl⟩; rw [hθ'σ']; exact hαR₂ r hr)
  rcases hres with h | h | ⟨g', hg1, r₁', hr₁', hg2⟩
  · exact Or.inl h
  · refine Or.inr (Or.inl ?_)
    rw [h, hθ'σ']
  · refine Or.inr (Or.inr ⟨σ.symm g', ?_, ?_⟩)
    · intro r hr
      have e1 : ∀ r₀ : spinGroup (quadPlus 4 (GaloisField p f)),
          θ' (g' * σ r₀ * g'⁻¹) = θ (σ.symm g' * r₀ * (σ.symm g')⁻¹) := fun r₀ => by
        simp [hθ']
      have := hg1 (σ r) ⟨r, hr, rfl⟩
      rw [hθ'σ', e1] at this
      exact this
    · obtain ⟨r₁, hr₁, rfl⟩ := hr₁'
      refine ⟨r₁, hr₁, ?_⟩
      have e1 : ∀ r₀ : spinGroup (quadPlus 4 (GaloisField p f)),
          θ' (g' * σ.toMonoidHom r₀ * g'⁻¹) = θ (σ.symm g' * r₀ * (σ.symm g')⁻¹) := fun r₀ => by
        simp [hθ']
      rw [e1] at hg2
      exact hg2

theorem sqTrichotomyOn_plus4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .POmegaPlus 4 p f) :
    SqTrichotomyOn .POmegaPlus
      (CFSG.ClassicalInvolution.Generic.modelUniv .POmegaPlus 4 p f Fact.out) := by
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus 4 (GaloisField p f)),
      plusDatum 4 (GaloisField p f) (by norm_num)⟩ → SqTrichotomyOn .POmegaPlus M := by
    intro M hM
    subst hM
    exact sqTrichotomyOn_plus4_aux d4FixLift_proved hp2 hq hadm
  exact key _ (CFSG.ClassicalInvolution.ModelFacts.modelUniv_POmegaPlus (by norm_num))

end D4

end CFSG.ClassicalInvolution.RouteD.TWT4
