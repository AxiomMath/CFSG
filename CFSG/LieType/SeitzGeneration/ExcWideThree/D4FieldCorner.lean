module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4FieldCaseA
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4Fixed

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent
  CFSG.RankThree.PartOne.CTP
  CFSG.LieType.SeitzGeneration.ExcOuterLeOne
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

section Corner


theorem rootDiagAut_mem_inner_D4_of_odd (K : Type) [Field K] [Finite K] (h : ¬ 2 ∣ Nat.card K - 1)
    (a : Fin Tag.D4.rank → Kˣ) : rootDiagAut Tag.D4 K a ∈ inner (adjointGroup Tag.D4 K) := by
  classical
  set M := Tag.D4.cartan.transpose with hM
  set R := (CFSG.LocalAnalysis.ComponentInitial.monomialHom (G := Kˣ) M).range with hR
  have h4 : R.index ∣ 4 := by
    have h1 := (CFSG.LocalAnalysis.ComponentInitial.index_range_monomialHom_dvd K M).2
    rwa [hM, Matrix.det_transpose, det_cartan_D4] at h1
  have hcard : R.index ∣ (Nat.card K - 1) ^ Tag.D4.rank := by
    have h1 := R.index_dvd_card
    rwa [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Nat.card_units] at h1
  have h1 : R.index = 1 := by
    have h2 : R.index ∣ 2 ^ 2 := by simpa using h4
    obtain ⟨i, hi, hRi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simpa using hRi
    · exfalso
      have h2R : 2 ∣ R.index := by rw [hRi]; exact dvd_pow_self 2 hi0.ne'
      exact h (Nat.prime_two.dvd_of_dvd_pow (h2R.trans hcard))
  rw [Subgroup.index_eq_one] at h1
  obtain ⟨t, ht⟩ : a ∈ R := h1 ▸ Subgroup.mem_top a
  rw [← ht, monomialHom_transpose_cartan]
  exact rootDiagAut_cartanChar_mem_inner t

theorem eq_one_of_mem_inner_of_fix_D4 {K : Type} [Field K] [Finite K] (T : K ≃+* K)
    (hT3 : T ^ 3 = 1)
    (hmax : ∀ M : Subgroup ↥(adjointGroup Tag.D4 K), subfieldGroup Tag.D4 T ≤ M →
      M = subfieldGroup Tag.D4 T ∨ M = ⊤)
    {ι : MulAut ↥(adjointGroup Tag.D4 K)} (hι : ι ∈ inner (adjointGroup Tag.D4 K))
    (hfix : ∀ x ∈ subfieldGroup Tag.D4 T, ι x = x) : ι = 1 := by
  obtain ⟨h, rfl⟩ := hι
  have hcomm : ∀ x ∈ subfieldGroup Tag.D4 T, h * x = x * h := fun x hx => by
    have h1 := hfix x hx
    rw [MulAut.conj_apply] at h1
    calc h * x = (h * x * h⁻¹) * h := by group
      _ = x * h := by rw [h1]
  have hle : subfieldGroup Tag.D4 T ≤ Subgroup.centralizer {h} := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (hcomm x hx).symm
  have hh : h = 1 := by
    rcases hmax _ hle with hc | hc
    · have hmem : h ∈ subfieldGroup Tag.D4 T := by
        rw [← hc]
        exact Subgroup.mem_centralizer_iff.2 fun z hz => by rw [Set.mem_singleton_iff.1 hz]
      exact eq_one_of_central_fixed_D4 T hT3 hmem fun y hy => hcomm y hy
    · have hz : h ∈ Subgroup.center ↥(adjointGroup Tag.D4 K) := by
        rw [Subgroup.mem_center_iff]
        intro y
        have : y ∈ Subgroup.centralizer {h} := by rw [hc]; exact Subgroup.mem_top y
        exact Subgroup.mem_centralizer_singleton_iff.1 this
      rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hz
      exact hz
  rw [hh, map_one]

theorem d4_caseA_eight {ℓ f e : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K] [CharP K ℓ]
    (hK : Nat.card K = ℓ ^ f) (hK4 : 4 ≤ Nat.card K) (he : 1 ≤ e) (hef : e * 3 = f)
    (T σ : K ≃+* K) (hT : ∀ c, T c = c ^ (ℓ ^ e)) (hT3 : T ^ 3 = 1) (hT1 : T ≠ 1)
    (hσ : σ = T ∨ σ = T ^ 2)
    (hmax : ∀ M : Subgroup ↥(adjointGroup Tag.D4 K), subfieldGroup Tag.D4 T ≤ M →
      M = subfieldGroup Tag.D4 T ∨ M = ⊤)
    (hodd : ¬ 2 ∣ Nat.card K - 1)
    {E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K))} [hE : CFSG.IsElementaryAbelian 3 ↥E]
    {α ι : MulAut ↥(adjointGroup Tag.D4 K)} (hαE : α ∈ E) (hιE : ι ∈ E)
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ)
    (hα : α = MulAut.conj g * exactNormalAut Tag.D4 K a σ 0)
    (g' : adjointGroup Tag.D4 K) (b : Fin Tag.D4.rank → Kˣ)
    (hι : ι = MulAut.conj g' * rootDiagAut Tag.D4 K b) (hι1 : ι ≠ 1) :
    Subgroup.closure (fixUnion E) = ⊤ := by
  classical
  have : Finite (ModGL Tag.D4 K) := finite_modGL
  have : Finite (adjointGroup Tag.D4 K) := Subtype.finite
  haveI := inner_normal (adjointGroup Tag.D4 K)
  have hα3 : α ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian α hαE
  have hβ3 : (α * ι) ^ 3 = 1 :=
    CFSG.elemPow_eq_one_of_isElementaryAbelian (α * ι) (E.mul_mem hαE hιE)
  obtain ⟨g₃, a₃, hαι⟩ := normalForm_mul g g' a b σ 1 0
  simp only [d4Graph_zero, mul_one] at hαι
  rw [← rootDiagAut_eq_normalAut, ← hα, ← hι] at hαι
  set L := AlgebraicClosure K
  obtain ⟨ψa, -, hFa⟩ := exists_conj_fixedSubgroup_D4_field hK hK4 he hef T σ hT hT3 hσ L g a α
    hα hα3
  obtain ⟨ψb, -, hFb⟩ := exists_conj_fixedSubgroup_D4_field hK hK4 he hef T σ hT hT3 hσ L g₃ a₃
    (α * ι) hαι hβ3
  have hα1 : α ≠ 1 := by
    rintro rfl
    rw [fixedSubgroup_conj_one] at hFa
    exact subfieldGroup_ne_top_D4 hT1 hFa.symm
  have hβ1 : α * ι ≠ 1 := by
    intro h
    rw [h, fixedSubgroup_conj_one] at hFb
    exact subfieldGroup_ne_top_D4 hT1 hFb.symm
  have hιinner : ι ∈ inner (adjointGroup Tag.D4 K) := by
    rw [hι]
    exact mul_mem ⟨g', rfl⟩ (rootDiagAut_mem_inner_D4_of_odd K hodd b)
  exact closure_fixUnion_eq_top_of_kernel_escape (N := inner (adjointGroup Tag.D4 K)) hmax
    (fun ι' hι' hfix => eq_one_of_mem_inner_of_fix_D4 T hT3 hmax hι' hfix) hαE hιE hα1 hβ1 hι1
    hιinner hFa hFb

end Corner

end CFSG.LieType.SeitzGeneration.ExcWideThree
