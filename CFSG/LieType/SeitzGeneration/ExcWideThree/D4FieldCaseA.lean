module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4FieldConj
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Escape
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4FieldNF

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent
  CFSG.RankThree.PartOne.CTP
  CFSG.LieType.SeitzGeneration.ExcOuterLeOne
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

section Abstract

variable {P : Type*} [Group P]

theorem closure_fixUnion_eq_top_of_kernel_escape_of_mem [Finite P] {N : Subgroup (MulAut P)}
    {R : Subgroup P} (hmax : ∀ M : Subgroup P, R ≤ M → M = R ∨ M = ⊤)
    (hker : ∀ ι ∈ N, (∀ x ∈ R, ι x = x) → ι = 1) {E : Subgroup (MulAut P)}
    {α ι ψa ψb : MulAut P} (hαE : α ∈ E) (hιE : ι ∈ E) (hα1 : α ≠ 1) (hβ1 : α * ι ≠ 1)
    (hι1 : ι ≠ 1) (hιN : ι ∈ N) (hψa : ψa ∈ N) (hFa : fixedSubgroup (ψa * α * ψa⁻¹) = R)
    (hFb : fixedSubgroup (ψb * (α * ι) * ψb⁻¹) = R) :
    Subgroup.closure (fixUnion E) = ⊤ := by
  rw [fixedSubgroup_conj] at hFa hFb
  have hmaxα : ∀ M : Subgroup P, fixedSubgroup α ≤ M → M = fixedSubgroup α ∨ M = ⊤ := by
    intro M hM
    have hle : R ≤ M.map ψa.toMonoidHom := by
      rw [← hFa]
      exact Subgroup.map_mono hM
    have hMeq : M = (M.map ψa.toMonoidHom).comap ψa.toMonoidHom :=
      (Subgroup.comap_map_eq_self_of_injective ψa.injective M).symm
    rcases hmax _ hle with h | h
    · left
      rw [hMeq, h, ← hFa]
      exact Subgroup.comap_map_eq_self_of_injective ψa.injective _
    · right
      rw [hMeq, h]
      exact Subgroup.comap_top _
  refine closure_fixUnion_eq_top_of_maximal_escape hαE hα1 (E.mul_mem hαE hιE) hβ1 hmaxα ?_
  intro hle
  have hcard : Nat.card (fixedSubgroup (α * ι)) = Nat.card (fixedSubgroup α) := by
    have h1 := congrArg (fun H : Subgroup P => Nat.card H) hFb
    have h2 := congrArg (fun H : Subgroup P => Nat.card H) hFa
    rw [Subgroup.card_map_of_injective ψb.injective] at h1
    rw [Subgroup.card_map_of_injective ψa.injective] at h2
    rw [h1, h2]
  have heq : fixedSubgroup (α * ι) = fixedSubgroup α :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  have hιfix : ∀ x ∈ fixedSubgroup α, ι x = x := by
    intro x hx
    have hx' : x ∈ fixedSubgroup (α * ι) := heq ▸ hx
    have h1 : (α * ι) x = x := hx'
    have h2 : α x = x := hx
    simp only [MulAut.mul_apply] at h1
    exact α.injective (h1.trans h2.symm)
  have hι'fix : ∀ x ∈ R, (ψa * ι * ψa⁻¹) x = x := by
    intro x hx
    rw [← hFa] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    show (ψa * ι * ψa⁻¹) (ψa y) = ψa y
    simp [MulAut.mul_apply, hιfix y hy]
  have h1 := hker _ (N.mul_mem (N.mul_mem hψa hιN) (N.inv_mem hψa)) hι'fix
  apply hι1
  have h2 : ψa⁻¹ * (ψa * ι * ψa⁻¹) * ψa = ι := by group
  rw [← h2, h1]
  simp

theorem fixedSubgroup_conj_one (ψ : MulAut P) : fixedSubgroup (ψ * 1 * ψ⁻¹) = ⊤ := by
  rw [mul_one, mul_inv_cancel]
  exact (Subgroup.eq_top_iff' _).2 fun x => rfl

end Abstract

section CaseA


theorem coe_conj_mul_rootDiagAut_D4 {K : Type} [Field K] [Finite K] (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) (x : adjointGroup Tag.D4 K) :
    ((MulAut.conj g * rootDiagAut Tag.D4 K a) x : ModGL Tag.D4 K) =
      (g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * (x : ModGL Tag.D4 K) *
        (rootDiagUnit Tag.D4 a)⁻¹ * (g : ModGL Tag.D4 K)⁻¹ := by
  rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, coe_rootDiagAut,
    Subgroup.coe_inv]
  simp only [mul_assoc]

theorem conj_mul_rootDiagAut_mem_matrixInner {K : Type} [Field K] [Finite K] (L : Type) [Field L]
    [Algebra K L] (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) :
    MulAut.conj g * rootDiagAut Tag.D4 K a ∈ matrixInner Tag.D4 K L := by
  refine ⟨baseChangeGL (algebraMap K L) ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a),
    fun u => ?_⟩
  rw [coe_conj_mul_rootDiagAut_D4]
  simp only [map_mul, map_inv, mul_inv_rev]
  group

theorem subfieldGroup_ne_top_D4 {K : Type} [Field K] [Finite K] {T : K ≃+* K} (hT1 : T ≠ 1) :
    subfieldGroup Tag.D4 T ≠ ⊤ := by
  intro h
  apply hT1
  have h1 : entrywiseAdjointAut Tag.D4 T = 1 := by
    refine MulEquiv.ext fun x => ?_
    have : x ∈ subfieldGroup Tag.D4 T := h ▸ Subgroup.mem_top x
    exact this
  exact (injective_iff_map_eq_one _).1
    (CFSG.RankThree.Chevalley.SteinbergBT.entrywiseAdjointAutHom_injective (τ := Tag.D4) (K := K)
      Tag.D4.rank_pos) T h1

theorem d4_caseA_big {ℓ f e : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K] [CharP K ℓ]
    (hK : Nat.card K = ℓ ^ f) (hK4 : 4 ≤ Nat.card K) (he : 1 ≤ e) (hef : e * 3 = f)
    (T σ : K ≃+* K) (hT : ∀ c, T c = c ^ (ℓ ^ e)) (hT3 : T ^ 3 = 1) (hT1 : T ≠ 1)
    (hσ : σ = T ∨ σ = T ^ 2)
    (hmax : ∀ M : Subgroup ↥(adjointGroup Tag.D4 K), subfieldGroup Tag.D4 T ≤ M →
      M = subfieldGroup Tag.D4 T ∨ M = ⊤)
    (hbig : 2 < Nat.card (fixSubfield T))
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
  have hα3 : α ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian α hαE
  have hβ3 : (α * ι) ^ 3 = 1 :=
    CFSG.elemPow_eq_one_of_isElementaryAbelian (α * ι) (E.mul_mem hαE hιE)
  obtain ⟨g₃, a₃, hαι⟩ := normalForm_mul g g' a b σ 1 0
  simp only [d4Graph_zero, mul_one] at hαι
  rw [← rootDiagAut_eq_normalAut, ← hα, ← hι] at hαι
  set L := AlgebraicClosure K
  obtain ⟨ψa, hψa, hFa⟩ := exists_conj_fixedSubgroup_D4_field hK hK4 he hef T σ hT hT3 hσ L g a α
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
  have hdeg : entryDegreeBound Tag.D4 = 2 := by simp [entryDegreeBound]
  refine closure_fixUnion_eq_top_of_kernel_escape_of_mem (N := matrixInner Tag.D4 K L) hmax ?_
    hαE hιE hα1 hβ1 hι1 (hι ▸ conj_mul_rootDiagAut_mem_matrixInner L g' b) hψa hFa hFb
  intro ι' hι'N hι'fix
  refine eq_one_of_mem_matrixInner_of_fix_subfield (fixSubfield T) (by rw [hdeg]; exact hbig)
    hι'N ?_
  intro x hx
  apply hι'fix
  have h1 := fixedFieldImage_le (σ := T) hx
  rw [mem_fixedSubgroup]
  refine Subtype.ext ?_
  rw [coe_entrywiseAdjointAut]
  exact ((mem_entrywiseFixedGroup).1 h1).2

end CaseA

end CFSG.LieType.SeitzGeneration.ExcWideThree
