module

public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour
import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4L34
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516Tools
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransfer
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.ComponentClassification.GrSLit.KSw

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def autConjHom {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    MulAut X →* MulAut Y where
  toFun α := (e.symm.trans α).trans e
  map_one' := by
    ext y
    simp
  map_mul' α β := by
    ext y
    simp [MulAut.mul_apply]

theorem autConjHom_conj {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (x : X) :
    autConjHom e (MulAut.conj x) = MulAut.conj (e x) := by
  ext y
  simp [autConjHom, MulAut.conj_apply, map_mul, map_inv]

theorem autConjHom_symm_autConjHom {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (α : MulAut X) : autConjHom e.symm (autConjHom e α) = α := by
  ext y
  simp [autConjHom]

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_outerAct {K : Subgroup G} (hKL : IsL34Type (K ⧸ Open.fusionZStar K))
    (hKZ : zStarIn K = oddIn K) :
    ∃ θ : ↥(normalizer (K : Set G)) →* Multiplicative (ZMod 2) × Multiplicative (ZMod 2),
      (∀ (y : G) (hy : y ∈ normalizer (K : Set G)), y ∈ coreActionKernel K → θ ⟨y, hy⟩ = 1) ∧
      ∀ (y : G) (hy : y ∈ normalizer (K : Set G)), y * y = 1 → θ ⟨y, hy⟩ = 1 →
        y ∈ withKernel K := by
  obtain ⟨k, _, _, hk4, ⟨e₀⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hKL
  have hk : Nat.card k = 4 := by rw [hk4]; norm_num
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  set σ := frobeniusEquiv k 2 with hσdef
  have hσ : ∀ x, σ x = x ^ 2 := fun x => frobeniusEquiv_apply k 2 x
  obtain ⟨Ψ, hΨ⟩ := LinearThreeFourOuter.exists_outerHom hσ hk
  have hq : pPrimeCore 2 ↥K = Open.fusionZStar ↥K :=
    (Subgroup.map_injective K.subtype_injective hKZ).symm
  set e₁ : (↥K ⧸ pPrimeCore 2 ↥K) ≃* projectiveSL 3 k :=
    (QuotientGroup.quotientMulEquivOfEq hq).trans e₀ with he₁
  set θ := (SemidirectProduct.rightHom).comp (Ψ.comp ((autConjHom e₁).comp (GSThmB.oddBarConj K)))
    with hθ
  refine ⟨θ, fun y hy hyC => ?_, fun y hy hyy hθy => ?_⟩
  · have h1 : GSThmB.oddBarConj K ⟨y, hy⟩ = 1 :=
      GSThmB.oddBarConj_eq_one_of_mem_coreActionKernel hyC
    simp only [hθ, MonoidHom.comp_apply, h1, map_one]
  ·
    set α := autConjHom e₁ (GSThmB.oddBarConj K ⟨y, hy⟩) with hαdef
    obtain ⟨⟨A, a₁, b₁⟩, hα⟩ := LinearThreeFourOuter.exists_nf hσ hk α
    have hΨα := hΨ A a₁ b₁
    have hr : (Multiplicative.ofAdd a₁, Multiplicative.ofAdd b₁) = 1 := by
      have h1 : θ ⟨y, hy⟩ = SemidirectProduct.rightHom (Ψ α) := rfl
      rw [hθy, hα, hΨα] at h1
      exact h1.symm
    obtain ⟨ha₁, hb₁⟩ : a₁ = 0 ∧ b₁ = 0 := by
      simpa [Prod.ext_iff] using hr
    subst ha₁ hb₁
    have hΨα' : Ψ α = SemidirectProduct.inl (Matrix.GeneralLinearGroup.det A) := by
      rw [hα, hΨα]
      refine SemidirectProduct.ext rfl ?_
      simp
    have hαα : α * α = 1 := by
      rw [hαdef, ← map_mul, ← map_mul]
      have : (⟨y, hy⟩ : ↥(normalizer (K : Set G))) * ⟨y, hy⟩ = 1 := Subtype.ext hyy
      rw [this, map_one, map_one]
    have h2 : Matrix.GeneralLinearGroup.det A * Matrix.GeneralLinearGroup.det A = 1 := by
      apply SemidirectProduct.inl_injective (φ := LinearThreeFourOuter.inversionAction kˣ)
      rw [map_mul, ← hΨα', ← map_mul, hαα, map_one, map_one]
    have h3 := LinearThreeFourOuter.units_pow_three hk (Matrix.GeneralLinearGroup.det A)
    have hdet : Matrix.GeneralLinearGroup.det A = 1 := by
      calc Matrix.GeneralLinearGroup.det A
          = Matrix.GeneralLinearGroup.det A ^ 3 *
            (Matrix.GeneralLinearGroup.det A * Matrix.GeneralLinearGroup.det A)⁻¹ := by group
        _ = 1 := by rw [h3, h2]; group
    obtain ⟨p, hp⟩ : α ∈ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range := by
      rw [hα, LinearThreeFourOuter.nf_zero_zero]
      exact (LinearThreeFourOuter.conjAut_mem_range_conj_iff hk A).2 hdet
    obtain ⟨k₀, hk₀⟩ := QuotientGroup.mk_surjective (e₁.symm p)
    have h4 : GSThmB.oddBarConj K ⟨y, hy⟩ =
        MulAut.conj (QuotientGroup.mk k₀ : ↥K ⧸ pPrimeCore 2 ↥K) := by
      have h5 := autConjHom_symm_autConjHom e₁ (GSThmB.oddBarConj K ⟨y, hy⟩)
      rw [← hαdef, ← hp, autConjHom_conj] at h5
      rw [← h5, ← hk₀]
    have h6 : GSThmB.oddBarConj K (⟨y, hy⟩ * ⟨(k₀ : G), le_normalizer k₀.2⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, h4, CatFactsL4U4.oddBarConj_mk_eq_conj K k₀.2 (le_normalizer k₀.2)]
      exact mul_inv_cancel _
    have h7 := GSThmB.mem_coreActionKernel_of_oddBarConj_eq_one h6
    have h8 : y = y * (k₀ : G)⁻¹ * k₀ := by group
    rw [h8]
    exact mul_mem (mem_sup_right h7) (mem_sup_left k₀.2)

end CFSG.ComponentClassification.GrSLit.KSw
