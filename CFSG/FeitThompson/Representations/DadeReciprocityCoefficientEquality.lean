module

public import CFSG.FeitThompson.Representations.DadeReciprocityAveraging
public import CFSG.FeitThompson.Definitions.CoherentExtensionOfACharacterFamilyMap
public import CFSG.FeitThompson.Representations.DadeAveragingClassFunction

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open ComplexConjugate

variable {G : Type*} [Group G] {L : Subgroup G} {A : Set G} {R : G → Subgroup G}
  {N : Subgroup ↥L}

section Domain

variable [Fintype ↥L] [N.Normal]

theorem indClassFun_sub_mem_dadeDomain
    (hNA : ∀ x : ↥L, x ∈ N → x ≠ 1 → (x : G) ∈ A) {θ θ' : ↥N → ℂ} (hdeg : θ 1 = θ' 1) :
    indClassFun N θ - indClassFun N θ' ∈ dadeDomain L A := by
  refine mem_dadeDomain.2 ⟨mem_classFun.2 fun x y hxy => ?_, fun x hx => ?_⟩
  · obtain ⟨c, rfl⟩ := isConj_iff.1 hxy
    simp only [Pi.sub_apply, indClassFun_conj]
  · by_cases hxN : x ∈ N
    · have hx1 : x = 1 := by
        by_contra h
        exact hx (hNA x hxN h)
      subst hx1
      simp only [Pi.sub_apply, indClassFun_one, hdeg, sub_self]
    · simp only [Pi.sub_apply, indClassFun_eq_zero_of_notMem N _ hxN, sub_self]

end Domain

section Bridge

variable [Finite G] [Fintype ↥L] [N.Normal]

theorem dadeMap_indClassFun_sub_coe (hD : IsDadeData L A R)
    (hNA : ∀ x : ↥L, x ∈ N → x ≠ 1 → (x : G) ∈ A) {θ θ' : ↥N → ℂ} (hdeg : θ 1 = θ' 1) :
    ((dadeMap hD ⟨indClassFun N θ - indClassFun N θ',
        indClassFun_sub_mem_dadeDomain hNA hdeg⟩ : classFun G) : G → ℂ)
      = dadeSupportExtension A R (extendByZero L (indClassFun N θ - indClassFun N θ')) :=
  dadeMap_apply_coe hD _

end Bridge

section Main

variable [Fintype G]

theorem dadeAverage_res_mem_classFun (hD : IsDadeData L A R) {Ψ : G → ℂ} (hΨ : Ψ ∈ classFun G) :
    resClassFun N (fun y : ↥L => dadeAverage A R Ψ (y : G)) ∈ classFun ↥N :=
  resClassFun_mem_classFun N (dadeAverage_restrict_mem_classFun hD hΨ)

variable [Fintype ↥L] [Fintype ↥N] [N.Normal]

theorem cfInner_dadeAverage_res_eq_of_cfInner_dadeMap_eq_zero
    (hD : IsDadeData L A R) (hNA : ∀ x : ↥L, x ∈ N → x ≠ 1 → (x : G) ∈ A)
    {Ψ : G → ℂ} (hΨ : Ψ ∈ classFun G)
    (hortho : ∀ θ ∈ Irr ↥N, ∀ θ' ∈ Irr ↥N, θ ≠ 1 → θ' ≠ 1 → ∀ hdeg : θ 1 = θ' 1,
      cfInner Ψ ((dadeMap hD ⟨indClassFun N θ - indClassFun N θ',
        indClassFun_sub_mem_dadeDomain hNA hdeg⟩ : classFun G) : G → ℂ) = 0)
    {lam mu : ↥N → ℂ} (hlam : lam ∈ Irr ↥N) (hmu : mu ∈ Irr ↥N)
    (hlam1 : lam ≠ 1) (hmu1 : mu ≠ 1) (hdeg : lam 1 = mu 1) :
    cfInner (resClassFun N (fun y : ↥L => dadeAverage A R Ψ (y : G))) lam
      = cfInner (resClassFun N (fun y : ↥L => dadeAverage A R Ψ (y : G))) mu := by
  have hρ : (fun y : ↥L => dadeAverage A R Ψ (y : G)) ∈ classFun ↥L :=
    dadeAverage_restrict_mem_classFun hD hΨ
  have hzero : cfInner (indClassFun N lam - indClassFun N mu)
      (fun y : ↥L => dadeAverage A R Ψ (y : G)) = 0 := by
    rw [← cfInner_dadeMap_eq_cfInner_dadeAverage hD
      ⟨indClassFun N lam - indClassFun N mu, indClassFun_sub_mem_dadeDomain hNA hdeg⟩ hΨ,
      ← conj_cfInner, hortho lam hlam mu hmu hlam1 hmu1 hdeg, map_zero]
  rw [cfInner_sub_left, cfInner_indClassFun N lam hρ, cfInner_indClassFun N mu hρ,
    sub_eq_zero] at hzero
  rw [← conj_cfInner lam _, ← conj_cfInner mu _, hzero]

end Main

end CFSG.FeitThompson
