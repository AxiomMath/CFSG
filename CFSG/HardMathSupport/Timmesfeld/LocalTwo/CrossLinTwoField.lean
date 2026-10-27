module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinTwoBase
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAction
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossBase
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearOuter
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OuterPlane
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.Dihedral.GorensteinWalter.GLSemilinearDescent
public import CFSG.GH74.GLS.IVK.L2.FixedSL
public import CFSG.GH74.GLS.IVK.L2.Hilbert90
public import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG CFSG.GorensteinWalter CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.GH74.GLS.IVK

section Basic

variable {F : Type} [Field F] [Finite F]

theorem not_comm_of_commutator_eq_top {P : Type*} [Group P] [Nontrivial P]
    (h : commutator P = ⊤) : ¬ ∀ a b : P, a * b = b * a := by
  intro hc
  obtain ⟨x, hx⟩ := exists_ne (1 : P)
  have hxm : x ∈ commutator P := h ▸ Subgroup.mem_top x
  have hle : commutator P ≤ ⊥ := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hc g₁ g₂
  exact hx (Subgroup.mem_bot.1 (hle hxm))

theorem mem_innerAut_of_right_eq_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {d : MulAut (PSL2 F)} (hd : d ^ p = 1)
    (h1 : ((semilinearEquivAut F).symm d).right = 1) : d ∈ innerAut (PSL2 F) := by
  let Ψ : PGammaL2 F ≃* MulAut (PSL2 F) := semilinearEquivAut F
  have hmem : Ψ.symm d ∈ (SemidirectProduct.inl : PGL2 F →* PGammaL2 F).range := by
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    exact h1
  obtain ⟨g, hg⟩ := hmem
  have hdg : d = pglAction F g := by
    have : d = Ψ (SemidirectProduct.inl g) := by rw [hg]; simp
    rw [this]
    exact semilinearAction_inl F g
  have hgp : g ^ p = 1 := by
    have h1 : Ψ.symm (d ^ p) = 1 := by rw [hd, map_one]
    rw [map_pow, ← hg, ← map_pow] at h1
    exact SemidirectProduct.inl_injective (by rw [map_one]; exact h1)
  obtain ⟨y, hy⟩ := mem_range_toPGL_of_pow_eq_one' hp hp2 g hgp
  exact ⟨y, by rw [hdg, ← hy, pglAction_toPGL]⟩

theorem exists_outer_data {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : MulAut (PSL2 F)}
    (hx : x ^ p = 1) (hxo : x ∉ innerAut (PSL2 F)) :
    ∃ (σ : F ≃+* F) (h : MulAut (PSL2 F)), orderOf σ = p ∧
      x = h * psl2FieldAut F σ * h⁻¹ := by
  have : Fact p.Prime := ⟨hp⟩
  let Ψ : PGammaL2 F ≃* MulAut (PSL2 F) := semilinearEquivAut F
  set z := Ψ.symm x with hz
  have hzp : z ^ p = 1 := by rw [hz, ← map_pow, hx, map_one]
  have hσp : z.right ^ p = 1 := by
    have := congrArg (SemidirectProduct.rightHom : PGammaL2 F →* (F ≃+* F)) hzp
    rwa [map_pow, map_one] at this
  have hσ1 : z.right ≠ 1 := fun h =>
    hxo (mem_innerAut_of_right_eq_one hp hp2 hx (by rw [← hz]; exact h))
  have hord : orderOf z.right = p := orderOf_eq_prime hσp hσ1
  have hzo : z ^ orderOf z.right = 1 := by rw [hord]; exact hzp
  obtain ⟨C, hC⟩ := CFSG.GH74.GLS.IVK.H90.pgammaL2_conj_inr_of_pow_eq_one z hzo
  refine ⟨z.right, Ψ (SemidirectProduct.inl C), hord, ?_⟩
  have hzC : z = SemidirectProduct.inl C * SemidirectProduct.inr z.right *
      (SemidirectProduct.inl C)⁻¹ := by
    rw [← hC]; group
  have hxz : x = Ψ z := by rw [hz]; simp
  have hinr : Ψ (SemidirectProduct.inr z.right) = psl2FieldAut F z.right :=
    semilinearAction_inr F _
  calc x = Ψ z := hxz
    _ = Ψ (SemidirectProduct.inl C * SemidirectProduct.inr z.right *
        (SemidirectProduct.inl C)⁻¹) := congrArg Ψ hzC
    _ = _ := by rw [map_mul, map_mul, map_inv, hinr]

omit [Finite F] in
theorem orderOf_psl2FieldAut (σ : F ≃+* F) : orderOf (psl2FieldAut F σ) = orderOf σ :=
  orderOf_injective _ (psl2FieldAut_injective F) σ

theorem four_le_card_fixedField {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) {σ : F ≃+* F}
    (hσ : orderOf σ = p) (hpF : ¬ p ∣ Nat.card (fixedField σ)) (k : PSL2 F)
    (hk : psl2FieldAut F σ k = k) (hko : orderOf k = p) : 4 ≤ Nat.card (fixedField σ) := by
  have hodd : Odd (orderOf σ) := by rw [hσ]; exact hp.odd_of_ne_two (by omega)
  have hkJ : k ∈ (pslIncl σ).range := (mem_range_pslIncl_iff σ hodd k).2 hk
  have hdvdJ : p ∣ Nat.card (pslIncl σ).range := by
    have : orderOf (⟨k, hkJ⟩ : (pslIncl σ).range) = p := by
      rw [Subgroup.orderOf_mk]; exact hko
    rw [← this]; exact orderOf_dvd_natCard _
  have hcardJ : Nat.card (pslIncl σ).range = Nat.card (PSL2 (fixedField σ)) :=
    (Nat.card_congr (MonoidHom.ofInjective (pslIncl_injective σ)).toEquiv).symm
  have hdvdSL : Nat.card (PSL2 (fixedField σ)) ∣
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (fixedField σ)) := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (fixedField σ)))
    exact Dvd.intro _ this.symm
  have hdiv : p ∣ Nat.card (fixedField σ) * (Nat.card (fixedField σ) ^ 2 - 1) := by
    rw [← sl2_card_formula (fixedField σ)]
    rw [hcardJ] at hdvdJ
    exact hdvdJ.trans hdvdSL
  by_contra hlt
  push Not at hlt
  have h2 : 2 ≤ Nat.card (fixedField σ) := Finite.one_lt_card
  generalize Nat.card (fixedField σ) = q₀ at hdiv hlt h2
  interval_cases q₀
  · have h6 : p ≤ 6 := Nat.le_of_dvd (by norm_num) hdiv
    have : p = 6 := by omega
    subst this
    exact absurd hp (by norm_num)
  · have h24 : p ≤ 24 := Nat.le_of_dvd (by norm_num) hdiv
    interval_cases p <;> first | omega | exact absurd hp (by norm_num)

end Basic

section Stabilizer

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem commute_of_pglAction_apply_eq (g : PGL2 F) (u : PSL2 F) (h : pglAction F g u = u) :
    Commute g (Matrix.ProjectiveSpecialLinearGroup.toPGL u) := by
  have h1 := congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL h
  rw [toPGL_pglAction] at h1
  exact (mul_inv_eq_iff_eq_mul.1 h1)

theorem mem_zpowers_of_fixes_range (σ : F ≃+* F) (hodd : Odd (orderOf σ))
    (β : MulAut (PSL2 F)) (hβ : ∀ u ∈ (pslIncl σ).range, β u = u) :
    β ∈ Subgroup.zpowers (psl2FieldAut F σ) := by
  obtain ⟨z, hz⟩ := semilinearAction_surjective F β
  have hβz : β = pglAction F z.left * psl2FieldAut F z.right := by
    rw [← hz]
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right z]
    rw [map_mul, semilinearAction_inl, semilinearAction_inr]
  have hmem : ∀ (i j : Fin 2) (hij : i ≠ j) (a : F), σ a = a → tvPSL i j hij a ∈ (pslIncl σ).range :=
    fun i j hij a ha => (mem_range_pslIncl_iff σ hodd _).2 (by
      rw [psl2FieldAut_tvPSL, ha])
  have hU : pglAction F z.left (tvPSL 0 1 (by decide) (1 : F)) =
      tvPSL 0 1 (by decide) (1 : F) := by
    have := hβ _ (hmem 0 1 (by decide) 1 (map_one σ))
    rwa [hβz, MulAut.mul_apply, psl2FieldAut_tvPSL, map_one] at this
  have hL : pglAction F z.left (tvPSL 1 0 (by decide) (1 : F)) =
      tvPSL 1 0 (by decide) (1 : F) := by
    have := hβ _ (hmem 1 0 (by decide) 1 (map_one σ))
    rwa [hβz, MulAut.mul_apply, psl2FieldAut_tvPSL, map_one] at this
  have hg1 : z.left = 1 :=
    pgl2_eq_one_of_commute_unit_tv _ (commute_of_pglAction_apply_eq _ _ hU)
      (commute_of_pglAction_apply_eq _ _ hL)
  have hβτ : β = psl2FieldAut F z.right := by rw [hβz, hg1, map_one, one_mul]
  have hfixτ : ∀ a : F, σ a = a → z.right a = a := by
    intro a ha
    have := hβ _ (hmem 0 1 (by decide) a ha)
    rw [hβτ, psl2FieldAut_tvPSL] at this
    exact tvPSL_injective 0 1 (by decide) this
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (ringEquiv_mem_zpowers_of_fixes σ z.right hfixτ)
  exact Subgroup.mem_zpowers_iff.2 ⟨n, by rw [hβτ, ← hn, map_zpow]⟩

end Stabilizer

section Outer

variable {F : Type} [Field F] [Finite F]

theorem fieldCoreAt_of_outer {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (hpF : ¬ p ∣ Nat.card F)
    (hinj : Function.Injective (MulAut.conj : PSL2 F →* MulAut (PSL2 F)))
    {D : Subgroup (MulAut (PSL2 F))} (hD : IsElemAbelian p D) (hcard : Nat.card D = p ^ 2)
    (hDin : ¬ D ≤ innerAut (PSL2 F)) :
    ∃ x ∈ D, x ∉ innerAut (PSL2 F) ∧ FieldCoreAt p x := by
  classical
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hDfin : Finite D :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hp.ne_zero)
  let Ψ : PGammaL2 F ≃* MulAut (PSL2 F) := semilinearEquivAut F
  have : IsCyclic (F ≃+* F) := fieldAut_isCyclic F
  let α : D →* (F ≃+* F) :=
    ((SemidirectProduct.rightHom : PGammaL2 F →* (F ≃+* F)).comp Ψ.symm.toMonoidHom).comp
      D.subtype
  have hle := card_le_mul_card_ker' hp (fun h : D => Subtype.ext (hD.2 h h.2)) α
  obtain ⟨y, hyker, hy1⟩ : ∃ y ∈ α.ker, y ≠ 1 := by
    by_contra hno
    push Not at hno
    have hbot : α.ker = ⊥ := eq_bot_iff.2 fun z hz => (Subgroup.mem_bot).2 (hno z hz)
    rw [hbot, Subgroup.card_bot, hcard] at hle
    have : p ^ 2 = p * p := by ring
    have := hp.two_le
    nlinarith
  have hyp : (y : MulAut (PSL2 F)) ^ p = 1 := hD.2 y y.2
  have hy1' : (y : MulAut (PSL2 F)) ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hyin : (y : MulAut (PSL2 F)) ∈ innerAut (PSL2 F) :=
    mem_innerAut_of_right_eq_one hp hp2 hyp (MonoidHom.mem_ker.1 hyker)
  obtain ⟨x, hxD, hxin⟩ := IsConcreteLE.not_le_iff_exists.1 hDin
  obtain ⟨σ, h, hσ, hxh⟩ := exists_outer_data hp hp2 (hD.2 x hxD) hxin
  have hcomm : (y : MulAut (PSL2 F)) * x = x * y :=
    congrArg Subtype.val (hD.1.is_comm.comm y ⟨x, hxD⟩)
  have hodd : Odd (orderOf σ) := by rw [hσ]; exact hp.odd_of_ne_two hp2
  have hδp : orderOf (psl2FieldAut F σ) = p := by rw [orderOf_psl2FieldAut, hσ]
  have hpF0 : ¬ p ∣ Nat.card (fixedField σ) := fun hd =>
    hpF (by
      rw [← fixedField_card_pow σ, hσ]
      exact dvd_pow hd hp.ne_zero)
  obtain ⟨k, hkδ, hkord⟩ := exists_fixed_orderOf_of_canonical_conj hp hinj hxh hyin hy1' hyp hcomm
  have h4 := four_le_card_fixedField hp hp5 hσ hpF0 k hkδ hkord
  have : Fintype (fixedField σ) := Fintype.ofFinite _
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (fixedField σ))) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
  have hsimple := CFSG.LinearGroups.linear_projective_simple (n := 2) (K := fixedField σ)
    (by norm_num) (Or.inr ⟨s, hs⟩)
  have hperf := (CFSG.LinearGroups.linear_projective_perfect (n := 2) (K := fixedField σ)
    (by norm_num) (Or.inr ⟨s, hs⟩)).commutator_eq_top
  have := hsimple.1
  have := hsimple.2.1
  let eJ : PSL2 (fixedField σ) ≃* (pslIncl σ).range :=
    MonoidHom.ofInjective (pslIncl_injective σ)
  have : IsSimpleGroup ((pslIncl σ).range) := eJ.symm.isSimpleGroup
  have hJq : CFSG.IsQuasisimple ((pslIncl σ).range) := by
    refine isQuasisimple_of_simple_nonabelian ?_
    intro hc
    refine not_comm_of_commutator_eq_top hperf fun a b => ?_
    apply eJ.injective
    have := hc (eJ a) (eJ b)
    simpa [map_mul] using this
  refine ⟨x, hxD, hxin, ?_⟩
  exact fieldCoreAt_of_canonical_conj hp hinj hδp hJq
    (fun g => mem_range_pslIncl_iff σ hodd g)
    (fun β hβ => mem_zpowers_of_fixes_range σ hodd β hβ) hxh hyin hy1' hyp hcomm

end Outer

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
