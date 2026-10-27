module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EUAnti
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EUMat
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7U4Inner

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7L4EU

open CFSG Subgroup Module Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.CatalogueBUnitaryB CFSG.LinearGroups
open CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.CentralQuotientLift
open CFSG.ComponentClassification.CatFactsL4U4.UnitaryOut (uStar uStar_mul uStar_one)
open CFSG.ComponentClassification.CatFactsL4U4.UnitaryConj (stdG)
open CFSG.ComponentClassification.CatFactsL4U4.HBlocks (X1)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem inner_type (hp : p ≠ 2) {A : GL (Fin 4) K}
    (hAu : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1)
    (hT : orderOf (QuotientGroup.mk (Catalog7U4.toSesqU h A hAu) :
      sesqProjUnitary h (stdHermForm h 4)) = 2)
    {Y : Subgroup (sesqUnitaryGroup (stdHermForm h 4))}
    (hY : CFSG.Assembly.IsComponentOf Y
      (centralizer ({Catalog7U4.toSesqU h A hAu} : Set (sesqUnitaryGroup (stdHermForm h 4)))))
    {X' : Type} [Group X'] {X : Subgroup X'} (σ : Y →* X) (hσs : Function.Surjective σ)
    (hσk : σ.ker ≤ center Y)
    (hker : ∀ y : Y, σ y = 1 → (y : sesqUnitaryGroup (stdHermForm h 4)) ∈
      sesqNormOneScalars h (stdHermForm h 4))
    (hs : SmallSource X) :
    Nonempty (X ⧸ center X ≃* GorensteinWalter.PSL2 K) ∧
      ∃ (l : K) (Q : GL (Fin 4) K), l ≠ 0 ∧ h.norm l = -1 ∧
        uStar h (Q : Matrix (Fin 4) (Fin 4) K) * (Q : Matrix (Fin 4) (Fin 4) K) = stdG ∧
        (A : Matrix (Fin 4) (Fin 4) K) * Q = Q * X1 l := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.finite
  have hAv : ∀ v, unitaryOp (Catalog7U4.toSesqU h A hAu) v =
      (A : Matrix (Fin 4) (Fin 4) K) *ᵥ v := fun v => by
    rw [Catalog7U4.unitaryOp_toSesqU, Matrix.toLin'_apply]
  generalize Catalog7U4.toSesqU h A hAu = T at hT hY hAv
  have hB : (stdHermForm h 4).IsSymm := stdHermForm_isSymm h 4
  have hBl : (stdHermForm h 4).SeparatingLeft := stdHermForm_separatingLeft h 4
  have hn : finrank K (Fin 4 → K) = 4 := Module.finrank_fin_fun K
  obtain ⟨l, hl0, hAA, hN, hP, hM, hc, hsplit, hpaired, -⟩ :=
    projective_unitary_involution_centralizer_matrix_structure h hp (by omega) hB hBl hT
  have hY₁ := (isComponentOf_iff_isComponent_subgroupOf hY.1).mp hY
  let eY : Y.subgroupOf (centralizer ({T} : Set (sesqUnitaryGroup (stdHermForm h 4)))) ≃* Y :=
    Subgroup.subgroupOfEquivOfLe hY.1
  rcases hN with hN | hN
  ·
    exfalso
    obtain ⟨-, hsepP, hsepM, e, he⟩ := hsplit hN
    have hsymm : ∀ P : Submodule K (Fin 4 → K), ((stdHermForm h 4).domRestrict₁₂ P P).IsSymm :=
      fun P =>
      ⟨fun x y => hB.eq (x : Fin 4 → K) (y : Fin 4 → K)⟩
    rcases fst_eq_or_snd_eq_of_isComponent_prod (isComponent_map_of_isComponent e hY₁) with
      h2 | h1
    · have h2' : ∀ x ∈ Y.subgroupOf (centralizer ({T} : Set (sesqUnitaryGroup (stdHermForm h 4)))),
          (e x).2 = 1 := fun x hx => h2 _ (mem_map_of_mem _ hx)
      obtain ⟨ρ₁, hρ₁i, hρ₁c, -⟩ := OddClassSelector.restrict_component e hY₁ h2'
      have hYF : ∀ y ∈ Y, ∀ w ∈ eigenMinus l (unitaryOp T), unitaryOp y w = w := by
        intro y hy w hw
        have h4 := LinearMap.congr_fun (he (eY.symm ⟨y, hy⟩)).2 ⟨w, hw⟩
        rw [h2' _ (eY.symm ⟨y, hy⟩).2] at h4
        exact h4.symm
      refine OddClassSelector.su_half_false h hp (hsymm _) hsepP
        (Submodule.one_le_finrank_iff.mpr hP) hM hYF (ρ₁.comp eY.symm.toMonoidHom)
        (hρ₁i.comp eY.symm.injective) ?_ σ hσs hσk hker hs
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eY.symm.surjective,
        ← MonoidHom.range_eq_map]
      exact hρ₁c
    · have h1' : ∀ x ∈ Y.subgroupOf (centralizer ({T} : Set (sesqUnitaryGroup (stdHermForm h 4)))),
          ((e.trans MulEquiv.prodComm) x).2 = 1 := fun x hx => h1 _ (mem_map_of_mem _ hx)
      obtain ⟨ρ₁, hρ₁i, hρ₁c, -⟩ :=
        OddClassSelector.restrict_component (e.trans MulEquiv.prodComm) hY₁ h1'
      have hYF : ∀ y ∈ Y, ∀ w ∈ eigenPlus l (unitaryOp T), unitaryOp y w = w := by
        intro y hy w hw
        have h4 := LinearMap.congr_fun (he (eY.symm ⟨y, hy⟩)).1 ⟨w, hw⟩
        rw [show (e (eY.symm ⟨y, hy⟩)).1 = 1 from h1' _ (eY.symm ⟨y, hy⟩).2] at h4
        exact h4.symm
      refine OddClassSelector.su_half_false h hp (hsymm _) hsepM
        (Submodule.one_le_finrank_iff.mpr hM) hP hYF (ρ₁.comp eY.symm.toMonoidHom)
        (hρ₁i.comp eY.symm.injective) ?_ σ hσs hσk hker hs
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eY.symm.surjective,
        ← MonoidHom.range_eq_map]
      exact hρ₁c
  ·
    obtain ⟨hisoP, hisoM, -, hdim2, -, hpairM, e, -⟩ := hpaired hN
    have hm2 : finrank K (eigenPlus l (unitaryOp T)) = 2 := by omega
    have hm2' : finrank K (eigenMinus l (unitaryOp T)) = 2 := by
      have h1 := Submodule.finrank_add_eq_of_isCompl hc
      omega
    let bP : Module.Basis (Fin 2) K (eigenPlus l (unitaryOp T)) :=
      Module.finBasisOfFinrankEq K _ hm2
    let e' := e.trans (Units.mapEquiv (LinearMap.toMatrixAlgEquiv bP).toMulEquiv)
    have hL' := isComponent_map_of_isComponent e' hY₁
    have : Group.IsPerfect ((Y.subgroupOf
        (centralizer ({T} : Set (sesqUnitaryGroup (stdHermForm h 4))))).map e'.toMonoidHom) :=
      hL'.1.1
    have : Nontrivial ((Y.subgroupOf
        (centralizer ({T} : Set (sesqUnitaryGroup (stdHermForm h 4))))).map e'.toMonoidHom) :=
      CFSG.LocalCores.isQuasisimple_nontrivial hL'.1
    have hE9 : 9 ≤ Nat.card K := by
      rw [h.card, pow_mul]
      have hp3 : 3 ≤ p := by have := h.prime.two_le; omega
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
        _ ≤ (p ^ 2) ^ f := Nat.le_self_pow (by have := h.one_le; omega) _
    obtain ⟨hm2'', h22, h23⟩ := CatalogueBGeneralLinear.retained_parameters 2 K (by norm_num)
      (by omega)
    have hSL := CatalogueBGeneralLinear.perfect_subnormal_eq_specialLinearRange 2 K hm2'' h22 h23
      _ hL'.2
    let eY' : Y ≃* SpecialLinearGroup (Fin 2) K :=
      (eY.symm.trans (Subgroup.equivMapOfInjective _ e'.toMonoidHom e'.injective)).trans
        ((MulEquiv.subgroupCongr hSL).trans
          (MonoidHom.ofInjective SpecialLinearGroup.toGL_injective).symm)
    have : Group.IsPerfect Y := ⟨hY.2.2.1⟩
    refine ⟨center_quotient_equiv_of_sl σ hσs hσk eY', ?_⟩
    obtain ⟨Q, hQ, hAQ⟩ := exists_hyperbolic_basis_of_eigen h _ _ hm2 hm2' hisoP hisoM hpairM
      (M := (A : Matrix (Fin 4) (Fin 4) K)) (l := l)
      (fun v hv => by
        rw [← hAv]
        exact CatFactsL4U4.UnitaryConj.apply_eq_of_mem_eigenPlus hl0 hv)
      (fun w hw => by
        rw [← hAv]
        exact CatFactsL4U4.UnitaryConj.apply_eq_of_mem_eigenMinus hl0 hw)
    have hQ0 : Q.det ≠ 0 := by
      intro h0
      have h1 := congrArg Matrix.det hQ
      rw [det_mul, h0, mul_zero, show (stdG : Matrix (Fin 4) (Fin 4) K).det = 1 from
        CatFactsL4U4.UnitaryConj.det_stdG] at h1
      exact zero_ne_one h1
    exact ⟨l, GeneralLinearGroup.mkOfDetNeZero Q hQ0, hl0, hN, hQ, hAQ⟩

end Catalog7L4EU

end CFSG.ComponentClassification.GSThmB
