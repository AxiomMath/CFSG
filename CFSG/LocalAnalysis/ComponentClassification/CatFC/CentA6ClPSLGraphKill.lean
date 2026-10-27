module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLGraphBase
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinOrthLow
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearHigherBPureGraph

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Matrix
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.ComponentClassification.CatalogueBGraphForm (pureGraphAction)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem A6Hyp.false_of_commuting_components {n : ℕ} {K : Type} [Field K] [Finite K]
    (A : GL (Fin n) K) {D : Subgroup ↥(fixedSubgroup (pureGraphAction n K A))}
    (h : A6Hyp (pureGraphAction n K A) D) {G₀ : Type} [Group G₀]
    (e₁ : ↥(CatalogueBGraphForm.isometryGroup n K A⁻¹) ≃* G₀) {La Lb : Subgroup G₀}
    (hLa : IsQuasisimple La) (hLb : IsQuasisimple Lb)
    (hLaΩ : La ≤ commutator G₀) (hLbΩ : Lb ≤ commutator G₀)
    (hc : ∀ x ∈ La, ∀ y ∈ Lb, x * y = y * x)
    (hA : Nonempty (La ⧸ center La ≃* alternatingGroup (Fin 6))) : False := by
  obtain ⟨eA⟩ := hA
  set Ω := commutator G₀ with hΩ
  let j : ↥Ω →* ↥(CatalogueBGraphForm.isometryGroup n K A⁻¹) :=
    e₁.symm.toMonoidHom.comp Ω.subtype
  have hj : Function.Injective j := e₁.symm.injective.comp Ω.subtype_injective
  have hdet : ∀ x, Matrix.GeneralLinearGroup.det ((j x : GL (Fin n) K)) = 1 := by
    intro x
    let F : G₀ →* Kˣ := (Matrix.GeneralLinearGroup.det (n := Fin n) (R := K)).comp
      ((CatalogueBGraphForm.isometryGroup n K A⁻¹).subtype.comp e₁.symm.toMonoidHom)
    exact MonoidHom.mem_ker.1 (Abelianization.commutator_subset_ker F x.2)
  have hker := pgPhi_ker_le_center A j hdet hj
  have hperf : ∀ {L : Subgroup G₀}, IsQuasisimple L → L ≤ Ω → ⁅L.subgroupOf Ω, L.subgroupOf Ω⁆ =
      L.subgroupOf Ω := fun {L} hL hLΩ => by
    have hq : IsQuasisimple (L.subgroupOf Ω) :=
      LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLΩ).symm hL
    exact Subgroup.isPerfect_iff.mp hq.1
  refine h.false_of_commuting_pair (pgPhi A j hdet) hker (L₁ := La.subgroupOf Ω)
    (L₂ := Lb.subgroupOf Ω) (hperf hLa hLaΩ) (hperf hLb hLbΩ) ?_ ?_ ?_
  · intro x hx y hy
    exact Subtype.ext (hc x.1 hx y.1 hy)
  · have e1 : ↥(La.subgroupOf Ω) ⧸ center ↥(La.subgroupOf Ω) ≃* alternatingGroup (Fin 6) := by
      let eL := Subgroup.subgroupOfEquivOfLe hLaΩ
      exact (QuotientGroup.congr _ _ eL (Subgroup.map_center_eq eL)).trans eA
    rw [Nat.card_congr e1.toEquiv, a6sq_card]
  · intro hle
    obtain ⟨a, b, hab⟩ := CatLeafProof.exists_mul_ne_of_isQuasisimple hLb (MulEquiv.refl ↥Lb)
    have ha : (⟨a.1, hLbΩ a.2⟩ : ↥Ω) ∈ Lb.subgroupOf Ω := a.2
    have h1 := Subgroup.mem_center_iff.1 (hle ha) ⟨b.1, hLbΩ b.2⟩
    have h2 : a.1 * b.1 = b.1 * a.1 := congrArg (Subtype.val : ↥Ω → G₀) h1.symm
    exact hab (Subtype.ext h2)

theorem centerQuotient_map_equiv {G H : Type} [Group G] [Group H] (e : G ≃* H) (N : Subgroup G) :
    Nonempty (N ⧸ center N ≃* (N.map e.toMonoidHom) ⧸ center (N.map e.toMonoidHom)) :=
  ⟨QuotientGroup.congr _ _ (N.equivMapOfInjective e.toMonoidHom e.injective)
    (Subgroup.map_center_eq _)⟩

open CFSG.ComponentClassification.CatalogueBLinearHigherB in
theorem a6_pureGraph_not_four_two (hO : LieOrderFormulasInput) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3 ^ 2) (A : GL (Fin 4) K)
    (hord : orderOf (pureGraphAction 4 K A) = 2)
    (D : Subgroup ↥(fixedSubgroup (pureGraphAction 4 K A)))
    (hD : A6Hyp (pureGraphAction 4 K A) D) : False := by
  have hcharP : CharP K 3 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      (by norm_num) hK
  have hodd : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  have hsq2 : pureGraphAction 4 K A ^ 2 = 1 := by rw [← hord, pow_orderOf_eq_one]
  have hform := CatalogueBGraphForm.pureGraph_involution_form_data 4 K (by norm_num) hodd A hsq2
  obtain ⟨hDc, hDZ⟩ := hD.component
  obtain ⟨N, hN, ⟨eDN⟩⟩ := pureGraph_component_transfer A hDc
  have hNA : Nonempty (N ⧸ center N ≃* alternatingGroup (Fin 6)) := ⟨eDN.symm.trans hDZ.some⟩
  have hdim : Module.finrank K (Fin 4 → K) = 4 := by rw [Module.finrank_fin_fun]
  rcases hform with hsymm | ⟨halt, -⟩
  ·
    have hR := transpose_inv_of_transpose_eq A hsymm
    have hQ₀ : (matrixQuadraticForm A⁻¹).polarBilin.Nondegenerate :=
      polarBilin_matrixQuadraticForm_nondegenerate hodd A⁻¹ hR
    let e₁ : ↥(CatalogueBGraphForm.isometryGroup 4 K A⁻¹) ≃*
        ↥(TauCeti.QuadraticMap.orthogonalGroup (matrixQuadraticForm A⁻¹)) :=
      (isometryGroupEquiv A⁻¹).symm.trans
        (MulEquiv.subgroupCongr (orthogonalGroup_matrixQuadraticForm hodd A⁻¹ hR).symm)
    have hN₀ : IsComponent (N.map e₁.toMonoidHom) := LocalCores.isComponent_map_mulEquiv e₁ hN
    have hNA₀ : Nonempty (↥(N.map e₁.toMonoidHom) ⧸ center ↥(N.map e₁.toMonoidHom) ≃*
        alternatingGroup (Fin 6)) :=
      ⟨(centerQuotient_map_equiv e₁ N).some.symm.trans hNA.some⟩
    have hK2 : Nat.card K ≠ 2 := by rw [hK]; norm_num
    have hK3 : Nat.card K ≠ 3 := by rw [hK]; norm_num
    by_cases hS : ∃ S : Submodule K (Fin 4 → K), Module.finrank K S = 2 ∧
        ∀ x ∈ S, matrixQuadraticForm A⁻¹ x = 0
    · obtain ⟨ψ, e', -, -, hsup, hq₁, hq₂, hn₁, hn₂, hcomm, -, -⟩ :=
        LocalAnalysis.ComponentInitial.orthogonal_split_four_derived hK2 hK3
          (matrixQuadraticForm A⁻¹) hQ₀ hdim hS
      have hN₀Ω : N.map e₁.toMonoidHom ≤
          commutator ↥(TauCeti.QuadraticMap.orthogonalGroup (matrixQuadraticForm A⁻¹)) := by
        calc N.map e₁.toMonoidHom = ⁅N.map e₁.toMonoidHom, N.map e₁.toMonoidHom⁆ :=
              (Subgroup.isPerfect_iff.mp hN₀.1.1).symm
          _ ≤ commutator _ := Subgroup.commutator_mono le_top le_top
      have key : ∀ La Lb : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup
          (matrixQuadraticForm A⁻¹)), IsQuasisimple La → IsQuasisimple Lb →
          La ≤ commutator _ → Lb ≤ commutator _ → (∀ x ∈ La, ∀ y ∈ Lb, x * y = y * x) →
          Nonempty (La ⧸ center La ≃* alternatingGroup (Fin 6)) → False :=
        fun La Lb hLa hLb hLaΩ hLbΩ hc hA =>
          hD.false_of_commuting_components A e₁ hLa hLb hLaΩ hLbΩ hc hA
      rcases CatLeafProof.eq_or_eq_of_isComponent_le_sup hsup hq₁ hq₂ hn₁ hn₂ hN₀ hN₀Ω with
        h | h
      · refine key _ _ hN₀.1 hq₂ hN₀Ω (by rw [hsup]; exact le_sup_right) ?_ hNA₀
        intro x hx y hy
        rw [h] at hx
        exact hcomm x hx y hy
      · refine key _ _ hN₀.1 hq₁ hN₀Ω (by rw [hsup]; exact le_sup_left) ?_ hNA₀
        intro x hx y hy
        rw [h] at hx
        exact (hcomm y hy x hx).symm
    · have hmodel := CatLeafProof.X10Lin.centralModel_orthogonal_nonsplit_four Nat.prime_three
        (by norm_num) (by norm_num : 1 ≤ 2) hK (matrixQuadraticForm A⁻¹) hQ₀ hdim hS hN₀
      have h := a6sq_lieModel_a6 hO hNA₀ hmodel.1 (by norm_num) hmodel.2
      exact absurd h.2.2.2 (by norm_num)
  ·
    have hR := transpose_inv_of_transpose_eq_neg A halt
    let eI := isometryGroupEquiv A⁻¹
    have hN' : IsComponent (N.map eI.symm.toMonoidHom) :=
      LocalCores.isComponent_map_mulEquiv eI.symm hN
    have hNA' : Nonempty (↥(N.map eI.symm.toMonoidHom) ⧸ center ↥(N.map eI.symm.toMonoidHom) ≃*
        alternatingGroup (Fin 6)) :=
      ⟨(centerQuotient_map_equiv eI.symm N).some.symm.trans hNA.some⟩
    have hmodel := CatLeafProof.X10Sp.centralModel_isometryGroup_component (ℓ := 3) (j := 2)
      (m := 2) Nat.prime_three (by norm_num) (by norm_num) hK (matrixForm A⁻¹)
      (matrixForm_isAlt hodd A⁻¹ hR) (matrixForm_nondegenerate A⁻¹)
      (by rw [Module.finrank_fin_fun]) le_rfl hN'
    have h := a6sq_lieModel_a6 hO hNA' hmodel.1 (by norm_num) hmodel.2
    exact absurd h.1 (by decide)

end CFSG.ComponentClassification.CatFC
