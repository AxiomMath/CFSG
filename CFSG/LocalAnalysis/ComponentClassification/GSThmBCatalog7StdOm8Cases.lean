module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Two
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Tools
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Corr
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8One

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8

open CFSG Subgroup Module
open CFSG.GroupTheory.WeirSylow (IsPlusType)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareForms
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure

attribute [local instance] finite_linearEquiv

variable {H : Type} [Group H] [Finite H] {G : Subgroup H} [G.Normal] {K : Type} [Field K]
  [Finite K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {Θ : G ≃* projectiveDerived Q} {t : H}

omit [Finite H] in
theorem caseA_data {r e : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = r ^ e) (hQ : Q.polarBilin.Nondegenerate) (hdim : finrank K V = 8)
    (D : InvData G Q Θ t) (β : Kˣ) (hβ : (D.c : K) = (β : K) ^ 2) :
    ∃ (W W' : Submodule K V) (ι : orthogonalOperatorCentralizer Q D.A.toLinearMap ≃*
        TauCeti.QuadraticMap.orthogonalGroup (Q.comp W.subtype) ×
          TauCeti.QuadraticMap.orthogonalGroup (Q.comp W'.subtype)),
      IsCompl W W' ∧ (Q.comp W.subtype).polarBilin.Nondegenerate ∧
        (Q.comp W'.subtype).polarBilin.Nondegenerate ∧
        ∀ h (x : W) (y : W'), (ι.symm h).val.val (x.val + y.val) =
          (h.1.val x).val + (h.2.val y).val := by
  obtain ⟨-, -, hA, -⟩ := scalar_square_centralizer_structure r e hr hr2 he hK (by omega) Q hQ
    D.A D.c D.μ D.hsq (polar_similarity Q D.A D.μ D.hsim) D.hns
  have hμd : (D.μ : K) / (D.c : K) = 1 := by rw [D.hμc]; exact div_self (Units.ne_zero _)
  obtain ⟨hcompl, -, -, hpos, -⟩ := hA β hβ
  obtain ⟨-, hnd₁, hnd₂, ι, -, -, hι⟩ := hpos hμd
  exact ⟨_, _, ι, hcompl, hnd₁, hnd₂, hι⟩

omit [Finite H] in
theorem caseB_data {r e : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = r ^ e) (hQ : Q.polarBilin.Nondegenerate) (hdim : finrank K V = 8)
    (hnp : ¬ IsPlusType Q) (D : InvData G Q Θ t) (hns : ¬ IsSquare (D.c : K)) :
    ∃ (T : Type) (_ : Group T) (_ : Finite T)
      (_ : orthogonalOperatorCentralizer Q D.A.toLinearMap ≃* T),
      ∀ M' : Subgroup T, IsPComponent 2 M' → IsQuasisimple M' ∧
        Blueprint.LieModel (M' ⧸ center M') .PSL 2 r (2 * (2 * e)) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by rw [hdim]; norm_num)
  obtain ⟨-, -, -, hB⟩ := scalar_square_centralizer_structure r e hr hr2 he hK (by omega) Q hQ
    D.A D.c D.μ D.hsq (polar_similarity Q D.A D.μ D.hsim) D.hns
  have hμd : (D.μ : K) / (D.c : K) = 1 := by rw [D.hμc]; exact div_self (Units.ne_zero _)
  obtain ⟨-, hpos, -⟩ := hB hns
  obtain ⟨-, -, -, -, -, -, ι, -⟩ := hpos hμd
  let := scalarField D.A.toLinearMap (D.c : K) hns (original_endomorphism_square D.A D.c D.hsq)
  let := evaluationModule D.A.toLinearMap
  have hfin : Finite V := Module.finite_of_finite K
  refine ⟨_, inferInstance, ?_, ι, ?_⟩
  · exact Finite.of_injective (fun g => ((g.val : V ≃ₗ[scalarAlgebra D.A.toLinearMap] V) : V → V))
      (fun g h hgh => Subtype.ext (LinearEquiv.ext (congrFun hgh)))
  · exact actualPositive_pComponent hr hr2 he hK Q hQ hdim hnp D.A.toLinearMap D.c
      (Units.ne_zero _) hns _ _

variable {U U' : Submodule K V}

omit [Finite H] [Finite K] [FiniteDimensional K V] in
theorem swap_compat (D : InvData G Q Θ t)
    (ι : orthogonalOperatorCentralizer Q D.A.toLinearMap ≃*
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype) ×
        TauCeti.QuadraticMap.orthogonalGroup (Q.comp U'.subtype))
    (hι : ∀ h (x : U) (y : U'), (ι.symm h).val.val (x.val + y.val) =
      (h.1.val x).val + (h.2.val y).val) :
    ∀ h (x : U') (y : U), ((ι.trans (MulEquiv.prodComm)).symm h).val.val (x.val + y.val) =
      (h.1.val x).val + (h.2.val y).val := by
  intro h x y
  rw [add_comm x.val y.val, add_comm (h.1.val x).val]
  exact hι (h.2, h.1) y x

omit [Finite H] [Finite K] [FiniteDimensional K V] in
theorem map_prodComm_bot_prod {X Y : Type*} [Group X] [Group Y] (L : Subgroup Y) :
    ((⊥ : Subgroup X).prod L).map (MulEquiv.prodComm : X × Y ≃* Y × X).toMonoidHom =
      L.prod (⊥ : Subgroup X) := by
  ext ⟨y, x⟩
  constructor
  · rintro ⟨⟨x', y'⟩, ⟨hx', hy'⟩, h⟩
    have h' : (y', x') = (y, x) := h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h'
    exact ⟨hy', hx'⟩
  · rintro ⟨hy, hx⟩
    exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩

omit [Finite H] in
theorem left_normal_form (D : InvData G Q Θ t) {W W' : Submodule K V}
    (ι : orthogonalOperatorCentralizer Q D.A.toLinearMap ≃*
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp W.subtype) ×
        TauCeti.QuadraticMap.orthogonalGroup (Q.comp W'.subtype))
    (hcompl : IsCompl W W') (hnd : (Q.comp W.subtype).polarBilin.Nondegenerate)
    (hnd' : (Q.comp W'.subtype).polarBilin.Nondegenerate)
    (hι : ∀ h (x : W) (y : W'), (ι.symm h).val.val (x.val + y.val) =
      (h.1.val x).val + (h.2.val y).val)
    (M : Subgroup (FN D)) (hM : IsPComponent 2 (M.map (epsT D ι))) :
    ∃ (U U' : Submodule K V) (ψ : orthogonalOperatorCentralizer Q D.A.toLinearMap ≃*
        TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype) ×
          TauCeti.QuadraticMap.orthogonalGroup (Q.comp U'.subtype)),
      IsCompl U U' ∧ (Q.comp U.subtype).polarBilin.Nondegenerate ∧
        (Q.comp U'.subtype).polarBilin.Nondegenerate ∧
        (∀ h (x : U) (y : U'), (ψ.symm h).val.val (x.val + y.val) =
          (h.1.val x).val + (h.2.val y).val) ∧
        ∃ L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype)),
          IsPComponent 2 L ∧ M.map (epsT D ψ) = L.prod ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases CatalogueBProjectiveInvolutionProduct.pComponent_eq_left_or_right_factor 2 _ hM with
    h | h
  · refine ⟨W, W', ι, hcompl, hnd, hnd', hι, _, ?_, h⟩
    exact isPComponent_of_prod_bot (h ▸ hM)
  · set L := (M.map (epsT D ι)).map (MonoidHom.snd _ _)
    have hmap : M.map (epsT D (ι.trans MulEquiv.prodComm)) = L.prod ⊥ := by
      have h1 : epsT D (ι.trans MulEquiv.prodComm) =
          (MulEquiv.prodComm).toMonoidHom.comp (epsT D ι) := rfl
      rw [h1, ← map_map, h, map_prodComm_bot_prod]
    refine ⟨W', W, ι.trans MulEquiv.prodComm, hcompl.symm, hnd', hnd, swap_compat D ι hι, L,
      ?_, hmap⟩
    have h2 := CatalogueBAlternating.pComponent_map_equiv 2 MulEquiv.prodComm _ hM
    rw [h, map_prodComm_bot_prod] at h2
    exact isPComponent_of_prod_bot h2

omit [Finite H] [Finite K] [FiniteDimensional K V] in
theorem quotient_of_left (D : InvData G Q Θ t)
    (ψ : orthogonalOperatorCentralizer Q D.A.toLinearMap ≃*
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype) ×
        TauCeti.QuadraticMap.orthogonalGroup (Q.comp U'.subtype))
    (M : Subgroup (FN D)) (L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype)))
    (hL : IsQuasisimple L) (hML : M.map (epsT D ψ) = L.prod ⊥) :
    IsQuasisimple (M.map (toHD D)) ∧
      Nonempty ((M.map (toHD D)) ⧸ center (M.map (toHD D)) ≃* L ⧸ center L) := by
  set e₁ : M.map (epsT D ψ) ≃* L := (MulEquiv.subgroupCongr hML).trans (prodBotEquiv L)
  have hq : IsQuasisimple (M.map (epsT D ψ)) := LocalCores.isQuasisimple_of_mulEquiv e₁.symm hL
  obtain ⟨hqJ, ⟨e₂⟩⟩ := centerQuotient_equiv D ψ M hq
  exact ⟨hqJ, ⟨e₂.trans (centerQuotientCongr e₁)⟩⟩

omit [Finite H] [Finite K] [FiniteDimensional K V] in
theorem commute_of_centralizes (D : InvData G Q Θ t) {s : H} (Ds : InvData G Q Θ s)
    (M : Subgroup (FN D)) (hperf : ⁅M, M⁆ = M)
    (hcent : ∀ m ∈ M, s * toHD D m = toHD D m * s) :
    ∀ m ∈ M, ∀ v, m.val.val.val (Ds.A v) = Ds.A (m.val.val.val v) := by
  set φ : FN D →* TauCeti.QuadraticMap.orthogonalGroup Q :=
    (fixedSubgroup (similarityConjugation Q D.A D.μ D.hsim)).subtype.comp (FN D).subtype
  set ψ := (similarityConjugation Q Ds.A Ds.μ Ds.hsim).toMonoidHom
  have hsign : ∀ m ∈ M, (φ m)⁻¹ * ψ (φ m) ∈ scalarSigns Q := by
    intro m hm
    have hjG := toH_mem_G G Q Θ t D.A D.μ D.hsim D.hconj m
    have h1 : MulAut.conjNormal s (⟨toHD D m, hjG⟩ : G) = ⟨toHD D m, hjG⟩ := by
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, hcent m hm, mul_inv_cancel_right]
    have h2 := Ds.hconj ⟨toHD D m, hjG⟩
    rw [h1] at h2
    have h3 : (⟨toHD D m, hjG⟩ : G) = Θ.symm (QuotientGroup.mk'
        ((scalarSigns Q).subgroupOf (orthogonalDerived Q)) ⟨m.val.val, m.property⟩) :=
      Subtype.ext rfl
    rw [h3, MulEquiv.apply_symm_apply, projectiveConjugation_mk] at h2
    have h4 := QuotientGroup.eq.mp h2
    rw [mem_subgroupOf] at h4
    exact h4
  have hP : ⁅M.map φ, M.map φ⁆ = M.map φ := by
    rw [← Subgroup.map_commutator, hperf]
  have hcen : ∀ x ∈ M.map φ, x⁻¹ * ψ x ∈ center (TauCeti.QuadraticMap.orthogonalGroup Q) := by
    rintro _ ⟨m, hm, rfl⟩
    exact scalarSigns_central Q (hsign m hm)
  have key := eq_of_perfect (M.map φ) hP ψ
    (fun x hx y _ => (mem_center_iff.mp (hcen x hx) y).symm)
    (fun x hx y hy => (mem_center_iff.mp (hcen x hx) (y⁻¹ * ψ y)).symm)
  intro m hm v
  have h1 := congrArg Subtype.val (key (φ m) (mem_map_of_mem φ hm))
  rw [MulEquiv.coe_toMonoidHom, similarityConjugation_val] at h1
  have h2 : Ds.A * (φ m).val = (φ m).val * Ds.A := by
    calc Ds.A * (φ m).val = Ds.A * (φ m).val * Ds.A⁻¹ * Ds.A := by group
      _ = (φ m).val * Ds.A := by rw [h1]
  exact (LinearEquiv.congr_fun h2 v).symm

end CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8
