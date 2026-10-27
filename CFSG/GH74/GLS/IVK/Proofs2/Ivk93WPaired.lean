module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovPGU
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93W

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup Module CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification CFSG.ComponentClassification.Sp4Rec
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.CatalogueBUnitaryB
  CFSG.ComponentClassification.OddClassSelector
open scoped MatrixGroups

variable {p f : ℕ} {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]
  {P : Type} [AddCommGroup P] [Module E P]

theorem ivk93w_exists_neg_one {G : Type} [Group G]
    (eC : G ≃* LinearMap.GeneralLinearGroup E P) (b : Module.Basis (Fin 2) E P)
    (h2 : (2 : E) ≠ 0) {N : Subgroup G}
    (hN : N.map ((eC.trans ((LinearMap.GeneralLinearGroup.generalLinearEquiv E P).trans
      (CatalogueBAlternatingIsometry.basisMatrixEquiv b))).toMonoidHom) =
        CatalogueBGeneralLinear.specialLinearRange 2 E) :
    ∃ g₀ ∈ N, g₀ ≠ 1 ∧
      ((eC g₀ : LinearMap.GeneralLinearGroup E P) : Module.End E P) = (-1 : E) • 1 := by
  set eGL := eC.trans ((LinearMap.GeneralLinearGroup.generalLinearEquiv E P).trans
      (CatalogueBAlternatingIsometry.basisMatrixEquiv b)) with heGL
  have hdet : Matrix.GeneralLinearGroup.det (-1 : Matrix.GeneralLinearGroup (Fin 2) E) = 1 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    simp [Matrix.det_fin_two]
  have hmem : (-1 : Matrix.GeneralLinearGroup (Fin 2) E) ∈
      CatalogueBGeneralLinear.specialLinearRange 2 E := by
    rw [CatalogueBGeneralLinear.specialLinearRange_eq_detKernel, MonoidHom.mem_ker]
    exact hdet
  rw [← hN] at hmem
  obtain ⟨g₀, hg₀, hg₀e⟩ := hmem
  refine ⟨g₀, hg₀, ?_, ?_⟩
  · rintro rfl
    have h1 : (-1 : Matrix.GeneralLinearGroup (Fin 2) E) = 1 := by
      rw [← hg₀e]
      exact map_one _
    have h3 := congrArg (fun u : Matrix.GeneralLinearGroup (Fin 2) E =>
      (u : Matrix (Fin 2) (Fin 2) E) 0 0) h1
    simp at h3
    exact h2 (by linear_combination (-1 : E) * h3)
  · have h1 : (eGL g₀ : Matrix (Fin 2) (Fin 2) E) = -1 := by
      rw [show (eGL g₀) = -1 from hg₀e]
      simp
    rw [heGL] at h1
    change (CatalogueBAlternatingIsometry.basisMatrixEquiv b
      (LinearMap.GeneralLinearGroup.generalLinearEquiv E P (eC g₀)) : Matrix (Fin 2) (Fin 2) E) = -1 at h1
    rw [CatalogueBAlternatingIsometry.basisMatrixEquiv_val] at h1
    apply (LinearMap.toMatrix b b).injective
    rw [map_smul, LinearMap.toMatrix_one]
    simpa using h1

theorem ivk93w_unitary_paired_simple (h : UnitaryFieldData p f E) (hp : p ≠ 2)
    [FiniteDimensional E V] {B : V →ₛₗ[h.bar] V →ₗ[E] E} {A : sesqUnitaryGroup B}
    {P : Submodule E V}
    (eC : centralizer ({A} : Set (sesqUnitaryGroup B)) ≃* LinearMap.GeneralLinearGroup E P)
    (hEq : ∀ g : centralizer ({A} : Set (sesqUnitaryGroup B)),
      (g : sesqUnitaryGroup B) ∈ sesqNormOneScalars h B ↔
        ∃ c : E, h.norm c = 1 ∧
          ((eC g : LinearMap.GeneralLinearGroup E P) : Module.End E P) = c • 1)
    (hP2 : finrank E P = 2)
    {N : Subgroup (centralizer ({A} : Set (sesqUnitaryGroup B)))}
    (hN : IsPComponent 2 N) (hNq : CFSG.IsQuasisimple ↥N)
    {M : Subgroup (centralizer ({(QuotientGroup.mk' (sesqNormOneScalars h B)) A} :
      Set (sesqProjUnitary h B)))}
    (hm : N.map (centralizerImageHom A) = M) : IsSimpleGroup ↥M := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite E := h.finite
  have : CharP E p := h.charP
  have h2 : (2 : E) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq E p]; exact hp)
  let b : Module.Basis (Fin 2) E P := Module.finBasisOfFinrankEq E P hP2
  set eGL := eC.trans ((LinearMap.GeneralLinearGroup.generalLinearEquiv E P).trans
      (CatalogueBAlternatingIsometry.basisMatrixEquiv b)) with heGL
  obtain ⟨-, -, -, k₁, -⟩ := CatalogueBGeneralLinear.pComponent_classification 2 E (by norm_num) 2 _
    (CatalogueBAlternating.pComponent_map_equiv 2 eGL _ hN)
  obtain ⟨g₀, hg₀N, hg₀1, hg₀eC⟩ := ivk93w_exists_neg_one eC b h2 k₁
  have hnorm1 : h.norm (-1 : E) = 1 := by
    simp [UnitaryFieldData.norm]
  have hg₀Z : ((g₀ : centralizer ({A} : Set (sesqUnitaryGroup B))) : sesqUnitaryGroup B) ∈
      sesqNormOneScalars h B := (hEq g₀).2 ⟨-1, hnorm1, hg₀eC⟩
  let ψ : ↥N →* ↥M := ((centralizerImageHom A).comp N.subtype).codRestrict M
    (fun n => hm ▸ Subgroup.mem_map_of_mem _ n.2)
  have hψs : Function.Surjective ψ := by
    intro m
    have hm' : (m : centralizer ({(QuotientGroup.mk' (sesqNormOneScalars h B)) A} :
        Set (sesqProjUnitary h B))) ∈ N.map (centralizerImageHom A) := hm ▸ m.2
    obtain ⟨n, hn, hnm⟩ := hm'
    exact ⟨⟨n, hn⟩, Subtype.ext hnm⟩
  have hker_le : ψ.ker ≤ center ↥N := by
    intro n hn
    have h1 : centralizerImageHom A (n : centralizer ({A} : Set (sesqUnitaryGroup B))) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hn)
    have h2' := ker_centralizerImageHom_le_center (h := h) A h1
    rw [mem_center_iff] at h2' ⊢
    intro y
    exact Subtype.ext (h2' (y : centralizer ({A} : Set (sesqUnitaryGroup B))))
  have hg₀ker : (⟨g₀, hg₀N⟩ : ↥N) ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff _).2 hg₀Z
  have hcard : Nat.card (center ↥N) = 2 := by
    let eSL : SL(2, E) ≃* ↥N :=
      ((CatalogueBGeneralLinear.rangeEquivSpecialLinear 2 E).symm.trans
        (MulEquiv.subgroupCongr k₁.symm)).trans
        (N.equivMapOfInjective eGL.toMonoidHom eGL.injective).symm
    rw [← Subgroup.map_center_eq eSL, Subgroup.card_map_of_injective eSL.injective]
    exact CFSG.RankThree.SubgroupLists.natCard_center_sl2 h2
  have hker_eq : ψ.ker = center ↥N := by
    apply Subgroup.eq_of_le_of_card_ge hker_le
    rw [hcard]
    have : ψ.ker ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.mem_bot] at hg₀ker
      exact hg₀1 (congrArg Subtype.val hg₀ker)
    exact (Subgroup.one_lt_card_iff_ne_bot _).2 this
  let eQ : ↥N ⧸ center ↥N ≃* ↥M :=
    (QuotientGroup.quotientMulEquivOfEq hker_eq.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
  have := hNq.2.1
  exact MulEquiv.isSimpleGroup eQ.symm

theorem ivk93w_unitary_block (h : UnitaryFieldData p f E) (hp : p ≠ 2)
    [FiniteDimensional E V] (hn : 2 ≤ finrank E V) {B : V →ₛₗ[h.bar] V →ₗ[E] E}
    (hB : B.IsSymm) (hBl : B.SeparatingLeft) {A : sesqUnitaryGroup B}
    (hA : orderOf (QuotientGroup.mk A : sesqProjUnitary h B) = 2)
    {M : Subgroup (centralizer
      ({(QuotientGroup.mk' (sesqNormOneScalars h B)) A} : Set (sesqProjUnitary h B)))}
    (hM : IsPComponent 2 M) :
    CFSG.IsQuasisimple ↥M ∧
      ((∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = p ^ f ∧ p ^ f ≠ 3 ∧
          Nonempty (SL(2, k) ≃* ↥M)) ∨
        (∃ d : ℕ, 3 ≤ d ∧ d < finrank E V ∧
          Nonempty (↥M ⧸ center ↥M ≃* StatedProj (StatedSU d (p ^ f) E))) ∨
        (∃ m : ℕ, 2 * m = finrank E V ∧ (m = 2 → IsSimpleGroup ↥M))) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite E := h.finite
  obtain ⟨hq, N, hc, hN₁, hm⟩ := ivk93cov_lift_data h hp hn hB hBl hA hM
  refine ⟨hq, ?_⟩
  obtain ⟨l, -, -, hN, hP, hMne, hcompl, hsplit, hpaired, -⟩ :=
    projective_unitary_involution_centralizer_matrix_structure h hp hn hB hBl hA
  rcases hN with hN | hN
  · obtain ⟨-, hsepP, hsepM, e, he⟩ := hsplit hN
    rcases ivk93cov_unitary_split h hp hB hP hMne hcompl hsepP hsepM e he hc hm with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · obtain ⟨-, -, -, h2m, -, -, eC, -, -, hEq⟩ := hpaired hN
    exact Or.inr (Or.inr ⟨_, h2m, fun hm2 =>
      ivk93w_unitary_paired_simple h hp eC hEq hm2 hN₁ hc.1 hm⟩)

namespace Ivk93W

variable {J : Type} [Group J] [Finite J] {x : J} {q : ℕ} {B : Subgroup J}

theorem false_of_simple (h : Ivk93W x q B) (hs : IsSimpleGroup ↥B) : False := by
  have hx : (⟨x, h.mem⟩ : ↥B) ∈ center ↥B := by
    rw [Subgroup.mem_center_iff]
    intro b
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (h.le b.2))
  have := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥B) with h1 | h1
  · rw [h1, Subgroup.mem_bot] at hx
    exact h.ne_one (congrArg Subtype.val hx)
  · apply h.not_solvable
    apply Group.isSolvable_of_comm
    intro a b
    have : a ∈ center ↥B := by rw [h1]; exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp this b).symm

end Ivk93W

end CFSG.GH74.GLS.IVK.Proofs2
