module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinear
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTISymplectic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalEvenUnitaryComponents
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalEvenOrthogonalComponents
public import CFSG.LocalAnalysis.ComponentInitial.EscapingBlockQuotient
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public noncomputable section

namespace CFSG.ComponentClassification.OutcomeLocal

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification

theorem map_centralizer_mulEquiv {T X : Type*} [Group T] [Group X] (e : T ≃* X) (u : T) :
    (centralizer ({u} : Set T)).map e.toMonoidHom = centralizer ({e u} : Set X) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hx
    rw [mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul, hx]
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [mem_centralizer_singleton_iff] at hy
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy]

theorem no_component_centralizer_of_mulEquiv {T X : Type*} [Group T] [Group X] (e : T ≃* X)
    (hX : ∀ x : X, orderOf x = 2 → ∀ B : Subgroup (centralizer ({x} : Set X)),
      ¬ CFSG.IsComponent B)
    (u : T) (hu : orderOf u = 2) (B : Subgroup (centralizer ({u} : Set T))) :
    ¬ CFSG.IsComponent B := by
  let ec : centralizer ({u} : Set T) ≃* centralizer ({e u} : Set X) :=
    ((centralizer ({u} : Set T)).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (map_centralizer_mulEquiv e u))
  intro hB
  exact hX (e u) ((orderOf_injective e.toMonoidHom e.injective u).trans hu) _
    (((CFSG.LocalCores.component_isomorphism ec).1 B).mp hB)

theorem no_component_of_even_classical_model {T : Type} [Group T] {t : StatedLieTag} {n f : ℕ}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (hT : StatedClassicalModel T t n 2 f) (u : T) (hu : orderOf u = 2)
    (B : Subgroup (centralizer ({u} : Set T))) : ¬ CFSG.IsComponent B := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  ·
    obtain ⟨⟨-, hf, hn, -, -⟩, K, _, _, hK, ⟨eT⟩⟩ := hT
    let e' : T ≃* LinearFlag.projectiveSL n K :=
      eT.trans ((projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K))
    exact no_component_centralizer_of_mulEquiv e'
      (fun x hx => even_linear_involution_centralizers_component_free hf hn hK x hx) u hu B
  ·
    obtain ⟨⟨-, hf, hn, hq⟩, K, _, _, hK, ⟨eT⟩⟩ := hT
    have h : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, mul_comm]⟩
    have hq' : ¬ (n = 3 ∧ 2 ^ f = 2) := fun ⟨h1, h2⟩ => hq (by rw [h1, h2])
    let e' : T ≃* unitaryPSU h n := eT.trans (unitaryPSUEquiv h (by omega)).symm
    exact no_component_centralizer_of_mulEquiv e'
      (fun x hx => UnbalancingLocal.even_unitary_involution_centralizers_component_free h hn hq'
        x hx) u hu B
  ·
    obtain ⟨⟨-, hf, hn, -⟩, K, _, _, hK, ⟨eT⟩⟩ := hT
    exact no_component_centralizer_of_mulEquiv eT
      (fun x hx => even_symplectic_involution_centralizers_component_free hf (by omega) hK x hx)
      u hu B
  ·
    obtain ⟨-, hf, hn⟩ := hT.1
    exact UnbalancingLocal.even_orthogonal_involution_centralizers_component_free (Or.inl rfl)
      hn hf hT u hu B
  ·
    obtain ⟨-, hf, hn⟩ := hT.1
    exact UnbalancingLocal.even_orthogonal_involution_centralizers_component_free (Or.inr rfl)
      hn hf hT u hu B

theorem commuting_block_even_classical_overgroup_exclusion {G : Type} [Group G] [Finite G]
    {J : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial) {L : Subgroup G}
    (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G)) (t : StatedLieTag)
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus) (n f : ℕ) :
    ¬ StatedClassicalModel (L ⧸ center L) t n 2 f := by
  intro hT
  obtain ⟨-, -, -, -, u, hu, Q, hQ⟩ :=
    escaping_block_quotient_inherits_local_components hq heven hJ hΔ hL hML hLH
  exact no_component_of_even_classical_model ht hT u hu _
    ((isComponentOf_iff_isComponent_subgroupOf hQ.1).1 hQ)

end CFSG.ComponentClassification.OutcomeLocal
