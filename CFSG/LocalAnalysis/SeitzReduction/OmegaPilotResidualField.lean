module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotFusion
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotInnerActionCore
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRigidityResidual

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus regular_coordinateQuadPlus commutator_coordinateQuadPlus)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  (EvenOrthogonalRealization evenOrthogonalRealization_of_regular)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  (isometryConjugationHom inner_eq_map_commutator relIndex_inner_dvd
    card_abelianization_matrixIsometries_reindex)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section AutField

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {f : ℕ}

@[expose] noncomputable def orthAutFieldPart (hR : EvenOrthogonalRealization Q f)
    (hE : matrixProjectiveImage Q = ⊤) : MulAut (matrixProjectiveDerived Q) →* (K ≃+* K) :=
  (Classical.choose hR.2.2.2.2).comp
    ((MonoidHom.id _).codRestrict (matrixProjectiveImage Q) fun β => by
      rw [hE]
      exact Subgroup.mem_top β)

theorem orthAutFieldPart_kappa (hR : EvenOrthogonalRealization Q f)
    (hE : matrixProjectiveImage Q = ⊤) (g : similarityPairs Q) :
    orthAutFieldPart hR hE (matrixProjectiveConjugationHom Q g) = g.val.right := by
  rw [← (Classical.choose_spec hR.2.2.2.2).1 g]
  rfl

theorem orthAutFieldPart_eq_one_iff (hR : EvenOrthogonalRealization Q f)
    (hE : matrixProjectiveImage Q = ⊤) (β : MulAut (matrixProjectiveDerived Q)) :
    orthAutFieldPart hR hE β = 1 ↔ β ∈ (isometryConjugationHom Q).range := by
  have hker := (Classical.choose_spec hR.2.2.2.2).2.1
  have hβ : β ∈ matrixProjectiveImage Q := by
    rw [hE]
    exact Subgroup.mem_top β
  change Classical.choose hR.2.2.2.2 ⟨β, hβ⟩ = 1 ↔ _
  rw [← MonoidHom.mem_ker, hker, mem_subgroupOf]
  rfl

theorem orthAutFieldPart_mem_inner (hR : EvenOrthogonalRealization Q f)
    (hE : matrixProjectiveImage Q = ⊤) {β : MulAut (matrixProjectiveDerived Q)}
    (hβ : β ∈ inner (matrixProjectiveDerived Q)) : orthAutFieldPart hR hE β = 1 := by
  rw [orthAutFieldPart_eq_one_iff]
  rw [inner_eq_map_commutator] at hβ
  exact Subgroup.map_le_range _ _ hβ

theorem orthAutFieldPart_conj (hR : EvenOrthogonalRealization Q f)
    (hE : matrixProjectiveImage Q = ⊤) (x : matrixProjectiveDerived Q) :
    orthAutFieldPart hR hE (MulAut.conj x) = 1 :=
  orthAutFieldPart_mem_inner hR hE ⟨x, rfl⟩

end AutField

section Plus

variable {K : Type} [Field K] [Finite K] {n f : ℕ}

omit [Finite K] in
theorem plusRealization (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n) :
    EvenOrthogonalRealization (coordinateQuadPlus n K) f :=
  evenOrthogonalRealization_of_regular hf hK (by omega) _ (regular_coordinateQuadPlus n K hn).1
    (regular_coordinateQuadPlus n K hn).2 (commutator_coordinateQuadPlus n K hn)

theorem plusImage_eq_top (hn : 5 ≤ n) : matrixProjectiveImage (coordinateQuadPlus n K) = ⊤ :=
  CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn

@[expose] noncomputable def plusFieldPart (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n) :
    MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)) →* (K ≃+* K) :=
  orthAutFieldPart (plusRealization hf hK (by omega)) (plusImage_eq_top hn)

theorem card_abelianization_isometries_plus_le_two (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) :
    Nat.card (Abelianization (matrixIsometries (coordinateQuadPlus n K))) ≤ 2 := by
  have h : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedOmega
        (CFSG.Assembly.LowTwoRank.StatedQuadPlus n K))) .POmegaPlus n 2 f :=
    ⟨⟨Nat.prime_two, hf, hn⟩, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  have hab := CFSG.LocalAnalysis.ComponentInitial.orthogonal_model_isometry_abelianization_order_bound
    _ .POmegaPlus (.inr (.inl rfl)) n 2 f h K hK (CFSG.LieType.Universal.Spin.quadPlus n K)
    (CFSG.LieType.Universal.Spin.coe_quadPlus n K) (MulEquiv.refl _)
  rw [coordinateQuadPlus, card_abelianization_matrixIsometries_reindex]
  exact hab.2.2 rfl

end Plus

section Index

variable {K : Type} [Field K] [Finite K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

theorem inv_mul_mem_inner_of_not_mem
    (hA : Nat.card (Abelianization (matrixIsometries Q)) ≤ 2)
    {β₁ β₂ : MulAut (matrixProjectiveDerived Q)} (h₁ : β₁ ∈ (isometryConjugationHom Q).range)
    (h₂ : β₂ ∈ (isometryConjugationHom Q).range) (h₁' : β₁ ∉ inner (matrixProjectiveDerived Q))
    (h₂' : β₂ ∉ inner (matrixProjectiveDerived Q)) :
    β₁⁻¹ * β₂ ∈ inner (matrixProjectiveDerived Q) := by
  have hdvd := relIndex_inner_dvd Q
  have hpos : 0 < Nat.card (Abelianization (matrixIsometries Q)) := Nat.card_pos
  have hle : (inner (matrixProjectiveDerived Q)).relIndex (isometryConjugationHom Q).range ≤ 2 :=
    (Nat.le_of_dvd hpos hdvd).trans hA
  have hne : (inner (matrixProjectiveDerived Q)).relIndex (isometryConjugationHom Q).range ≠ 0 :=
    fun h0 => by rw [h0] at hdvd; exact absurd (Nat.eq_zero_of_zero_dvd hdvd) hpos.ne'
  rcases (by omega : (inner (matrixProjectiveDerived Q)).relIndex
      (isometryConjugationHom Q).range = 1 ∨
    (inner (matrixProjectiveDerived Q)).relIndex (isometryConjugationHom Q).range = 2) with
    h1 | h2
  · exact absurd (Subgroup.relIndex_eq_one.1 h1 h₁) h₁'
  · have hidx : ((inner (matrixProjectiveDerived Q)).subgroupOf
        (isometryConjugationHom Q).range).index = 2 := h2
    have key := (Subgroup.mul_mem_iff_of_index_two hidx
      (a := (⟨β₁, h₁⟩ : (isometryConjugationHom Q).range)⁻¹) (b := ⟨β₂, h₂⟩)).2
      (by
        rw [inv_mem_iff, mem_subgroupOf, mem_subgroupOf]
        exact iff_of_false h₁' h₂')
    rw [mem_subgroupOf] at key
    exact key

end Index

section Commutators

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {d : ℕ}
  {Q : QuadraticForm K (Fin d → K)} {f : ℕ}

theorem exists_eq_or_eq_mul_of_normalizerAut_mem_inner (e : L ≃* matrixProjectiveDerived Q)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) {s : G}
    (hs : s ∈ centralizer ({t} : Set G))
    (hin : E6Pilot.normalizerAut e ⟨s, hCN hs⟩ ∈ inner (matrixProjectiveDerived Q)) :
    ∃ l ∈ L, s = l ∨ s = l * t := by
  obtain ⟨p, hp⟩ := hin
  have hLt : L ≤ centralizer ({t} : Set G) :=
    SeitzQ2.le_centralizer_singleton_of_mem_centralizer (mem_centralizer_of_inf_eq hKt)
  refine ⟨e.symm p, (e.symm p).2, LinearPilot.eq_or_eq_mul_of_conj_eq' hLt ht hKt hs (e.symm p).2
    fun y hy => ?_⟩
  have h1 := E6Pilot.coe_symm_normalizerAut_apply e ⟨s, hCN hs⟩ (e ⟨y, hy⟩)
  rw [← hp, MulAut.conj_apply, MulEquiv.symm_apply_apply] at h1
  have h2 : e.symm (p * e ⟨y, hy⟩ * p⁻¹) = e.symm p * ⟨y, hy⟩ * (e.symm p)⁻¹ := by
    rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  rw [h2] at h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
  exact h1.symm

theorem commutator_mem_of_orthAutFieldPart_eq_one [Finite K] (hR : EvenOrthogonalRealization Q f)
    (hE : matrixProjectiveImage Q = ⊤)
    (hA : Nat.card (Abelianization (matrixIsometries Q)) ≤ 2)
    (e : L ≃* matrixProjectiveDerived Q) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) {S : Subgroup G}
    (hSt : S ≤ centralizer ({t} : Set G))
    (hfp : ∀ (s : G) (hs : s ∈ S),
      orthAutFieldPart hR hE (E6Pilot.normalizerAut e ⟨s, hCN (hSt hs)⟩) = 1) :
    ∀ y ∈ S, ∀ z ∈ S, y * z * y⁻¹ * z⁻¹ ∈ L := by
  have hO : ∀ (s : G) (hs : s ∈ S),
      E6Pilot.normalizerAut e ⟨s, hCN (hSt hs)⟩ ∈ (isometryConjugationHom Q).range :=
    fun s hs => (orthAutFieldPart_eq_one_iff hR hE _).1 (hfp s hs)
  intro y hy z hz
  by_cases hyI : E6Pilot.normalizerAut e ⟨y, hCN (hSt hy)⟩ ∈ inner (matrixProjectiveDerived Q)
  · obtain ⟨l, hl, hyl⟩ :=
      exists_eq_or_eq_mul_of_normalizerAut_mem_inner e ht hKt hCN (hSt hy) hyI
    exact LinearPilot.commutator_mem_of_eq_or_eq_mul hl hyl (hCN (hSt hz)) (hSt hz)
  by_cases hzI : E6Pilot.normalizerAut e ⟨z, hCN (hSt hz)⟩ ∈ inner (matrixProjectiveDerived Q)
  · obtain ⟨l, hl, hzl⟩ :=
      exists_eq_or_eq_mul_of_normalizerAut_mem_inner e ht hKt hCN (hSt hz) hzI
    have h := LinearPilot.commutator_mem_of_eq_or_eq_mul hl hzl (hCN (hSt hy)) (hSt hy)
    have e' : y * z * y⁻¹ * z⁻¹ = (z * y * z⁻¹ * y⁻¹)⁻¹ := by group
    rw [e']
    exact L.inv_mem h
  have hd : z⁻¹ * y ∈ S := S.mul_mem (S.inv_mem hz) hy
  have hdI : E6Pilot.normalizerAut e ⟨z⁻¹ * y, hCN (hSt hd)⟩ ∈ inner (matrixProjectiveDerived Q) := by
    have h1 : (⟨z⁻¹ * y, hCN (hSt hd)⟩ : normalizer (L : Set G)) =
        (⟨z, hCN (hSt hz)⟩ : normalizer (L : Set G))⁻¹ * ⟨y, hCN (hSt hy)⟩ := rfl
    rw [h1, map_mul, map_inv]
    exact inv_mul_mem_inner_of_not_mem Q hA (hO z hz) (hO y hy) hzI hyI
  obtain ⟨l, hl, hdl⟩ := exists_eq_or_eq_mul_of_normalizerAut_mem_inner e ht hKt hCN (hSt hd) hdI
  have h := LinearPilot.commutator_mem_of_eq_or_eq_mul hl hdl (hCN (hSt hz)) (hSt hz)
  have e' : y * z * y⁻¹ * z⁻¹ = z * ((z⁻¹ * y) * z * (z⁻¹ * y)⁻¹ * z⁻¹) * z⁻¹ := by group
  rw [e']
  exact (mem_normalizer_iff.1 (hCN (hSt hz)) _).1 h

theorem exists_orthAutFieldPart_ne_one_of_commutator_not_mem [Finite K]
    (hR : EvenOrthogonalRealization Q f) (hE : matrixProjectiveImage Q = ⊤)
    (hA : Nat.card (Abelianization (matrixIsometries Q)) ≤ 2)
    (e : L ≃* matrixProjectiveDerived Q) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) {S : Subgroup G}
    (hSt : S ≤ centralizer ({t} : Set G))
    (hcomm : ∃ y ∈ S, ∃ z ∈ S, y * z * y⁻¹ * z⁻¹ ∉ L) :
    ∃ (s : G) (hs : s ∈ S), orthAutFieldPart hR hE (E6Pilot.normalizerAut e ⟨s, hCN (hSt hs)⟩) ≠ 1 := by
  by_contra hno
  push Not at hno
  obtain ⟨y, hy, z, hz, hyz⟩ := hcomm
  exact hyz (commutator_mem_of_orthAutFieldPart_eq_one hR hE hA e ht hKt hCN hSt hno y hy z hz)

end Commutators

end CFSG.SeitzReduction.OmegaPilot
