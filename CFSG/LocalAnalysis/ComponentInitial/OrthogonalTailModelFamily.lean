module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelBorel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataIntrinsic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbitReduction
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointReindexCovarianceAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataFamily

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Spin Module
open CFSG.ComponentClassification
open CatalogueBOrthogonalPointAction (Points statedPointAction statedPointAction_mk_submodule
  stated_action_properties)
open CatalogueBStabilizerFamily (pointStabilizer family familyAut mem_familyAut_iff
  mem_pointStabilizer_iff pointStabilizer_conj)
open CatalogueBOrthogonalPointPlusBorel
open scoped Pointwise
open CatalogueBOrthogonalPointData (projectivePointFamilyAut coordinateQuadOdd coordinateQuadMinus
  oddIndexEquiv minusIndexEquiv pointStabilizer_isCoatom_of_properties)

theorem familyAut_eq_top_of_image {G G' X X' : Type*} [Group G] [Group G']
    (ρ : G →* Equiv.Perm X) (ρ' : G' →* Equiv.Perm X') (Ψ : G ≃* G')
    (hfam : (fun U : Subgroup G => U.map Ψ.toMonoidHom) '' family ρ = family ρ')
    (htop : familyAut ρ = ⊤) : familyAut ρ' = ⊤ := by
  refine eq_top_iff.2 fun α' _ => ?_
  rw [mem_familyAut_iff]
  have hα : (Ψ.trans α').trans Ψ.symm ∈ familyAut ρ := htop ▸ Subgroup.mem_top _
  rw [mem_familyAut_iff] at hα
  have hcomm : α'.toMonoidHom.comp Ψ.toMonoidHom =
      Ψ.toMonoidHom.comp ((Ψ.trans α').trans Ψ.symm).toMonoidHom :=
    MonoidHom.ext fun g => by simp
  rw [← hfam, Set.image_image]
  conv_rhs => rw [← hα]
  rw [Set.image_image]
  refine Set.image_congr fun U _ => ?_
  rw [Subgroup.map_map, Subgroup.map_map, hcomm]

theorem family_image_of_equivariant {G G' X X' : Type*} [Group G] [Group G']
    (ρ : G →* Equiv.Perm X) (ρ' : G' →* Equiv.Perm X') (Ψ : G ≃* G') (χ : X ≃ X')
    (h : ∀ g x, χ (ρ g x) = ρ' (Ψ g) (χ x)) :
    (fun U : Subgroup G => U.map Ψ.toMonoidHom) '' family ρ = family ρ' := by
  have hstab : ∀ x, (pointStabilizer ρ x).map Ψ.toMonoidHom = pointStabilizer ρ' (χ x) := by
    intro x
    ext g'
    rw [Subgroup.mem_map_equiv, mem_pointStabilizer_iff, mem_pointStabilizer_iff,
      ← χ.injective.eq_iff, h, MulEquiv.apply_symm_apply]
  ext U
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨χ x, (hstab x).symm⟩
  · rintro ⟨x', rfl⟩
    refine ⟨pointStabilizer ρ (χ.symm x'), ⟨χ.symm x', rfl⟩, ?_⟩
    change (pointStabilizer ρ (χ.symm x')).map Ψ.toMonoidHom = pointStabilizer ρ' x'
    rw [hstab, Equiv.apply_symm_apply]

section Stated

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q : QuadraticForm K (ι → K)} {Q0 : (ι → K) → K}

theorem pointStabilizer_statedPointAction (hQ : ⇑Q = Q0) (L : Points Q) :
    pointStabilizer (statedPointAction hQ) L = statedProjectiveSubspaceStabilizer Q0 L.val := by
  ext x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ x
  rw [mem_pointStabilizer_iff, mem_statedProjectiveSubspaceStabilizer_mk,
    mem_statedDerivedSubspaceStabilizer]
  constructor
  · intro h
    have h' := congrArg Subtype.val h
    rwa [statedPointAction_mk_submodule] at h'
  · intro h
    exact Subtype.ext (by rw [statedPointAction_mk_submodule]; exact h)

variable {A : Type} [AddCommGroup A] [Module K A] {r : ℕ} {qA : QuadraticForm K A}
  (ψ : (quadTail r qA).IsometryEquiv Q) (hQ : ⇑Q = Q0)
  (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
    elementaryGroup Q)

include ψ hE in
theorem familyAut_statedPointAction_eq_top [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hr : 3 ≤ r) (hani : qA.Anisotropic) (hreg : (polarBilin qA).Nondegenerate)
    (hm : finrank K A = 1 ∨ finrank K A = 2) {F : Fin r → Submodule K (ι → K)}
    (hF : ∀ i, F i = (tailFlag K A r (i + 1)).map ψ.toLinearMap)
    (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    familyAut (statedPointAction hQ) = ⊤ := by
  obtain ⟨hFs, -, hB, hC, hidx⟩ := borelInterface_of_tailIsometry ψ hQ hE hr hani hreg hm hF
  have ha := stated_action_properties hQ hE hnd hT
  have hr0 : 0 < r := by omega
  set i₀ : Fin r := ⟨0, hr0⟩
  have hF0s : ∀ x ∈ F i₀, Q x = 0 := fun x hx => by rw [hQ]; exact (hFs i₀).1 x hx
  set L₀ : Points Q := ⟨F i₀, by rw [(hFs i₀).2], hF0s⟩
  have hD : pointStabilizer (statedPointAction hQ) L₀ =
      statedProjectiveSubspaceStabilizer Q0 (F i₀) := pointStabilizer_statedPointAction hQ L₀
  have htrans : ∀ y : Points Q, ∃ g, statedPointAction hQ g L₀ = y := by
    let := MulAction.compHom (Points Q) (statedPointAction hQ)
    have : MulAction.IsPreprimitive (StatedProj (StatedOmega Q0)) (Points Q) := ha.2.2.2.2.1
    intro y
    exact MulAction.exists_smul_eq _ L₀ y
  have hfam : family (statedPointAction hQ) = CatalogueBOrthogonalSmallFamilyOrbit.conjugacyFamily
      (pointStabilizer (statedPointAction hQ) L₀) := by
    ext U
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨g, hg⟩ := htrans y
      refine ⟨g, ?_⟩
      change (pointStabilizer (statedPointAction hQ) L₀).map (MulAut.conj g).toMonoidHom =
        pointStabilizer (statedPointAction hQ) y
      rw [pointStabilizer_conj, hg]
    · rintro ⟨g, rfl⟩
      exact ⟨statedPointAction hQ g L₀, (pointStabilizer_conj _ g L₀).symm⟩
  change MulAction.stabilizer (MulAut (StatedProj (StatedOmega Q0)))
    (family (statedPointAction hQ)) = ⊤
  rw [hfam]
  have hDco : IsCoatom (pointStabilizer (statedPointAction hQ) L₀) :=
    pointStabilizer_isCoatom_of_properties Q (statedPointAction hQ) ha L₀
  refine CatalogueBOrthogonalPointPlusFamilyOrbit.familyStabilizer_eq_top_of_borel
    (statedProjectiveFlagStabilizer Q0 F) _ ?_ hDco ?_
    {M | ∃ i, M = statedProjectiveSubspaceStabilizer Q0 (F i)} hC ?_
  · rw [hD]
    exact iInf_le _ i₀
  · exact hB
  · rintro M ⟨i, rfl⟩ hMD
    rw [hD] at hMD ⊢
    by_cases hi : (i : ℕ) = 0
    · rw [show i = i₀ from Fin.ext hi]
    · exfalso
      have hlt := hidx (F i) (F i₀) (hFs i).1 (by rw [(hFs i).2]; omega) (hFs i₀).1
        (by rw [(hFs i₀).2])
      omega

end Stated

theorem orthogonal_geometry_tail_model_point_family_invariant (G : Type) [Group G]
    (t : StatedLieTag) (ht : t = .POmegaOdd ∨ t = .POmegaMinus) (n p f : ℕ)
    (h : StatedClassicalModel G t n p f) :
    match t with
    | .POmegaOdd => ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
        familyAut (statedPointAction (coe_quadOdd n K)) = ⊤ ∧
          projectivePointFamilyAut (coordinateQuadOdd n K) = ⊤
    | .POmegaMinus => ∀ (hn : 1 ≤ n) (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
        ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
        familyAut (statedPointAction (coe_quadMinus n K b c)) = ⊤ ∧
          projectivePointFamilyAut (coordinateQuadMinus n K hn b c) = ⊤
    | _ => False := by
  rcases ht with rfl | rfl
  · obtain ⟨hp, hf, hn, hp2⟩ := h.1
    intro K _ _ hK
    have hchar := ringChar_eq_of_card_eq hp hf hK
    have : Fact p.Prime := ⟨hp⟩
    have : CharP K p := hchar ▸ ringChar.charP K
    have h2 : (2 : K) ≠ 0 := by
      rw [Ne, two_eq_zero_iff_ringChar_eq_two (hchar ▸ hp), hchar]
      exact hp2
    have hreg := regular_quadOdd h2 hn
    have hst := familyAut_statedPointAction_eq_top (oddTailIsometry n K) (coe_quadOdd n K)
      (commutator_orthogonalGroup_quadOdd h2 hn) hn anisotropic_oddTailForm
      (nondegenerate_oddTailForm h2) (Or.inl finrank_unit_fun)
      (tailModelFlag_eq_map (oddTailIsometry n K) fun _ => rfl) hreg.1 hreg.2
    exact ⟨hst, familyAut_eq_top_of_image _ _ _ (family_image_of_equivariant _ _ _ _
      (CatalogueBOrthogonalPointReindexCovariance.statedPointAction_reindex (oddIndexEquiv n)
        (quadOdd n K) (coe_quadOdd n K))) hst⟩
  · obtain ⟨hp, hf, hn⟩ := h.1
    intro hn1 K _ _ hK b c hirr
    have hchar := ringChar_eq_of_card_eq hp hf hK
    have : Fact p.Prime := ⟨hp⟩
    have : CharP K p := hchar ▸ ringChar.charP K
    have hreg := regular_quadMinus hn hirr
    have hst := familyAut_statedPointAction_eq_top (minusTailIsometry n K b c)
      (coe_quadMinus n K b c) (commutator_orthogonalGroup_quadMinus hn hirr) (by omega)
      (anisotropic_minusTailForm hirr) (nondegenerate_minusTailForm hirr)
      (Or.inr finrank_fin_two_fun)
      (tailModelFlag_eq_map (minusTailIsometry n K b c) fun _ => rfl) hreg.1 hreg.2
    exact ⟨hst, familyAut_eq_top_of_image _ _ _ (family_image_of_equivariant _ _ _ _
      (CatalogueBOrthogonalPointReindexCovariance.statedPointAction_reindex (minusIndexEquiv n hn1)
        (quadMinus n K b c) (coe_quadMinus n K b c))) hst⟩

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
