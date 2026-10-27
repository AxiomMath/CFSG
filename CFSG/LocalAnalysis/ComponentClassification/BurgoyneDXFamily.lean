module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXSpin
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Center
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutLift
public import Certificates.Data.ExceptionalSL3

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX

open CFSG CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed
open CFSG.ClassicalInvolution.G2D4Models.Twin
open scoped Pointwise

section Triality

variable {F : Type} [Field F]

@[expose] def IsTriality (ρ : Sp8 F ≃* Sp8 F) : Prop :=
  ∀ k : Fin 4, (rankOne (plusDatum 4 F (by norm_num)).rootGroup k).map ρ.toMonoidHom =
    rankOne (plusDatum 4 F (by norm_num)).rootGroup (triPerm k)

theorem negOne8_eq_z2_mul_z3 : negOne8 F = z2 F * z3 F :=
  ((eq_negOne_iff _ (quadPlus_ne_zero (n := 4) (K := F) (by norm_num)) _).2 coe_z2_mul_z3).symm

theorem triality_moves_negOne8 [Finite F] (h2 : (2 : F) ≠ 0) {ρ : Sp8 F ≃* Sp8 F}
    (hρ : IsTriality ρ) : ρ (negOne8 F) ≠ negOne8 F := by
  rw [negOne8_eq_z2_mul_z3, map_mul, triality_z2 h2 ρ hρ, triality_z3 h2 ρ hρ]
  intro h
  have h1 := congrArg (spinAction (quadPlus 4 F)) h
  rw [spinAction_z3_mul_z0, spinAction_z2_mul_z3] at h1
  have h3 : -(1 : F) = 1 := by
    have := congrFun (LinearEquiv.congr_fun h1 (Pi.single (Sum.inl 0) 1)) (Sum.inl 0)
    simpa using this
  apply h2
  linear_combination -h3

end Triality

@[expose] def D4TrialityThreeInput : Prop :=
  ∃ ρ : Sp8 (GaloisField 3 1) ≃* Sp8 (GaloisField 3 1), IsTriality ρ

section Family

variable (F : Type) [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]

instance isPerfect_Sp8 : Group.IsPerfect (Sp8 F) := isPerfect_spinGroup_quadPlus (by norm_num)

omit [Finite F] [Fact p.Prime] [CharP F p]
  in
theorem ker_proj_le_center8 :
    (matrixProjectiveProjection (Q8 F)).ker ≤ Subgroup.center (matrixDerived (Q8 F)) := by
  rw [matrixProjectiveProjection, QuotientGroup.ker_mk']
  exact matrixDerivedScalars_le_center _

theorem spinM_liftAut_kappa (hp2 : p ≠ 2) (g : similarityPairs (Q8 F)) :
    (spinM F).comp (liftAut F hp2 (matrixProjectiveConjugationHom (Q8 F) g)).toMonoidHom =
      (matrixDerivedConjugation (Q8 F) g).toMonoidHom.comp (spinM F) := by
  refine CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.hom_eq_of_central_ker_perfect
    (ker_proj_le_center8 F) _ _ fun x => ?_
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [← pi8_eq_proj_spinM, pi8_liftAut, ← matrixProjectiveConjugation_mk, pi8_eq_proj_spinM]
  rfl

theorem liftAut_negOne8_of_mem_image (hp2 : p ≠ 2) {γ : MulAut (P8 F)}
    (hγ : γ ∈ matrixProjectiveImage (Q8 F)) : liftAut F hp2 γ (negOne8 F) = negOne8 F := by
  obtain ⟨g, rfl⟩ := hγ
  have hk : liftAut F hp2 (matrixProjectiveConjugationHom (Q8 F) g) (negOne8 F) ∈
      (spinM F).ker := by
    rw [MonoidHom.mem_ker]
    have := DFunLike.congr_fun (spinM_liftAut_kappa F hp2 g) (negOne8 F)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at this
    rw [this, MonoidHom.mem_ker.1 (negOne8_mem_ker_spinM F), map_one]
  rcases (mem_ker_spinM_iff F _).1 hk with h | h
  · exfalso
    have : negOne8 F = 1 := (liftAut F hp2 _).injective (h.trans (map_one _).symm)
    exact negOne8_ne_one F (two_ne_zero8 F hp2) this
  · exact h

omit [Finite F] [Fact p.Prime] [CharP F p]
  in
theorem map_ker_pi8 (ρ : Sp8 F ≃* Sp8 F) :
    (pi8 F).ker.map (ρ : Sp8 F →* Sp8 F) = (pi8 F).ker := by
  rw [ker_pi8, ← MulEquiv.toMonoidHom_eq_coe]
  exact Subgroup.characteristic_iff_map_eq.mp inferInstance ρ

@[expose] def descend8 (ρ : Sp8 F ≃* Sp8 F) : MulAut (P8 F) :=
  descendAut (pi8 F) (pi8_surjective F) ρ (map_ker_pi8 F ρ)

omit [Finite F] [Fact p.Prime] [CharP F p]
  in
theorem pi8_descend8 (ρ : Sp8 F ≃* Sp8 F) (x : Sp8 F) :
    pi8 F (ρ x) = descend8 F ρ (pi8 F x) :=
  (descendAut_apply _ _ _ _ x).symm

theorem liftAut_descend8 (hp2 : p ≠ 2) (ρ : Sp8 F ≃* Sp8 F) : liftAut F hp2 (descend8 F ρ) = ρ :=
  liftAut_unique F hp2 fun x => pi8_descend8 F ρ x

theorem finite_mulAut_P8 : Finite (MulAut (P8 F)) :=
  Finite.of_injective (fun e : MulAut (P8 F) => (e : P8 F → P8 F)) DFunLike.coe_injective

omit [Fact p.Prime]
  in
theorem exists_model8 : ∃ f : ℕ, Nat.card F = p ^ f ∧
    StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus 4 F))) .POmegaPlus 4 p f := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F p
  refine ⟨n, by rw [Nat.card_eq_fintype_card, hn], ?_⟩
  exact ⟨⟨hp, n.pos, le_rfl⟩, F, inferInstance, inferInstance,
    by rw [Nat.card_eq_fintype_card, hn], ⟨MulEquiv.refl _⟩⟩

theorem liftAut_negOne8_iff (hp2 : p ≠ 2) {ρ : Sp8 F ≃* Sp8 F} (hρ : IsTriality ρ)
    (γ : MulAut (P8 F)) :
    liftAut F hp2 γ (negOne8 F) = negOne8 F ↔ γ ∈ projectivePointFamilyAut (Q8 F) := by
  have := finite_mulAut_P8 F
  set H := projectivePointFamilyAut (Q8 F) with hH
  set N : Subgroup (MulAut (P8 F)) :=
    (MulAction.stabilizer (MulAut (Sp8 F)) (negOne8 F)).comap (liftAut F hp2) with hN
  have hmemN : ∀ δ, δ ∈ N ↔ liftAut F hp2 δ (negOne8 F) = negOne8 F := fun δ => Iff.rfl
  obtain ⟨f, hcard, hmod⟩ := exists_model8 F (p := p)
  have hHN : H ≤ N := by
    intro δ hδ
    rw [hmemN]
    refine liftAut_negOne8_of_mem_image F hp2 ?_
    rw [← coordinate_plus_family_eq_matrixImage hmod F hcard (MulEquiv.refl _)]
    exact hδ
  have hNtop : N ≠ ⊤ := by
    intro h
    have hd : descend8 F ρ ∈ N := h ▸ Subgroup.mem_top _
    rw [hmemN, liftAut_descend8] at hd
    exact triality_moves_negOne8 (two_ne_zero8 F hp2) hρ hd
  have hHstab : H = MulAction.stabilizer (MulAut (P8 F)) (projectivePointFamily (Q8 F)) := by
    ext δ
    exact Iff.rfl
  have hHidx : H.index = 1 ∨ H.index = 3 := by
    rw [hHstab, MulAction.index_stabilizer, ← Nat.card_coe_set_eq]
    exact (CatalogueBOrthogonalInvolutionConjugacy.plus_four_conjugacy (K := F)).2
  have hH3 : H.index = 3 := by
    rcases hHidx with h | h
    · exact absurd (top_le_iff.mp ((Subgroup.index_eq_one.mp h) ▸ hHN)) hNtop
    · exact h
  have hN3 : N.index = 3 := by
    have hd : N.index ∣ 3 := hH3 ▸ Subgroup.index_dvd_of_le hHN
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exact absurd (Subgroup.index_eq_one.mp h) hNtop
    · exact h
  have hrel : H.relIndex N = 1 := by
    have h := Subgroup.relIndex_mul_index hHN
    rw [hH3, hN3] at h
    omega
  have hNH : N ≤ H := Subgroup.relIndex_eq_one.mp hrel
  rw [← hmemN]
  exact ⟨fun h => hNH h, fun h => hHN h⟩

end Family

end CFSG.ComponentClassification.Burgoyne.DX
