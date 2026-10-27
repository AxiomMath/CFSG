module

public import CFSG.ClassicalInvolution.ModelFacts.OrthAutLift
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusCenter
public import
  CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbitModel
public import CFSG.LieType.Steinberg.CentralExt.OrthogonalPerfect
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusCentrallyClosed

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX

open CFSG CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit (plusCoordinateEquiv)
open CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed
open CFSG.ClassicalInvolution.ModelFacts.OrthAut

section Defs

variable (F : Type) [Field F]

abbrev Sp8 : Type := spinGroup (quadPlus 4 F)

abbrev Q8 : QuadraticForm F (Fin (2 * 4) → F) := coordinateQuadPlus 4 F

abbrev P8 : Type := matrixProjectiveDerived (Q8 F)

@[expose] def spinM : Sp8 F →* matrixDerived (Q8 F) :=
  (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 F) (coe_quadPlus 4 F)).toMonoidHom.comp
    ((spinMatrix (quadPlus 4 F)).codRestrict _
      (spinMatrix_mem_of_range_eq _ (range_spinMatrix_quadPlus (by norm_num))))

@[expose] def pi8 : Sp8 F →* P8 F :=
  (plusCoordinateEquiv 4 F).toMonoidHom.comp
    (spinToStatedProj (quadPlus 4 F) (range_spinMatrix_quadPlus (by norm_num)))

abbrev negOne8 : Sp8 F := negOneS F (n := 4) (by norm_num)

theorem pi8_eq_proj_spinM (x : Sp8 F) :
    pi8 F x = matrixProjectiveProjection (Q8 F) (spinM F x) := by
  change plusCoordinateEquiv 4 F (spinToStatedProj _ _ x) = _
  rw [spinToStatedProj_apply]
  exact statedProjectiveReindexEquiv_mk _ _ _ _

theorem pi8_surjective : Function.Surjective (pi8 F) :=
  (plusCoordinateEquiv 4 F).surjective.comp
    (spinToStatedProj_quadPlus (K := F) (n := 4) (by norm_num)).1

theorem ker_pi8 : (pi8 F).ker = Subgroup.center (Sp8 F) := by
  have h := (spinToStatedProj_quadPlus (K := F) (n := 4) (by norm_num)).2.2
  rw [← h]
  ext x
  simp only [pi8, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]

theorem ker_pi8_eq_scalarSpin : (pi8 F).ker = scalarSpin 4 F := by
  rw [ker_pi8, ← (spinToStatedProj_quadPlus (K := F) (n := 4) (by norm_num)).2.2,
    (spinToStatedProj_quadPlus (K := F) (n := 4) (by norm_num)).2.1]

theorem mem_ker_spinM_iff (x : Sp8 F) : x ∈ (spinM F).ker ↔ x = 1 ∨ x = negOne8 F := by
  have hk : x ∈ (spinM F).ker ↔ x ∈ (spinMatrix (quadPlus 4 F)).ker := by
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    change (statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 F) (coe_quadPlus 4 F))
      (((spinMatrix (quadPlus 4 F)).codRestrict _
        (spinMatrix_mem_of_range_eq _ (range_spinMatrix_quadPlus (by norm_num)))) x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [hk]
  constructor
  · exact eq_one_or_eq_negOneS_of_mem_ker (by norm_num)
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact negOne_mem_ker (by norm_num)

theorem negOne8_mem_ker_spinM : negOne8 F ∈ (spinM F).ker :=
  (mem_ker_spinM_iff F _).2 (Or.inr rfl)

theorem negOne8_mem_center : negOne8 F ∈ Subgroup.center (Sp8 F) := by
  rw [← ker_pi8, MonoidHom.mem_ker, pi8_eq_proj_spinM, MonoidHom.mem_ker.1
    (negOne8_mem_ker_spinM F), map_one]

theorem negOne8_ne_one (h2 : (2 : F) ≠ 0) : negOne8 F ≠ 1 := negOneS_ne_one (by norm_num) h2

theorem isKleinFour_center8 (h2 : (2 : F) ≠ 0) : IsKleinFour (Subgroup.center (Sp8 F)) := by
  rw [← ker_pi8, ker_pi8_eq_scalarSpin]
  exact isKleinFour_scalarSpin (by norm_num) h2 (by decide)

theorem mul_self_eq_one_of_mem_center8 (h2 : (2 : F) ≠ 0) {z : Sp8 F}
    (hz : z ∈ Subgroup.center (Sp8 F)) : z * z = 1 := by
  have := isKleinFour_center8 F h2
  have h := IsKleinFour.mul_self (G := Subgroup.center (Sp8 F)) ⟨z, hz⟩
  exact congrArg Subtype.val h

theorem card_center8 (h2 : (2 : F) ≠ 0) : Nat.card (Subgroup.center (Sp8 F)) = 4 :=
  (isKleinFour_center8 F h2).card_four

end Defs

section Descend

variable {G H : Type*} [Group G] [Group H]

theorem quotientKerEquivOfSurjective_mk' (φ : G →* H) (hφ : Function.Surjective φ) (g : G) :
    QuotientGroup.quotientKerEquivOfSurjective φ hφ (g : G ⧸ φ.ker) = φ g := by
  unfold QuotientGroup.quotientKerEquivOfSurjective
  rw [QuotientGroup.quotientKerEquivOfRightInverse_apply, QuotientGroup.kerLift_mk]

@[expose] def descendAut (φ : G →* H) (hφ : Function.Surjective φ) (s : G ≃* G)
    (hs : φ.ker.map (s : G →* G) = φ.ker) : MulAut H :=
  (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.trans
    ((QuotientGroup.congr φ.ker φ.ker s hs).trans (QuotientGroup.quotientKerEquivOfSurjective φ hφ))

theorem descendAut_apply (φ : G →* H) (hφ : Function.Surjective φ) (s : G ≃* G)
    (hs : φ.ker.map (s : G →* G) = φ.ker) (x : G) : descendAut φ hφ s hs (φ x) = φ (s x) := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm (φ x) = (x : G ⧸ φ.ker) := by
    rw [MulEquiv.symm_apply_eq, quotientKerEquivOfSurjective_mk']
  rw [descendAut, MulEquiv.trans_apply, h1, MulEquiv.trans_apply, QuotientGroup.congr_mk,
    quotientKerEquivOfSurjective_mk']

end Descend

section Lift

variable (F : Type) [Field F] {p : ℕ} [Fact p.Prime]

theorem not_dvd_card_ker_pi8 (h2 : (2 : F) ≠ 0) (hp2 : p ≠ 2) : ¬ p ∣ Nat.card (pi8 F).ker := by
  rw [ker_pi8, card_center8 F h2]
  intro h
  have hp4 : p ∣ 2 ^ 2 := by norm_num; exact h
  have hp := (Fact.out : p.Prime).dvd_of_dvd_pow hp4
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 hp)

variable [CharP F p]

omit [Fact p.Prime] in
theorem two_ne_zero8 (hp2 : p ≠ 2) : (2 : F) ≠ 0 :=
  Ring.two_ne_zero (ringChar_ne_two_of_ne_two (F := F) hp2)

variable [Finite F]

instance finite_Sp8 : Finite (Sp8 F) :=
  CFSG.LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := 4))

include p in
theorem centralPSection8 : CentralPSection p (Sp8 F) :=
  centralPSection_spinPlus (F := F) (p := p) (n := 4) (by norm_num)

include p in
theorem exists_lift8 (hp2 : p ≠ 2) (γ : MulAut (P8 F)) :
    ∃ α : MulAut (Sp8 F), ∀ x, pi8 F (α x) = γ (pi8 F x) :=
  (centralPSection8 F (p := p)).exists_mulEquiv_lift (pi8 F) (pi8_surjective F)
    (ker_pi8 F).le (not_dvd_card_ker_pi8 F (two_ne_zero8 F hp2) hp2) γ

include p in
theorem lift8_unique (hp2 : p ≠ 2) {α β : Sp8 F →* Sp8 F}
    (h : ∀ x, pi8 F (α x) = pi8 F (β x)) : α = β := by
  obtain ⟨_, -, huniq⟩ := (centralPSection8 F (p := p)).existsUnique_lift (pi8_surjective F)
    (ker_pi8 F).le (not_dvd_card_ker_pi8 F (two_ne_zero8 F hp2) hp2) ((pi8 F).comp β)
  exact (huniq α (MonoidHom.ext fun x => h x)).trans (huniq β rfl).symm

include p in
theorem liftAut_ext (hp2 : p ≠ 2) {α β : MulAut (Sp8 F)}
    (h : ∀ x, pi8 F (α x) = pi8 F (β x)) : α = β := by
  have := lift8_unique F hp2 (α := α.toMonoidHom) (β := β.toMonoidHom) h
  exact MulEquiv.ext fun x => DFunLike.congr_fun this x

@[expose] def liftAut (hp2 : p ≠ 2) : MulAut (P8 F) →* MulAut (Sp8 F) where
  toFun γ := Classical.choose (exists_lift8 F hp2 γ)
  map_one' := liftAut_ext F hp2 fun x => by
    rw [Classical.choose_spec (exists_lift8 F hp2 1) x]
    simp
  map_mul' γ δ := liftAut_ext F hp2 fun x => by
    rw [Classical.choose_spec (exists_lift8 F hp2 (γ * δ)) x, MulAut.mul_apply, MulAut.mul_apply,
      Classical.choose_spec (exists_lift8 F hp2 γ), Classical.choose_spec (exists_lift8 F hp2 δ)]

theorem pi8_liftAut (hp2 : p ≠ 2) (γ : MulAut (P8 F)) (x : Sp8 F) :
    pi8 F (liftAut F hp2 γ x) = γ (pi8 F x) :=
  Classical.choose_spec (exists_lift8 F hp2 γ) x

theorem liftAut_unique (hp2 : p ≠ 2) {γ : MulAut (P8 F)} {α : MulAut (Sp8 F)}
    (h : ∀ x, pi8 F (α x) = γ (pi8 F x)) : liftAut F hp2 γ = α :=
  liftAut_ext F hp2 fun x => by rw [pi8_liftAut, h]

theorem liftAut_injective (hp2 : p ≠ 2) : Function.Injective (liftAut F hp2) := by
  intro γ δ h
  ext y
  obtain ⟨x, rfl⟩ := pi8_surjective F y
  rw [← pi8_liftAut F hp2, ← pi8_liftAut F hp2, h]

end Lift

end CFSG.ComponentClassification.Burgoyne.DX
