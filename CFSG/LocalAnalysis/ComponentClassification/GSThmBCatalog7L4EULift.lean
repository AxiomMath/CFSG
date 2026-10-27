module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4NoPSpUGraph
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBHyperbolic
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthLift
public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotOddUnitary
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7L4EU

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.CatalogueBUnitaryB CFSG.LinearGroups
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatFactsL4U4.UnitaryOut (uStar uStar_mul uStar_one)
open scoped commutatorElement

section Group

variable {S P : Type*} [Group S] [Group P]

theorem le_ker_of_perfect {M : Type*} [CommGroup M] (χ : S →* M) {Y : Subgroup S}
    (hY : ⁅Y, Y⁆ = Y) : Y ≤ χ.ker := by
  rw [← hY, Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

theorem commutatorElement_mul_central_left {a c z : S} (hz : z ∈ center S) :
    ⁅a * z, c⁆ = ⁅a, c⁆ := by
  have hz' := mem_center_iff.mp hz
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * c * (a * z)⁻¹ * c⁻¹ = a * (z * c) * z⁻¹ * a⁻¹ * c⁻¹ := by group
    _ = a * (c * z) * z⁻¹ * a⁻¹ * c⁻¹ := by rw [← hz' c]
    _ = a * c * a⁻¹ * c⁻¹ := by group

theorem commutatorElement_mul_central_right {a c w : S} (hw : w ∈ center S) :
    ⁅a, c * w⁆ = ⁅a, c⁆ := by
  have hw' := mem_center_iff.mp hw
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (c * w) * a⁻¹ * (c * w)⁻¹ = a * c * (w * a⁻¹) * w⁻¹ * c⁻¹ := by group
    _ = a * c * (a⁻¹ * w) * w⁻¹ * c⁻¹ := by rw [← hw' a⁻¹]
    _ = a * c * a⁻¹ * c⁻¹ := by group

theorem commutatorElement_mul_central {a b z w : S} (hz : z ∈ center S) (hw : w ∈ center S) :
    ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_central_left hz, commutatorElement_mul_central_right hw]

theorem commutator_comap_perfect (θ : S →* P) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ center S) {X : Subgroup P} (hX : ⁅X, X⁆ = X) :
    ⁅⁅X.comap θ, X.comap θ⁆, ⁅X.comap θ, X.comap θ⁆⁆ = ⁅X.comap θ, X.comap θ⁆ ∧
      ⁅X.comap θ, X.comap θ⁆.map θ = X := by
  set C := X.comap θ with hC
  have hCmap : C.map θ = X := Subgroup.map_comap_eq_self_of_surjective hθ X
  have hYmap : ⁅C, C⁆.map θ = X := by rw [Subgroup.map_commutator, hCmap, hX]
  refine ⟨le_antisymm (Subgroup.commutator_le_self _) ?_, hYmap⟩
  have hdec : ∀ c ∈ C, ∃ y ∈ ⁅C, C⁆, ∃ z ∈ center S, c = y * z := by
    intro c hc
    have hθc : θ c ∈ ⁅C, C⁆.map θ := by rw [hYmap]; exact hc
    obtain ⟨y, hy, hyc⟩ := hθc
    refine ⟨y, hy, y⁻¹ * c, hker ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyc, inv_mul_cancel]
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨y₁, hy₁, z₁, hz₁, rfl⟩ := hdec a ha
  obtain ⟨y₂, hy₂, z₂, hz₂, rfl⟩ := hdec b hb
  rw [commutatorElement_mul_central hz₁ hz₂]
  exact Subgroup.commutator_mem_commutator hy₁ hy₂

theorem eq_of_mem_commutator_comap (θ : S →* P) (hker : θ.ker ≤ center S) {X : Subgroup P}
    (ψ : S →* S) (hψ : ∀ g ∈ X.comap θ, θ (ψ g) = θ g) :
    ∀ g ∈ ⁅X.comap θ, X.comap θ⁆, ψ g = g := by
  have hle : ⁅X.comap θ, X.comap θ⁆ ≤ ψ.eqLocus (MonoidHom.id S) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hza : a⁻¹ * ψ a ∈ center S := hker (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hψ a ha, inv_mul_cancel])
    have hzb : b⁻¹ * ψ b ∈ center S := hker (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hψ b hb, inv_mul_cancel])
    change ψ ⁅a, b⁆ = ⁅a, b⁆
    rw [map_commutatorElement, show ψ a = a * (a⁻¹ * ψ a) by group,
      show ψ b = b * (b⁻¹ * ψ b) by group, commutatorElement_mul_central hza hzb]
  exact fun g hg => hle hg

theorem isComponentOf_map_of_intertwine {D : Type*} [Group D] (ι : P →* D)
    (hι : Function.Injective ι) (hιn : ι.range.Normal) {β : MulAut P} {βD : MulAut D}
    (he : ∀ y, ι (β y) = βD (ι y)) {X : Subgroup P}
    (hX : CFSG.Assembly.IsComponentOf X (fixedSubgroup β)) :
    CFSG.Assembly.IsComponentOf (X.map ι) (fixedSubgroup βD) := by
  have hmap : (fixedSubgroup β).map ι = ι.range ⊓ fixedSubgroup βD := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨⟨y, rfl⟩, ?_⟩
      change βD (ι y) = ι y
      rw [← he]
      exact congrArg ι hy
    · rintro ⟨⟨y, rfl⟩, hzψ⟩
      refine ⟨y, ?_, rfl⟩
      change β y = y
      apply hι
      rw [he]
      exact hzψ
  have h1 := SymmetricLocal.isComponentOf_map_of_injective ι hι hX
  rw [hmap] at h1
  refine OddClassSelector.isComponentOf_of_normal_le h1 inf_le_right ?_
  constructor
  intro m hm g
  rw [Subgroup.mem_subgroupOf] at hm ⊢
  exact ⟨hιn.conj_mem _ hm.1 (g : D),
    Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2 hm.2) (Subgroup.inv_mem _ g.2)⟩

theorem comap_conj_map_eq {H : Type*} [Group H] {W : Subgroup H} (φ : W ≃* P)
    {ρ : H →* MulAut P} (hρW : ∀ w : W, ρ w = MulAut.conj (φ w))
    (hcj : Function.Injective (MulAut.conj : P →* MulAut P)) {X : Subgroup H} (hXW : X ≤ W) :
    (X.map ρ).comap MulAut.conj = (X.subgroupOf W).map φ.toMonoidHom := by
  ext y
  constructor
  · rintro ⟨z, hz, hzy⟩
    refine ⟨⟨z, hXW hz⟩, mem_subgroupOf.mpr hz, ?_⟩
    apply hcj
    rw [← hzy, MulEquiv.coe_toMonoidHom, ← hρW]
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, mem_subgroupOf.mp hw, hρW w⟩

end Group

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem mem_range_toSesqUnitary {y : sesqUnitaryGroup (stdHermForm h 4)}
    (hy : LinearMap.det (unitaryOp y) = 1) :
    y ∈ (EscapingNotOddUnitary.toSesqUnitary h 4).range := by
  set M : GL (Fin 4) K :=
    Matrix.GeneralLinearGroup.toLin.symm (y : LinearMap.GeneralLinearGroup K (Fin 4 → K))
    with hMdef
  have hM : Matrix.GeneralLinearGroup.toLin M = (y : LinearMap.GeneralLinearGroup K (Fin 4 → K)) :=
    MulEquiv.apply_symm_apply _ _
  have hMv : ∀ x, (M : Matrix (Fin 4) (Fin 4) K).mulVec x =
      ((y : LinearMap.GeneralLinearGroup K (Fin 4 → K)) : (Fin 4 → K) →ₗ[K] Fin 4 → K) x :=
    fun x => by
      rw [← hM]
      rfl
  have hdet : (M : Matrix (Fin 4) (Fin 4) K).det = 1 := by
    rw [← LinearMap.det_toLin', Matrix.toLin'_apply']
    have hMl : (M : Matrix (Fin 4) (Fin 4) K).mulVecLin =
        ((y : LinearMap.GeneralLinearGroup K (Fin 4 → K)) : (Fin 4 → K) →ₗ[K] Fin 4 → K) :=
      LinearMap.ext hMv
    rw [hMl]
    exact hy
  have hMmem : M ∈ unitarySU p f K 4 := by
    rw [mem_unitarySU_iff_isometry h]
    refine ⟨hdet, fun x z => ?_⟩
    rw [hMv, hMv]
    exact y.2 x z
  exact ⟨⟨M, hMmem⟩, Subtype.ext hM⟩

theorem le_range_toSesqUnitary {Y : Subgroup (sesqUnitaryGroup (stdHermForm h 4))}
    (hY : ⁅Y, Y⁆ = Y) : Y ≤ (EscapingNotOddUnitary.toSesqUnitary h 4).range := by
  let χ : sesqUnitaryGroup (stdHermForm h 4) →* Kˣ :=
    (LinearMap.det.comp ((Units.coeHom _).comp
      (sesqUnitaryGroup (stdHermForm h 4)).subtype)).toHomUnits
  intro y hy
  apply mem_range_toSesqUnitary h
  have h1 := le_ker_of_perfect χ hY hy
  rw [MonoidHom.mem_ker] at h1
  have h2 := congrArg Units.val h1
  simpa [χ] using h2

theorem toSesqUnitary_antiConj {A : GL (Fin 4) K}
    (hAu : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1)
    (g g' : unitarySU p f K 4)
    (hg' : ((g' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (A : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar *
        (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)) :
    antiConj h (antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K))
        (CatFactsL4U4.StabU.antiunitaryMap_bijective h A)
        (CatFactsL4U4.StabU.stdHermForm_antiunitaryMap h hAu)
        (EscapingNotOddUnitary.toSesqUnitary h 4 g) =
      EscapingNotOddUnitary.toSesqUnitary h 4 g' := by
  have hτ := CatFactsL4U4.StabU.antiunitaryMap_bijective h A
  have hAi : (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine Subtype.ext (Units.ext (LinearMap.ext fun v => ?_))
  obtain ⟨w, rfl⟩ := hτ.2 v
  have h1 := unitaryOp_antiConj_apply h _ hτ (CatFactsL4U4.StabU.stdHermForm_antiunitaryMap h hAu)
    (EscapingNotOddUnitary.toSesqUnitary h 4 g) w
  refine h1.trans ?_
  change antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K)
      (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ w) =
    ((g' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ
      antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K) w
  rw [antiunitaryMap_apply, antiunitaryMap_apply, hg', CatFactsL4U4.StabU.bar_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hAi,
    Matrix.mul_one]

end Catalog7L4EU

end CFSG.ComponentClassification.GSThmB
