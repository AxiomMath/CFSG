module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCompFamFix
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryAllDimensions
public import CFSG.GroupTheory.LocalCores.Components
import CFSG.Blueprint.SourceClassicalTransport
import CFSG.CGT.PushingUpLit.Transport
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
import CFSG.Quasithin.Vol2.Ch10SecKGA318
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
import CFSG.RankThree.SteinbergR3ECALinearSplitBlocks

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open Matrix Module CFSG.GroupTheory.SteinbergBK CFSG.ComponentClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

section Gen

variable {A : GL ι K} {σ : K ≃+* K} {U : Submodule K (ι → K)}

theorem odd_card_fixedSubfield [Finite K] (hodd : Odd (Nat.card K)) (σ : K ≃+* K) :
    Odd (Nat.card (semilinearFixedSubfield σ)) := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (semilinearFixedSubfield σ) := Fintype.ofFinite _
  have h := Module.card_eq_pow_finrank (K := semilinearFixedSubfield σ) (V := K)
  rw [Nat.card_eq_fintype_card] at hodd
  rw [h] at hodd
  rw [Nat.card_eq_fintype_card]
  have hpos : finrank (semilinearFixedSubfield σ) K ≠ 0 := Module.finrank_pos.ne'
  exact (Nat.odd_pow_iff hpos).1 hodd

theorem restr_mem_fixU {τ : K →+* K} {β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[τ] K}
    {W : Submodule K (ι → K)} {x : GL ι K} (hx : x ∈ blkSub β U W)
    (hxa : x ∈ centGL {(ModelGen.semiMap A σ).toAddMonoidHom}) {y : U} (hy : y ∈ fixU A σ U) :
    (⟨glEquiv x y, hx.2.1 y y.2⟩ : U) ∈ fixU A σ U := by
  rw [mem_fixU]
  have h : glEquiv x (ModelGen.semiMap A σ y) = ModelGen.semiMap A σ (glEquiv x y) :=
    (mem_centGL.1 hxa) _ rfl (y : ι → K)
  show ModelGen.semiMap A σ (glEquiv x y) = glEquiv x y
  rw [← h, (mem_fixU A σ U).1 hy]

theorem exists_mem_isomU₀_orderOf [Finite K] {τ : K →+* K}
    {β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[τ] K} {W : Submodule K (ι → K)} (hUW : IsCompl U W)
    (horth : ∀ u ∈ U, ∀ w ∈ W, β u w = 0 ∧ β w u = 0) {p : ℕ} (hp : p.Prime)
    (hσ : orderOf σ = p) (hU : ∀ u ∈ U, ModelGen.semiMap A σ u ∈ U) {x : GL ι K}
    (hx : x ∈ blkSub β U W ⊓ centGL {(ModelGen.semiMap A σ).toAddMonoidHom}) :
    ∃ g ∈ isomU₀ U β (fixU A σ U), orderOf g = orderOf x := by
  have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
  obtain ⟨b, b₀, hb⟩ := exists_fixBasis hp.pos hσp hU hσ
  set e : U ≃ₗ[K] U := ((blkSubEquiv hUW horth ⟨x, hx.1⟩ : isomU β U) : U ≃ₗ[K] U) with he
  have heU : ∀ y : U, (e y : ι → K) = glEquiv x y := fun y => rfl
  have hxa : ∀ v, glEquiv x (ModelGen.semiMap A σ v) = ModelGen.semiMap A σ (glEquiv x v) :=
    fun v => (mem_centGL.1 hx.2) _ rfl v
  have he0 : ∀ y ∈ fixU A σ U, e y ∈ fixU A σ U := fun y hy => restr_mem_fixU hx.1 hx.2 hy
  have he0' : ∀ y ∈ fixU A σ U, e.symm y ∈ fixU A σ U := fun y hy => by
    rw [mem_fixU]
    apply (glEquiv x).injective
    rw [← heU, LinearEquiv.apply_symm_apply, hxa, ← heU, LinearEquiv.apply_symm_apply]
    exact hy
  refine ⟨resFix e he0 he0', fun y y' => ?_, ?_⟩
  · rw [coe_resFix_apply, coe_resFix_apply]
    exact (blkSubEquiv hUW horth ⟨x, hx.1⟩).2 y y'
  · rw [← orderOf_injective (extHom' b b₀ hb) (extHom'_injective b b₀ hb), extHom'_apply,
      extEquiv_resFix, he, orderOf_blkSubEquiv]

theorem forall_of_forall_fixU [Finite K] {p : ℕ} (hp : p.Prime) (hσ : orderOf σ = p)
    (hU : ∀ u ∈ U, ModelGen.semiMap A σ u ∈ U) (f : U →ₗ[K] K)
    (hf : ∀ y : fixU A σ U, f y = 0) (u : U) : f u = 0 := by
  have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
  obtain ⟨b, b₀, hb⟩ := exists_fixBasis hp.pos hσp hU hσ
  rw [← b.sum_repr u, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_smul, ← hb, hf, smul_zero]

end Gen

section Symplectic

variable {A : GL ι K} {σ : K ≃+* K} {U W : Submodule K (ι → K)}

theorem glaPLayer_inf_centGL_ne_bot_toBilin' [Finite K] (hodd : Odd (Nat.card K))
    {J : Matrix ι ι K} (hJ : ∀ x, Matrix.toBilin' J x x = 0) (hUW : IsCompl U W)
    (horth : ∀ u ∈ U, ∀ w ∈ W, Matrix.toBilin' J u w = 0 ∧ Matrix.toBilin' J w u = 0)
    (hnd : ∀ u ∈ U, (∀ u' ∈ U, Matrix.toBilin' J u u' = 0) → u = 0) {p : ℕ} (hp : p.Prime)
    (hσ : orderOf σ = p) (hU : ∀ u ∈ U, ModelGen.semiMap A σ u ∈ U)
    (hW : ∀ w ∈ W, ModelGen.semiMap A σ w ∈ W) (hform : ModelGen.FormRel (Matrix.toBilin' J) A σ)
    (hdim : 2 ≤ finrank K U)
    (hexc : finrank K U ≠ 2 ∨ Nat.card (semilinearFixedSubfield σ) ≠ 3) {x : GL ι K}
    (hx : x ∈ blkSub (Matrix.toBilin' J) U W ⊓ centGL {(ModelGen.semiMap A σ).toAddMonoidHom})
    (hxp : orderOf x = p) :
    CFSG.Open.GLAPLayer p
      (blkI (Matrix.toBilin' J) U W ⊓ centGL {(ModelGen.semiMap A σ).toAddMonoidHom}) ≠ ⊥ := by
  have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
  obtain ⟨b, b₀, hb⟩ := exists_fixBasis hp.pos hσp hU hσ
  obtain ⟨c, hc⟩ := hform
  set K₀ := semilinearFixedSubfield σ
  set U₀ := fixU A σ U
  have hval : ∀ y y' : U₀, (c : K) * Matrix.toBilin' J ((y : U) : ι → K) ((y' : U) : ι → K) ∈ K₀ :=
    fun y y' => by
      have h := hc ((y : U) : ι → K) ((y' : U) : ι → K)
      rw [(mem_fixU A σ U).1 y.2, (mem_fixU A σ U).1 y'.2] at h
      exact RingHom.mem_eqLocusField.2 h.symm
  let B₀ : LinearMap.BilinForm K₀ U₀ := LinearMap.mk₂ K₀ (fun y y' => ⟨_, hval y y'⟩)
    (fun y₁ y₂ y' => Subtype.ext (by
      simp only [Submodule.coe_add, map_add, LinearMap.add_apply, mul_add]; rfl))
    (fun k y y' => Subtype.ext (by
      simp only [Submodule.coe_smul, Subfield.smul_def, map_smul, LinearMap.smul_apply,
        smul_eq_mul]
      show (c : K) * ((k : K) * _) = (k : K) * ((c : K) * _)
      ring))
    (fun y y₁ y₂ => Subtype.ext (by
      simp only [Submodule.coe_add, map_add, mul_add]; rfl))
    (fun k y y' => Subtype.ext (by
      simp only [Submodule.coe_smul, Subfield.smul_def, map_smul, smul_eq_mul]
      show (c : K) * ((k : K) * _) = (k : K) * ((c : K) * _)
      ring))
  have hB₀ : ∀ y y' : U₀, ((B₀ y y' : K₀) : K) =
      (c : K) * Matrix.toBilin' J ((y : U) : ι → K) ((y' : U) : ι → K) := fun y y' => rfl
  have hG : isomU₀ U (Matrix.toBilin' J) U₀ = TauCeti.BilinForm.isometryGroup B₀ := by
    ext g
    rw [mem_isomU₀, TauCeti.BilinForm.mem_isometryGroup_iff]
    refine ⟨fun h y y' => Subtype.ext ?_, fun h y y' => ?_⟩
    · rw [hB₀, hB₀, h]
    · have h1 := congrArg Subtype.val (h y y')
      rw [hB₀, hB₀] at h1
      exact mul_left_cancel₀ c.ne_zero h1
  have hJ' : (Matrix.toBilin' J).IsAlt := hJ
  have hB₀alt : B₀.IsAlt := fun y => Subtype.ext (by rw [hB₀, hJ, mul_zero]; rfl)
  have hB₀nd : B₀.Nondegenerate := by
    have hleft : ∀ y : U₀, (∀ y' : U₀, B₀ y y' = 0) → y = 0 := fun y hy => by
      have h0 : ∀ y' : U₀, Matrix.toBilin' J ((y : U) : ι → K) ((y' : U) : ι → K) = 0 :=
        fun y' => by
          have h1 := congrArg Subtype.val (hy y')
          rw [hB₀] at h1
          exact (mul_eq_zero.1 h1).resolve_left c.ne_zero
      have h2 : ∀ u : U, Matrix.toBilin' J ((y : U) : ι → K) (u : ι → K) = 0 :=
        forall_of_forall_fixU hp hσ hU (((Matrix.toBilin' J) ((y : U) : ι → K)).comp U.subtype)
          h0
      exact Subtype.ext (Subtype.ext (hnd _ (y : U).2 fun u' hu' => h2 ⟨u', hu'⟩))
    refine ⟨hleft, fun y hy => hleft y fun y' => ?_⟩
    rw [← LinearMap.IsAlt.neg hB₀alt y' y, hy y', neg_zero]
  have hdim₀ : finrank K₀ U₀ = finrank K U := by
    rw [finrank_eq_card_basis b₀, Fintype.card_fin]
  haveI : FiniteDimensional K₀ U₀ := Module.Finite.of_basis b₀
  have hq := CatalogueBAlternatingIsometry.isometry_quasisimple (K := K₀) (V := U₀) B₀ hB₀alt
    hB₀nd (by rw [hdim₀]; exact hdim) (odd_card_fixedSubfield hodd σ) (by rw [hdim₀]; exact hexc)
  have hq' : CFSG.Open.IsQuasisimple ↥(isomU₀ U (Matrix.toBilin' J) U₀) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv (MulEquiv.subgroupCongr hG)
      ⟨Group.isPerfect_def.1 hq.1, hq.2.1⟩
  have heq := commutator_eq_of_perfect (Subgroup.commutator_le_self _) le_rfl hq'.1
  obtain ⟨g, hg, hgo⟩ := exists_mem_isomU₀_orderOf hUW horth hp hσ hU hx
  refine glaPLayer_ne_bot_of_fix hUW horth hp hσ hU hW (by rw [heq]; exact hq') ?_
  have h := orderOf_dvd_natCard (⟨g, by rw [heq]; exact hg⟩ : ↥⁅isomU₀ U (Matrix.toBilin' J) U₀,
    isomU₀ U (Matrix.toBilin' J) U₀⁆)
  rwa [Subgroup.orderOf_mk, hgo, hxp] at h

end Symplectic

section AbsLin

variable {F : Type} [Field F] [Finite F] {E : Type} [AddCommGroup E] [Module F E]
  [FiniteDimensional F E]

omit [Finite F] [FiniteDimensional F E] in
theorem commutator_le_ker_det' (H : Subgroup (E ≃ₗ[F] E)) :
    ⁅H, H⁆ ≤ (LinearEquiv.det : (E ≃ₗ[F] E) →* Fˣ).ker := by
  rw [Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

omit [Finite F] [FiniteDimensional F E] in
@[expose] noncomputable def slEquivKerDet' :
    SpecialLinearGroup F E ≃* (LinearEquiv.det : (E ≃ₗ[F] E) →* Fˣ).ker where
  toFun g := ⟨g.1, g.2⟩
  invFun g := ⟨g.1, g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem isQuasisimple_ker_det_of_finrank
    (hdim : 3 ≤ finrank F E ∨ (finrank F E = 2 ∧ 4 ≤ Nat.card F)) :
    CFSG.Open.IsQuasisimple (LinearEquiv.det : (E ≃ₗ[F] E) →* Fˣ).ker := by
  have hq : CFSG.IsQuasisimple (SpecialLinearGroup F E) := by
    rcases hdim with h3 | ⟨h2, h4⟩
    · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (Matrix.SpecialLinearGroup.toLin_equiv (finBasis F E))
        (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup h3)
    · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (Matrix.SpecialLinearGroup.toLin_equiv (finBasisOfFinrankEq F E h2))
        (CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le le_rfl h4)
  exact CFSG.Open.IsQuasisimple.of_mulEquiv slEquivKerDet'.symm
    ⟨Group.isPerfect_def.1 hq.1, hq.2.1⟩

theorem dvd_card_ker_det_of_orderOf (hdim : 2 ≤ finrank F E) {p : ℕ} (hp : p.Prime)
    {g : E ≃ₗ[F] E} (hg : orderOf g = p) :
    p ∣ Nat.card (LinearEquiv.det : (E ≃ₗ[F] E) →* Fˣ).ker := by
  haveI := Fact.mk hp
  by_cases hζ : LinearEquiv.det g = 1
  · have h := orderOf_dvd_natCard
      (⟨g, MonoidHom.mem_ker.2 hζ⟩ : (LinearEquiv.det : (E ≃ₗ[F] E) →* Fˣ).ker)
    rwa [Subgroup.orderOf_mk, hg] at h
  · have hζp : LinearEquiv.det g ^ p = 1 := by
      rw [← map_pow, ← hg, pow_orderOf_eq_one, map_one]
    have hord : orderOf (LinearEquiv.det g) = p := orderOf_eq_prime hζp hζ
    let b := finBasis F E
    let i₀ : Fin (finrank F E) := ⟨0, by omega⟩
    let i₁ : Fin (finrank F E) := ⟨1, by omega⟩
    have hi : i₀ ≠ i₁ := Fin.ne_of_val_ne zero_ne_one
    let e := CatalogueBAlternatingIsometry.basisMatrixEquiv b
    have ht : e.symm (torHom i₀ i₁ (LinearEquiv.det g)) ∈
        (LinearEquiv.det : (E ≃ₗ[F] E) →* Fˣ).ker := by
      rw [MonoidHom.mem_ker]
      apply Units.ext
      rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix b,
        ← CatalogueBAlternatingIsometry.basisMatrixEquiv_val, MulEquiv.apply_symm_apply,
        det_torHom, Units.val_one]
    have h := orderOf_dvd_natCard (⟨_, ht⟩ : (LinearEquiv.det : (E ≃ₗ[F] E) →* Fˣ).ker)
    rwa [Subgroup.orderOf_mk, MulEquiv.orderOf_eq, orderOf_torHom hi hp hord] at h

end AbsLin

section Linear

variable {A : GL ι K} {σ : K ≃+* K} {U W : Submodule K (ι → K)}

theorem glaPLayer_inf_centGL_ne_bot_zero [Finite K] {σ₀ : K →+* K} (hUW : IsCompl U W) {p : ℕ}
    (hp : p.Prime) (hσ : orderOf σ = p) (hU : ∀ u ∈ U, ModelGen.semiMap A σ u ∈ U)
    (hW : ∀ w ∈ W, ModelGen.semiMap A σ w ∈ W)
    (hdim : 3 ≤ finrank K U ∨ (finrank K U = 2 ∧ 4 ≤ Nat.card (semilinearFixedSubfield σ)))
    {x : GL ι K}
    (hx : x ∈ blkSub (0 : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ₀] K) U W ⊓
      centGL {(ModelGen.semiMap A σ).toAddMonoidHom}) (hxp : orderOf x = p) :
    CFSG.Open.GLAPLayer p (blkI (0 : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ₀] K) U W ⊓
      centGL {(ModelGen.semiMap A σ).toAddMonoidHom}) ≠ ⊥ := by
  have horth : ∀ u ∈ U, ∀ w ∈ W, (0 : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ₀] K) u w = 0 ∧
      (0 : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ₀] K) w u = 0 := fun _ _ _ _ => ⟨rfl, rfl⟩
  have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
  obtain ⟨b, b₀, hb⟩ := exists_fixBasis hp.pos hσp hU hσ
  haveI : FiniteDimensional (semilinearFixedSubfield σ) (fixU A σ U) := Module.Finite.of_basis b₀
  have hdim₀ : finrank (semilinearFixedSubfield σ) (fixU A σ U) = finrank K U := by
    rw [finrank_eq_card_basis b₀, Fintype.card_fin]
  have hG : isomU₀ U (0 : (ι → K) →ₗ[K] (ι → K) →ₛₗ[σ₀] K) (fixU A σ U) = ⊤ :=
    eq_top_iff.2 fun _ _ _ _ => rfl
  have hq := isQuasisimple_ker_det_of_finrank (F := semilinearFixedSubfield σ)
    (E := fixU A σ U) (by rw [hdim₀]; exact hdim)
  have h1 := commutator_le_ker_det' (F := semilinearFixedSubfield σ) (E := fixU A σ U) ⊤
  have heq := commutator_eq_of_perfect h1 le_top hq.1
  obtain ⟨g, -, hgo⟩ := exists_mem_isomU₀_orderOf hUW horth hp hσ hU hx
  have hdvd := dvd_card_ker_det_of_orderOf (F := semilinearFixedSubfield σ) (E := fixU A σ U)
    (by rw [hdim₀]; omega) hp (hgo.trans hxp)
  refine glaPLayer_ne_bot_of_fix hUW horth hp hσ hU hW (by rw [hG, heq]; exact hq) ?_
  rw [hG, heq]
  exact hdvd

end Linear

section AbsUni

variable {F : Type} [Field F] {E : Type} [AddCommGroup E] [Module F E]

private theorem det_conjTr' (τ : F ≃+* F) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    (CFSG.LieType.Universal.Unitary.conjTr τ M).det = τ M.det := by
  rw [CFSG.LieType.Universal.Unitary.conjTr, Matrix.det_transpose, RingEquiv.map_det]
  rfl

private theorem torHom_mem_Uid' (τ : F ≃+* F) {n : ℕ} (i j : Fin n) {ζ : Fˣ}
    (hζ : τ (ζ : F) * ζ = 1) : torHom i j ζ ∈ CatalogueBUnitaryIsometry.Uid τ n := by
  have h1 : ∀ u : Fˣ, τ (u : F) * u = 1 → ∀ (l k : Fin n),
      τ ((Pi.mulSingle l u : Fin n → Fˣ) k : F) * ((Pi.mulSingle l u : Fin n → Fˣ) k : F) = 1 := by
    intro u hu l k
    by_cases hk : k = l
    · subst hk
      simpa using hu
    · simp [Pi.mulSingle_eq_of_ne hk]
  have hinv : τ ((ζ⁻¹ : Fˣ) : F) * ((ζ⁻¹ : Fˣ) : F) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv, hζ, inv_one]
  rw [CatalogueBUnitaryIsometry.mem_Uid_iff, torHom_val, CFSG.LieType.Universal.Unitary.conjTr,
    Matrix.diagonal_map (map_zero τ), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext k
  simp only [Units.val_mul, map_mul]
  rw [mul_mul_mul_comm, h1 ζ hζ i k, h1 ζ⁻¹ hinv j k, one_mul]

private theorem map_isometryGroup_eq {r f : ℕ} [Fact r.Prime] [Finite F]
    (hE : Nat.card F = (r ^ f) ^ 2)
    (h : E →ₛₗ[(CatalogueBUnitaryTwo.unitaryFieldConjugation r f hE).toRingHom] E →ₗ[F] F) :
    (CatalogueBUnitaryIsometry.specialIsometry h).map
        (CatalogueBUnitaryIsometry.isometryGroup h).subtype =
      CatalogueBUnitaryIsometry.isometryGroup h ⊓ (LinearEquiv.det : (E ≃ₗ[F] E) →* Fˣ).ker := by
  ext g
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s.2, hs⟩
  · rintro ⟨hg, hdet⟩
    exact ⟨⟨g, hg⟩, hdet, rfl⟩

private theorem isQuasisimple_isometry_inf_ker_det [Finite F] [FiniteDimensional F E] {r f : ℕ}
    [Fact r.Prime] (hE : Nat.card F = (r ^ f) ^ 2)
    (h : E →ₛₗ[(CatalogueBUnitaryTwo.unitaryFieldConjugation r f hE).toRingHom] E →ₗ[F] F)
    (hr : r ≠ 2) (hf : 1 ≤ f) (hsym : h.IsSymm)
    (hnd : h.Nondegenerate) (hdim : 3 ≤ finrank F E ∨ (finrank F E = 2 ∧ r ^ f ≠ 3)) :
    CFSG.Open.IsQuasisimple ↥(CatalogueBUnitaryIsometry.isometryGroup h ⊓
      (LinearEquiv.det : (E ≃ₗ[F] E) →* Fˣ).ker) := by
  have hnq : (finrank F E, r ^ f) ≠ (2, 3) := by
    intro he
    have h1 : finrank F E = 2 := congrArg Prod.fst he
    have h2 : r ^ f = 3 := congrArg Prod.snd he
    rcases hdim with h3 | ⟨-, h3⟩
    · omega
    · exact h3 h2
  obtain ⟨-, -, hcase⟩ := CatalogueBUnitaryTwo.odd_unitary_all_dimensional_isometry_p_components
    r f hr hf hE h hsym hnd (by omega)
  have hq := (hcase ⟨by omega, hnq⟩).1
  exact CFSG.Open.IsQuasisimple.of_mulEquiv ((MulEquiv.subgroupCongr
    (map_isometryGroup_eq hE h).symm).trans
    (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).symm)
    ⟨Group.isPerfect_def.1 hq.1, hq.2.1⟩

private theorem dvd_card_isometry_inf_ker_det [Finite F] [FiniteDimensional F E] {r f : ℕ}
    [Fact r.Prime] (hE : Nat.card F = (r ^ f) ^ 2)
    (h : E →ₛₗ[(CatalogueBUnitaryTwo.unitaryFieldConjugation r f hE).toRingHom] E →ₗ[F] F)
    (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hdim : 2 ≤ finrank F E) {p : ℕ} (hp : p.Prime) {g : E ≃ₗ[F] E}
    (hg : g ∈ CatalogueBUnitaryIsometry.isometryGroup h) (hgp : orderOf g = p) :
    p ∣ Nat.card ↥(CatalogueBUnitaryIsometry.isometryGroup h ⊓
      (LinearEquiv.det : (E ≃ₗ[F] E) →* Fˣ).ker) := by
  haveI := Fact.mk hp
  by_cases hζ : LinearEquiv.det g = 1
  · have h1 := orderOf_dvd_natCard (⟨g, Subgroup.mem_inf.2 ⟨hg, MonoidHom.mem_ker.2 hζ⟩⟩ :
      ↥(CatalogueBUnitaryIsometry.isometryGroup h ⊓ (LinearEquiv.det : (E ≃ₗ[F] E) →* Fˣ).ker))
    rwa [Subgroup.orderOf_mk, hgp] at h1
  have hζp : LinearEquiv.det g ^ p = 1 := by
    rw [← map_pow, ← hgp, pow_orderOf_eq_one, map_one]
  have hord : orderOf (LinearEquiv.det g) = p := orderOf_eq_prime hζp hζ
  obtain ⟨hsigma, hne, -⟩ := CatalogueBUnitaryTwo.unitaryFieldConjugation_data r f hE
  obtain ⟨b, hb⟩ := CatalogueBHermitian.exists_orthonormal_basis h hsym hnd hsigma hne
  let e := CatalogueBAlternatingIsometry.basisMatrixEquiv b
  have hyU : e g ∈ CatalogueBUnitaryIsometry.Uid
      (CatalogueBUnitaryTwo.unitaryFieldConjugation r f hE) (finrank F E) :=
    (CatalogueBUnitaryIsometry.isometry_iff_Uid h b hb g).1 hg
  have hnorm : CatalogueBUnitaryTwo.unitaryFieldConjugation r f hE (LinearEquiv.det g : F) *
      (LinearEquiv.det g : F) = 1 := by
    have h1 := congrArg Matrix.det ((CatalogueBUnitaryIsometry.mem_Uid_iff _ _ _).1 hyU)
    rw [Matrix.det_mul, det_conjTr', Matrix.det_one,
      CatalogueBAlternatingIsometry.basisMatrixEquiv_val, LinearMap.det_toMatrix,
      ← LinearEquiv.coe_det] at h1
    exact h1
  let i₀ : Fin (finrank F E) := ⟨0, by omega⟩
  let i₁ : Fin (finrank F E) := ⟨1, by omega⟩
  have hi : i₀ ≠ i₁ := Fin.ne_of_val_ne zero_ne_one
  have htH : e.symm (torHom i₀ i₁ (LinearEquiv.det g)) ∈
      CatalogueBUnitaryIsometry.isometryGroup h := by
    rw [CatalogueBUnitaryIsometry.isometry_iff_Uid h b hb, MulEquiv.apply_symm_apply]
    exact torHom_mem_Uid' _ i₀ i₁ hnorm
  have htdet : e.symm (torHom i₀ i₁ (LinearEquiv.det g)) ∈
      (LinearEquiv.det : (E ≃ₗ[F] E) →* Fˣ).ker := by
    rw [MonoidHom.mem_ker]
    apply Units.ext
    rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix b,
      ← CatalogueBAlternatingIsometry.basisMatrixEquiv_val, MulEquiv.apply_symm_apply,
      det_torHom, Units.val_one]
  have h1 := orderOf_dvd_natCard (⟨_, Subgroup.mem_inf.2 ⟨htH, htdet⟩⟩ :
    ↥(CatalogueBUnitaryIsometry.isometryGroup h ⊓ (LinearEquiv.det : (E ≃ₗ[F] E) →* Fˣ).ker))
  rwa [Subgroup.orderOf_mk, MulEquiv.orderOf_eq, orderOf_torHom hi hp hord] at h1

end AbsUni



section Unitary

variable {A : GL ι K} {σ : K ≃+* K} {U W : Submodule K (ι → K)}

theorem unitary_card_fixedSubfield {r f : ℕ}
    (hK : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData r f K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hσ : orderOf σ = p) (hU : ∀ u ∈ U, ModelGen.semiMap A σ u ∈ U) :
    p ∣ f ∧ Nat.card (semilinearFixedSubfield σ) = (r ^ (f / p)) ^ 2 := by
  haveI : Finite K := hK.finite
  have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
  obtain ⟨hdvd, hcard, -⟩ := coprime_finite_field_semilinear_fixed_basis hK.prime
    (by have := hK.one_le; omega : 1 ≤ 2 * f) hK.card σ hσ rfl (semiU A σ hp.pos hσp U hU)
    (semiU_smul hp.pos hσp hU) fun v => Subtype.ext (by
      rw [coe_semiU_iterate, ModelGen.semiMap_iterate_eq_self A hσp])
  have hpf : p ∣ f := by
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h2 | h2
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2) hp2
    · exact h2
  refine ⟨hpf, ?_⟩
  rw [hcard, ← pow_mul]
  congr 1
  obtain ⟨f₀, rfl⟩ := hpf
  rw [Nat.mul_div_cancel_left _ hp.pos, mul_comm 2 (p * f₀), Nat.mul_assoc,
    Nat.mul_div_cancel_left _ hp.pos, mul_comm]

theorem glaPLayer_inf_centGL_ne_bot_unitForm {r f : ℕ}
    (hK : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData r f K) (hr : r ≠ 2)
    (hUW : IsCompl U W)
    (horth : ∀ u ∈ U, ∀ w ∈ W, unitForm hK.bar u w = 0 ∧ unitForm hK.bar w u = 0)
    (hnd : ∀ u ∈ U, (∀ u' ∈ U, unitForm hK.bar u u' = 0) → u = 0) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hσ : orderOf σ = p) (hU : ∀ u ∈ U, ModelGen.semiMap A σ u ∈ U)
    (hW : ∀ w ∈ W, ModelGen.semiMap A σ w ∈ W)
    (hform : ∀ u v, unitForm hK.bar (ModelGen.semiMap A σ u) (ModelGen.semiMap A σ v) =
      σ (unitForm hK.bar u v))
    (hdim : 3 ≤ finrank K U ∨ (finrank K U = 2 ∧ r ^ (f / p) ≠ 3)) {x : GL ι K}
    (hx : x ∈ blkSub (unitForm hK.bar) U W ⊓ centGL {(ModelGen.semiMap A σ).toAddMonoidHom})
    (hxp : orderOf x = p) :
    CFSG.Open.GLAPLayer p
      (blkI (unitForm hK.bar) U W ⊓ centGL {(ModelGen.semiMap A σ).toAddMonoidHom}) ≠ ⊥ := by
  haveI : Fact r.Prime := ⟨hK.prime⟩
  haveI : Finite K := hK.finite
  have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
  obtain ⟨hpf, hE₀⟩ := unitary_card_fixedSubfield hK hp hp2 hσ hU
  obtain ⟨b, b₀, hb⟩ := exists_fixBasis hp.pos hσp hU hσ
  have hf₀ : 1 ≤ f / p := by
    obtain ⟨f₀, hf₀⟩ := hpf
    have h1 := hK.one_le
    rw [hf₀, Nat.mul_div_cancel_left _ hp.pos]
    rcases Nat.eq_zero_or_pos f₀ with h0 | h0
    · rw [h0, mul_zero] at hf₀
      omega
    · exact h0
  let conj₀ := CatalogueBUnitaryTwo.unitaryFieldConjugation r (f / p) hE₀
  have hcompat : ∀ k : semilinearFixedSubfield σ,
      ((conj₀ k : semilinearFixedSubfield σ) : K) = hK.bar k := by
    intro k
    haveI : Fintype (semilinearFixedSubfield σ) := Fintype.ofFinite _
    obtain ⟨j, hj⟩ := hp.odd_of_ne_two hp2
    have hk2 : k ^ (((r ^ (f / p)) ^ 2) ^ j) = k := by
      have h := FiniteField.pow_card_pow j k
      rwa [Fintype.card_eq_nat_card, hE₀] at h
    have hk2' : (k : K) ^ (((r ^ (f / p)) ^ 2) ^ j) = k := by
      rw [← SubmonoidClass.coe_pow, hk2]
    have hf : f = f / p * p := (Nat.div_mul_cancel hpf).symm
    rw [CatalogueBUnitaryTwo.unitaryFieldConjugation_apply, SubmonoidClass.coe_pow,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply,
      show r ^ f = ((r ^ (f / p)) ^ 2) ^ j * r ^ (f / p) by
        rw [← pow_mul, ← pow_mul, ← pow_add]
        congr 1
        nth_rewrite 1 [hf]
        rw [hj]
        ring,
      pow_mul, hk2']
  have hval : ∀ y y' : fixU A σ U,
      unitForm hK.bar ((y' : U) : ι → K) ((y : U) : ι → K) ∈ semilinearFixedSubfield σ :=
    fun y y' => by
      have h := hform ((y' : U) : ι → K) ((y : U) : ι → K)
      rw [(mem_fixU A σ U).1 y'.2, (mem_fixU A σ U).1 y.2] at h
      exact RingHom.mem_eqLocusField.2 h.symm
  let h₀ : fixU A σ U →ₛₗ[conj₀.toRingHom] fixU A σ U →ₗ[semilinearFixedSubfield σ]
      semilinearFixedSubfield σ :=
    LinearMap.mk₂'ₛₗ conj₀.toRingHom (RingHom.id _) (fun y y' => ⟨_, hval y y'⟩)
      (fun y₁ y₂ y' => Subtype.ext (by
        simp only [Submodule.coe_add, map_add]; rfl))
      (fun c y y' => Subtype.ext (by
        simp only [Submodule.coe_smul, Subfield.smul_def, map_smulₛₗ, smul_eq_mul]
        show hK.bar (c : K) * _ = ((conj₀ c : semilinearFixedSubfield σ) : K) * _
        rw [hcompat]))
      (fun y y₁ y₂ => Subtype.ext (by
        simp only [Submodule.coe_add, map_add, LinearMap.add_apply]; rfl))
      (fun c y y' => Subtype.ext (by
        simp only [Submodule.coe_smul, Subfield.smul_def, map_smul, LinearMap.smul_apply,
          smul_eq_mul]
        rfl))
  have hh₀ : ∀ y y' : fixU A σ U, ((h₀ y y' : semilinearFixedSubfield σ) : K) =
      unitForm hK.bar ((y' : U) : ι → K) ((y : U) : ι → K) := fun _ _ => rfl
  have hsym₀ : h₀.IsSymm := ⟨fun y y' => Subtype.ext (by
    show ((conj₀ (h₀ y y') : semilinearFixedSubfield σ) : K) = _
    rw [hcompat, hh₀, hh₀, unitForm_swap hK.bar_bar])⟩
  have hspan : ∀ z : U, (∀ y : fixU A σ U, unitForm hK.bar ((y : U) : ι → K) (z : ι → K) = 0) →
      z = 0 := fun z hz => by
    have h1 : ∀ u : U, unitForm hK.bar (u : ι → K) (z : ι → K) = 0 :=
      forall_of_forall_fixU hp hσ hU (((unitForm hK.bar).flip (z : ι → K)).comp U.subtype) hz
    exact Subtype.ext (hnd _ z.2 fun u' hu' => by
      rw [← unitForm_swap hK.bar_bar, h1 ⟨u', hu'⟩, map_zero])
  have hnd₀ : h₀.Nondegenerate := by
    refine ⟨fun y hy => Subtype.ext (hspan _ fun y' => ?_), fun y' hy' => Subtype.ext
      (hspan _ fun y => ?_)⟩
    · have h1 := congrArg Subtype.val (hy y')
      rw [hh₀, ZeroMemClass.coe_zero] at h1
      exact h1
    · have h1 := congrArg Subtype.val (hy' y)
      rw [hh₀, ZeroMemClass.coe_zero] at h1
      rw [← unitForm_swap hK.bar_bar, h1, map_zero]
  have hG : isomU₀ U (unitForm hK.bar) (fixU A σ U) =
      CatalogueBUnitaryIsometry.isometryGroup (K := semilinearFixedSubfield σ) (V := fixU A σ U)
        h₀ := by
    ext g
    rw [mem_isomU₀, CatalogueBUnitaryIsometry.mem_isometryGroup_iff]
    refine ⟨fun hg y y' => Subtype.ext ((hh₀ _ _).trans ((hg y' y).trans (hh₀ y y').symm)),
      fun hg y y' => ?_⟩
    have h1 := congrArg Subtype.val (hg y' y)
    rw [hh₀, hh₀] at h1
    exact h1
  haveI : FiniteDimensional (semilinearFixedSubfield σ) (fixU A σ U) := Module.Finite.of_basis b₀
  have hdim₀ : finrank (semilinearFixedSubfield σ) (fixU A σ U) = finrank K U := by
    rw [finrank_eq_card_basis b₀, Fintype.card_fin]
  have hq := isQuasisimple_isometry_inf_ker_det (F := semilinearFixedSubfield σ)
    (E := fixU A σ U) hE₀ h₀ hr hf₀ hsym₀ hnd₀ (by rw [hdim₀]; exact hdim)
  have hle := commutator_le_ker_det' (F := semilinearFixedSubfield σ) (E := fixU A σ U)
    (CatalogueBUnitaryIsometry.isometryGroup (K := semilinearFixedSubfield σ) (V := fixU A σ U) h₀)
  have heq := commutator_eq_of_perfect (le_inf (Subgroup.commutator_le_self _) hle)
    inf_le_left hq.1
  obtain ⟨g, hg, hgo⟩ := exists_mem_isomU₀_orderOf hUW horth hp hσ hU hx
  have hdvd := dvd_card_isometry_inf_ker_det (F := semilinearFixedSubfield σ)
    (E := fixU A σ U) hE₀ h₀ hsym₀ hnd₀ (by rw [hdim₀]; omega) hp
    (by rw [← hG]; exact hg) (hgo.trans hxp)
  refine glaPLayer_ne_bot_of_fix hUW horth hp hσ hU hW (by rw [hG, heq]; exact hq) ?_
  rw [hG, heq]
  exact hdvd

end Unitary

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls

end
