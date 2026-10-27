module

public import CFSG.HardMathSupport.Dickson.Bal207.D4Semilin
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge
public import CFSG.RankThree.PartOne.S11d.OrthModels

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.OrthFix

open Polynomial Module QuadraticMap CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.RankThree.PartOne.KCOrthogonalAut

section Pair

variable {F : Type} [Field F] {d : ℕ}

theorem exists_pair_of_semilin (σ : F ≃+* F) (s : (Fin d → F) ≃+ (Fin d → F))
    (hs : ∀ (c : F) (v : Fin d → F), s (c • v) = σ c • s v) :
    ∃ g : coordinateSemilinearGroup d F, g.right = σ ∧
      ∀ v, coordinateSemilinearMap g v = s v := by
  let L : (Fin d → F) ≃ₗ[F] (Fin d → F) :=
    ((coordinateFieldMap d σ).symm.trans s).toLinearEquiv fun c v => by
      show s ((coordinateFieldMap d σ).symm (c • v)) = c • s ((coordinateFieldMap d σ).symm v)
      have h1 : (coordinateFieldMap d σ).symm (c • v) =
          σ.symm c • (coordinateFieldMap d σ).symm v := by
        funext i
        exact σ.symm.map_mul c (v i)
      rw [h1, hs, RingEquiv.apply_symm_apply]
  refine ⟨⟨(matrixLinearIso (d := d) (K := F)).symm L, σ⟩, rfl, fun v => ?_⟩
  rw [coordinateSemilinearMap_apply]
  change matrixLinearIso ((matrixLinearIso (d := d) (K := F)).symm L) (fun i => σ (v i)) = s v
  rw [MulEquiv.apply_symm_apply]
  change s ((coordinateFieldMap d σ).symm (fun i => σ (v i))) = s v
  congr 1
  funext i
  exact σ.symm_apply_apply (v i)

end Pair

theorem semilinD4EightAut_of_mem_image {S : Type} [Group S] {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 8) (Ψ : S ≃* matrixProjectiveDerived (coordinateQuadPlus 4 F))
    {φ : MulAut S} (h : MulAut.congr Ψ φ ∈ matrixProjectiveImage (coordinateQuadPlus 4 F)) :
    SemilinD4EightAut S φ := by
  let R₀ : _ ≃* matrixProjectiveDerived (coordinateQuadPlus 4 F) :=
    coordinatePlusWitnessEquiv F (MulEquiv.refl _)
  refine ⟨F, inferInstance, inferInstance, Ψ.trans R₀.symm, hF, ?_⟩
  have hc : coordinatePlusWitnessEquiv F (Ψ.trans R₀.symm) = Ψ :=
    MulEquiv.ext fun s => R₀.apply_symm_apply (Ψ s)
  rw [hc]
  exact h

section Fixed

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {x : V ≃ₗ[F] V}

@[expose] noncomputable def fixRho [Nontrivial V] (hQ : (polarBilin Q).Nondegenerate) {p : ℕ}
    (hx : OddOrderIsometry Q p x) :
    ↥(supportedFixedDerived Q x) ≃* ↥(fixedComponentImage Q x) :=
  MulEquiv.ofBijective
    (((piOrth Q).comp (Subgroup.inclusion hx.supportedFixedDerived_le_orthDerived)).codRestrict
      (fixedComponentImage Q x) fun g =>
        ⟨⟨g, hx.supportedFixedDerived_le_orthDerived g.2⟩, g.2, rfl⟩)
    ⟨fun g h hgh => Subgroup.inclusion_injective _
        (piOrth_injective hQ (congrArg Subtype.val hgh)),
      fun y => by
        obtain ⟨k, hk, hky⟩ := y.2
        exact ⟨⟨k, hk⟩, Subtype.ext hky⟩⟩

theorem coe_fixRho [Nontrivial V] (hQ : (polarBilin Q).Nondegenerate) {p : ℕ}
    (hx : OddOrderIsometry Q p x) (g : ↥(supportedFixedDerived Q x)) :
    (fixRho hQ hx g : ProjOrthDerived Q) =
      piOrth Q ⟨g, hx.supportedFixedDerived_le_orthDerived g.2⟩ := rfl

@[expose] noncomputable def fixRestr {p : ℕ} (hx : OddOrderIsometry Q p x) :
    ↥(supportedFixedDerived Q x) ≃* ↥(orthDerived (Q.comp (fixedSpace x).subtype)) :=
  MulEquiv.ofBijective
    (((restrictFixed Q x).comp
      (Subgroup.inclusion supportedFixedDerived_le_supportedBlock)).codRestrict _ fun g => by
        obtain ⟨_, h⟩ := mem_supportedFixedDerived.mp g.2
        exact h)
    ⟨fun g h hgh => Subgroup.inclusion_injective _
        (restrictFixed_injective hx (congrArg Subtype.val hgh)),
      fun h => by
        obtain ⟨f, hf⟩ := restrictFixed_surjective hx h.1
          (KCOrthogonal.orthDerived_le_orthogonalGroup h.2)
        exact ⟨⟨f, mem_supportedFixedDerived.mpr ⟨f.2, by rw [hf]; exact h.2⟩⟩, Subtype.ext hf⟩⟩

theorem coe_fixRestr_apply {p : ℕ} (hx : OddOrderIsometry Q p x)
    (g : ↥(supportedFixedDerived Q x)) (w : fixedSpace x) :
    ((((fixRestr hx g : ↥(orthDerived (Q.comp (fixedSpace x).subtype))) :
      fixedSpace x ≃ₗ[F] fixedSpace x) w : fixedSpace x) : V) = (g : V ≃ₗ[F] V) w := rfl

@[expose] noncomputable def orthProjEquiv [Nontrivial V] (hQ : (polarBilin Q).Nondegenerate) :
    orthDerived Q ≃* ProjOrthDerived Q :=
  MulEquiv.ofBijective (piOrth Q) ⟨piOrth_injective hQ, QuotientGroup.mk'_surjective _⟩

@[expose] noncomputable def fixEquiv [Nontrivial V] (hQ : (polarBilin Q).Nondegenerate) {p : ℕ}
    (hx : OddOrderIsometry Q p x)
    (ι : (Q.comp (fixedSpace x).subtype).IsometryEquiv (coordinateQuadPlus 4 F))
    (hQ₀ : (polarBilin (coordinateQuadPlus 4 F)).Nondegenerate) :
    ↥(fixedComponentImage Q x) ≃* matrixProjectiveDerived (coordinateQuadPlus 4 F) :=
  (fixRho hQ hx).symm.trans ((fixRestr hx).trans ((orthDerivedEquiv ι).trans
    ((orthProjEquiv hQ₀).trans (coordBridge (coordinateQuadPlus 4 F) (by norm_num)).symm)))

@[expose] def semilinFix (Fs : V ≃+ V) (hc : ∀ v, Fs (x v) = x (Fs v)) :
    fixedSpace x ≃+ fixedSpace x where
  toFun w := ⟨Fs w, mem_fixedSpace.mpr (by rw [← hc, mem_fixedSpace.mp w.2])⟩
  invFun w := ⟨Fs.symm w, mem_fixedSpace.mpr (by
    apply Fs.injective
    rw [hc, AddEquiv.apply_symm_apply, mem_fixedSpace.mp w.2])⟩
  left_inv w := Subtype.ext (Fs.symm_apply_apply (w : V))
  right_inv w := Subtype.ext (Fs.apply_symm_apply (w : V))
  map_add' w w' := Subtype.ext (map_add Fs (w : V) (w' : V))

theorem mulAut_congr_mem_image_of_semilin [Nontrivial V] (hQ : (polarBilin Q).Nondegenerate)
    {p : ℕ} (hx : OddOrderIsometry Q p x)
    (ι : (Q.comp (fixedSpace x).subtype).IsometryEquiv (coordinateQuadPlus 4 F))
    (hQ₀ : (polarBilin (coordinateQuadPlus 4 F)).Nondegenerate)
    {σ : F ≃+* F} {Fs : V ≃+ V} (hFs : ∀ (c : F) (v : V), Fs (c • v) = σ c • Fs v) {μ : F}
    (hμ : μ ≠ 0) (hQF : ∀ v, Q (Fs v) = μ * σ (Q v)) (hc : ∀ v, Fs (x v) = x (Fs v))
    (γ : MulAut ↥(fixedComponentImage Q x))
    (hγ : ∀ g : ↥(supportedFixedDerived Q x), ∃ g' : ↥(supportedFixedDerived Q x),
      (∀ v, (g' : V ≃ₗ[F] V) v = Fs ((g : V ≃ₗ[F] V) (Fs.symm v))) ∧
        γ (fixRho hQ hx g) = fixRho hQ hx g') :
    MulAut.congr (fixEquiv hQ hx ι hQ₀) γ ∈ matrixProjectiveImage (coordinateQuadPlus 4 F) := by
  classical
  let FsW := semilinFix Fs hc
  let s : (Fin (2 * 4) → F) ≃+ (Fin (2 * 4) → F) :=
    (ι.toLinearEquiv.toAddEquiv.symm.trans FsW).trans ι.toLinearEquiv.toAddEquiv
  have hs_apply : ∀ v, s v = ι (FsW (ι.symm v)) := fun v => rfl
  have hs_symm : ∀ v, s.symm v = ι (FsW.symm (ι.symm v)) := fun v => rfl
  have hFsW : ∀ (c : F) (w : fixedSpace x), FsW (c • w) = σ c • FsW w := fun c w =>
    Subtype.ext (hFs c (w : V))
  have hs : ∀ (c : F) v, s (c • v) = σ c • s v := fun c v => by
    rw [hs_apply, hs_apply, map_smul, hFsW, map_smul]
  have hQs : ∀ v, coordinateQuadPlus 4 F (s v) = μ * σ (coordinateQuadPlus 4 F v) := fun v => by
    rw [hs_apply, ι.map_app]
    have h2 : coordinateQuadPlus 4 F v = (Q.comp (fixedSpace x).subtype) (ι.symm v) := by
      rw [← ι.map_app, ι.apply_symm_apply]
    rw [h2]
    exact hQF _
  obtain ⟨g₀, hg₀r, hg₀⟩ := exists_pair_of_semilin σ s hs
  have hg₀mem : g₀ ∈ similarityPairs (coordinateQuadPlus 4 F) :=
    ⟨Units.mk0 μ hμ, fun v => by rw [hg₀, hg₀r]; exact hQs v⟩
  have hg₀s : coordinateSemilinearMap
      (⟨g₀, hg₀mem⟩ : similarityPairs (coordinateQuadPlus 4 F)).val = s := AddEquiv.ext hg₀
  let Rest := (fixRestr hx).trans ((orthDerivedEquiv ι).trans
    ((orthProjEquiv hQ₀).trans (coordBridge (coordinateQuadPlus 4 F) (by norm_num)).symm))
  have hE : fixEquiv hQ hx ι hQ₀ = (fixRho hQ hx).symm.trans Rest := rfl
  refine ⟨⟨g₀, hg₀mem⟩, MulEquiv.ext fun z => ?_⟩
  obtain ⟨g, rfl⟩ := Rest.surjective z
  obtain ⟨g', hg', hγg⟩ := hγ g
  have hsymm : (fixEquiv hQ hx ι hQ₀).symm (Rest g) = fixRho hQ hx g := by
    rw [hE, MulEquiv.symm_trans_apply, MulEquiv.symm_symm, MulEquiv.symm_apply_apply]
  have h1 : (MulAut.congr (fixEquiv hQ hx ι hQ₀) γ) (Rest g) = Rest g' := by
    change fixEquiv hQ hx ι hQ₀ (γ ((fixEquiv hQ hx ι hQ₀).symm (Rest g))) = Rest g'
    rw [hsymm, hγg, hE, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [h1]
  have hR : ∀ k : ↥(supportedFixedDerived Q x),
      Rest k = (coordBridge (coordinateQuadPlus 4 F) (by norm_num)).symm
        (QuotientGroup.mk (orthDerivedEquiv ι (fixRestr hx k))) := fun k => rfl
  have hODE : ∀ (h : ↥(orthDerived (Q.comp (fixedSpace x).subtype))) (v : Fin (2 * 4) → F),
      ((orthDerivedEquiv ι h : ↥(orthDerived (coordinateQuadPlus 4 F))) :
        (Fin (2 * 4) → F) ≃ₗ[F] (Fin (2 * 4) → F)) v =
        ι ((h : fixedSpace x ≃ₗ[F] fixedSpace x) (ι.symm v)) := fun h v => rfl
  have h2 := coordBridge_conjugation (coordinateQuadPlus 4 F) (by norm_num) ⟨g₀, hg₀mem⟩
    (orthDerivedEquiv ι (fixRestr hx g)) (orthDerivedEquiv ι (fixRestr hx g')) fun v => by
      rw [hg₀s, hs_symm, hs_apply, hODE, hODE, ι.symm_apply_apply, ι.symm_apply_apply]
      congr 1
      apply Subtype.ext
      rw [coe_fixRestr_apply, hg']
      rfl
  rw [hR, hR, ← h2, MulEquiv.symm_apply_apply]

end Fixed

end CFSG.HardMathSupport.Dickson.Bal207.OrthFix

end
