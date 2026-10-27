module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Blocks4
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.SteinbergR3ECALinearSplitBlocks

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open
open CFSG.RankThree.PartOne.KCOrthogonal (glue glue_apply glue_mul glue_one restrictEquiv
  exists_coe_add_of_isCompl)

namespace LinEngine

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

theorem det_glue [FiniteDimensional F V] {U W : Submodule F V} (hc : IsCompl U W)
    (a : U ≃ₗ[F] U) (b : W ≃ₗ[F] W) :
    LinearEquiv.det (glue hc a b) = LinearEquiv.det a * LinearEquiv.det b := by
  haveI : Module.Free F U := Module.Free.of_divisionRing F U
  haveI : Module.Free F W := Module.Free.of_divisionRing F W
  rw [glue, ← LinearEquiv.trans_assoc, LinearEquiv.det_conj]
  apply Units.ext
  rw [Units.val_mul, LinearEquiv.coe_det, LinearEquiv.coe_det, LinearEquiv.coe_det,
    LinearEquiv.coe_prodCongr, LinearMap.det_prodMap]

theorem glue_eq_of_maps [FiniteDimensional F V] {U W : Submodule F V} (hc : IsCompl U W)
    (g : V ≃ₗ[F] V) (hU1 : ∀ u ∈ U, g u ∈ U) (hU2 : ∀ u ∈ U, g.symm u ∈ U)
    (hW1 : ∀ w ∈ W, g w ∈ W) (hW2 : ∀ w ∈ W, g.symm w ∈ W) :
    g = glue hc (restrictEquiv U g hU1 hU2) (restrictEquiv W g hW1 hW2) := by
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨u, r, -, rfl⟩ := exists_coe_add_of_isCompl hc v
  rw [map_add, glue_apply]
  rfl

theorem restrictEquiv_eq_one_of_fixes {U : Submodule F V} (g : V ≃ₗ[F] V)
    (hU1 : ∀ u ∈ U, g u ∈ U) (hU2 : ∀ u ∈ U, g.symm u ∈ U) (hfix : ∀ u ∈ U, g u = u) :
    restrictEquiv U g hU1 hU2 = 1 := by
  refine LinearEquiv.ext fun u => Subtype.ext ?_
  show g (u : V) = ((1 : U ≃ₗ[F] U) u : V)
  simpa using hfix u u.2

theorem symm_apply_eq_self_of_apply_eq_self {g : V ≃ₗ[F] V} {u : V} (h : g u = u) :
    g.symm u = u := by
  calc g.symm u = g.symm (g u) := by rw [h]
    _ = u := g.symm_apply_apply u

@[expose] def pointwiseStabCentralizer (T : Set (V ≃ₗ[F] V)) (U : Submodule F V) :
    Subgroup (SpecialLinearGroup F V) where
  carrier := {g | (∀ u ∈ U, (g : V ≃ₗ[F] V) u = u) ∧
    ∀ t ∈ T, (g : V ≃ₗ[F] V) * t = t * (g : V ≃ₗ[F] V)}
  one_mem' := by
    refine ⟨fun u _ => rfl, fun t _ => ?_⟩
    simp
  mul_mem' := by
    rintro g h ⟨hgU, hgT⟩ ⟨hhU, hhT⟩
    refine ⟨fun u hu => ?_, fun t ht => ?_⟩
    · change (((g : V ≃ₗ[F] V) * (h : V ≃ₗ[F] V)) u) = u
      rw [LinearEquiv.mul_apply, hhU u hu, hgU u hu]
    · change (((g : V ≃ₗ[F] V) * (h : V ≃ₗ[F] V)) * t) = t * ((g : V ≃ₗ[F] V) * (h : V ≃ₗ[F] V))
      rw [mul_assoc, hhT t ht, ← mul_assoc, hgT t ht, mul_assoc]
  inv_mem' := by
    rintro g ⟨hgU, hgT⟩
    refine ⟨fun u hu => ?_, fun t ht => ?_⟩
    · have h : (g : V ≃ₗ[F] V) u = u := hgU u hu
      change ((g : V ≃ₗ[F] V)⁻¹) u = u
      exact symm_apply_eq_self_of_apply_eq_self h
    · have h := hgT t ht
      change ((g : V ≃ₗ[F] V)⁻¹) * t = t * ((g : V ≃ₗ[F] V)⁻¹)
      calc ((g : V ≃ₗ[F] V)⁻¹) * t
          = ((g : V ≃ₗ[F] V)⁻¹) * t * ((g : V ≃ₗ[F] V) * (g : V ≃ₗ[F] V)⁻¹) := by group
        _ = ((g : V ≃ₗ[F] V)⁻¹) * (t * (g : V ≃ₗ[F] V)) * (g : V ≃ₗ[F] V)⁻¹ := by group
        _ = ((g : V ≃ₗ[F] V)⁻¹) * ((g : V ≃ₗ[F] V) * t) * (g : V ≃ₗ[F] V)⁻¹ := by rw [h]
        _ = t * ((g : V ≃ₗ[F] V)⁻¹) := by group

@[simp] theorem mem_pointwiseStabCentralizer {T : Set (V ≃ₗ[F] V)} {U : Submodule F V}
    {g : SpecialLinearGroup F V} :
    g ∈ pointwiseStabCentralizer T U ↔
      (∀ u ∈ U, (g : V ≃ₗ[F] V) u = u) ∧
        ∀ t ∈ T, (g : V ≃ₗ[F] V) * t = t * (g : V ≃ₗ[F] V) :=
  Iff.rfl

abbrev fixedBySet (T : Set (V ≃ₗ[F] V)) : Submodule F V :=
  ⨅ t ∈ T, CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks.fixedByEnd t

@[simp] theorem mem_fixedBySet {T : Set (V ≃ₗ[F] V)} {w : V} :
    w ∈ fixedBySet T ↔ ∀ t ∈ T, t w = w := by
  simp [fixedBySet, CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks.mem_fixedByEnd]

theorem mapsTo_fixedBySet {T : Set (V ≃ₗ[F] V)} {g : V ≃ₗ[F] V}
    (hg : ∀ t ∈ T, g * t = t * g) : ∀ w ∈ fixedBySet T, g w ∈ fixedBySet T := by
  intro w hw
  rw [mem_fixedBySet] at hw ⊢
  intro t ht
  rw [← LinearEquiv.mul_apply, ← hg t ht, LinearEquiv.mul_apply, hw t ht]

theorem mapsTo_fixedBySet_inv {T : Set (V ≃ₗ[F] V)} {g : V ≃ₗ[F] V}
    (hg : ∀ t ∈ T, g * t = t * g) : ∀ w ∈ fixedBySet T, g.symm w ∈ fixedBySet T := by
  have hginv : ∀ t ∈ T, g.symm * t = t * g.symm := by
    intro t ht
    have h := hg t ht
    have h' : Commute g t := h
    have h2 : Commute g.symm t := h'.inv_left
    exact h2.eq
  intro w hw
  rw [mem_fixedBySet] at hw ⊢
  intro t ht
  rw [← LinearEquiv.mul_apply, ← hginv t ht, LinearEquiv.mul_apply, hw t ht]

variable [FiniteDimensional F V]

noncomputable def restrictStabHom {U W : Submodule F V} (hc : IsCompl U W)
    (T : Set (V ≃ₗ[F] V)) (hW : W = fixedBySet T) :
    ↥(pointwiseStabCentralizer T U) →* SpecialLinearGroup F W where
  toFun g :=
    ⟨restrictEquiv W (g : V ≃ₗ[F] V)
        (by rw [hW]; exact mapsTo_fixedBySet g.2.2)
        (by rw [hW]; exact mapsTo_fixedBySet_inv g.2.2),
      by
        have hglue := glue_eq_of_maps hc (g : V ≃ₗ[F] V)
          (fun u hu => by rw [g.2.1 u hu]; exact hu)
          (fun u hu => by rw [symm_apply_eq_self_of_apply_eq_self (g.2.1 u hu)]; exact hu)
          (by rw [hW]; exact mapsTo_fixedBySet g.2.2)
          (by rw [hW]; exact mapsTo_fixedBySet_inv g.2.2)
        have hdet := congrArg LinearEquiv.det hglue
        rw [det_glue] at hdet
        have hUdet : LinearEquiv.det (restrictEquiv U (g : V ≃ₗ[F] V)
            (fun u hu => by rw [g.2.1 u hu]; exact hu)
            (fun u hu => by
              rw [symm_apply_eq_self_of_apply_eq_self (g.2.1 u hu)]; exact hu)) = 1 := by
          rw [restrictEquiv_eq_one_of_fixes _ _ _ g.2.1]
          exact map_one _
        rw [hUdet, one_mul] at hdet
        rw [g.1.2] at hdet
        exact hdet.symm⟩
  map_one' := by
    apply Subtype.ext
    refine LinearEquiv.ext fun w => Subtype.ext ?_
    rfl
  map_mul' g h := by
    apply Subtype.ext
    refine LinearEquiv.ext fun w => Subtype.ext ?_
    rfl

noncomputable def restrictStabEquiv {U W : Submodule F V} (hc : IsCompl U W)
    (T : Set (V ≃ₗ[F] V)) (hW : W = fixedBySet T)
    (hU : ∀ t ∈ T, ∀ u ∈ U, t u ∈ U) :
    ↥(pointwiseStabCentralizer T U) ≃* SpecialLinearGroup F W := by
  have hfixW : ∀ t ∈ T, ∀ w ∈ W, t w = w := by
    intro t ht w hw
    rw [hW, mem_fixedBySet] at hw
    exact hw t ht
  refine MulEquiv.ofBijective (restrictStabHom hc T hW) ⟨?_, ?_⟩
  ·
    intro g h hgh
    have hglueg := glue_eq_of_maps hc (g : V ≃ₗ[F] V)
      (fun u hu => by rw [g.2.1 u hu]; exact hu)
      (fun u hu => by rw [symm_apply_eq_self_of_apply_eq_self (g.2.1 u hu)]; exact hu)
      (by rw [hW]; exact mapsTo_fixedBySet g.2.2)
      (by rw [hW]; exact mapsTo_fixedBySet_inv g.2.2)
    have hglueh := glue_eq_of_maps hc (h : V ≃ₗ[F] V)
      (fun u hu => by rw [h.2.1 u hu]; exact hu)
      (fun u hu => by rw [symm_apply_eq_self_of_apply_eq_self (h.2.1 u hu)]; exact hu)
      (by rw [hW]; exact mapsTo_fixedBySet h.2.2)
      (by rw [hW]; exact mapsTo_fixedBySet_inv h.2.2)
    have hU : restrictEquiv U (g : V ≃ₗ[F] V)
        (fun u hu => by rw [g.2.1 u hu]; exact hu)
        (fun u hu => by rw [symm_apply_eq_self_of_apply_eq_self (g.2.1 u hu)]; exact hu) =
      restrictEquiv U (h : V ≃ₗ[F] V)
        (fun u hu => by rw [h.2.1 u hu]; exact hu)
        (fun u hu => by rw [symm_apply_eq_self_of_apply_eq_self (h.2.1 u hu)]; exact hu) := by
      rw [restrictEquiv_eq_one_of_fixes _ _ _ g.2.1,
        restrictEquiv_eq_one_of_fixes _ _ _ h.2.1]
    have hWr : restrictEquiv W (g : V ≃ₗ[F] V)
        (by rw [hW]; exact mapsTo_fixedBySet g.2.2)
        (by rw [hW]; exact mapsTo_fixedBySet_inv g.2.2) =
      restrictEquiv W (h : V ≃ₗ[F] V)
        (by rw [hW]; exact mapsTo_fixedBySet h.2.2)
        (by rw [hW]; exact mapsTo_fixedBySet_inv h.2.2) := by
      have h1 := congrArg (fun s : SpecialLinearGroup F W => (s : W ≃ₗ[F] W)) hgh
      exact h1
    apply Subtype.ext
    apply Subtype.ext
    rw [hglueg, hglueh, hU, hWr]
  ·
    intro s
    refine ⟨⟨⟨glue hc 1 (s : W ≃ₗ[F] W), ?_⟩, ?_, ?_⟩, ?_⟩
    · rw [det_glue, map_one, one_mul]
      exact s.2
    · intro u hu
      have h := glue_apply hc 1 (s : W ≃ₗ[F] W) ⟨u, hu⟩
        ⟨0, Submodule.zero_mem (p := W)⟩
      have h0 : ((s : W ≃ₗ[F] W) ⟨0, Submodule.zero_mem (p := W)⟩ : W) = 0 := map_zero _
      rw [h0] at h
      simpa using h
    · intro t ht
      refine LinearEquiv.ext fun v => ?_
      obtain ⟨u, w, -, rfl⟩ := exists_coe_add_of_isCompl hc v
      have htu : t (u : V) ∈ U := hU t ht u u.2
      have htw : t (w : V) = (w : V) := hfixW t ht w w.2
      have hsw : ((s : W ≃ₗ[F] W) w : V) ∈ W := ((s : W ≃ₗ[F] W) w).2
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      have h1 : t ((u : V) + (w : V)) = t (u : V) + (w : V) := by rw [map_add, htw]
      have e1 : t (u : V) = ((⟨t (u : V), htu⟩ : U) : V) := rfl
      have e2 : glue hc 1 (s : W ≃ₗ[F] W) ((u : V) + (w : V)) =
          (u : V) + ((s : W ≃ₗ[F] W) w : V) := by
        rw [glue_apply]
        rfl
      rw [h1, e1, glue_apply, e2, map_add]
      rw [hfixW t ht ((s : W ≃ₗ[F] W) w) hsw]
      rfl
    ·
      apply Subtype.ext
      refine LinearEquiv.ext fun w => Subtype.ext ?_
      change (glue hc 1 (s : W ≃ₗ[F] W)) (w : V) = ((s : W ≃ₗ[F] W) w : V)
      have h := glue_apply hc 1 (s : W ≃ₗ[F] W) ⟨0, Submodule.zero_mem (p := U)⟩ w
      simpa using h

theorem isQuasisimple_specialLinearGroup_of_three_le {W : Submodule F V} {k : ℕ}
    (b : Module.Basis (Fin k) F W) (hk : 3 ≤ k) :
    CFSG.IsQuasisimple (SpecialLinearGroup F W) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (Matrix.SpecialLinearGroup.toLin_equiv b)
    (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup hk)

theorem isQuasisimple_specialLinearGroup_of_two {W : Submodule F V} [Finite F]
    (b : Module.Basis (Fin 2) F W) (h4 : 4 ≤ Nat.card F) :
    CFSG.IsQuasisimple (SpecialLinearGroup F W) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (Matrix.SpecialLinearGroup.toLin_equiv b)
    (CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le le_rfl h4)

theorem card_center_specialLinearGroup_dvd {W : Submodule F V} [Finite F] :
    Nat.card (Subgroup.center (SpecialLinearGroup F W)) ∣ Nat.card F - 1 := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Module.Free F W := Module.Free.of_divisionRing F W
  haveI : Module.Finite F W :=
    Module.Finite.of_injective (Submodule.subtype W) Subtype.val_injective
  have hcard : Nat.card (Subgroup.center (SpecialLinearGroup F W)) =
      Nat.card (rootsOfUnity (max (Module.finrank F W) 1) F) :=
    Nat.card_congr (SpecialLinearGroup.centerEquivRootsOfUnity).toEquiv
  rw [hcard]
  have h := Subgroup.card_subgroup_dvd_card (rootsOfUnity (max (Module.finrank F W) 1) F)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units] at h
  simpa only [Nat.card_eq_fintype_card] using h

end LinEngine

end CFSG.LocalAnalysis.GLTheoremA.Y10F
