module

public import CFSG.HardMathSupport.Lang.Triality.WeylOrbitSum
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutG2
public import CFSG.RankThree.PartOne.KGD.D4T36Core
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der61a
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der69
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Field
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Prop67
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Statements
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt7
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.LinearAlgebra.OddSolvableUnitary.HomologySaturation
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.RankThree.Chevalley.SteinbergCFOddG2SplitInnerActor
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneOrthogonal
public import CFSG.Sporadic.ThSchreier.AutCore

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Lang.Triality

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Timmesfeld.ExceptionalOrders CFSG.GH74.GLS.Stage2.Bender.Thm1

section Torus

variable {K : Type} [Field K]

theorem compat_inf_ker_D4_id {K : Type} [Field K] :
    Nat.card ↥(compatSubgroup (t := TwistTag.D4) (RingHom.id K) ⊓
      (zpowMatrix (G := Kˣ) TwistTag.D4.tag.cartan).ker) = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => ?_⟩, ⟨1⟩⟩
  suffices h : ∀ x : ↥(compatSubgroup (t := TwistTag.D4) (RingHom.id K) ⊓
      (zpowMatrix (G := Kˣ) TwistTag.D4.tag.cartan).ker), x = 1 by rw [h a, h b]
  rintro ⟨x, hxc, hxk⟩
  have hc := (mem_compatSubgroup (RingHom.id K)).1 hxc
  have hk : ∀ j, ∏ i, x i ^ (TwistTag.D4.tag.cartan i j) = 1 := fun j =>
    congrFun (MonoidHom.mem_ker.1 hxk) j
  let x' : Fin 4 → Kˣ := x
  have hc' : ∀ i : Fin 4, x' (TwistTag.D4.perm i) = x' i := hc
  have h0 : x' 1 = x' 0 := hc' 0
  have h1 : x' 3 = x' 1 := hc' 1
  have e0 : ∏ i : Fin 4, x' i ^ (Tag.D4.cartan i (0 : Fin 4)) = 1 := hk (0 : Fin 4)
  have e2 : ∏ i : Fin 4, x' i ^ (Tag.D4.cartan i (2 : Fin 4)) = 1 := hk (2 : Fin 4)
  simp [Fin.prod_univ_four, Tag.cartan] at e0 e2
  have hx2 : x' 0 ^ 2 = x' 2 := mul_inv_eq_one.1 e0
  rw [h1, h0, ← hx2] at e2
  have hx0 : x' 0 = 1 := by
    have : x' 0 = (x' 0)⁻¹ * (x' 0)⁻¹ * (x' 0 ^ 2) ^ 2 * (x' 0)⁻¹ := by group
    rw [this, e2]
  have key : ∀ i : Fin 4, x' i = 1 := by
    intro i
    fin_cases i
    · show x' 0 = 1
      exact hx0
    · show x' 1 = 1
      rw [h0, hx0]
    · show x' 2 = 1
      rw [← hx2, hx0]; simp
    · show x' 3 = 1
      rw [h1, h0, hx0]
  apply Subtype.ext
  funext i
  exact key i

theorem card_orbitField_id_aux (t : TwistTag) (a : Fin t.foldedTag.rank) :
    orbitField t K (RingHom.id K) a = ⊤ := by
  ext c
  simp only [mem_orbitField, Subfield.mem_top, iff_true]
  have h : ∀ n : ℕ, (RingHom.id K ^ n) = RingHom.id K := fun n => one_pow n
  rw [h]
  rfl

end Torus


section Orders

variable {K : Type} [Field K]

theorem card_orbitField_id (t : TwistTag) (a : Fin t.foldedTag.rank) :
    Nat.card (orbitField t K (RingHom.id K) a) = Nat.card K := by
  rw [card_orbitField_id_aux]
  exact Nat.card_congr Subfield.topEquiv.toEquiv

theorem card_compatTorus_D4_id [Finite K] :
    Nat.card (compatTorus (t := TwistTag.D4) (RingHom.id K)) = (Nat.card K - 1) ^ 2 := by
  have h := card_compatTorus_mul (t := TwistTag.D4) (K := K) (σ := RingHom.id K)
  rw [compat_inf_ker_D4_id, card_compatSubgroup, mul_one] at h
  simp only [card_orbitField_id] at h
  rw [h]
  change ∏ _a : Fin 2, (Nat.card K - 1) = _
  simp [sq]

theorem orbitsIn_pos_D4 :
    orbitsIn TwistTag.D4 {α : Fin TwistTag.D4.tag.rank → ℤ | IsRoot TwistTag.D4.tag α ∧
      0 < height α} = 6 := by
  classical
  have key := orbitsIn_eq_card_image (t := TwistTag.D4)
    {α : Fin TwistTag.D4.tag.rank → ℤ | IsRoot TwistTag.D4.tag α ∧ 0 < height α}
    (((rootList TwistTag.D4.tag).filter fun γ => decide (0 < height γ)).toFinset)
    (fun γ => by simp [mem_rootList]) (fun γ hγ => hγ.1)
    (fun γ hγ => ⟨hγ.1.permLattice TwistTag.D4.cartan_perm, by
      rw [height_permLattice]; exact hγ.2⟩)
  rw [key]
  decide +kernel

theorem card_graphFixedRootGroup_D4_id [Finite K] :
    Nat.card (graphFixedRootGroup TwistTag.D4 K (RingHom.id K)) =
      Nat.card K ^ 6 * (Nat.card K ^ 6 - 1) * (Nat.card K ^ 2 - 1) := by
  have : Fintype (WeylGroup TwistTag.D4.tag) := Fintype.ofFinite _
  have hq : ∀ a, Nat.card (orbitField TwistTag.D4 K (RingHom.id K) a) = Nat.card K :=
    card_orbitField_id TwistTag.D4
  rw [card_graphFixedRootGroup_const Function.surjective_id hq, card_compatTorus_D4_id,
    orbitsIn_pos_D4, sum_orbitsIn_D4]
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have h2 : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ hq1
  have h6 : 1 ≤ Nat.card K ^ 6 := Nat.one_le_pow _ _ hq1
  zify [hq1, h2, h6]
  ring

end Orders

section Fixed

variable {K : Type} [Field K] [Finite K]

@[expose] def fixedEquivTrialityFieldImage (σ : K ≃+* K) (hσ3 : ∀ c, σ (σ (σ c)) = c) :
    {g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom //
        fieldActor (t := TwistTag.D4) σ σ g = g} ≃ trialityFieldImage σ σ where
  toFun g := ⟨(g.1 : ModGL TwistTag.D4.tag K),
    (d4_mem_trialityFieldImage_self_iff σ hσ3 g.1).2 g.2⟩
  invFun x := ⟨⟨x.1, d4_trialityFieldImage_self_le σ x.2⟩,
    (d4_mem_trialityFieldImage_self_iff σ hσ3 ⟨x.1, d4_trialityFieldImage_self_le σ x.2⟩).1 x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_fixed_fieldActor_D4 (σ : K ≃+* K) (hσ3 : ∀ c, σ (σ (σ c)) = c) :
    Nat.card {g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom //
        fieldActor (t := TwistTag.D4) σ σ g = g} =
      Nat.card (fixSubfield σ) ^ 6 * (Nat.card (fixSubfield σ) ^ 6 - 1) *
        (Nat.card (fixSubfield σ) ^ 2 - 1) := by
  rw [Nat.card_congr (fixedEquivTrialityFieldImage σ hσ3), trialityFieldImage,
    Subgroup.card_map_of_injective (baseChangeGL_injective _)]
  have hσ₀ : (fixSubfieldRestrict σ σ).toRingHom = RingHom.id (fixSubfield σ) :=
    RingHom.ext fun c => Subtype.ext (by
      rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, coe_fixSubfieldRestrict]
      exact c.2)
  rw [hσ₀]
  exact card_graphFixedRootGroup_D4_id

theorem card_fixed_fieldActor_D4_of_frobenius {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    Nat.card {g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom //
        fieldActor (t := TwistTag.D4) σ σ g = g} =
      CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .G2 0 (ℓ ^ f) := by
  rw [card_fixed_fieldActor_D4 σ (ringEquiv_cube_apply_eq hK hσ),
    CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube hℓ hf hK σ hσ]
  rfl

end Fixed

end CFSG.HardMathSupport.Lang.Triality
