module

public import CFSG.Monster.Existence.MilestoneInputs
public import CFSG.Monster.B.GSide.TwoDNativeOrderFinal
public import CFSG.Monster.B.CTIB.FourClasses
public import CFSG.Monster.B.CTIB.UniqueComponent
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M5AssemblyInv
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Twist
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Rank3
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.LargeExtraspecial.BridgeSetting
public import CFSG.LargeExtraspecial.S3Asch
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.ComponentClassification.TBLitPropC
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma118T
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.EmptyFaithful.S146zYFacts
public import CFSG.Quasithin.EmptyFaithful.S146zYRes
public import CFSG.Quasithin.H13.NQCoreP134Main
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Inputs
public import CFSG.Sporadic.Co1Block.Perm
public import CFSG.Sporadic.Co2Smith.Defs
public import CFSG.Sporadic.Recognition.LyonsSimsEndgame
public import CFSG.Sporadic.Schreier.LyFixedSet
public import Certificates.Certificate2323

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Blueprint CFSG.Monster.GMS Subgroup
open CFSG.Monster.B.GSide (t2DS T9S rhoPlus rhoPlus_surjective rhoPlus_eq_one_iff orderOf_t2DS
  isPGroup_centralizer_T9S centralizer_t2DS_le_normalizer natCard_centralizer_t2DS)
open CFSG.Monster.B.TwoA (Shat)
open CFSG.Monster.B.TwoA.Sp8 (qPlus V8)

private theorem card_le_orthPlus (F : Subgroup (TauCeti.QuadraticMap.orthogonalGroup qPlus))
    (hF : IsElemAbelian 3 F) : Nat.card F ≤ 3 ^ 4 := by
  have e : (V8 ≃ₗ[ZMod 2] V8) ≃* GL (Fin 8) (ZMod 2) :=
    (Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V8)).symm
  obtain ⟨F', hF', hcard⟩ : ∃ F' : Subgroup (GL (Fin 8) (ZMod 2)), IsElemAbelian 3 F' ∧
      Nat.card F' = Nat.card F :=
    ⟨_, (hF.map (TauCeti.QuadraticMap.orthogonalGroup qPlus).subtype).map e.toMonoidHom, by
      rw [card_map_of_injective e.injective, card_map_of_injective (subtype_injective _)]⟩
  haveI := hF'.1
  have h := CFSG.LocalAnalysis.GLTheoremA.CatB.Rank3.card_le_three_pow_of_injective' (E := ↥F')
    (fun a b => mul_comm' a b)
    (fun x => Subtype.ext (by simpa using hF'.2 (x : GL (Fin 8) (ZMod 2)) x.2))
    F'.subtype Subtype.val_injective
  rw [← hcard]
  simpa using h

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid


theorem card_le_of_babyInv_two {t : NativeSporadic.B} (ht : BabyInv 2 t)
    (E : Subgroup NativeSporadic.B) (hEt : E ≤ centralizer ({t} : Set NativeSporadic.B))
    (hE : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 4 := by
  obtain ⟨ε⟩ : Nonempty (Shat ≃* NativeSporadic.B) :=
    ⟨CFSG.Monster.B.CTIB.sEquiv.symm.trans CFSG.Monster.B.CTIB.iotaEquiv.symm⟩
  have h2D : BabyInv 2 (ε t2DS) := by
    refine ⟨?_, ?_⟩
    · rw [MulEquiv.orderOf_eq]
      exact orderOf_t2DS
    · rw [← Nat.card_congr (CFSG.Monster.B.CTIB.centralizerEquiv ε t2DS).toEquiv,
        natCard_centralizer_t2DS]
      rfl
  obtain ⟨g, hg⟩ := isConj_iff.1 (CFSG.Monster.Existence.babyTableIII.2 2 t _ ht h2D)
  have hE' : E.map (MulAut.conj g).toMonoidHom ≤
      centralizer ({ε t2DS} : Set NativeSporadic.B) := by
    have h := H1017.map_conj_le_centralizer_singleton g hEt
    rwa [hg] at h
  have hE₁ : (E.map (MulAut.conj g).toMonoidHom).map ε.symm.toMonoidHom ≤
      centralizer ({t2DS} : Set Shat) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_singleton_iff]
    apply ε.injective
    simpa only [MulEquiv.coe_toMonoidHom, map_mul, MulEquiv.apply_symm_apply] using
      mem_centralizer_singleton_iff.1 (hE' hy)
  have hN6 := centralizer_t2DS_le_normalizer
  have hker : IsPGroup 2 (rhoPlus hN6).ker := by
    refine (isPGroup_centralizer_T9S.comap_subtype
      (K := centralizer ({t2DS} : Set Shat))).to_le ?_
    intro x hx
    rw [MonoidHom.mem_ker, rhoPlus_eq_one_iff] at hx
    rw [mem_comap, mem_centralizer_iff]
    intro y hy
    exact (mul_inv_eq_iff_eq_mul.1 (hx y hy)).symm
  rw [← card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective,
    ← card_map_of_injective (K := E.map (MulAut.conj g).toMonoidHom)
      (f := ε.symm.toMonoidHom) ε.symm.injective]
  exact H1017.H1016M5.card_le_of_le_quot Nat.prime_three (by norm_num) hker card_le_orthPlus
    (QuotientGroup.quotientKerEquivOfSurjective _ (rhoPlus_surjective hN6)) hE₁
    ((hE.map _).map _)

end CFSG.LocalAnalysis.GLTheoremA.H301B
