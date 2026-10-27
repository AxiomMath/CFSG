module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF3
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.UnitaryInner
import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalPlane
import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryHermitian
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodUnitaryDiag
import CFSG.LocalAnalysis.StandardType.GGPGLToralityMatrix
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdTorality
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel
import CFSG.RankThree.PartOne.KC.UnitaryGoodModel
import CFSG.RankThree.PartOne.KC.UnitaryRigidityFrame
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Bridge
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04BCRes
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S11.Defs
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210Aux
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Projection
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.SemisimpleFactors
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinHeisCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open Matrix CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.StandardType
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryFrame
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (perfectInLayer_primeFormConjHom)
open CFSG.HardMathSupport.Timmesfeld.CrossChar (scalarU rescale_pow_eq_one conjHom_scalarU)

namespace SF

variable {m n p : ℕ} {F : Type} [Field F]

theorem glaPLayer_ne_bot_of_unitary_diag_eq (hF : UnitaryFieldData 2 m F) (hn : 3 ≤ n)
    (hp : p.Prime) (hq : 3 < 2 ^ m) (hpq : p ∣ 2 ^ m + 1)
    {A : primeFormUnitary hF ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)} {c : Fˣ}
    (hA : (A : GL (Fin n) F) ^ p = GeneralLinearGroup.scalar (Fin n) c) {P : GL (Fin n) F}
    (hP : P ∈ primeFormUnitary hF ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
    {t : Fin n → F} (ht : ((P⁻¹ * A * P : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal t)
    {i j : Fin n} (hij : i ≠ j) (htij : t i = t j) :
    GLAPLayer p (fixSubgroup (primeFormConjHom hF
      ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) A)) ≠ ⊥ := by
  haveI := hF.finite
  have hp2 := TableBUD.ne_two_of_dvd hF hpq
  have hne : ¬(n = 3 ∧ 2 ^ m = 2) := fun h' => by have := h'.2; omega
  have hbar : hF.bar (t i) * t i = 1 := by
    have h1 := mem_primeFormUnitary.1 (mul_mem (mul_mem (inv_mem hP) A.2) hP)
    simp only [Units.val_one, Matrix.mul_one, ht, diagonal_map (map_zero hF.bar),
      diagonal_transpose, diagonal_mul_diagonal] at h1
    simpa using congrFun (congrFun h1 i) i
  obtain ⟨a, ha⟩ : ∃ a : Fˣ, (a : F) = t i :=
    ⟨Units.mk0 _ (TypeA.PGLTor.diag_ne_zero_of_eq_diagonal ht i), rfl⟩
  have han : hF.norm ((a⁻¹ : Fˣ) : F) = 1 := by
    change ((a⁻¹ : Fˣ) : F) * hF.bar ((a⁻¹ : Fˣ) : F) = 1
    rw [Units.val_inv_eq_inv_val, ha, map_inv₀, ← mul_inv, mul_comm, hbar, inv_one]
  have hc : (A : GL (Fin n) F) ^ p = GeneralLinearGroup.scalar (Fin n) (a ^ p) := by
    have h1 : (P⁻¹ * (A : GL (Fin n) F) * P⁻¹⁻¹) ^ p = GeneralLinearGroup.scalar (Fin n) c := by
      rw [conj_pow, hA, ← GeneralLinearGroup.scalar_commute c P⁻¹, mul_inv_cancel_right]
    rw [inv_inv] at h1
    have h2 := congrArg (fun B : GL (Fin n) F => (B : Matrix (Fin n) (Fin n) F) i i) h1
    simp only [Units.val_pow_eq_pow_val, ht, diagonal_pow, diagonal_apply_eq, Pi.pow_apply,
      GeneralLinearGroup.coe_scalar, scalar_apply] at h2
    rw [hA]
    congr 1
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, ha, h2])
  have hAP : ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (P : Matrix (Fin n) (Fin n) F) =
      (P : Matrix (Fin n) (Fin n) F) * diagonal t := by
    rw [← ht, ← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  have hON : IsOrthonormalFamily hF
      (fun k => (P : Matrix (Fin n) (Fin n) F) *ᵥ Pi.single k 1) := fun r s => by
    have h1 := (mem_sesqUnitaryGroup.mp (toLinU_mem (⟨P, hP⟩ : primeFormUnitary hF (idGram F n))))
      (Pi.single r 1) (Pi.single s 1)
    change idForm hF n ((P : Matrix (Fin n) (Fin n) F) *ᵥ Pi.single r 1)
      ((P : Matrix (Fin n) (Fin n) F) *ᵥ Pi.single s 1) = _ at h1
    rw [h1, idForm_eq_dotProduct, dotProduct_single, mul_one]
    by_cases hrs : r = s
    · subst hrs
      simp
    · simp [hrs, Ne.symm hrs]
  have hfix : ∀ k, t k = t i → ((toLinU hF n (scalarU hF n a⁻¹ han * A) :
      LinearMap.GeneralLinearGroup F (Fin n → F)) : Module.End F (Fin n → F))
        ((P : Matrix (Fin n) (Fin n) F) *ᵥ Pi.single k 1) =
          (1 : F) • ((P : Matrix (Fin n) (Fin n) F) *ᵥ Pi.single k 1) := fun k hk => by
    change ((GeneralLinearGroup.scalar (Fin n) a⁻¹ * (A : GL (Fin n) F) : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) *ᵥ ((P : Matrix (Fin n) (Fin n) F) *ᵥ Pi.single k 1) = _
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, TableBUD.scalar_mul_eq_smul, smul_mulVec,
      mulVec_mulVec, hAP, ← mulVec_mulVec, diagonal_mulVec_single, ← smul_eq_mul,
      Pi.single_smul', mulVec_smul, smul_smul, hk, Units.val_inv_eq_inv_val, ha,
      inv_mul_cancel₀ (TypeA.PGLTor.diag_ne_zero_of_eq_diagonal ht i)]
  have hxρ : primeFormConjHom hF (idGram F n) (scalarU hF n a⁻¹ han * A) =
      primeFormConjHom hF (idGram F n) A := by
    rw [map_mul, conjHom_scalarU (by omega) hne, one_mul]
  obtain ⟨Q, hQf, hQc, hQp⟩ := KD264Lie.exists_perfect_fixSubgroup_of_onPair (by omega) hne hq hp
    hp2 hpq (rescale_pow_eq_one (by omega) hne han hc) (hON.pair hij) (hfix i rfl)
    (hfix j htij.symm)
  rw [hxρ] at hQf
  exact glaPLayer_ne_bot_of_le_glaLayer hp
    (perfectInLayer_primeFormConjHom hF hp hp2 A hA Q hQf hQc) hQp

theorem card_le_of_unitary_diag_nl (hF : UnitaryFieldData 2 m F) (hn : 3 ≤ n) (hp : p.Prime)
    (hq : 3 < 2 ^ m) (hpq : p ∣ 2 ^ m + 1)
    {X : Subgroup (MulAut (primeFormP hF ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)))}
    (hXr : X ≤ primeFormD hF ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
    (hX : IsElemAbelian p X) (hnl : ∀ α ∈ X, α ≠ 1 → GLAPLayer p (fixSubgroup α) = ⊥)
    {P : GL (Fin n) F}
    (hP : P ∈ primeFormUnitary hF ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
    (hPd : ∀ A ∈ X.comap (primeFormConjHom hF ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)),
      ((P⁻¹ * (A : GL (Fin n) F) * P : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag) :
    Nat.card X ≤ p := by
  haveI := hF.finite
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hne : ¬(n = 3 ∧ 2 ^ m = 2) := fun h' => by have := h'.2; omega
  set G := X.comap (primeFormConjHom hF (idGram F n)) with hGdef
  obtain ⟨i, j, hij⟩ : ∃ i j : Fin n, i ≠ j := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  obtain ⟨e, he⟩ : ∃ e : primeFormUnitary hF (idGram F n) → Fin n → F, ∀ A k,
      e A k = ((P⁻¹ * (A : GL (Fin n) F) * P : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) k k :=
    ⟨_, fun _ _ => rfl⟩
  have hd : ∀ A ∈ G, ((P⁻¹ * (A : GL (Fin n) F) * P : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) = diagonal (e A) := fun A hA =>
    (hPd A hA).diagonal_diag.symm.trans (congrArg diagonal (funext fun k => (he A k).symm))
  have he0 : ∀ A ∈ G, ∀ k, e A k ≠ 0 := fun A hA =>
    TypeA.PGLTor.diag_ne_zero_of_eq_diagonal (hd A hA)
  have hemul : ∀ A ∈ G, ∀ B ∈ G, ∀ k, e (A * B) k = e A k * e B k := by
    intro A hA B hB k
    simp only [he]
    rw [Subgroup.coe_mul, show P⁻¹ * ((A : GL (Fin n) F) * B) * P =
      P⁻¹ * A * P * (P⁻¹ * B * P) by group, Units.val_mul (P⁻¹ * (A : GL (Fin n) F) * P),
      hd A hA, hd B hB, diagonal_mul_diagonal]
    simp only [diagonal_apply_eq]
  have hpow : ∀ A ∈ G, ∃ u : Fˣ, (A : GL (Fin n) F) ^ p = GeneralLinearGroup.scalar (Fin n) u :=
    fun A hA => by
      obtain ⟨u, -, hu⟩ := (primeFormConjHom_eq_one_iff_of_ne (by omega) hne (A ^ p)).1
        (by rw [map_pow]; exact hX.2 _ hA)
      exact ⟨u, by rw [← Subgroup.coe_pow]; exact hu⟩
  obtain ⟨χ, hχ⟩ : ∃ χ : ↥G →* Fˣ, ∀ A : ↥G, (χ A : F) = e A j / e A i :=
    ⟨{ toFun := fun A => Units.mk0 (e A j / e A i) (div_ne_zero (he0 A A.2 j) (he0 A A.2 i))
       map_one' := Units.ext (by
         simp only [Subgroup.coe_one, Units.val_mk0, he, mul_one, inv_mul_cancel, Units.val_one,
           one_apply_eq, div_one])
       map_mul' := fun A B => Units.ext (by
         simp only [Subgroup.coe_mul, Units.val_mk0, Units.val_mul, hemul A A.2 B B.2]
         exact mul_div_mul_comm _ _ _ _) }, fun _ => rfl⟩
  have hχp : ∀ A : ↥G, χ A ^ p = 1 := fun A => by
    obtain ⟨u, hu⟩ := hpow A A.2
    have hs : ∀ k, e ((A : primeFormUnitary hF (idGram F n)) ^ p) k = u := fun k => by
      rw [he, Subgroup.coe_pow, hu, ← GeneralLinearGroup.scalar_commute u P⁻¹,
        inv_mul_cancel_right, GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq]
    rw [← map_pow]
    exact Units.ext (by rw [hχ, Subgroup.coe_pow, hs, hs, div_self u.ne_zero, Units.val_one])
  have hker : χ.ker ≤ ((primeFormConjHom hF (idGram F n)).comp G.subtype).ker := fun A hA => by
    rw [MonoidHom.mem_ker] at hA ⊢
    change primeFormConjHom hF (idGram F n) (A : primeFormUnitary hF (idGram F n)) = 1
    by_contra h1
    have h2 : e A j / e A i = 1 := by rw [← hχ, hA, Units.val_one]
    rw [div_eq_one_iff_eq (he0 A A.2 i)] at h2
    obtain ⟨u, hu⟩ := hpow A A.2
    exact glaPLayer_ne_bot_of_unitary_diag_eq hF hn hp hq hpq hu hP (hd A A.2) hij h2.symm
      (hnl _ A.2 h1)
  have hrange : ((primeFormConjHom hF (idGram F n)).comp G.subtype).range = X := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hGdef, Subgroup.map_comap_eq_self hXr]
  have hχr : χ.range ≤ rootsOfUnity p F := by
    rintro _ ⟨A, rfl⟩
    exact (mem_rootsOfUnity p _).2 (hχp A)
  have h1 := Subgroup.card_ker_mul_card_range χ
  have h2 := Subgroup.card_ker_mul_card_range ((primeFormConjHom hF (idGram F n)).comp G.subtype)
  rw [hrange] at h2
  have h3 : Nat.card ((primeFormConjHom hF (idGram F n)).comp G.subtype).ker * Nat.card X ≤
      Nat.card ((primeFormConjHom hF (idGram F n)).comp G.subtype).ker * p := by
    rw [h2, ← h1]
    exact Nat.mul_le_mul (Subgroup.card_le_of_le hker)
      ((Subgroup.card_le_of_le hχr).trans (card_rootsOfUnity F p))
  exact Nat.le_of_mul_le_mul_left h3 Nat.card_pos

end SF

end CFSG.LocalAnalysis.GLTheoremA.S265

end
