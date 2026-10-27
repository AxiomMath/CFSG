module

public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryOutdiag
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryDvdFrame
import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryInnFrame
import CFSG.RankThree.PartOne.KF.U4Calc
import CFSG.RankThree.PartOne.KF.U4Model
import CFSG.RankThree.PartOne.KF.UnitaryDiag
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.LocalAnalysis.SectionRank.SporadicCover
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSetting
import CFSG.RankThree.PartOne.KC.UnitaryLiftBlocks
import CFSG.RankThree.PartOne.KF.UnitaryModel
import CFSG.Sporadic.M23.M23Group
import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.StandardType
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.SectionRank.OddCover (diagHom coe_diagHom)

variable {F : Type} [Field F] {n d : ℕ} (h : UnitaryFieldData 2 n F)

private theorem diag_conj_blk {i j : Fin d} (hij : i ≠ j) {σ : Fin d → Fˣ} (hσ : σ i = σ j)
    {b : GL (Fin d) F} (hb : b ∈ RankThree.PartOne.KFU.blk h hij) :
    diagHom d σ * b * (diagHom d σ)⁻¹ = b := by
  obtain ⟨X, -, hX⟩ := (RankThree.PartOne.KFU.mem_blk_iff hij).mp hb
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagHom, hX]
  exact RankThree.PartOne.KCUnitaryCoord.diagonal_mul_coordEmbed _ (congrArg Units.val hσ) _

private noncomputable abbrev blkFrame {i j : Fin d} (hij : i ≠ j) (Q : GL (Fin d) F)
    (hQ : Q ∈ primeFormUnitary h (idGram F d)) :
    ↥(RankThree.PartOne.KFU.blk h hij) →* LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n)) :=
  (InndiagSU.frameMk h Q hQ).comp (Subgroup.inclusion (RankThree.PartOne.KFU.blk_le_unitarySU hij))

private theorem range_blkFrame_le_fix {i j : Fin d} (hij : i ≠ j) {Q : GL (Fin d) F}
    {hQ : Q ∈ primeFormUnitary h (idGram F d)}
    {e : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n)))} {σ : Fin d → Fˣ}
    (he : TableBUD.FrameAct h Q hQ e σ) (hσ : σ i = σ j) :
    (blkFrame h hij Q hQ).range ≤ fixSubgroup e := by
  rintro _ ⟨b, rfl⟩
  exact he.apply _ _ (diag_conj_blk h hij hσ b.2).symm

private theorem blkFrame_injective (hd : 3 ≤ d) {i j : Fin d} (hij : i ≠ j) (Q : GL (Fin d) F)
    (hQ : Q ∈ primeFormUnitary h (idGram F d)) : Function.Injective (blkFrame h hij Q hQ) := by
  obtain ⟨l, -, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {i, j})
    (t := Finset.univ) (by
      rw [Finset.card_univ, Fintype.card_fin]
      exact Finset.card_le_two.trans_lt (by omega))
  have hli : l ≠ i := fun e => hl (by simp [e])
  have hlj : l ≠ j := fun e => hl (by simp [e])
  rw [injective_iff_map_eq_one]
  intro b hb
  obtain ⟨c, hc⟩ := TableBUI.exists_scalar_of_frameMk_eq h Q hQ (u := 1)
    (v := Subgroup.inclusion (RankThree.PartOne.KFU.blk_le_unitarySU hij) b)
    (by rw [map_one]; exact hb.symm)
  have hbc : (b : GL (Fin d) F) = Matrix.GeneralLinearGroup.scalar (Fin d) c := by
    rw [Subgroup.coe_one, mul_one] at hc
    exact hc
  obtain ⟨X, -, hX⟩ := (RankThree.PartOne.KFU.mem_blk_iff hij).mp b.2
  have hentry : ((b : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) l l = 1 := by
    rw [hX, RankThree.PartOne.KFU.coordEmbed_apply_of_not_mem_left hli hlj]
    simp
  have hsc : ((b : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) l l = (c : F) := by
    rw [hbc]
    simp [Matrix.GeneralLinearGroup.scalar]
  have hc1 : c = 1 := Units.ext (hsc.symm.trans hentry)
  rw [hc1, map_one] at hbc
  exact Subtype.ext hbc

private theorem three_dvd_card_blk (h3 : 3 ∣ 2 ^ n + 1) {i j : Fin d} (hij : i ≠ j) :
    3 ∣ Nat.card ↥(RankThree.PartOne.KFU.blk h hij) := by
  haveI := Fact.mk Nat.prime_three
  obtain ⟨ζ, hζ⟩ := RankThree.PartOne.KFU.exists_isPrimitiveRoot h Nat.prime_three h3
  set u : Fˣ := Units.mk0 ζ (hζ.ne_zero (by norm_num))
  have hun : h.norm (u : F) = 1 := by
    obtain ⟨k, hk⟩ := h3
    rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply, Units.val_mk0, ← pow_succ', hk,
      pow_mul, hζ.pow_eq_one, one_pow]
  set g := RankThree.PartOne.KCUnitaryCoord.diagonalCoord h hij u hun
  set b : ↥(RankThree.PartOne.KFU.blk h hij) :=
    ⟨g, g, RankThree.PartOne.KCUnitaryCoord.diagonalCoord_mem_coordSU h hij u hun, rfl⟩
  have hcoe : ((b : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      diagonal (fun k => if k = i then ζ else if k = j then ((u⁻¹ : Fˣ) : F) else 1) :=
    RankThree.PartOne.KCUnitaryCoord.coe_diagonalCoord h hij u hun
  have hb3 : b ^ 3 = 1 := by
    refine Subtype.ext (Units.ext ?_)
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hcoe, diagonal_pow]
    simp only [Subgroup.coe_one, Units.val_one, ← diagonal_one]
    congr 1
    funext k
    have hu3 : ((u⁻¹ : Fˣ) : F) ^ 3 = 1 := by
      rw [Units.val_inv_eq_inv_val, inv_pow, Units.val_mk0, hζ.pow_eq_one, inv_one]
    rw [Pi.pow_apply]
    split_ifs <;> first | exact hζ.pow_eq_one | exact hu3 | exact one_pow 3
  have hb1 : b ≠ 1 := fun e => by
    have := congrArg (fun y : ↥(RankThree.PartOne.KFU.blk h hij) =>
      ((y : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i i) e
    simp only [hcoe, diagonal_apply_eq, if_pos rfl, Subgroup.coe_one, Units.val_one,
      one_apply_eq] at this
    exact hζ.ne_one (by norm_num) this
  rw [← orderOf_eq_prime hb3 hb1]
  exact orderOf_dvd_natCard b

theorem SG.uniS_core (hn : 2 ≤ n) (h3 : 3 ∣ 2 ^ n + 1) (hd4 : 4 ≤ d) (hd5 : d ≤ 5)
    {X : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n))))}
    (hX : IsElemAbelian 3 X) (hXD : X ≤ InndiagSU.inndiagU h (by omega))
    (hcard : Nat.card X = 3 ^ 3) {α : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n)))}
    (hα : α ∈ X) :
    ∃ A : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n))), IsSimpleGroup ↥A ∧
      (∃ a b : ↥A, a * b ≠ b * a) ∧ 3 ∣ Nat.card ↥A ∧ A ≤ fixSubgroup α ∧
      ∃ Y : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n)))),
        Y.relIndex X ≤ 3 ∧ ∀ ε ∈ Y, A ≤ fixSubgroup ε := by
  haveI := h.finite
  haveI : NeZero (3 : ℕ) := ⟨three_ne_zero⟩
  have hF : Nat.card F = (2 ^ n) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hd3 : 3 ≤ d := by omega
  have hdq : (d, 2 ^ n) ≠ (3, 2) := fun e => (show d ≠ 3 by omega) (congrArg Prod.fst e)
  have hbig : 3 ^ (d / 3 + 1) < Nat.card X := by
    rw [hcard]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  obtain ⟨Q, hQ, hfr⟩ := TableBUD.exists_frame_inndiag hF hd3 hdq
    (fun e => absurd e.1 (by omega)) Nat.prime_three h3 hX hXD hbig
  choose! σ _ hσ3 hσn hσf using hfr
  obtain ⟨i, j, hij, hσij⟩ : ∃ i j : Fin d, i ≠ j ∧ σ α i = σ α j := by
    by_contra! hne
    have hinj : Function.Injective fun k : Fin 4 =>
        (⟨σ α (Fin.castLE hd4 k), (mem_rootsOfUnity _ _).2 (hσ3 α hα _)⟩ : rootsOfUnity 3 F) := by
      refine fun a b hab => Fin.castLE_injective hd4 ?_
      by_contra hne'
      exact hne _ _ hne' (congrArg Subtype.val hab)
    have h4 := Nat.card_le_card_of_injective _ hinj
    have h3' := card_rootsOfUnity F 3
    rw [Nat.card_fin] at h4
    omega
  have hmul : ∀ e₁ ∈ X, ∀ e₂ ∈ X,
      σ (e₁ * e₂) i / σ (e₁ * e₂) j = σ e₁ i / σ e₁ j * (σ e₂ i / σ e₂ j) := by
    intro e₁ he₁ e₂ he₂
    obtain ⟨c, hc⟩ := TableBUD.FrameAct.eq_smul hF hd3 hdq Nat.prime_three h3
      (fun k => by rw [Pi.mul_apply, Units.val_mul, mul_pow, hσn _ he₁, hσn _ he₂, one_mul])
      (hσn _ (X.mul_mem he₁ he₂)) ((hσf _ he₁).mul (hσf _ he₂) (hσn _ he₂))
      (hσf _ (X.mul_mem he₁ he₂))
    rw [hc i, hc j, Pi.mul_apply, Pi.mul_apply, mul_div_mul_left_eq_div, mul_div_mul_comm]
  obtain ⟨χ, hχ⟩ : ∃ χ : ↥X →* Fˣ, ∀ e : ↥X, χ e = σ e i / σ e j :=
    ⟨MonoidHom.mk' (fun e => σ e i / σ e j) fun e₁ e₂ => hmul _ e₁.2 _ e₂.2, fun _ => rfl⟩
  obtain ⟨⟨-, hsimp, a₀, b₀, hab₀⟩, hZ, -⟩ := RankThree.PartOne.KFU.blk_model h hn hij
  haveI := hsimp
  obtain ⟨eA⟩ : Nonempty (↥(RankThree.PartOne.KFU.blk h hij) ≃* ↥(blkFrame h hij Q hQ).range) :=
    ⟨MonoidHom.ofInjective (blkFrame_injective h hd3 hij Q hQ)⟩
  set e₀ := ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans eA
  refine ⟨(blkFrame h hij Q hQ).range, e₀.symm.isSimpleGroup,
    ⟨e₀ a₀, e₀ b₀, fun hc => hab₀ (e₀.injective (by rw [map_mul, map_mul]; exact hc))⟩, ?_,
    range_blkFrame_le_fix h hij (hσf α hα) hσij, χ.ker.map X.subtype, ?_, ?_⟩
  · rw [← Nat.card_congr eA.toEquiv]
    exact three_dvd_card_blk h h3 hij
  · have hYX : (χ.ker.map X.subtype).subgroupOf X = χ.ker := (Subgroup.comap_subtype _ _).symm.trans
      (Subgroup.comap_map_eq_self_of_injective X.subtype_injective _)
    rw [Subgroup.relIndex, hYX, Subgroup.index_ker]
    refine (Subgroup.card_le_of_le (K := rootsOfUnity 3 F) ?_).trans (card_rootsOfUnity F 3)
    rintro _ ⟨e, rfl⟩
    rw [mem_rootsOfUnity, hχ, div_pow, hσ3 _ e.2, hσ3 _ e.2, div_one]
  · rintro _ ⟨e, he, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, hχ, div_eq_one] at he
    exact range_blkFrame_le_fix h hij (hσf _ e.2) he

end CFSG.LocalAnalysis.GLTheoremA.S265

end
