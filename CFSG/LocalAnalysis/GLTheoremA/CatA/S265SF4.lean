module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF3
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LinearInner
import CFSG.HardMathSupport.Timmesfeld.CrossChar.DiagSplit
import CFSG.LieType.SeitzGeneration.NonabLinear
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodLinear
import CFSG.LocalAnalysis.StandardType.GGPGLTorality
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

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open Matrix CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.StandardType
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (perfectInLayer_conjAut)
open CFSG.HardMathSupport.Timmesfeld.CrossChar (glConj_eq_diagonal glRescale_lift)

namespace SF

variable {n p : ℕ} {F : Type} [Field F] [Finite F]

private theorem glaPLayer_ne_bot_of_diag_eq (hp : p.Prime) (hp2 : p ≠ 2)
    (hpF : p ∣ Nat.card F - 1) {A A₀ : GL (Fin n) F} {c : Fˣ}
    (hA : A ^ p = GeneralLinearGroup.scalar (Fin n) c) {t : Fin n → F}
    (ht : ((A₀ * A * A₀⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal t)
    {i j : Fin n} (hij : i ≠ j) (htij : t i = t j) :
    GLAPLayer p (fixSubgroup (conjAut n F A)) ≠ ⊥ := by
  obtain ⟨a, ha⟩ : ∃ a : Fˣ, (a : F) = t i :=
    ⟨Units.mk0 _ (TypeA.PGLTor.diag_ne_zero_of_eq_diagonal ht i), rfl⟩
  have hc : A ^ p = GeneralLinearGroup.scalar (Fin n) (a ^ p) := by
    have h1 : (A₀ * A * A₀⁻¹) ^ p = GeneralLinearGroup.scalar (Fin n) c := by
      rw [conj_pow, hA, ← GeneralLinearGroup.scalar_commute c A₀, mul_inv_cancel_right]
    have h2 := congrArg (fun B : GL (Fin n) F => (B : Matrix (Fin n) (Fin n) F) i i) h1
    simp only [Units.val_pow_eq_pow_val, ht, diagonal_pow, diagonal_apply_eq, Pi.pow_apply,
      GeneralLinearGroup.coe_scalar, scalar_apply] at h2
    rw [hA]
    congr 1
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, ha, h2])
  obtain ⟨hMp, hMc⟩ := glRescale_lift hc
  have hconj : A₀ * (GeneralLinearGroup.scalar (Fin n) a⁻¹ * A) * A₀⁻¹ =
      GeneralLinearGroup.scalar (Fin n) a⁻¹ * (A₀ * A * A₀⁻¹) := by
    rw [← mul_assoc A₀, ← GeneralLinearGroup.scalar_commute a⁻¹ A₀]
    simp only [mul_assoc]
  have hM : ((A₀ * (GeneralLinearGroup.scalar (Fin n) a⁻¹ * A) * A₀⁻¹ : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) = diagonal fun k => ((a⁻¹ : Fˣ) : F) * t k := by
    rw [hconj, Units.val_mul, ht, GeneralLinearGroup.coe_scalar, scalar_apply,
      diagonal_mul_diagonal]
  obtain ⟨Q, hQf, hQc, hQp⟩ := KD264Lie.exists_perfect_fixSubgroup_of_diagonal_eq (P := A₀) hp
    hp2 hpF hMp (fun r s hrs => by rw [hM]; exact diagonal_apply_ne _ hrs) hij
    (by rw [hM]; simp only [diagonal_apply_eq, htij])
  rw [hMc] at hQf
  exact glaPLayer_ne_bot_of_le_glaLayer hp (perfectInLayer_conjAut
    (CFSG.LieType.SeitzGeneration.natCast_ne_zero_of_dvd_card_sub_one hp hpF) hA Q hQf hQc) hQp

private theorem card_le_of_diag_nl (hn : 2 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpF : p ∣ Nat.card F - 1) {X : Subgroup (MulAut (projectiveSL n F))}
    (hXr : X ≤ (conjAut n F).range) (hG : TypeA.PGLTor.IsProjElem p (X.comap (conjAut n F)))
    (hnl : ∀ α ∈ X, α ≠ 1 → GLAPLayer p (fixSubgroup α) = ⊥) {A₀ : GL (Fin n) F}
    (hA₀ : ∀ g ∈ X.comap (conjAut n F), ∀ i j, i ≠ j →
      ((A₀ : Matrix (Fin n) (Fin n) F) * (g : Matrix (Fin n) (Fin n) F) *
        ((A₀⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) i j = 0) :
    Nat.card X ≤ p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set G := X.comap (conjAut n F) with hGdef
  obtain ⟨i, j, hij⟩ : ∃ i j : Fin n, i ≠ j := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  obtain ⟨e, he⟩ : ∃ e : GL (Fin n) F → Fin n → F, ∀ g k,
      e g k = ((A₀ * g * A₀⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) k k :=
    ⟨_, fun _ _ => rfl⟩
  have hd : ∀ g ∈ G,
      ((A₀ * g * A₀⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal (e g) :=
    fun g hg => (glConj_eq_diagonal (P := A₀) (x := g) fun r s hrs => by
      rw [Units.val_mul, Units.val_mul]
      exact hA₀ g hg r s hrs).trans (congrArg diagonal (funext fun k => (he g k).symm))
  have he0 : ∀ g ∈ G, ∀ k, e g k ≠ 0 := fun g hg =>
    TypeA.PGLTor.diag_ne_zero_of_eq_diagonal (hd g hg)
  have hemul : ∀ g ∈ G, ∀ h ∈ G, ∀ k, e (g * h) k = e g k * e h k := by
    intro g hg h hh k
    simp only [he]
    rw [show A₀ * (g * h) * A₀⁻¹ = A₀ * g * A₀⁻¹ * (A₀ * h * A₀⁻¹) by group,
      Units.val_mul (A₀ * g * A₀⁻¹), hd g hg, hd h hh, diagonal_mul_diagonal]
    simp only [diagonal_apply_eq]
  obtain ⟨χ, hχ⟩ : ∃ χ : ↥G →* Fˣ, ∀ g : ↥G, (χ g : F) = e g j / e g i :=
    ⟨{ toFun := fun g => Units.mk0 (e g j / e g i) (div_ne_zero (he0 g g.2 j) (he0 g g.2 i))
       map_one' := Units.ext (by
         simp only [Subgroup.coe_one, Units.val_mk0, he, mul_one, mul_inv_cancel, Units.val_one,
           one_apply_eq, div_one])
       map_mul' := fun g h => Units.ext (by
         simp only [Subgroup.coe_mul, Units.val_mk0, Units.val_mul, hemul g g.2 h h.2]
         exact mul_div_mul_comm _ _ _ _) }, fun _ => rfl⟩
  have hχp : ∀ g : ↥G, χ g ^ p = 1 := fun g => by
    obtain ⟨u, hu⟩ := hG.pow_scalar g g.2
    have hs : ∀ k, e ((g : GL (Fin n) F) ^ p) k = u := fun k => by
      rw [he, hu, ← GeneralLinearGroup.scalar_commute u A₀, mul_inv_cancel_right,
        GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq]
    rw [← map_pow]
    exact Units.ext (by rw [hχ, Subgroup.coe_pow, hs, hs, div_self u.ne_zero, Units.val_one])
  have hker : χ.ker ≤ ((conjAut n F).comp G.subtype).ker := fun g hg => by
    rw [MonoidHom.mem_ker] at hg ⊢
    change conjAut n F (g : GL (Fin n) F) = 1
    by_contra h1
    have h2 : e g j / e g i = 1 := by rw [← hχ, hg, Units.val_one]
    rw [div_eq_one_iff_eq (he0 g g.2 i)] at h2
    obtain ⟨u, hu⟩ := hG.pow_scalar g g.2
    exact glaPLayer_ne_bot_of_diag_eq hp hp2 hpF hu (hd g g.2) hij h2.symm
      (hnl (conjAut n F g) g.2 h1)
  have hrange : ((conjAut n F).comp G.subtype).range = X := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hGdef, Subgroup.map_comap_eq_self hXr]
  have hχr : χ.range ≤ rootsOfUnity p F := by
    rintro _ ⟨g, rfl⟩
    exact (mem_rootsOfUnity p _).2 (hχp g)
  have h1 := Subgroup.card_ker_mul_card_range χ
  have h2 := Subgroup.card_ker_mul_card_range ((conjAut n F).comp G.subtype)
  rw [hrange] at h2
  have h3 : Nat.card ((conjAut n F).comp G.subtype).ker * Nat.card X ≤
      Nat.card ((conjAut n F).comp G.subtype).ker * p := by
    rw [h2, ← h1]
    exact Nat.mul_le_mul (Subgroup.card_le_of_le hker)
      ((Subgroup.card_le_of_le hχr).trans (card_rootsOfUnity F p))
  exact Nat.le_of_mul_le_mul_left h3 Nat.card_pos

theorem card_le_of_nl_linear (hn : 3 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpF : p ∣ Nat.card F - 1) {X : Subgroup (MulAut (projectiveSL n F))}
    (hX : IsElemAbelian p X) (hnl : ∀ α ∈ X, α ≠ 1 → GLAPLayer p (fixSubgroup α) = ⊥) :
    Nat.card X ≤ p ^ (n / p + 1) := by
  have hXr : X ≤ (conjAut n F).range :=
    (le_linearAutGroup_of_nl hn hp hp2 hpF hX hnl).trans linearAutGroup_eq_range.le
  have hG := TypeA.isProjElem_comap (by omega : 0 < n) hX
  rcases TypeA.PGLTor.toral_or_card_le hp hp2 hpF hG with ⟨A₀, hA₀⟩ | hbound
  · exact (card_le_of_diag_nl (by omega) hp hp2 hpF hXr hG hnl hA₀).trans
      (Nat.le_self_pow (Nat.succ_ne_zero _) p)
  · rw [TypeA.card_comap_eq (by omega) (fun _ hx => hXr hx), Fintype.card_fin] at hbound
    exact Nat.le_of_mul_le_mul_right hbound (by have := Finite.one_lt_card (α := F); omega)

end SF

end CFSG.LocalAnalysis.GLTheoremA.S265

end
