module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K144TriFixCard
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GTriField
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GTriRed
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Glue
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTriD4Conj
import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K144

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.Assembly
open CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.Blueprint
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (FieldKind)

section OutTD4Two


theorem card_fix_le_TD4two {S : Type} [Group S] [Finite S] (hcen : Subgroup.center S = ⊥)
    {β : MulAut S} (hβ3 : β ^ 3 = 1) (hfld : FieldKind S (⟨.triD4, 0, 1⟩ : GLALabel) β) :
    Nat.card ↥(fixSubgroup β) ≤ 12096 := by
  unfold FieldKind CFSG.Assembly.LargeEvenMarking at hfld
  obtain ⟨-, lab', hlam', hraw⟩ := hfld
  obtain ⟨_, _, _, _, hQ0⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, hlab, -⟩ := hQ0
  subst hlab
  unfold CFSG.Assembly.LargeEvenRawDatum at hraw
  dsimp only at hraw
  obtain ⟨K, hKF, hKfin, hK, hQ⟩ := hraw
  obtain ⟨hsR, hnaR, θ, -, ⟨i, hi, f, hf, hind⟩, hout⟩ := hQ
  obtain ⟨σ, hσ, ⟨eR⟩⟩ := Y10GTri.triRecipe_equiv (n := 1) le_rfl hK
  let eS : S ≃* S ⧸ Subgroup.center S :=
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm
  let e := eS.trans θ
  let eY := e.trans eR
  have hkey : ∀ s : S, (i * f) (e s) = e (β s) := fun s => hind s (β s) rfl
  have hβe : MulAut.congr e β = i * f := by
    ext r
    have h := hkey (e.symm r)
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm
  have hnotI : i * f ∉ LargeEvenChevIDImage TwistTag.D4.tag.cartan K
      (LargeEvenTwistedH TwistTag.D4.tag.cartan K TwistTag.D4.perm 1) :=
    fun h => hout ⟨i * f, h, hind⟩
  have hφ3 : MulAut.congr eY β ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  have hcongr0 : MulAut.congr eY β = MulAut.congr eR (MulAut.congr e β) :=
    MulEquiv.ext fun x => rfl
  have hcongr : MulAut.congr eY β = MulAut.congr eR (i * f) := by rw [hcongr0, hβe]
  have hφout : MulAut.congr eY β ∉
      (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
        MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
    rw [hcongr]
    exact Y10GTri.tri_not_inner_of_not_mem eR (Y10GTri.tri_inn_mem_idImage _ K _) hnotI
  have hfix : (fixSubgroup β).map eY.toMonoidHom = fixSubgroup (MulAut.congr eY β) :=
    Y10F.fixSubgroup_map_congr eY β
  let eC : ↥(fixSubgroup β) ≃* ↥(fixSubgroup (MulAut.congr eY β)) :=
    (Subgroup.equivMapOfInjective _ eY.toMonoidHom eY.injective).trans (MulEquiv.subgroupCongr hfix)
  have hcard : Nat.card ↥(fixSubgroup β) = Nat.card ↥(fixSubgroup (MulAut.congr eY β)) :=
    Nat.card_congr eC.toEquiv
  rw [hcard]
  exact card_fix_le_triFix hK σ hσ (MulAut.congr eY β) hφ3 hφout

end OutTD4Two

end CFSG.LocalAnalysis.GLTheoremA.K144
