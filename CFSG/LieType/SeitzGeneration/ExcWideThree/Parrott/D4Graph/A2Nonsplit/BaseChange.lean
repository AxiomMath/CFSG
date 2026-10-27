module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit.Frame
public import CFSG.LieType.Chevalley.GraphFixedF4GroupRestriction
public import CFSG.LieType.Chevalley.GraphFixedF4GroupDescent
public import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {L L' : Type} [Field L] [Field L'] (f : L →+* L')

local notation "𝕩" => xPar (rootOperatorFamily Tag.D4)

@[expose] noncomputable def bcAd : ↥(adjointGroup Tag.D4 L) →* ↥(adjointGroup Tag.D4 L') :=
  ((baseChangeGL f).comp (adjointGroup Tag.D4 L).subtype).codRestrict _
    fun h => CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup f h.2

theorem coe_bcAd (h : ↥(adjointGroup Tag.D4 L)) :
    ((bcAd f h : ↥(adjointGroup Tag.D4 L')) : ModGL Tag.D4 L') =
      baseChangeGL f (h : ModGL Tag.D4 L) :=
  rfl

theorem bcAd_injective : Function.Injective (bcAd f) := fun _ _ h =>
  Subtype.ext (baseChangeGL_injective f (congrArg Subtype.val h))

theorem coe_xPar_eq_pinnedX {K : Type} [Field K] {γ : Fin Tag.D4.rank → ℤ}
    (hγ : IsRoot Tag.D4 γ) (c : K) :
    ((𝕩 γ c : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
      pinnedX Tag.D4 K γ (((rootOperatorFamily Tag.D4).pinnedFamilySign γ : K) * c) := by
  rw [(rootOperatorFamily Tag.D4).pinnedX_eq_eltUnit K hγ, ← mul_assoc,
    (rootOperatorFamily Tag.D4).pinnedFamilySign_mul_self K γ, one_mul, xPar_of_isRoot hγ]
  rfl

theorem bcAd_xPar {γ : Fin Tag.D4.rank → ℤ} (hγ : IsRoot Tag.D4 γ) (c : L) :
    bcAd f (𝕩 γ c) = 𝕩 γ (f c) := by
  apply Subtype.ext
  rw [coe_bcAd, coe_xPar_eq_pinnedX hγ, coe_xPar_eq_pinnedX hγ, baseChangeGL_pinnedX, map_mul,
    map_intCast]

theorem bcAd_nW (i : Fin Tag.D4.rank) : bcAd f (nW i) = nW i := by
  unfold nW CFSG.LieType.Steinberg.weylElement
  simp only [map_mul, bcAd_xPar f (isRoot_single Tag.D4 i),
    bcAd_xPar f (isRoot_neg_single Tag.D4 i),
    Units.val_one, inv_one, map_neg, map_one]

theorem bcAd_sl2At (i : Fin Tag.D4.rank) (A : SL2 L) :
    bcAd f (sl2At L i A) = sl2At L' i (Matrix.SpecialLinearGroup.map f A) := by
  apply Subtype.ext
  rw [coe_bcAd, coe_sl2At, coe_sl2At, CFSG.RankThree.Chevalley.baseChangeGL_simpleRootSL2_of_field]

theorem bcAd_d4Graph (h : ↥(adjointGroup Tag.D4 L)) :
    bcAd f (d4Graph L 1 h) = d4Graph L' 1 (bcAd f h) := by
  have hP : baseChangeGL f (d4P L) = d4P L' := baseChangeGL_diagramMap f TwistTag.D4
  apply Subtype.ext
  rw [coe_bcAd, coe_d4Graph, coe_d4Graph, coe_bcAd, map_mul, map_mul, map_inv, map_pow, hP]

theorem coe_bcAd_of_eq_rootDiagUnit {h : ↥(adjointGroup Tag.D4 L)} {a : Fin Tag.D4.rank → Lˣ}
    (ha : (h : ModGL Tag.D4 L) = rootDiagUnit Tag.D4 a) :
    ((bcAd f h : ↥(adjointGroup Tag.D4 L')) : ModGL Tag.D4 L') =
      rootDiagUnit Tag.D4 (fun j => Units.map f.toMonoidHom (a j)) := by
  rw [coe_bcAd, ha, baseChangeGL_rootDiagUnit]

theorem bcAd_gammaP (B : SL2 L) (h : ↥(adjointGroup Tag.D4 L)) :
    bcAd f (gammaP L B h) = gammaP L' (Matrix.SpecialLinearGroup.map f B) (bcAd f h) := by
  rw [gammaP, gammaP, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply,
    map_mul, map_mul, map_inv, bcAd_sl2At, bcAd_d4Graph]

theorem bcAd_frameK₁ (A : SL2 L) :
    bcAd f (frameK₁ L A) = frameK₁ L' (Matrix.SpecialLinearGroup.map f A) := by
  rw [frameK₁_apply, frameK₁_apply]
  simp only [map_mul, map_inv, bcAd_nW, bcAd_sl2At]

theorem bcAd_frameK₃ (A : SL2 L) :
    bcAd f (frameK₃ L A) = frameK₃ L' (Matrix.SpecialLinearGroup.map f A) := by
  rw [frameK₃_apply, frameK₃_apply, bcAd_d4Graph, bcAd_frameK₁]

theorem bcAd_frameK₂ (A : SL2 L) :
    bcAd f (frameK₂ L A) = frameK₂ L' (Matrix.SpecialLinearGroup.map f A) := by
  rw [frameK₂_apply, frameK₂_apply, bcAd_d4Graph, bcAd_frameK₃]

theorem bcAd_frameDiag (A : SL2 L) :
    bcAd f (frameDiag A) = frameDiag (Matrix.SpecialLinearGroup.map f A) := by
  rw [frameDiag, frameDiag, map_mul, map_mul, bcAd_frameK₁, bcAd_frameK₃, bcAd_frameK₂]

theorem bcAd_frameD (B : SL2 L) :
    bcAd f (frameD L B) = frameD L' (Matrix.SpecialLinearGroup.map f B) := by
  rw [frameD, frameD, map_mul, map_inv, bcAd_frameK₂, bcAd_frameK₃]

theorem bcAd_weylG2 : bcAd f (weylG2 : ↥(adjointGroup Tag.D4 L)) = weylG2 := by
  have h := bcAd_nW (L := L) f
  unfold nW at h
  unfold weylG2
  simp only [map_mul, h]

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit
