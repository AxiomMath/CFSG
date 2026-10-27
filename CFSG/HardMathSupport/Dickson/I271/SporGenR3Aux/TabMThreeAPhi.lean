module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeAY442
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeARef
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeADense
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeAWords

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271.TabMThreeA

open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Griess CFSG.Monster.GMS
  CFSG.Monster.Existence CFSG.YGroups CFSG.YGroups.Y443 CFSG.Open
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons evalWord_append)

@[expose] noncomputable def yM
    (hG : Gmat = AutO) : YGroup 4 4 2 →* MGriess :=
  (griessEquivGmat hG).symm.toMonoidHom.comp (fM.comp (y443TlHom.comp y442Iota))

theorem yM_yGen
    (hG : Gmat = AutO) {u : ℕ} (hu : u < 11) : yM hG (yGen 4 4 2 u) = refT hG u := by
  show (griessEquivGmat hG).symm (fM (y443TlHom (y442Iota (yGen 4 4 2 u)))) = refT hG u
  rw [y442Iota_yGen hu, y443TlHom_yGen (show u < 12 by omega)]
  rfl

theorem yM_evalWord
    (hG : Gmat = AutO) (w : List ℕ) (hw : ∀ c ∈ w, c < 11) :
    yM hG (evalWord (yGen 4 4 2) w) = evalWord (refT hG) w := by
  rw [Relabel.map_evalWord]
  exact evalWord_congr fun c hc => yM_yGen hG (hw c hc)

theorem yM_yF0
    (hG : Gmat = AutO) : yM hG (evalWord (yGen 4 4 2) yF0) = tGriess := by
  have h := symm_fM_C hG
  rw [EdgeNoncomm.y443C_eq] at h
  rw [← h, yM_evalWord hG yF0 (by decide), yF0, Y443.evalWord_replicate_flatten]
  simp only [map_pow, map_mul, evalWord_cons, evalWord_nil, mul_one, refT, mul_assoc]

theorem yM_yVWord
    (hG : Gmat = AutO) :
    yM hG (evalWord (yGen 4 4 2) yVWord) = (griessEquivGmat hG).symm denseV := by
  rw [yVWord, evalWord_append, evalWord_append, map_mul, map_mul, yM_yF0 hG,
    yM_evalWord hG _ (by decide), yM_evalWord hG _ (by decide)]
  simp only [denseV, map_mul, symm_fM_C hG, evalWord_cons, evalWord_nil, mul_one, refT,
    mul_assoc]

theorem tGriess_mul_yM_yVWord_pow_ne
    (hG : Gmat = AutO) :
    tGriess * yM hG (evalWord (yGen 4 4 2) yVWord) ^ 17 ≠
      yM hG (evalWord (yGen 4 4 2) yVWord) ^ 17 * tGriess := by
  intro h
  rw [yM_yVWord hG, ← symm_fM_C hG] at h
  have h' : (griessEquivGmat hG).symm (fM y443C * denseV ^ 17) =
      (griessEquivGmat hG).symm (denseV ^ 17 * fM y443C) := by
    simp only [map_mul, map_pow]
    exact h
  exact fM_C_mul_denseV_pow_ne ((griessEquivGmat hG).symm.injective h')

theorem tGriess_comm_yM_evalWord
    (hG : Gmat = AutO) {w : List ℕ} (hw : ∀ c ∈ w, c < 11) (h4 : 4 ∉ w) :
    tGriess * yM hG (evalWord (yGen 4 4 2) w) = yM hG (evalWord (yGen 4 4 2) w) * tGriess := by
  rw [yM_evalWord hG w hw]
  induction w with
  | nil => simp only [evalWord_nil, mul_one, one_mul]
  | cons c w ih =>
    have hc : c < 11 := hw c List.mem_cons_self
    have hc4 : c ≠ 4 := fun h => h4 (h ▸ List.mem_cons_self)
    have hw' : ∀ d ∈ w, d < 11 := fun d hd => hw d (List.mem_cons_of_mem _ hd)
    have h4' : 4 ∉ w := fun h => h4 (List.mem_cons_of_mem _ h)
    rw [evalWord_cons, ← mul_assoc, tGriess_mul_refT hG (show c < 12 by omega) hc4, mul_assoc,
      ih hw' h4', mul_assoc]

end CFSG.HardMathSupport.Dickson.I271.TabMThreeA
