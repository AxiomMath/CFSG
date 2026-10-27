module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeARecog
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeAFi24Inv
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeARef

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabMThreeA

open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Griess CFSG.Monster.Existence

section Cent


theorem centralizer_eq_of_cover_MGriess (hB3 : TabBThreeACard) (hG : Gmat = AutO)
    {D : Subgroup MGriess} {ζ : MGriess}
    (hDζ : D ≤ Subgroup.centralizer ({ζ} : Set MGriess)) (hζD : ζ ∈ D) (hζ3 : orderOf ζ = 3)
    (hinv : tGriess * ζ * tGriess⁻¹ = ζ⁻¹)
    (h23 : 23 ∣ Nat.card ↥(Subgroup.centralizer ({tGriess} : Set MGriess) ⊓
      Subgroup.centralizer ({ζ} : Set MGriess)))
    (ρ : ↥D →* CFSG.Sporadic.Fi24.J) (hρ : Function.Surjective ρ)
    (hker : ∀ d : ↥D, ρ d = 1 ↔ (d : MGriess) ∈ Subgroup.zpowers ζ)
    (htA : tGriess * refT hG 3 ∈ D)
    {t : MGriess} (htD : t ∈ D) (htc : t * tGriess = tGriess * t) (htB : IsConj xGriess t) :
    Subgroup.centralizer ({ζ} : Set MGriess) = D := by
  haveI : Finite ↥CFSG.Sporadic.Fi24.J :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)
  obtain ⟨hJ, hc₀, hc₁⟩ := fi24J_involutions
  have hord : ∀ {a b : MGriess}, IsConj a b → orderOf a = orderOf b := by
    intro a b h
    obtain ⟨c, rfl⟩ := isConj_iff.1 h
    exact (orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective a).symm
  have hA : IsConj tGriess (tGriess * refT hG 3) := (isConj_tGriess_refT_three hG).2
  have hoA : orderOf (tGriess * refT hG 3) = 2 := (hord hA).symm.trans orderOf_tGriess
  have hoB : orderOf t = 2 := (hord htB).symm.trans orderOf_xGriess
  have hAB : ¬ IsConj (tGriess * refT hG 3) t := not_isConj_of_twoA_of_twoB hA htB
  have hAζ : ζ * (tGriess * refT hG 3) = tGriess * refT hG 3 * ζ :=
    (Subgroup.mem_centralizer_singleton_iff.1 (hDζ htA)).symm
  have htζ : t * ζ = ζ * t := Subgroup.mem_centralizer_singleton_iff.1 (hDζ htD)
  exact centralizer_eq_of_cover hDζ hζD hζ3 ρ hρ hker hJ hc₀ hc₁ (by norm_num) htA htD hoA hoB hAB
    (card_inf_le_twoA hB3 hG hζ3 hAζ hinv) (card_inf_le_twoB hζ3 hinv h23 htc htζ htB)

end Cent

end CFSG.HardMathSupport.Dickson.I271.TabMThreeA
