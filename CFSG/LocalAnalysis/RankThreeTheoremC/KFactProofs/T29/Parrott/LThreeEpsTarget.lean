module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsForm
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open CFSG.Open Subgroup
open CFSG.RankThree.PartTwo.Sec4
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.Coordinator (exists_etaPkg)

section Transport

theorem isInnDiagThree_of_mulEquiv {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y')
    {α : MulAut Y} (h : IsInnDiagThree α) : IsInnDiagThree (e.symm.trans (α.trans e)) := by
  have hc := Lemma511Ns.map_center_mulEquiv e
  let ē : Y ⧸ center Y ≃* Y' ⧸ center Y' := QuotientGroup.congr _ _ e hc
  have hē : ∀ y, ē (QuotientGroup.mk y) = QuotientGroup.mk (e y) := fun y =>
    QuotientGroup.congr_mk _ _ e hc y
  have hē' : ∀ y, ē.symm (QuotientGroup.mk (e y)) = QuotientGroup.mk y := fun y =>
    ē.symm_apply_eq.2 (hē y).symm
  rcases h with ⟨K, hK, hf, θ, φ, hφ, hθ⟩ | ⟨K, hK, hf, q, θ, φ, hcard, hφ, hθ⟩
  · left
    refine ⟨K, hK, hf, ē.symm.trans θ, φ, hφ, ?_⟩
    intro y'
    obtain ⟨y, rfl⟩ := e.surjective y'
    have h1 : (e.symm.trans (α.trans e)) (e y) = e (α y) := by simp
    rw [h1]
    simp only [MulEquiv.trans_apply, hē']
    exact hθ y
  · right
    refine ⟨K, hK, hf, q, ē.symm.trans θ, φ, hcard, hφ, ?_⟩
    intro y'
    obtain ⟨y, rfl⟩ := e.surjective y'
    have h1 : (e.symm.trans (α.trans e)) (e y) = e (α y) := by simp
    rw [h1]
    simp only [MulEquiv.trans_apply, hē']
    exact hθ y

end Transport

section BarAut

variable {X : Type} [Group X] {L : Subgroup X} [L.Normal]

@[expose] noncomputable def barEquivL (hcore : GLAPPrimeCore 3 ↥L = ⊥) :
    (↥L ⧸ GLAPPrimeCore 3 ↥L) ≃* ↥L :=
  (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot

theorem congr_barEquivL_barAut (hcore : GLAPPrimeCore 3 ↥L = ⊥) (g : X)
    (hn : g ∈ normalizer (L : Set X)) :
    MulAut.congr (barEquivL hcore) (barAut 3 L ⟨g, hn⟩) = MulAut.conjNormal g := by
  refine MulEquiv.ext fun w => ?_
  show barEquivL hcore (barAut 3 L ⟨g, hn⟩ ((barEquivL hcore).symm w)) = MulAut.conjNormal g w
  have hsymm : (barEquivL hcore).symm w = QuotientGroup.mk w := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [hsymm, barAut_mk]
  have hval : ((L.normalizerMonoidHom ⟨g, hn⟩ w : ↥L) : X) = g * (w : X) * g⁻¹ := rfl
  apply Subtype.ext
  change ((L.normalizerMonoidHom ⟨g, hn⟩ w : ↥L) : X) = _
  rw [hval, MulAut.conjNormal_apply]

theorem barAut_eq_congr (hcore : GLAPPrimeCore 3 ↥L = ⊥) (g : X)
    (hn : g ∈ normalizer (L : Set X)) :
    barAut 3 L ⟨g, hn⟩ =
      (barEquivL hcore).symm.symm.trans ((MulAut.conjNormal g).trans (barEquivL hcore).symm) := by
  have h := congr_barEquivL_barAut hcore g hn
  have h2 : MulAut.congr (barEquivL hcore).symm (MulAut.conjNormal g) = barAut 3 L ⟨g, hn⟩ := by
    rw [← h]
    ext w
    simp [MulAut.congr_apply]
  rw [← h2]
  rfl

theorem inv_mul_mem_centralizer_of_conjNormal_eq {g : X} {l : ↥L}
    (h : (MulAut.conjNormal g : MulAut ↥L) = MulAut.conj l) :
    (l : X)⁻¹ * g ∈ centralizer (L : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 := congrArg (fun α : MulAut ↥L => ((α ⟨y, hy⟩ : ↥L) : X)) h
  simp only [MulAut.conjNormal_apply, MulAut.conj_apply] at h1
  change g * y * g⁻¹ = (l : X) * y * (l : X)⁻¹ at h1
  calc y * ((l : X)⁻¹ * g) = (l : X)⁻¹ * ((l : X) * y * (l : X)⁻¹) * g := by group
    _ = (l : X)⁻¹ * (g * y * g⁻¹) * g := by rw [h1]
    _ = (l : X)⁻¹ * g * y := by group

end BarAut

section Conclusions

variable {X : Type} [Group X] {L : Subgroup X} [L.Normal] {π : Bool} {p f : ℕ} {K : Type}
  [Field K] {ν : ↥(slPi π 3 (p ^ f) K) →* ↥L}

theorem inducesInnDiagNonInner_of_isLiftAt (M : LModel L π p f K ν)
    (hcore : GLAPPrimeCore 3 ↥L = ⊥) {x : X} {y : GL (Fin 3) K} (hx : IsLiftAt ν x y)
    (hni : ∀ l ∈ L, l⁻¹ * x ∉ centralizer (L : Set X)) : InducesInnDiagNonInner L x := by
  have hn : x ∈ normalizer (L : Set X) := by
    rw [Subgroup.normalizer_eq_top L]
    exact Subgroup.mem_top x
  refine ⟨hn, ?_, ?_⟩
  · rw [barAut_eq_congr hcore x hn]
    exact isInnDiagThree_of_mulEquiv (barEquivL hcore).symm (M.isInnDiagThree_of_isLiftAt hx)
  · rintro ⟨lb, hlb⟩
    have h1 := congr_barEquivL_barAut hcore x hn
    rw [← hlb, CFSG.RankThree.PartTwo.KFacts.congr_mulAutConj] at h1
    exact hni _ (barEquivL hcore lb).2 (inv_mul_mem_centralizer_of_conjNormal_eq h1.symm)

theorem inducesNontrivialFieldAut_of_isFieldAt (M : LModel L π p f K ν)
    (hcore : GLAPPrimeCore 3 ↥L = ⊥) {g : X} {σ : K ≃+* K} {H : GL (Fin 3) K}
    (hg : IsFieldAt ν g σ H) : InducesNontrivialFieldAut L g := by
  have hn : g ∈ normalizer (L : Set X) := by
    rw [Subgroup.normalizer_eq_top L]
    exact Subgroup.mem_top g
  refine ⟨hn, ?_, fun h1 => ?_⟩
  · rw [barAut_eq_congr hcore g hn]
    exact Lemma511Ns.isFieldAutThree_of_mulEquiv (barEquivL hcore).symm
      (M.isFieldAutThree_of_isFieldAt hg)
  · have h2 := congr_barEquivL_barAut hcore g hn
    rw [h1, map_one] at h2
    apply M.not_mem_centralizer_of_isFieldAt hg
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h3 := congrArg (fun α : MulAut ↥L => ((α ⟨y, hy⟩ : ↥L) : X)) h2
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h3
    change y = g * y * g⁻¹ at h3
    calc y * g = g * y * g⁻¹ * g := by rw [← h3]
      _ = g * y := by group

end Conclusions

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
