module

public import CFSG.ClassicalInvolution.WeakCT.TwistedE6
public import CFSG.ClassicalInvolution.Q3.Q3E6TLayer
public import CFSG.ClassicalInvolution.Q3.Q3E6TFrame

public noncomputable section

namespace CFSG.ClassicalInvolution.Q3.Q3E6T

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6 CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.Assembly.LowTwoRank CFSG.Blueprint
  MinData.Valid
open CFSG.ClassicalInvolution.Models.TwistedPairs CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Q3.Q3TW
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Recognition

variable {k : Type} [Field k] [Finite k] [CharP k 3] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
  (hθ3 : ∀ x, θ x = x ^ 3) {ι : k} (hι : ι ^ 2 = -1)


include hθ3 hι in
theorem weakCT3_twistedE6_of_CT {t : StatedLieTag} {n p f : ℕ} (e : ZMod 3 ≃+* fixedField θ)
    (hk4 : 4 ≤ Nat.card k) (hC : TD4Collapse)
    (hCT : CurtisTitsConclusion.{0} (twistedDatum k θ) t n p f)
    (hL : LeviConePresented (twistedDatum k θ))
    {X : Type} [Group X] (U : Fin 4 → Subgroup X) (hgen : ⨆ i, U i = ⊤)
    (hcomm : ∀ i j : Fin 4, i.val + 1 < j.val → ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    (hp01 : ∃ W, LinearBlockStandardPair (fixedField θ) W (U 0) (U 1))
    (hp23 : ∃ W, LinearBlockStandardPair k W (U 2) (U 3))
    (htw : ∃ W, UnitaryB2BlockStandardPair θ hθ W (U 1) (U 2)) :
    ∃ Ψ : fixedGroup k θ →* X, Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center _ ∧
      IsQuasisimple X ∧ Subgroup.center X = (Subgroup.center (fixedGroup k θ)).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) t n p f ∧
      ∀ i, (CFSG.LieType.CurtisTits.rankOne (twistedDatum k θ).rootGroup i).map Ψ = U i := by
  classical
  obtain ⟨W, θ₀, -, -, hl, hs, hU1, hU2⟩ := htw
  let P := unitaryModel θ hθ
  have hF3 : 3 ≤ Nat.card (fixedField θ) := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_zmod]
  have hμ : ∃ s, P.mu s ≠ 1 := exists_unitaryMu_ne θ hθ hF3
  obtain ⟨L, hL1, hL2⟩ := exists_twistedLayer_unitary θ hθ hθ3 hι e
  let U' : Fin (4 - 1) → Subgroup X := fun i => U ⟨i.val, by omega⟩
  have hcomm' : ∀ i j : Fin (4 - 1), i.val + 1 < j.val → ∀ a ∈ U' i, ∀ b ∈ U' j,
      a * b = b * a := fun i j hij a ha b hb =>
    hcomm ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ hij a ha b hb
  have hpair' : ∀ i j : Fin (4 - 1), i.val + 1 = j.val → j.val + 2 < 4 →
      ∃ W, LinearBlockStandardPair (fixedField θ) W (U' i) (U' j) := by
    intro i j hij hj
    have hi : U' i = U 0 := congrArg U (Fin.ext (by simp only [Fin.val_zero]; omega))
    have hj' : U' j = U 1 := congrArg U (Fin.ext (by simp only [Fin.val_one]; omega))
    rw [hi, hj']
    exact hp01
  obtain ⟨θ', ρL, hS', hlast, hρLU, hρLψ⟩ := exists_frameOfLayer e L (ulb θ hθ) (usb θ hθ).range
    hL1 hL2 (n := 4) (le_refl 4) U' hcomm' hC hpair' θ₀ hl hU1 hU2
  have hlU : (θ'.comp P.lb).range = U 1 := by
    have h := (hρLU ⟨1, by omega⟩).2
    rw [hlast] at h
    exact h
  have hsU : (θ'.comp P.sb).range = U 2 := by
    rw [MonoidHom.range_comp]
    exact hS'
  have hs' : Function.Injective (θ'.comp P.sb) :=
    injective_of_range_eq hs (by
      rw [MonoidHom.range_comp, MonoidHom.range_comp]
      exact hU2.trans hS'.symm)
  let US : Fin 2 → Subgroup X := fun i => U ⟨i.val + 2, by omega⟩
  have hcommS : ∀ i j : Fin 2, i ≠ j → ¬ (i.val + 1 = j.val) → ¬ (j.val + 1 = i.val) →
      ∀ u ∈ US i, ∀ v ∈ US j, u * v = v * u := by
    intro i j hne h1 h2
    have h3 : i.val ≠ j.val := fun h => hne (Fin.ext h)
    have := i.2
    have := j.2
    omega
  have hpairS : ∀ i j : Fin 2, i.val + 1 = j.val →
      ∃ W, LinearBlockStandardPair k W (US i) (US j) := by
    intro i j hij
    have hi : i = 0 := Fin.ext (by have := j.2; simp only [Fin.val_zero]; omega)
    have hj : j = 1 := Fin.ext (by have := j.2; simp only [Fin.val_one]; omega)
    subst hi hj
    exact hp23
  have hVS : ∀ q : Fin 2, ((0 : Fin 2).val + 1 = q.val ∨ q.val + 1 = (0 : Fin 2).val) →
      ∀ x ∈ (θ'.comp P.lb).range, ∀ y ∈ US q, x * y = y * x := by
    intro q hq x hx y hy
    have hq1 : q = 1 := Fin.ext (by
      have := q.2
      simp only [Fin.val_zero] at hq
      simp only [Fin.val_one]
      omega)
    subst hq1
    rw [hlU] at hx
    exact hcomm 1 3 (by decide) x hx y hy
  have hsU' : (θ'.comp P.sb).range = US 0 := hsU
  obtain ⟨ρS, hρS₀, hρSU, hρSψ⟩ := exists_frame_of_tree_short P hμ (by omega : 4 ≤ Nat.card k)
    rootedTree_two_first ⟨1, Or.inl rfl⟩ hcommS hpairS hs' hsU' hVS
  let dat : ∀ i : Fin (twistedDatum k θ).rank, NodeData (twistedDatum k θ) X i (U i) := fun i =>
    match i with
    | ⟨0, _⟩ => nodeDataFixed θ (nd 1) rfl (i := nf 0) rfl (ρL 0) (hρLU 0).2
    | ⟨1, _⟩ => nodeDataFixed θ (nd 3) rfl (i := nf 1) rfl (ρL 1) (hρLU 1).2
    | ⟨2, _⟩ => nodeDataOrbit θ hθ (a := nd 2) (b := nd 4) (Or.inl ⟨rfl, rfl⟩) (i := nf 2) rfl
        (ρS 0) (hρSU 0).2
    | ⟨3, _⟩ => nodeDataOrbit θ hθ (a := nd 0) (b := nd 5) (Or.inr ⟨rfl, rfl⟩) (i := nf 3) rfl
        (ρS 1) (hρSU 1).2
    | ⟨n + 4, h⟩ => absurd h (by change ¬ n + 4 < 4; omega)
  have dP0 : (dat (nf 0)).IsParam (nodeHom0 θ) (ρL 0) :=
    nodeDataFixed_isParam θ (nd 1) rfl (i := nf 0) rfl (ρL 0) (hρLU 0).2
  have dP1 : (dat (nf 1)).IsParam (nodeHom1 θ) (ρL 1) :=
    nodeDataFixed_isParam θ (nd 3) rfl (i := nf 1) rfl (ρL 1) (hρLU 1).2
  have dP2 : (dat (nf 2)).IsParam (nodeHom2 θ hθ) (ρS 0) :=
    nodeDataOrbit_isParam θ hθ (a := nd 2) (b := nd 4) (Or.inl ⟨rfl, rfl⟩) (i := nf 2) rfl
      (ρS 0) (hρSU 0).2
  have dP3 : (dat (nf 3)).IsParam (nodeHom3 θ hθ) (ρS 1) :=
    nodeDataOrbit_isParam θ hθ (a := nd 0) (b := nd 5) (Or.inr ⟨rfl, rfl⟩) (i := nf 3) rfl
      (ρS 1) (hρSU 1).2
  have hnt : ∃ i, ∃ g, (dat i).ψp g ≠ 1 := by
    refine ⟨nf 0, ⟨nodeHom0 θ (tv 0 1 1), dP0.r_upper 1⟩, ?_⟩
    rw [dP0.ψp_eq 1]
    intro h
    exact tv_zero_one_one_ne_one ((hρLU 0).1 (h.trans (map_one _).symm))
  have m0 : ∀ A, ρL 0 A ∈ U 0 := fun A => (hρLU 0).2.le ⟨A, rfl⟩
  have m1 : ∀ A, ρL 1 A ∈ U 1 := fun A => (hρLU 1).2.le ⟨A, rfl⟩
  have m2 : ∀ A, ρS 0 A ∈ U 2 := fun A => (hρSU 0).2.le ⟨A, rfl⟩
  have m3 : ∀ A, ρS 1 A ∈ U 3 := fun A => (hρSU 1).2.le ⟨A, rfl⟩
  exact weakCT_of_twisted_nodes hCT hL rfl hgen dat hnt
    (exists_levi_twistedE6 θ hθ hcomm dat dP0 dP1 dP2 dP3 m0 m1 m2 m3
      (hρLψ 0 1 rfl) (hρSψ 0 1 rfl) hlast hρS₀)

end Recognition

section Field

theorem exists_sq_eq_neg_one_gf9 : ∃ ι : GaloisField 3 (2 * 1), ι ^ 2 = -1 := by
  have : Fintype (GaloisField 3 (2 * 1)) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 3 (2 * 1)) = 9 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  obtain ⟨r, hr⟩ := FiniteField.isSquare_neg_one_iff.mpr (by rw [hcard]; norm_num)
  exact ⟨r, by rw [sq, ← hr]⟩

end Field

section Main

open CFSG.LieType.Steinberg.Exceptional


theorem weakCT3_twistedE6 (hC : TD4Collapse) {X : Type} [Group X] (U : Fin 4 → Subgroup X)
    (hgen : ⨆ i, U i = ⊤)
    (hcomm : ∀ i j : Fin 4, i.val + 1 < j.val → ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u)
    (hp01 : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U 0) (U 1))
    (hp23 : ∃ W, LinearBlockStandardPair (GaloisField 3 (2 * 1)) W (U 2) (U 3))
    (htw : ∃ W, UnitaryB2BlockStandardPair (frobQ 3 1) (frobQ_frobQ 3 1 le_rfl) W (U 1) (U 2)) :
    ∃ Ψ : twistedE6Group 3 1 →* X, Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center _ ∧
      IsQuasisimple X ∧ Subgroup.center X = (Subgroup.center (twistedE6Group 3 1)).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .twistedE6 0 3 1 ∧
      ∀ i, (CFSG.LieType.CurtisTits.rankOne (twistedE6Datum 3 1).rootGroup i).map Ψ = U i := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hadm : StatedLieAdmissible .twistedE6 0 3 1 := ⟨Nat.prime_three, le_rfl, rfl⟩
  have hf : 1 ≤ 1 := le_rfl
  have hF1 : Nat.card (GaloisField 3 1) = 3 ^ 1 := GaloisField.card 3 1 (by norm_num)
  have hF3 : Nat.card (ZMod 3) = 3 ^ 1 := by rw [Nat.card_zmod]; norm_num
  obtain ⟨eF⟩ := nonempty_ringEquiv_fixedField_frobQ 3 1 hf hF1
  obtain ⟨e⟩ := nonempty_ringEquiv_fixedField_frobQ 3 1 hf hF3
  obtain ⟨ι, hι⟩ := exists_sq_eq_neg_one_gf9
  have hθ3 : ∀ x : GaloisField 3 (2 * 1), frobQ 3 1 x = x ^ 3 := fun x => by
    rw [frobQ_apply]
    norm_num
  have hk4 : 4 ≤ Nat.card (GaloisField 3 (2 * 1)) := by
    rw [GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  exact weakCT3_twistedE6_of_CT (frobQ 3 1) (frobQ_frobQ 3 1 hf) hθ3 hι e hk4 hC
    (CFSG.LieType.CurtisTits.curtisTitsConclusion_twistedE6.{0} 3 1 hadm)
    (leviConePresented_twistedE6 3 1 hf) U hgen hcomm (hp01.imp fun W h => h.of_ringEquiv eF)
    hp23 htw

end Main

end CFSG.ClassicalInvolution.Q3.Q3E6T
