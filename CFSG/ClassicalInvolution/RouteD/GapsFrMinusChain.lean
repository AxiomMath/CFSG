module

public import CFSG.ClassicalInvolution.RouteD.GapsFrBGen
public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusOrth
public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusLift

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub fundamentalSubgroups)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.CurtisTits (rankOne)
open CFSG.ClassicalInvolution.ModelFacts.OrthAut (toralNormal_minus_of_normalized_subgroups)
open scoped MatrixGroups commutatorElement

section Props

variable {F : Type} [Field F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ} {X : Type}
  [Group X]

@[expose] def MinusToral (θ : spinGroup (quadMinus n F b c) →* X) (σ : X ≃* X)
    (k₀ : spinGroup (quadMinus n F b c)) (v : Fin (n - 1) → ZMod 2) : Prop :=
  ∀ γ : Fin (n - 1) → ℤ, γ ∈ (minusDatum n hirr).roots →
    ((((minusDatum n hirr).rootGroup γ ⊔ (minusDatum n hirr).rootGroup (-γ)).map
        (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
      (((minusDatum n hirr).rootGroup γ ⊔ (minusDatum n hirr).rootGroup (-γ)).map
        (MulAut.conj k₀).toMonoidHom).map θ ∧
    ((∀ y ∈ (((minusDatum n hirr).rootGroup γ ⊔ (minusDatum n hirr).rootGroup (-γ)).map
        (MulAut.conj k₀).toMonoidHom).map θ, σ y = y) ↔ ∑ i, (γ i : ZMod 2) * v i = 0)

@[expose] def MinusOuter (θ : spinGroup (quadMinus n F b c) →* X) (σ : X ≃* X)
    (k₀ : spinGroup (quadMinus n F b c)) (v : Fin (n - 1) → ZMod 2) : Prop :=
  ∀ γ : Fin (n - 1) → ℤ, γ ∈ (minusDatum n hirr).roots →
    ((((minusDatum n hirr).rootGroup γ ⊔ (minusDatum n hirr).rootGroup (-γ)).map
        (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
      (((minusDatum n hirr).rootGroup γ ⊔ (minusDatum n hirr).rootGroup (-γ)).map
        (MulAut.conj k₀).toMonoidHom).map θ ∧
    ((∀ y ∈ (((minusDatum n hirr).rootGroup γ ⊔ (minusDatum n hirr).rootGroup (-γ)).map
        (MulAut.conj k₀).toMonoidHom).map θ, σ y = y) ↔
      (∑ i, (γ i : ZMod 2) * v i = 0 ∧
        ¬ ∃ (i : Fin (n - 1)) (s : Bool), toStdB (n - 1) γ = Pi.single i (boolSign s)))

end Props

section Roots

variable {F : Type} [Field F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {m : ℕ}

theorem rootGroup_sup_eq_longSL2_range_minus {i j : Fin (m - 1)} (hij : i ≠ j) (s t : Bool)
    {γ : Fin (m - 1) → ℤ}
    (hγ : toStdB (m - 1) γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) :
    (minusDatum m hirr).rootGroup γ ⊔ (minusDatum m hirr).rootGroup (-γ) =
      ((minusFrame m b c).longSL2 hij s t).range := by
  have hstd' : toStdB (m - 1) (-γ) =
      Pi.single j (boolSign (!t)) + Pi.single i (boolSign (!s)) := by
    rw [toStdB_neg, hγ, boolSign_not, boolSign_not, Pi.single_neg, Pi.single_neg, neg_add,
      add_comm]
  rw [longSL2_range_eq_sup]
  congr 1
  · exact minusRootGroup_eq_long m hirr hij s t hγ
  · exact minusRootGroup_eq_long m hirr hij.symm (!t) (!s) hstd'

theorem rankOne_minusDatum_of_lt {k : Fin (m - 1)} (hk : k.val + 1 < m - 1) :
    rankOne (minusDatum m hirr).rootGroup k =
      rootSL2 (minusFrame m b c).toHypFrame k.val (k.val + 1) k.isLt hk (by omega) true false := by
  have h : toStdB (m - 1) (Pi.single k 1) = Pi.single k (boolSign true) +
      Pi.single (⟨k.val + 1, hk⟩ : Fin (m - 1)) (boolSign false) := toStdB_single_of_lt' m hk
  exact rootGroup_sup_eq_longSL2_range_minus hirr (i := k) (j := ⟨k.val + 1, hk⟩)
    (Fin.ne_of_val_ne (by simp)) true false (γ := Pi.single k 1) h

end Roots

section Main

variable {p f : ℕ} [Fact p.Prime]

theorem toralNormal_minus_of_frame_chain (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {s : ℕ} (hs : 1 ≤ s)
    {X : Type} [Group X]
    (θ : spinGroup (quadMinus (s + 5) (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadMinus (s + 5) (GaloisField p f)
      (minusCoeffs p f).1 (minusCoeffs p f).2)))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    (x : spinGroup (quadMinus (s + 5) (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2))
    (t : Bool)
    {R : ℕ → Subgroup (spinGroup (quadMinus (s + 5) (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2))}
    {Rtw RM : Subgroup (spinGroup (quadMinus (s + 5) (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2))}
    (hR : ∀ a (ha : a ≤ s), R a = ((rootSL2 (minusFrame (s + 5) (minusCoeffs p f).1
      (minusCoeffs p f).2).toHypFrame a (a + 1) (by omega) (by omega) (by omega) true false).map
        (MulAut.conj x).toMonoidHom))
    (hRtw : Rtw = ((rootSL2 (minusFrame (s + 5) (minusCoeffs p f).1
      (minusCoeffs p f).2).toHypFrame s (s + 1) (by omega) (by omega) (by omega) true true).map
        (MulAut.conj x).toMonoidHom))
    (hRM : RM = ((rootSL2 (minusFrame (s + 5) (minusCoeffs p f).1
      (minusCoeffs p f).2).toHypFrame (s + 2) (s + 3) (by omega) (by omega) (by omega) true t).map
        (MulAut.conj x).toMonoidHom))
    (hfix : ∀ a, 1 ≤ a → a ≤ s → ∀ y ∈ R a, σ (θ y) = θ y)
    (hfixtw : ∀ y ∈ Rtw, σ (θ y) = θ y) (hfixM : ∀ y ∈ RM, σ (θ y) = θ y)
    (hnorm0 : ∀ y ∈ R 0, σ (θ y) ∈ (R 0).map θ) :
    ((∃ k₀ v, MinusToral (minusCoeffs_irr p f) θ σ k₀ v) ∨
      (∃ k₀ v, MinusOuter (minusCoeffs_irr p f) θ σ k₀ v)) ∧ MinusLift θ σ := by
  classical
  have hirr := minusCoeffs_irr p f
  obtain ⟨hf0, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hf : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr hf0
  have hscal : ∀ z ∈ Subgroup.center (spinGroup (quadMinus (s + 5) (GaloisField p f)
      (minusCoeffs p f).1 (minusCoeffs p f).2)),
      ∃ η : GaloisField p f, ∀ v, spinAction (quadMinus (s + 5) (GaloisField p f)
        (minusCoeffs p f).1 (minusCoeffs p f).2) z v = η • v := by
    intro z hz
    obtain ⟨c, hc⟩ := mem_scalars.mp (Exotic.spinAction_center_mem_scalars_minus (by omega) hirr hz)
    exact ⟨c, hc⟩
  obtain ⟨H1g, H2g, H3g⟩ := frame_chain_fixed_data hs
    (minusFrame (s + 5) (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame θ hker σ hscal x t hR
    hRtw hRM hfix hfixtw hfixM hnorm0
  let i₀ : Fin (s + 5 - 1) := ⟨s + 2, by omega⟩
  let i₁ : Fin (s + 5 - 1) := ⟨s + 3, by omega⟩
  let c₀ : Fin (s + 5 - 1) := ⟨0, by omega⟩
  let jj : Fin (s + 5 - 1) := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := fun h => by have := congrArg Fin.val h; simp [i₀, i₁] at this
  have hc0 : c₀ ≠ i₀ := fun h => by have := congrArg Fin.val h; simp [i₀, c₀] at this
  have hc1 : c₀ ≠ i₁ := fun h => by have := congrArg Fin.val h; simp [i₁, c₀] at this
  have hj0 : jj ≠ i₀ := fun h => by have := congrArg Fin.val h; simp [i₀, jj] at this
  have hj1 : jj ≠ i₁ := fun h => by have := congrArg Fin.val h; simp [i₁, jj] at this
  have hjc : c₀ ≠ jj := fun h => by have := congrArg Fin.val h; simp [c₀, jj] at this
  have hγ₀ : toStdB (s + 5 - 1) (ofStdB (s + 5 - 1) (Pi.single i₀ (boolSign true) +
      Pi.single i₁ (boolSign t))) = Pi.single i₀ (boolSign true) + Pi.single i₁ (boolSign t) :=
    toStdB_ofStdB _ _
  have hγ₁ : toStdB (s + 5 - 1) (ofStdB (s + 5 - 1) (Pi.single c₀ (boolSign false) +
      Pi.single jj (boolSign true))) = Pi.single c₀ (boolSign false) +
        Pi.single jj (boolSign true) := toStdB_ofStdB _ _
  set γ₀ := ofStdB (s + 5 - 1) (Pi.single i₀ (boolSign true) + Pi.single i₁ (boolSign t))
    with hγ₀d
  set γ₁ := ofStdB (s + 5 - 1) (Pi.single c₀ (boolSign false) + Pi.single jj (boolSign true))
    with hγ₁d
  have hH1 : ∀ y ∈ (((minusDatum (s + 5) hirr).rootGroup γ₀ ⊔
      (minusDatum (s + 5) hirr).rootGroup (-γ₀)).map (MulAut.conj x).toMonoidHom),
      σ (θ y) = θ y := by
    rw [rootGroup_sup_eq_longSL2_range_minus hirr h01 true t hγ₀]
    exact H1g
  have hH2 : ∀ (a a' : Fin (s + 5 - 1)), a ≠ a' → a ≠ i₀ → a ≠ i₁ → a ≠ c₀ → a' ≠ i₀ →
      a' ≠ i₁ → a' ≠ c₀ → ∀ (s' t' : Bool) {γ : Fin (s + 5 - 1) → ℤ},
        toStdB (s + 5 - 1) γ = Pi.single a (boolSign s') + Pi.single a' (boolSign t') →
          ∀ y ∈ ((minusDatum (s + 5) hirr).rootGroup γ).map (MulAut.conj x).toMonoidHom,
            σ (θ y) = θ y := by
    intro a b hab ha0 ha1 hac hb0 hb1 hbc s' t' γ hγ y hy
    have hXγ : (minusDatum (s + 5) hirr).rootGroup γ =
        ((minusFrame (s + 5) (minusCoeffs p f).1 (minusCoeffs p f).2).longRoot hab s' t').range :=
      minusRootGroup_eq_long (s + 5) hirr hab s' t' hγ
    rw [hXγ] at hy
    obtain ⟨g, ⟨c, rfl⟩, rfl⟩ := hy
    exact H2g a b hab (fun h => ha0 (Fin.ext h)) (fun h => ha1 (Fin.ext h))
      (fun h => hac (Fin.ext h)) (fun h => hb0 (Fin.ext h)) (fun h => hb1 (Fin.ext h))
      (fun h => hbc (Fin.ext h)) s' t' (Multiplicative.toAdd c)
  have hH3 : ∀ y ∈ ((minusDatum (s + 5) hirr).rootGroup γ₁).map (MulAut.conj x).toMonoidHom,
      σ (θ y) ∈ (((minusDatum (s + 5) hirr).rootGroup γ₁).map (MulAut.conj x).toMonoidHom).map
        θ := by
    have hXγ₁ : (minusDatum (s + 5) hirr).rootGroup γ₁ =
        ((minusFrame (s + 5) (minusCoeffs p f).1 (minusCoeffs p f).2).longRoot hjc false
          true).range :=
      minusRootGroup_eq_long (s + 5) hirr hjc false true hγ₁
    rw [hXγ₁]
    exact H3g
  exact ⟨toralNormal_minus_of_normalized_subgroups hp2 hf hK hirr (n := s + 5) (by omega) θ hker σ
      hσ2 hσr h01 hc0 hc1 hj0 hj1 hjc hγ₀ hγ₁ x hH1 hH2 hH3,
    minusLift_of_normalized_subgroups hp2 hf hK hirr (n := s + 5) (by omega) θ hker σ hσ2 hσr h01
      hc0 hc1 hj0 hj1 hjc hγ₀ hγ₁ x hH1 hH2 hH3⟩

theorem toralNormal_minus_of_chain_long (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {u : ℕ} {X : Type}
    [Group X]
    (θ : spinGroup (quadMinus (u + 3 + 5) (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadMinus (u + 3 + 5) (GaloisField p f)
      (minusCoeffs p f).1 (minusCoeffs p f).2)))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {R : ℕ → Subgroup (spinGroup (quadMinus (u + 3 + 5) (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2))}
    {Rtw RM : Subgroup (spinGroup (quadMinus (u + 3 + 5) (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2))}
    (hRf : ∀ a ≤ u + 3, R a ∈ fundamentalSubgroups .POmegaMinus
      (minusDatum (u + 3 + 5) (minusCoeffs_irr p f)))
    (hRtwf : Rtw ∈ fundamentalSubgroups .POmegaMinus
      (minusDatum (u + 3 + 5) (minusCoeffs_irr p f)))
    (hRMf : RM ∈ fundamentalSubgroups .POmegaMinus (minusDatum (u + 3 + 5) (minusCoeffs_irr p f)))
    (hadj : ∀ a < u + 3, ModelAdj (Subgroup.center _) (R a) (R (a + 1)))
    (hlin : ∀ a < u + 3, ∃ W, LinearBlockStandardPair (GaloisField p f) W (R a) (R (a + 1)))
    (hcomm : ∀ a b, a + 1 < b → b ≤ u + 3 → Commutes (R a) (R b))
    (hM : ∀ a ≤ u + 3, Commutes RM (R a))
    (hadjtw : ModelAdj (Subgroup.center _) (R (u + 2)) Rtw)
    (hcommtw : ∀ a, a ≤ u + 1 → Commutes (R a) Rtw) (hcommtw' : Commutes (R (u + 3)) Rtw)
    (hne : Rtw ≠ R (u + 3))
    (hfix : ∀ a, 1 ≤ a → a ≤ u + 3 → ∀ y ∈ R a, σ (θ y) = θ y)
    (hfixtw : ∀ y ∈ Rtw, σ (θ y) = θ y) (hfixM : ∀ y ∈ RM, σ (θ y) = θ y)
    (hnorm0 : ∀ y ∈ R 0, σ (θ y) ∈ (R 0).map θ) :
    ((∃ k₀ v, MinusToral (minusCoeffs_irr p f) θ σ k₀ v) ∨
      (∃ k₀ v, MinusOuter (minusCoeffs_irr p f) θ σ k₀ v)) ∧ MinusLift θ σ := by
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h
      simp at hq
    · exact h
  have hadm : StatedLieAdmissible .POmegaMinus (u + 3 + 5) p f :=
    ⟨Fact.out, hf1, by show 4 ≤ u + 3 + 5; omega⟩
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have : Invertible (2 : GaloisField p f) := invertibleOfNonzero h2
  have cq := Exotic.centralQuot_minus hp2 hq hadm
  have hdim : 9 ≤ Module.finrank (GaloisField p f)
      (Fin (u + 3 + 5 - 1) ⊕ Fin (u + 3 + 5 - 1) ⊕ Fin 2 → GaloisField p f) := by
    rw [finrank_minus p f _ (by omega)]
    omega
  have hQ : (quadMinus (u + 3 + 5) (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_quadMinus_of_finite _ (GaloisField p f) (minusCoeffs_irr p f))
  obtain ⟨hdist, htwin⟩ := chain_distinct_twin_gen hp2 hq hdim cq hRf hRtwf hadj hcomm hadjtw
    hcommtw hcommtw'
  obtain ⟨x, hxR, hxtw, t, hxM⟩ := spin_chain_recognition_gen hp2 hq hQ (s := u + 3) (by omega)
    (minusFrame (u + 3 + 5) (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame hdim cq hRf hRtwf
    hRMf hadj hlin hcomm hM hdist hne htwin
  exact toralNormal_minus_of_frame_chain hp2 hq (s := u + 3) (by omega) θ hker σ hσ2 hσr x t hxR
    hxtw hxM hfix hfixtw hfixM hnorm0

end Main

end CFSG.ClassicalInvolution.RouteD.Gaps
