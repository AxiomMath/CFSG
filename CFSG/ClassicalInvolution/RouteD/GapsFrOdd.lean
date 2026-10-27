module

public import CFSG.ClassicalInvolution.RouteD.GapsFrBGen
public import CFSG.ClassicalInvolution.RouteD.GapsOrthSpinOdd
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutOddNormalized

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub fundamentalSubgroups)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.CurtisTits (rankOne)
open CFSG.ClassicalInvolution.ModelFacts.OrthAut (toralNormal_odd_of_normalized_subgroups)
open scoped MatrixGroups commutatorElement

section Roots

variable {K : Type} [Field K] {m : ℕ}

theorem rootGroup_sup_eq_longSL2_range_odd {i j : Fin m} (hij : i ≠ j) (s t : Bool)
    {γ : Fin m → ℤ} (hγ : toStdB m γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) :
    (oddDatum m K).rootGroup γ ⊔ (oddDatum m K).rootGroup (-γ) =
      ((oddFrame m K).longSL2 hij s t).range := by
  have hstd' : toStdB m (-γ) = Pi.single j (boolSign (!t)) + Pi.single i (boolSign (!s)) := by
    rw [toStdB_neg, hγ, boolSign_not, boolSign_not, Pi.single_neg, Pi.single_neg, neg_add,
      add_comm]
  rw [longSL2_range_eq_sup]
  congr 1
  · exact oddRootGroup_eq_long hij s t hγ
  · exact oddRootGroup_eq_long hij.symm (!t) (!s) hstd'

theorem rankOne_oddDatum_of_lt {k : Fin m} (hk : k.val + 1 < m) :
    rankOne (oddDatum m K).rootGroup k =
      rootSL2 (oddFrame m K).toHypFrame k.val (k.val + 1) k.isLt hk (by omega) true false := by
  have h : toStdB m (Pi.single k 1) = Pi.single k (boolSign true) +
      Pi.single (⟨k.val + 1, hk⟩ : Fin m) (boolSign false) := by
    rw [toStdB_single_of_lt m hk, boolSign_true, boolSign_false, Pi.single_neg, sub_eq_add_neg]
  exact rootGroup_sup_eq_longSL2_range_odd (i := k) (j := ⟨k.val + 1, hk⟩)
    (Fin.ne_of_val_ne (by simp)) true false (γ := Pi.single k 1) h

end Roots

section Main

variable {p f : ℕ} [Fact p.Prime]

theorem toralNormal_odd_of_frame_chain (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {s : ℕ} (hs : 1 ≤ s)
    {X : Type} [Group X] (θ : spinGroup (quadOdd (s + 4) (GaloisField p f)) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadOdd (s + 4) (GaloisField p f))))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    (x : spinGroup (quadOdd (s + 4) (GaloisField p f))) (t : Bool)
    {R : ℕ → Subgroup (spinGroup (quadOdd (s + 4) (GaloisField p f)))}
    {Rtw RM : Subgroup (spinGroup (quadOdd (s + 4) (GaloisField p f)))}
    (hR : ∀ a (ha : a ≤ s), R a = ((rootSL2 (oddFrame (s + 4) (GaloisField p f)).toHypFrame a
      (a + 1) (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom))
    (hRtw : Rtw = ((rootSL2 (oddFrame (s + 4) (GaloisField p f)).toHypFrame s (s + 1) (by omega)
      (by omega) (by omega) true true).map (MulAut.conj x).toMonoidHom))
    (hRM : RM = ((rootSL2 (oddFrame (s + 4) (GaloisField p f)).toHypFrame (s + 2) (s + 3)
      (by omega) (by omega) (by omega) true t).map (MulAut.conj x).toMonoidHom))
    (hfix : ∀ a, 1 ≤ a → a ≤ s → ∀ y ∈ R a, σ (θ y) = θ y)
    (hfixtw : ∀ y ∈ Rtw, σ (θ y) = θ y) (hfixM : ∀ y ∈ RM, σ (θ y) = θ y)
    (hnorm0 : ∀ y ∈ R 0, σ (θ y) ∈ (R 0).map θ) :
    ∃ (k₀ : spinGroup (quadOdd (s + 4) (GaloisField p f))) (v : Fin (s + 4) → ZMod 2),
      ∀ γ : Fin (s + 4) → ℤ, γ ∈ (oddDatum (s + 4) (GaloisField p f)).roots →
        ((((oddDatum (s + 4) (GaloisField p f)).rootGroup γ ⊔
              (oddDatum (s + 4) (GaloisField p f)).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
          (((oddDatum (s + 4) (GaloisField p f)).rootGroup γ ⊔
              (oddDatum (s + 4) (GaloisField p f)).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ ∧
        ((∀ y ∈ (((oddDatum (s + 4) (GaloisField p f)).rootGroup γ ⊔
              (oddDatum (s + 4) (GaloisField p f)).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ, σ y = y) ↔
          ∑ i, (γ i : ZMod 2) * v i = 0) := by
  classical
  have hm3 : 3 ≤ s + 4 := by omega
  obtain ⟨hf0, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hf : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr hf0
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have hscal : ∀ z ∈ Subgroup.center (spinGroup (quadOdd (s + 4) (GaloisField p f))),
      ∃ η : GaloisField p f, ∀ v, spinAction (quadOdd (s + 4) (GaloisField p f)) z v = η • v := by
    intro z hz
    obtain ⟨c, hc⟩ := mem_scalars.mp (spinAction_center_mem_scalars_odd h2 hm3 hz)
    exact ⟨c, hc⟩
  obtain ⟨H1g, H2g, H3g⟩ := frame_chain_fixed_data hs (oddFrame (s + 4) (GaloisField p f)).toHypFrame
    θ hker σ hscal x t hR hRtw hRM hfix hfixtw hfixM hnorm0
  let i₀ : Fin (s + 4) := ⟨s + 2, by omega⟩
  let i₁ : Fin (s + 4) := ⟨s + 3, by omega⟩
  let c₀ : Fin (s + 4) := ⟨0, by omega⟩
  let jj : Fin (s + 4) := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := fun h => by have := congrArg Fin.val h; simp [i₀, i₁] at this
  have hc0 : c₀ ≠ i₀ := fun h => by have := congrArg Fin.val h; simp [i₀, c₀] at this
  have hc1 : c₀ ≠ i₁ := fun h => by have := congrArg Fin.val h; simp [i₁, c₀] at this
  have hj0 : jj ≠ i₀ := fun h => by have := congrArg Fin.val h; simp [i₀, jj] at this
  have hj1 : jj ≠ i₁ := fun h => by have := congrArg Fin.val h; simp [i₁, jj] at this
  have hjc : c₀ ≠ jj := fun h => by have := congrArg Fin.val h; simp [c₀, jj] at this
  have hγ₀ : toStdB (s + 4) (ofStdB (s + 4) (Pi.single i₀ (boolSign true) +
      Pi.single i₁ (boolSign t))) = Pi.single i₀ (boolSign true) + Pi.single i₁ (boolSign t) :=
    toStdB_ofStdB _ _
  have hγ₁ : toStdB (s + 4) (ofStdB (s + 4) (Pi.single c₀ (boolSign false) +
      Pi.single jj (boolSign true))) = Pi.single c₀ (boolSign false) +
        Pi.single jj (boolSign true) := toStdB_ofStdB _ _
  refine toralNormal_odd_of_normalized_subgroups hp2 hf hK (m := s + 4) (by omega) θ hker σ hσ2
    hσr h01 hc0 hc1 hj0 hj1 hjc hγ₀ hγ₁ x ?_ ?_ ?_
  · rw [rootGroup_sup_eq_longSL2_range_odd h01 true t hγ₀]
    exact H1g
  · intro a b hab ha0 ha1 hac hb0 hb1 hbc s' t' γ hγ y hy
    have hXγ : (oddDatum (s + 4) (GaloisField p f)).rootGroup γ =
        ((oddFrame (s + 4) (GaloisField p f)).longRoot hab s' t').range :=
      oddRootGroup_eq_long hab s' t' hγ
    rw [hXγ] at hy
    obtain ⟨g, ⟨c, rfl⟩, rfl⟩ := hy
    exact H2g a b hab (fun h => ha0 (Fin.ext h)) (fun h => ha1 (Fin.ext h))
      (fun h => hac (Fin.ext h)) (fun h => hb0 (Fin.ext h)) (fun h => hb1 (Fin.ext h))
      (fun h => hbc (Fin.ext h)) s' t' (Multiplicative.toAdd c)
  · have hXγ₁ : (oddDatum (s + 4) (GaloisField p f)).rootGroup
        (ofStdB (s + 4) (Pi.single c₀ (boolSign false) + Pi.single jj (boolSign true))) =
        ((oddFrame (s + 4) (GaloisField p f)).longRoot hjc false true).range :=
      oddRootGroup_eq_long hjc false true hγ₁
    rw [hXγ₁]
    exact H3g


theorem toralNormal_odd_of_chain_long (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {u : ℕ} {X : Type} [Group X]
    (θ : spinGroup (quadOdd (u + 3 + 4) (GaloisField p f)) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadOdd (u + 3 + 4) (GaloisField p f))))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {R : ℕ → Subgroup (spinGroup (quadOdd (u + 3 + 4) (GaloisField p f)))}
    {Rtw RM : Subgroup (spinGroup (quadOdd (u + 3 + 4) (GaloisField p f)))}
    (hRf : ∀ a ≤ u + 3, R a ∈ fundamentalSubgroups .POmegaOdd
      (oddDatum (u + 3 + 4) (GaloisField p f)))
    (hRtwf : Rtw ∈ fundamentalSubgroups .POmegaOdd (oddDatum (u + 3 + 4) (GaloisField p f)))
    (hRMf : RM ∈ fundamentalSubgroups .POmegaOdd (oddDatum (u + 3 + 4) (GaloisField p f)))
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
    ∃ (k₀ : spinGroup (quadOdd (u + 3 + 4) (GaloisField p f)))
      (v : Fin (u + 3 + 4) → ZMod 2),
      ∀ γ : Fin (u + 3 + 4) → ℤ, γ ∈ (oddDatum (u + 3 + 4) (GaloisField p f)).roots →
        ((((oddDatum (u + 3 + 4) (GaloisField p f)).rootGroup γ ⊔
              (oddDatum (u + 3 + 4) (GaloisField p f)).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
          (((oddDatum (u + 3 + 4) (GaloisField p f)).rootGroup γ ⊔
              (oddDatum (u + 3 + 4) (GaloisField p f)).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ ∧
        ((∀ y ∈ (((oddDatum (u + 3 + 4) (GaloisField p f)).rootGroup γ ⊔
              (oddDatum (u + 3 + 4) (GaloisField p f)).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ, σ y = y) ↔
          ∑ i, (γ i : ZMod 2) * v i = 0) := by
  have hm3 : 3 ≤ u + 3 + 4 := by omega
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have : Invertible (2 : GaloisField p f) := invertibleOfNonzero h2
  have cq := centralQuot_odd (m := u + 3 + 4) hp2 hm3 hq
  have hdim : 9 ≤ Module.finrank (GaloisField p f)
      (Fin (u + 3 + 4) ⊕ Fin (u + 3 + 4) ⊕ Unit → GaloisField p f) := by
    rw [finrank_odd]
    omega
  have hQ : (quadOdd (u + 3 + 4) (GaloisField p f)).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_quadOdd (u + 3 + 4) (GaloisField p f) h2)
  obtain ⟨hdist, htwin⟩ := chain_distinct_twin_gen hp2 hq hdim cq hRf hRtwf hadj hcomm hadjtw
    hcommtw hcommtw'
  obtain ⟨x, hxR, hxtw, t, hxM⟩ := spin_chain_recognition_gen hp2 hq hQ (s := u + 3) (by omega)
    (oddFrame (u + 3 + 4) (GaloisField p f)).toHypFrame hdim cq hRf hRtwf hRMf hadj hlin hcomm hM
    hdist hne htwin
  exact toralNormal_odd_of_frame_chain hp2 hq (s := u + 3) (by omega) θ hker σ hσ2 hσr x t hxR
    hxtw hxM hfix hfixtw hfixM hnorm0

end Main

end CFSG.ClassicalInvolution.RouteD.Gaps
