module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClD4Sit
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClOThree
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneD4Sign

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction (Points pointMk pointMk_submodule)
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.D4
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat signMat_mul_self
  commute_signMat_iff mul_conj_mul_inv commute_compInd_compl)
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K] {w : Fin (2 * 4) → K} (hw : ∀ i, w i ≠ 0)

theorem ClO.d4_klein_false (hK : ringChar K ≠ 2)
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    {t y : MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))}
    (h : ClO.D4Sit (oQ (diagGL hw)) t Ro y) {a b c : Fin (2 * 4)} (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) (hs₁ : signGL K {a, b} ∈ matrixDerived (oQ (diagGL hw)))
    (hs₂ : signGL K {b, c} ∈ matrixDerived (oQ (diagGL hw)))
    (hy₁ : y (projH _ ⟨signGL K {a, b}, hs₁⟩) = projH _ ⟨signGL K {a, b}, hs₁⟩)
    (hy₂ : y (projH _ ⟨signGL K {b, c}, hs₂⟩) = projH _ ⟨signGL K {b, c}, hs₂⟩) : False := by
  have hMc : 3 ≤ ({a, b, c} : Finset (Fin (2 * 4)))ᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_insert_of_notMem (by simp [hab, hac]),
      Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
    omega
  obtain ⟨L, v, hL, hv⟩ := exists_point_off hw hK hMc
  set H := closure ({projH _ ⟨signGL K {a, b}, hs₁⟩, projH _ ⟨signGL K {b, c}, hs₂⟩} :
    Set (StatedProj (matrixDerived (oQ (diagGL hw))))) with hH
  have hHL : H ≤ subStab (oQ (diagGL hw)) L.val := by
    rw [hH, closure_le, hL]
    rintro _ (rfl | rfl)
    · exact sign_mem_subStab_span hw hs₁ fun i hi => hv i (by simp at hi ⊢; tauto)
    · exact sign_mem_subStab_span hw hs₂ fun i hi => hv i (by simp at hi ⊢; tauto)
  have htri := h.geom y (ClSp.odd_orderOf_of_mem h.odd h.mem) h.move
  obtain ⟨W, hW, hHW⟩ := htri.exists_ts_of_pt (fix_pair hw hy₁ hy₂) hHL
  exact not_klein_invariant hK hw hW hab hbc hac
    (signMat_mulVec_mem hw hs₁ (hHW (subset_closure (Or.inl rfl))))
    (signMat_mulVec_mem hw hs₂ (hHW (subset_closure (Or.inr rfl))))

theorem ClO.d4_sign_false_comp (hK : ringChar K ≠ 2) {J : Finset (Fin (2 * 4))}
    (hNF : CFSG.ComponentClassification.Burgoyne.O.BlockNF w Jᶜ) (hK3 : Nat.card K ≠ 3)
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    {y : MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))}
    (h : ClO.D4Sit (oQ (diagGL hw)) (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J)) Ro y) :
    False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hHeq : matrixDerived (oQ (diagGL hw)) =
      ⁅CatalogueBGraphForm.isometryGroup (2 * 4) K (diagGL hw),
      CatalogueBGraphForm.isometryGroup (2 * 4) K (diagGL hw)⁆ :=
    matrixDerived_oQ h2 (diagGL hw) (diagGL_transpose hw)
  have h3 : 3 ≤ Jᶜ.card := by
    obtain ⟨I₀, hI₀, hI₀3, -, -⟩ := hNF
    exact hI₀3.trans (Finset.card_le_card hI₀)
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hwab, hwac⟩ := hNF.exists_triple
  have hwbc : w b = w c := hwab.symm.trans hwac
  have hs₁ := signGL_pair_mem_derived h2 hw hab hwab
  have hs₂ := signGL_pair_mem_derived h2 hw hbc hwbc
  set φ := (matrixDerivedConjugation (oQ (diagGL hw)) (sgnPair h2 hw J)).toMonoidHom with hφ
  have hφc : ∀ Y : matrixDerived (oQ (diagGL hw)),
      ((φ Y : matrixDerived (oQ (diagGL hw))) : GL (Fin (2 * 4)) K) =
      signGL K J * Y * (signGL K J)⁻¹ := fun Y => coe_conj_linPair _ _ Y
  have hF₀H : oBlock K hw Jᶜ ≤ matrixDerived (oQ (diagGL hw)) := by rw [hHeq]; exact oBlock_le hw Jᶜ
  have hfix : ∀ X (hX : X ∈ oBlock K hw Jᶜ), y (projH _ ⟨X, hF₀H hX⟩) = projH _ ⟨X, hF₀H hX⟩ := by
    intro X hX
    refine ClO.fix_of_compData h.inj h.odd h.comm h.norm φ
      (matrixDerivedConjugation (oQ (diagGL hw)) (sgnPair h2 hw J)).injective
      (fun Y => kappa_lift _ Y) hF₀H (fun X hX => ?_)
      (fun g hg X hX => ?_) (oBlock_componentData hK hw h3 fun h => hK3 h.1) h.mem hX
    · apply Subtype.ext
      rw [hφc, signGL_inv]
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, coe_signGL, commute_signMat_of_mem_oIsoBlock h2 hw
        (Or.inr rfl) (oBlock_le_oIsoBlock hw _ hX), Matrix.mul_assoc, signMat_mul_self,
        Matrix.mul_one]
    · have hgc : signMat K J * ((g : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) =
          ((g : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) * signMat K J := by
        have e := congrArg (fun Z : matrixDerived (oQ (diagGL hw)) => ((Z : GL (Fin (2 * 4)) K) :
          Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)) hg
        change ((φ g : matrixDerived (oQ (diagGL hw))) : GL (Fin (2 * 4)) K).val = _ at e
        rw [hφc, signGL_inv, Units.val_mul, Units.val_mul, coe_signGL] at e
        calc signMat K J * ((g : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) =
            (signMat K J * ((g : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *
              signMat K J) * signMat K J := by
              rw [Matrix.mul_assoc _ (signMat K J), signMat_mul_self, Matrix.mul_one]
          _ = _ := by rw [e]
      have hgI : (g : GL (Fin (2 * 4)) K) ∈ CatalogueBGraphForm.isometryGroup (2 * 4) K
          (diagGL hw) := Subgroup.commutator_le_self _ (by rw [← hHeq]; exact g.2)
      exact conj_mem_oBlock hw hgI
        (commute_compInd_compl ((commute_signMat_iff h2 J _).1 hgc)) hX
  exact ClO.d4_klein_false hw hK h hab hbc hac hs₁ hs₂
    (hfix _ (signGL_pair_mem_oBlock hw ha hb hab hwab))
    (hfix _ (signGL_pair_mem_oBlock hw hb hc hbc hwbc))

theorem ClO.d4_sign_false_three (hK : ringChar K ≠ 2) (h3 : Nat.card K = 3)
    {J : Finset (Fin (2 * 4))} (hNF : CFSG.ComponentClassification.Burgoyne.O.BlockNF w Jᶜ)
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    {y : MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))}
    (h : ClO.D4Sit (oQ (diagGL hw)) (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J)) Ro y) :
    False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hwab, hwac⟩ := hNF.exists_triple
  have hs₁ := signGL_pair_mem_derived h2 hw hab hwab
  set e := projH (matrixDerived (oQ (diagGL hw))) ⟨signGL K {a, b}, hs₁⟩ with he
  have hee : e * e = 1 := by
    rw [he, ← map_mul]
    convert map_one (projH (matrixDerived (oQ (diagGL hw))))
    apply Subtype.ext
    exact Units.ext (signMat_mul_self _)
  have hwbc : w b = w c := hwab.symm.trans hwac
  have hJa : a ∉ J := Finset.mem_compl.1 ha
  have hJb : b ∉ J := Finset.mem_compl.1 hb
  have hJc : c ∉ J := Finset.mem_compl.1 hc
  obtain ⟨hi1, hi2, hi3, hi4⟩ := ClO.cycle_inv_apply hab hac hbc
  have hρJ : ∀ x, (⁅Equiv.swap a b, Equiv.swap a c⁆)⁻¹ x ∈ J ↔ x ∈ J := by
    intro x
    by_cases hxa : x = a
    · subst hxa; rw [hi1]; exact ⟨fun h => absurd h hJc, fun h => absurd h hJa⟩
    by_cases hxb : x = b
    · subst hxb; rw [hi2]; exact ⟨fun h => absurd h hJa, fun h => absurd h hJb⟩
    by_cases hxc : x = c
    · subst hxc; rw [hi3]; exact ⟨fun h => absurd h hJb, fun h => absurd h hJc⟩
    rw [hi4 x hxa hxb hxc]
  have hba := hab.symm
  have hca := hac.symm
  have hcb := hbc.symm
  have hn := ClO.conj_mem_of_cycle hK hw h.norm (ClO.cycle_cube hab hac hbc) hρJ
    (ClO.permGL_cycle_mem (K := K) h2 hw hwab hwac) (M := {b, c}) (M' := {a, b})
    (signGL_pair_mem_derived h2 hw hbc hwbc) (by
      intro x
      by_cases hxa : x = a
      · subst hxa; rw [hi1]; simp_all
      by_cases hxb : x = b
      · subst hxb; rw [hi2]; simp_all
      by_cases hxc : x = c
      · subst hxc; rw [hi3]; simp_all
      rw [hi4 x hxa hxb hxc]
      simp [hxa, hxb])
  have hen : ∀ r ∈ Ro, MulAut.conj e * r * (MulAut.conj e)⁻¹ ∈ Ro := by
    intro r hr
    rw [he, ← oκ_sgnPair_eq_conj hw h2 hs₁]
    exact hn r hr
  obtain ⟨y', h', hy'e⟩ := h.exists_commute hee hen
  have hfix : y' e = e := by
    apply h'.inj
    rw [← mul_conj_mul_inv, ← hy'e, mul_inv_cancel_right]
  have hMc : 3 ≤ ({a, b} : Finset (Fin (2 * 4)))ᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_insert_of_notMem (by simp [hab]),
      Finset.card_singleton]
    omega
  obtain ⟨L, v, hL, hv⟩ := exists_point_off hw hK hMc
  set H := closure ({e} : Set (StatedProj (matrixDerived (oQ (diagGL hw))))) with hH
  have hHL : H ≤ subStab (oQ (diagGL hw)) L.val := by
    rw [hH, closure_le, hL, Set.singleton_subset_iff]
    exact sign_mem_subStab_span hw hs₁ hv
  have htri := h'.geom y' (ClSp.odd_orderOf_of_mem h'.odd h'.mem) h'.move
  obtain ⟨W, hW, hHW⟩ := htri.exists_ts_of_pt
    (fix_closure (by rintro _ rfl; exact hfix)) hHL
  refine not_aniso_invariant hK hw hW hab (fun x y hxy => ?_)
    (signMat_mulVec_mem hw hs₁ (hHW (subset_closure rfl)))
  rw [hwab, ← mul_add] at hxy
  exact eq_zero_of_sq_add_sq_three h3 hK ((mul_eq_zero.1 hxy).resolve_left (hw b))

theorem ClO.d4_sign_false (hK : ringChar K ≠ 2) {J : Finset (Fin (2 * 4))}
    (hNF : CFSG.ComponentClassification.Burgoyne.O.BlockNF w Jᶜ)
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    {y : MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))}
    (h : ClO.D4Sit (oQ (diagGL hw)) (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J)) Ro y) :
    False := by
  by_cases h3 : Nat.card K = 3
  · exact ClO.d4_sign_false_three hw hK h3 hNF h
  · exact ClO.d4_sign_false_comp hw hK hNF h3 h

end CFSG.ComponentClassification.Foote5.OddLieCore
