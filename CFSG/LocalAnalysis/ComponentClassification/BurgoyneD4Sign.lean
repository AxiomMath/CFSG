module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneD4SignGeom
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOInnerNF
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneD4Fix
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneD4Tri
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOThree

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.D4

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction (Points pointMk pointMk_submodule)
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat signMat_mul_self
  commute_signMat_iff mul_conj_mul_inv commute_compInd_compl)

variable {K : Type} [Field K]

section SignElements

variable {d : ℕ} {w : Fin d → K} (hw : ∀ i, w i ≠ 0)

theorem sign_mem_subStab_span {M : Finset (Fin d)}
    (hM : signGL K M ∈ matrixDerived (oQ (diagGL hw))) {v : Fin d → K} (hv : ∀ i ∈ M, v i = 0) :
    projH _ ⟨signGL K M, hM⟩ ∈ subStab (oQ (diagGL hw)) (Submodule.span K {v}) := by
  rw [proj_mem_subStab_iff, Submodule.map_span, Set.image_singleton]
  congr 1
  rw [Set.singleton_eq_singleton_iff]
  change (signGL K M : Matrix (Fin d) (Fin d) K) *ᵥ v = v
  rw [coe_signGL]
  exact signMat_mulVec_of_disjoint hv

theorem signMat_mulVec_mem {M : Finset (Fin d)}
    (hM : signGL K M ∈ matrixDerived (oQ (diagGL hw))) {W : Submodule K (Fin d → K)}
    (h : projH _ ⟨signGL K M, hM⟩ ∈ subStab (oQ (diagGL hw)) W) :
    ∀ v ∈ W, signMat K M *ᵥ v ∈ W := by
  intro v hv
  rw [proj_mem_subStab_iff] at h
  rw [← h]
  exact ⟨v, hv, rfl⟩

theorem oκ_sgnPair_eq_conj (h2 : (2 : K) ≠ 0) {M : Finset (Fin d)}
    (hM : signGL K M ∈ matrixDerived (oQ (diagGL hw))) :
    oκ _ (sgnPair h2 hw M) = MulAut.conj (projH _ ⟨signGL K M, hM⟩) :=
  oκ_linPair_eq_conj _ hM

theorem exists_point_off [Finite K] (hK : ringChar K ≠ 2) {M : Finset (Fin d)}
    (hM : 3 ≤ Mᶜ.card) :
    ∃ L : Points (oQ (diagGL hw)), ∃ v : Fin d → K, L.val = Submodule.span K {v} ∧
      ∀ i ∈ M, v i = 0 := by
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card.1 (by omega : 2 < Mᶜ.card)
  obtain ⟨v, hv0, hvs, hQ⟩ := exists_singular_on hK hw hxy hxz hyz
  refine ⟨pointMk v hv0 hQ, v, pointMk_submodule v hv0 hQ, fun i hi => hvs i ?_ ?_ ?_⟩ <;>
    rintro rfl <;> simp_all

end SignElements

variable [Finite K] {w : Fin (2 * 4) → K} (hw : ∀ i, w i ≠ 0)

omit [Finite K] in
theorem fix_pair {y : MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))}
    {x x' : StatedProj (matrixDerived (oQ (diagGL hw)))} (hx : y x = x) (hx' : y x' = x') :
    ∀ z ∈ closure ({x, x'} : Set _), y z = z :=
  fix_closure (by rintro _ (rfl | rfl) <;> assumption)

theorem klein_false (hK : ringChar K ≠ 2)
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    {t y : MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))}
    (h : Sit (oQ (diagGL hw)) B t y) {a b c : Fin (2 * 4)} (hab : a ≠ b) (hbc : b ≠ c)
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
  have htri := h.geom y (odd_orderOf_of_mem_oddCoreIn h.core) h.move
  obtain ⟨W, hW, hHW⟩ := htri.exists_ts_of_pt (fix_pair hw hy₁ hy₂) hHL
  exact not_klein_invariant hK hw hW hab hbc hac
    (signMat_mulVec_mem hw hs₁ (hHW (subset_closure (Or.inl rfl))))
    (signMat_mulVec_mem hw hs₂ (hHW (subset_closure (Or.inr rfl))))

theorem sign_false_comp (hK : ringChar K ≠ 2) {J : Finset (Fin (2 * 4))}
    (hNF : CFSG.ComponentClassification.Burgoyne.O.BlockNF w Jᶜ) (hK3 : Nat.card K ≠ 3)
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    {y : MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))}
    (h : Sit (oQ (diagGL hw)) B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J)) y) : False := by
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
    refine fix_of_compData h.inj h.inn φ (fun Y => kappa_lift _ Y) hF₀H (fun X hX => ?_)
      (fun g hg X hX => ?_) (oBlock_componentData hK hw h3 fun h => hK3 h.1) h.core hX
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
  exact klein_false hw hK h hab hbc hac hs₁ hs₂
    (hfix _ (signGL_pair_mem_oBlock hw ha hb hab hwab))
    (hfix _ (signGL_pair_mem_oBlock hw hb hc hbc hwbc))

theorem eq_zero_of_sq_add_sq_three (h3 : Nat.card K = 3) (hK : ringChar K ≠ 2) {x y : K}
    (h : x ^ 2 + y ^ 2 = 0) : x = 0 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have h1 : (1 : K) ≠ -1 := fun e => h2 (by linear_combination e)
  have huniv : ({0, 1, -1} : Finset K) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem (by simp [eq_comm]),
      Finset.card_insert_of_notMem (by simpa using h1), Finset.card_singleton,
      ← Nat.card_eq_fintype_card, h3]
  have hsq : ∀ z : K, z ^ 2 = 0 ∨ z ^ 2 = 1 := by
    intro z
    have hz : z ∈ ({0, 1, -1} : Finset K) := huniv ▸ Finset.mem_univ z
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> norm_num
  by_contra hx
  rcases hsq x with hx2 | hx2
  · exact hx (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hx2)
  · rcases hsq y with hy2 | hy2
    · rw [hx2, hy2] at h
      simp at h
    · rw [hx2, hy2] at h
      exact h2 (by linear_combination h)

theorem sign_false_three (hK : ringChar K ≠ 2) (h3 : Nat.card K = 3) {J : Finset (Fin (2 * 4))}
    (hNF : CFSG.ComponentClassification.Burgoyne.O.BlockNF w Jᶜ)
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    {y : MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))}
    (h : Sit (oQ (diagGL hw)) B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J)) y) : False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hwab, hwac⟩ := hNF.exists_triple
  have hs₁ := signGL_pair_mem_derived h2 hw hab hwab
  set e := projH (matrixDerived (oQ (diagGL hw))) ⟨signGL K {a, b}, hs₁⟩ with he
  have hee : e * e = 1 := by
    rw [he, ← map_mul]
    convert map_one (projH (matrixDerived (oQ (diagGL hw))))
    apply Subtype.ext
    exact Units.ext (signMat_mul_self _)
  have het : MulAut.conj e * oκ _ (sgnPair h2 hw J) = oκ _ (sgnPair h2 hw J) * MulAut.conj e := by
    rw [he, ← oκ_sgnPair_eq_conj hw h2 hs₁, ← map_mul, ← map_mul, sgnPair_comm]
  obtain ⟨y', h', hy'e⟩ := h.exists_commute hee het
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
  have htri := h'.geom y' (odd_orderOf_of_mem_oddCoreIn h'.core) h'.move
  obtain ⟨W, hW, hHW⟩ := htri.exists_ts_of_pt
    (fix_closure (by rintro _ rfl; exact hfix)) hHL
  refine not_aniso_invariant hK hw hW hab (fun x y hxy => ?_)
    (signMat_mulVec_mem hw hs₁ (hHW (subset_closure rfl)))
  rw [hwab, ← mul_add] at hxy
  exact eq_zero_of_sq_add_sq_three h3 hK ((mul_eq_zero.1 hxy).resolve_left (hw b))

theorem sign_false (hK : ringChar K ≠ 2) {J : Finset (Fin (2 * 4))}
    (hNF : CFSG.ComponentClassification.Burgoyne.O.BlockNF w Jᶜ)
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    {y : MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))}
    (h : Sit (oQ (diagGL hw)) B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J)) y) : False := by
  by_cases h3 : Nat.card K = 3
  · exact sign_false_three hw hK h3 hNF h
  · exact sign_false_comp hw hK hNF h3 h

end CFSG.ComponentClassification.Burgoyne.D4
