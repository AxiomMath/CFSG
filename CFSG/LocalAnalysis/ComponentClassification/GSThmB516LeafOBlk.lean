module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOGenRefl
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXExcT1
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafOddJ
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10OrthData

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.Orth516

open Matrix CFSG Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat reflGL compInd)
open CFSG.ComponentClassification.Burgoyne.C (blockP oBlock_le_matrixDerived
  commute_sign_of_mem_oIsoBlock)
open CFSG.ComponentClassification.GSThmB.Pump516 (NoCentralInv)
open scoped commutatorElement

variable {K : Type} [Field K] {d : ℕ} {w : Fin d → K} (hw : ∀ i, w i ≠ 0)

theorem signGL_mem_oBlock_of_square {I : Finset (Fin d)} (hI4 : I.card = 4) (hNF : BlockNF w I)
    (hsq : IsSquare (∏ i ∈ I, w i)) : signGL K I ∈ oBlock K hw I := by
  obtain ⟨I₀, hI₀, hI₀3, hI₀w, hns⟩ := hNF
  have hdiff : (I \ I₀).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    rw [Finset.mem_sdiff] at hx hy
    exact hns x hx.1 y hy.1 hx.2 hy.2
  have hI₀c : (I \ I₀).card = I.card - I₀.card := Finset.card_sdiff_of_subset hI₀
  have hI₀le : I₀.card ≤ I.card := Finset.card_le_card hI₀
  by_cases hI₀4 : 4 ≤ I₀.card
  · have hII₀ : I₀ = I := Finset.eq_of_subset_of_card_le hI₀ (by omega)
    exact DX.signGL_mem_oBlock_of_even hw hI₀ hI₀w 2 I (hII₀ ▸ le_rfl) (by omega)
  obtain ⟨e, he⟩ : ∃ e, I \ I₀ = {e} := Finset.card_eq_one.1 (by omega)
  have heI : e ∈ I := (Finset.mem_sdiff.1 (he ▸ Finset.mem_singleton_self e)).1
  have heI₀ : e ∉ I₀ := (Finset.mem_sdiff.1 (he ▸ Finset.mem_singleton_self e)).2
  obtain ⟨a, ha⟩ : I₀.Nonempty := Finset.card_pos.1 (by omega)
  have hae : a ≠ e := fun h => heI₀ (h ▸ ha)
  have hIeq : I = insert e I₀ := by
    ext x
    rw [Finset.mem_insert]
    constructor
    · intro hx
      by_cases hx0 : x ∈ I₀
      · exact Or.inr hx0
      · left
        have : x ∈ I \ I₀ := Finset.mem_sdiff.2 ⟨hx, hx0⟩
        rw [he] at this
        exact Finset.mem_singleton.1 this
    · rintro (rfl | hx)
      · exact heI
      · exact hI₀ hx
  have hprod : ∏ i ∈ I, w i = w a ^ 3 * w e := by
    rw [hIeq, Finset.prod_insert heI₀,
      Finset.prod_congr rfl (fun i hi => hI₀w i hi a ha), Finset.prod_const]
    rw [show I₀.card = 3 by omega]
    ring
  rw [hprod] at hsq
  obtain ⟨t, ht⟩ := hsq
  have hwa := hw a
  have hwe := hw e
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [mul_zero] at ht
    exact mul_ne_zero (pow_ne_zero _ hwa) hwe ht
  have hr0 : t / w a ^ 2 ≠ 0 := div_ne_zero ht0 (pow_ne_zero _ hwa)
  have hwr : w e = (t / w a ^ 2) ^ 2 * w a := by
    field_simp
    linear_combination ht
  have hpair := DX.signGL_pair_mem_oBlock_sq hw (hI₀ ha) heI hae hr0 hwr
  have hrest := DX.signGL_mem_oBlock_of_even hw hI₀ hI₀w 1 (I₀.erase a)
    (Finset.erase_subset _ _) (by rw [Finset.card_erase_of_mem ha]; omega)
  have hdisj : Disjoint ({a, e} : Finset (Fin d)) (I₀.erase a) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (Finset.mem_erase.1 hx').1 rfl
    · exact heI₀ (Finset.mem_of_mem_erase hx')
  have hunion : ({a, e} : Finset (Fin d)) ∪ I₀.erase a = I := by
    rw [hIeq]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]
    constructor
    · rintro ((rfl | rfl) | ⟨-, hx⟩)
      · exact Or.inr ha
      · exact Or.inl rfl
      · exact Or.inr hx
    · rintro (rfl | hx)
      · exact Or.inl (Or.inr rfl)
      · by_cases hxa : x = a
        · exact Or.inl (Or.inl hxa)
        · exact Or.inr ⟨hxa, hx⟩
  have hmul : signGL K I = signGL K {a, e} * signGL K (I₀.erase a) := by
    apply Units.ext
    rw [Units.val_mul, coe_signGL, coe_signGL, coe_signGL, signMat_mul_of_disjoint hdisj, hunion]
  rw [hmul]
  exact mul_mem hpair hrest

theorem central_involution_blockP (h2 : (2 : K) ≠ 0) {I : Finset (Fin d)} (hIn : I.Nonempty)
    (hIc : Iᶜ.Nonempty) (hS : signGL K I ∈ oBlock K hw I) (hZ : NoCentralInv (blockP K hw I)) :
    False := by
  set H := matrixDerived (oQ (diagGL hw)) with hH
  have hSH : signGL K I ∈ H := oBlock_le_matrixDerived hw h2 I hS
  set z := projH H ⟨signGL K I, hSH⟩ with hz
  have hzP : z ∈ blockP K hw I := ⟨⟨signGL K I, hSH⟩, mem_subgroupOf.2 hS, rfl⟩
  have hzz : z * z = 1 := by
    rw [hz, ← map_mul]
    have : (⟨signGL K I, hSH⟩ : H) * ⟨signGL K I, hSH⟩ = 1 :=
      Subtype.ext (Units.ext (by
        rw [Subgroup.coe_mul, Units.val_mul, coe_signGL, PSL.signMat_mul_self]
        rfl))
    rw [this, map_one]
  have hzc : ∀ y ∈ blockP K hw I, z * y = y * z := by
    rintro _ ⟨g, hg, rfl⟩
    rw [hz, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (commute_sign_of_mem_oIsoBlock hw (oBlock_le_oIsoBlock hw I (mem_subgroupOf.1 hg))).symm
  have h1 := hZ z hzP hzc hzz
  exact X10Orth.projH_ne_one (fun c => X10Orth.signGL_ne_scalar h2 hIn hIc c) h1

theorem signMat_pair_mulVec_left {a b : Fin d} (v : Fin d → K) :
    (signMat K {a, b} *ᵥ v) a = -v a := by
  simp [signMat, mulVec_diagonal]

theorem signGL_single_mem_oIsoBlock {I : Finset (Fin d)} {e : Fin d} (he : e ∈ I) :
    signGL K {e} ∈ oIsoBlock K hw I := by
  have : signGL K {e} = reflGL (K := K) e := rfl
  rw [this]
  exact reflGL_mem_oIsoBlock hw he

include hw in
theorem commutator_refl_mulVec_ne (h2 : (2 : K) ≠ 0) {u : Fin d → K} (hu : bil w u u ≠ 0)
    {e a : Fin d} (hae : a ≠ e) (hue : u e ≠ 0) (hua : u a ≠ 0) :
    ((⁅signGL K {e}, reflGLv w hu⁆ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ
      Pi.single e 1 ≠ Pi.single e 1 := by
  intro h
  set A : Matrix (Fin d) (Fin d) K := signMat K {e} with hA
  set B : Matrix (Fin d) (Fin d) K := reflM w u with hB
  have hAA : A * A = 1 := PSL.signMat_mul_self _
  have hBB : B * B = 1 := reflM_mul_self w hu
  have hg : ((⁅signGL K {e}, reflGLv w hu⁆ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      A * B * A * B := by
    rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul, signGL_inv,
      reflGLv_inv, coe_signGL, coe_reflGLv]
  rw [hg] at h
  have key : A *ᵥ (B *ᵥ Pi.single e 1) = B *ᵥ (A *ᵥ Pi.single e 1) := by
    have h' := congrArg (fun v => B *ᵥ (A *ᵥ v)) h
    simp only [mulVec_mulVec] at h'
    have e1 : B * (A * (A * B * A * B)) = A * B := by
      calc B * (A * (A * B * A * B)) = B * ((A * A) * B) * A * B := by
            simp only [Matrix.mul_assoc]
        _ = (B * B) * A * B := by rw [hAA, Matrix.one_mul]
        _ = A * B := by rw [hBB, Matrix.one_mul]
    rw [e1] at h'
    rw [mulVec_mulVec, mulVec_mulVec]
    exact h'
  have hAe : A *ᵥ Pi.single e 1 = -Pi.single e 1 := by
    funext j
    by_cases hj : j = e
    · subst hj
      simp [hA, signMat, mulVec_diagonal]
    · simp [hA, signMat, mulVec_diagonal, hj]
  rw [hAe, mulVec_neg] at key
  have ka := congrFun key a
  have hAa : ∀ v : Fin d → K, (A *ᵥ v) a = v a := fun v => by
    simp [hA, signMat, mulVec_diagonal, hae]
  rw [hAa, Pi.neg_apply, hB, reflM_mulVec, Pi.sub_apply, Pi.smul_apply,
    Pi.single_eq_of_ne hae, smul_eq_mul, zero_sub, neg_neg] at ka
  have hbil : bil w u (Pi.single e 1) = u e * w e := by
    rw [bil_eq_sum, Finset.sum_eq_single e (fun i _ hi => by simp [hi]) (by simp)]
    simp
  rw [hbil] at ka
  have h0 : (2 / bil w u u * (u e * w e)) * u a = 0 := by
    have : (2 : K) * ((2 / bil w u u * (u e * w e)) * u a) = 0 := by linear_combination -ka
    exact (mul_eq_zero.1 this).resolve_left h2
  rcases mul_eq_zero.1 h0 with h0 | h0
  · rcases mul_eq_zero.1 h0 with h0 | h0
    · exact div_ne_zero h2 hu h0
    · exact mul_ne_zero hue (hw e) h0
  · exact hua h0

theorem bil_add_left' (w x y z : Fin d → K) :
    bil w (x + y) z = bil w x z + bil w y z := by
  simp only [bil, add_dotProduct]

theorem bil_add_right' (w x y z : Fin d → K) : bil w x (y + z) = bil w x y + bil w x z := by
  simp only [bil, mulVec_add, dotProduct_add]

theorem bil_single_single (w : Fin d → K) (a b : Fin d) :
    bil w (Pi.single a 1) (Pi.single b 1) = if a = b then w a else 0 := by
  rw [bil_eq_sum]
  by_cases hab : a = b
  · subst hab
    rw [Finset.sum_eq_single a (fun i _ hi => by simp [hi]) (by simp)]
    simp
  · rw [ite_eq_right_iff.2 (fun h => absurd h hab), Finset.sum_eq_zero]
    intro i _
    by_cases hia : i = a
    · subst hia
      simp [hab]
    · simp [hia]

theorem eq_zero_of_fixed (h2 : (2 : K) ≠ 0) {I : Finset (Fin d)} (hNF : BlockNF w I)
    {v : Fin d → K} (hvI : ∀ i, i ∉ I → v i = 0)
    (hfix : ∀ g : GL (Fin d) K, g ∈ oBlock K hw I → (g : Matrix (Fin d) (Fin d) K) *ᵥ v = v) :
    v = 0 := by
  obtain ⟨I₀, hI₀, hI₀3, hI₀w, hns⟩ := hNF
  have hv₀ : ∀ a ∈ I₀, v a = 0 := by
    intro a ha
    obtain ⟨b, hb, hba⟩ : ∃ b ∈ I₀, b ≠ a := by
      obtain ⟨b, hb⟩ := Finset.card_pos.1 (by
        have := Finset.pred_card_le_card_erase (s := I₀) (a := a); omega :
          0 < (I₀.erase a).card)
      exact ⟨b, (Finset.mem_erase.1 hb).2, (Finset.mem_erase.1 hb).1⟩
    have hS := signGL_pair_mem_oBlock hw (hI₀ ha) (hI₀ hb) (Ne.symm hba) (hI₀w a ha b hb)
    have e := congrFun (hfix _ hS) a
    rw [coe_signGL, signMat_pair_mulVec_left] at e
    have : (2 : K) * v a = 0 := by linear_combination -e
    exact (mul_eq_zero.1 this).resolve_left h2
  by_contra hv0
  obtain ⟨e, hve⟩ : ∃ e, v e ≠ 0 := by
    by_contra hall
    exact hv0 (funext fun i => by_contra fun h => hall ⟨i, h⟩)
  have heI : e ∈ I := by
    by_contra h
    exact hve (hvI e h)
  have heI₀ : e ∉ I₀ := fun h => hve (hv₀ e h)
  have hvform : v = v e • Pi.single e 1 := by
    funext j
    by_cases hj : j = e
    · subst hj
      simp
    · rw [Pi.smul_apply, Pi.single_eq_of_ne hj, smul_zero]
      by_cases hjI : j ∈ I
      · by_cases hjI₀ : j ∈ I₀
        · exact hv₀ j hjI₀
        · exact absurd (hns j hjI e heI hjI₀ heI₀) hj
      · exact hvI j hjI
  have hfixe : ∀ g : GL (Fin d) K, g ∈ oBlock K hw I →
      (g : Matrix (Fin d) (Fin d) K) *ᵥ Pi.single e 1 = Pi.single e 1 := by
    intro g hg
    have h1 := hfix g hg
    rw [hvform, mulVec_smul] at h1
    have := congrArg (fun y => (v e)⁻¹ • y) h1
    simp only [smul_smul, inv_mul_cancel₀ hve, one_smul] at this
    exact this
  obtain ⟨a, ha⟩ : I₀.Nonempty := Finset.card_pos.1 (by omega)
  have hae : a ≠ e := fun h => heI₀ (h ▸ ha)
  obtain ⟨u, huI, hue, hua, hu⟩ : ∃ u : Fin d → K, (∀ i, i ∉ I → u i = 0) ∧ u e ≠ 0 ∧ u a ≠ 0 ∧
      bil w u u ≠ 0 := by
    by_cases hsum : w a + w e = 0
    · obtain ⟨b, hb, hba⟩ : ∃ b ∈ I₀, b ≠ a := by
        obtain ⟨b, hb⟩ := Finset.card_pos.1 (by
          have := Finset.pred_card_le_card_erase (s := I₀) (a := a); omega :
            0 < (I₀.erase a).card)
        exact ⟨b, (Finset.mem_erase.1 hb).2, (Finset.mem_erase.1 hb).1⟩
      have hbe : b ≠ e := fun h => heI₀ (h ▸ hb)
      refine ⟨Pi.single a 1 + Pi.single b 1 + Pi.single e 1, fun i hi => ?_, ?_, ?_, ?_⟩
      · have hia : i ≠ a := fun h => hi (h ▸ hI₀ ha)
        have hib : i ≠ b := fun h => hi (h ▸ hI₀ hb)
        have hie : i ≠ e := fun h => hi (h ▸ heI)
        simp [hia, hib, hie]
      · simp [hae.symm, hbe.symm]
      · simp [hba.symm, hae]
      · have hwb : w b = w a := hI₀w b hb a ha
        simp only [bil_add_left', bil_add_right', bil_single_single, ite_true,
          hba, hba.symm, hae, hae.symm, hbe, hbe.symm, ite_false]
        rw [hwb, show w e = -w a by linear_combination hsum]
        intro h0
        apply hw a
        linear_combination h0
    · refine ⟨Pi.single a 1 + Pi.single e 1, fun i hi => ?_, ?_, ?_, ?_⟩
      · have hia : i ≠ a := fun h => hi (h ▸ hI₀ ha)
        have hie : i ≠ e := fun h => hi (h ▸ heI)
        simp [hia, hie]
      · simp [hae.symm]
      · simp [hae]
      · simp only [bil_add_left', bil_add_right', bil_single_single, ite_true,
          hae, hae.symm, ite_false]
        intro h0
        apply hsum
        linear_combination h0
  have hmem : ⁅signGL K {e}, reflGLv w hu⁆ ∈ oBlock K hw I :=
    commutator_mem_commutator (signGL_single_mem_oIsoBlock hw heI)
      (reflGLv_mem_oIsoBlock hw hu huI)
  exact commutator_refl_mulVec_ne hw h2 hu hae hue hua (hfixe _ hmem)

theorem isolated_of_commute (h2 : (2 : K) ≠ 0) {I I₀ : Finset (Fin d)} (hI₀ : I₀ ⊆ I)
    (hI₀3 : 3 ≤ I₀.card) (hI₀w : ∀ i ∈ I₀, ∀ j ∈ I₀, w i = w j) {D : Matrix (Fin d) (Fin d) K}
    (hD : ∀ g : GL (Fin d) K, g ∈ oBlock K hw I →
      D * (g : Matrix (Fin d) (Fin d) K) = (g : Matrix (Fin d) (Fin d) K) * D)
    {x y : Fin d} (hxy : x ≠ y) (hxI : x ∈ I₀ ∨ y ∈ I₀) : D x y = 0 := by
  refine offDiag_eq_zero_of_commute_sign_on h2 hI₀3 (fun i hi j hj hij => ?_) hxy hxI
  have hS := signGL_pair_mem_oBlock hw (hI₀ hi) (hI₀ hj) hij (hI₀w i hi j hj)
  have := hD _ hS
  rwa [coe_signGL] at this

theorem mul_self_apply_of_isolated {D : Matrix (Fin d) (Fin d) K} {a : Fin d}
    (h : ∀ y, y ≠ a → D a y = 0) : (D * D) a a = D a a ^ 2 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a (fun y _ hy => by rw [h y hy, zero_mul])
    (by simp), sq]

theorem isSquare_of_commute (h2 : (2 : K) ≠ 0) {I : Finset (Fin d)} (hNF : BlockNF w I)
    {D : Matrix (Fin d) (Fin d) K} {c : K} (hDD : D * D = c • 1)
    (hD : ∀ g : GL (Fin d) K, g ∈ oBlock K hw I →
      D * (g : Matrix (Fin d) (Fin d) K) = (g : Matrix (Fin d) (Fin d) K) * D) : IsSquare c := by
  obtain ⟨I₀, hI₀, hI₀3, hI₀w, -⟩ := hNF
  obtain ⟨a, ha⟩ : I₀.Nonempty := Finset.card_pos.1 (by omega)
  have h := mul_self_apply_of_isolated (D := D) (a := a)
    fun y hy => isolated_of_commute hw h2 hI₀ hI₀3 hI₀w hD (Ne.symm hy) (Or.inl ha)
  rw [hDD] at h
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
  exact ⟨D a a, by rw [h, sq]⟩

theorem false_of_skew_commute (h2 : (2 : K) ≠ 0) {I : Finset (Fin d)} (hNF : BlockNF w I)
    {D : Matrix (Fin d) (Fin d) K} {c : K} (hc : c ≠ 0) (hDD : D * D = c • 1)
    (hskew : Dᵀ * diagonal w = (-1 : K) • (diagonal w * D))
    (hD : ∀ g : GL (Fin d) K, g ∈ oBlock K hw I →
      D * (g : Matrix (Fin d) (Fin d) K) = (g : Matrix (Fin d) (Fin d) K) * D) : False := by
  obtain ⟨I₀, hI₀, hI₀3, hI₀w, -⟩ := hNF
  obtain ⟨a, ha⟩ : I₀.Nonempty := Finset.card_pos.1 (by omega)
  have hiso := fun y (hy : y ≠ a) =>
    isolated_of_commute hw h2 hI₀ hI₀3 hI₀w hD (Ne.symm hy) (Or.inl ha)
  have h := mul_self_apply_of_isolated (D := D) (a := a) hiso
  rw [hDD] at h
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
  have hs := congrFun (congrFun hskew a) a
  simp only [mul_diagonal, diagonal_mul, transpose_apply, Matrix.smul_apply, smul_eq_mul] at hs
  have hDa : D a a = 0 := by
    have : (2 : K) * (D a a * w a) = 0 := by linear_combination hs
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 h2
    · exact (mul_eq_zero.1 h0).resolve_right (hw a)
  rw [hDa, sq, mul_zero] at h
  exact hc h

end CFSG.ComponentClassification.GSThmB.Orth516
