module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QOGen
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QOScal

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup Matrix
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (signMat compInd commute_signMat_iff
  commute_compInd_compl diagGL coe_diagGL det_eq_one_of_mem_commutator)

variable {K : Type} [Field K] {d : ℕ}

theorem smul_one_eq_blkScal (J : Finset (Fin d)) (μ : K) :
    (μ • 1 : Matrix (Fin d) (Fin d) K) = blkScal K J (μ • 1) μ := by
  ext x y
  by_cases hx : x ∈ J <;> by_cases hy : y ∈ J
  · rw [blkScal_apply_mem _ _ hx hy, Matrix.smul_apply, Matrix.smul_apply, one_apply, one_apply]
    simp only [EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq]
  · rw [blkScal_apply_not_mem _ _ (Or.inr hy), Matrix.smul_apply, one_apply]
    split_ifs <;> simp
  · rw [blkScal_apply_not_mem _ _ (Or.inl hx), Matrix.smul_apply, one_apply]
    split_ifs <;> simp
  · rw [blkScal_apply_not_mem _ _ (Or.inl hx), Matrix.smul_apply, one_apply]
    split_ifs <;> simp

theorem smul_blkScal (J : Finset (Fin d)) (μ : K) (Y : Matrix (Fin J.card) (Fin J.card) K)
    (c : K) : μ • blkScal K J Y c = blkScal K J (μ • Y) (μ * c) := by
  calc μ • blkScal K J Y c = (μ • (1 : Matrix (Fin d) (Fin d) K)) * blkScal K J Y c := by
        rw [Matrix.smul_mul, Matrix.one_mul]
    _ = blkScal K J (μ • Y) (μ * c) := by
        rw [smul_one_eq_blkScal J μ, blkScal_mul, Matrix.smul_mul, Matrix.one_mul]

theorem one_eq_blkScal (J : Finset (Fin d)) :
    (1 : Matrix (Fin d) (Fin d) K) = blkScal K J 1 1 := by
  have h := smul_one_eq_blkScal (K := K) J 1
  rwa [one_smul, one_smul] at h

theorem signMat_eq_blkScal_compl (J : Finset (Fin d)) :
    signMat K J = blkScal K Jᶜ 1 (-1) := by
  ext x y
  simp only [signMat, diagonal_apply]
  by_cases hx : x ∈ Jᶜ <;> by_cases hy : y ∈ Jᶜ
  · rw [blkScal_apply_mem _ _ hx hy, one_apply]
    simp only [EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq]
    rw [Finset.mem_compl] at hx hy
    split_ifs <;> simp_all
  · rw [blkScal_apply_not_mem _ _ (Or.inr hy)]
    rw [Finset.mem_compl] at hx
    split_ifs <;> simp_all
  · rw [blkScal_apply_not_mem _ _ (Or.inl hx)]
    rw [Finset.mem_compl, not_not] at hx
    split_ifs <;> simp_all
  · rw [blkScal_apply_not_mem _ _ (Or.inl hx)]
    rw [Finset.mem_compl, not_not] at hx
    split_ifs <;> simp_all

variable [Finite K]

theorem commute_oBlock_of_lift (hK : ringChar K ≠ 2) (hK3 : Nat.card K ≠ 3) {w : Fin d → K}
    (hw : ∀ i, w i ≠ 0) {J I : Finset (Fin d)} (hI : I = J ∨ I = Jᶜ) (hI3 : 3 ≤ I.card)
    (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw))) {X : Type} [Group X] [Finite X]
    (π : matrixDerived (oQ (diagGL hw)) →* X) (hπ : Function.Surjective π)
    (hker : ∀ s, π s = 1 → s ∈ center (matrixDerived (oQ (diagGL hw)))) {g : X}
    (hg : ∀ L : Subgroup (centralizer ({π ⟨signGL K J, hJ⟩} : Set X)), IsComponent L →
      Even (Nat.card L) → ∀ k ∈ L, (k : X) * g = g * k)
    {g' : matrixDerived (oQ (diagGL hw))} (hg' : π g' = g) :
    ∀ h ∈ oBlock K hw I, ((g' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
      (h : Matrix (Fin d) (Fin d) K) = h * ((g' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hIS : oBlock K hw I ≤ matrixDerived (oQ (diagGL hw)) := by
    rw [matrixDerived_oQ h2 _ (diagGL_transpose hw)]
    exact oBlock_le hw I
  obtain ⟨-, m, L, hsup, hL⟩ := oBlock_componentData hK hw hI3 (fun h => hK3 h.1)
  have hNC : (oBlock K hw I).subgroupOf (matrixDerived (oQ (diagGL hw))) ≤
      centralizer ({⟨signGL K J, hJ⟩} : Set (matrixDerived (oQ (diagGL hw)))) := by
    intro x hx
    rw [mem_subgroupOf] at hx
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    apply Units.ext
    simp only [coe_mul, Units.val_mul, coe_signGL]
    exact (commute_signMat_of_mem_oIsoBlock h2 hw hI (oBlock_le_oIsoBlock hw I hx)).symm
  have hNn : ∀ x ∈ centralizer ({⟨signGL K J, hJ⟩} : Set (matrixDerived (oQ (diagGL hw)))),
      ∀ n ∈ (oBlock K hw I).subgroupOf (matrixDerived (oQ (diagGL hw))),
        x * n * x⁻¹ ∈ (oBlock K hw I).subgroupOf (matrixDerived (oQ (diagGL hw))) := by
    intro x hx n hn
    rw [mem_subgroupOf] at hn ⊢
    rw [mem_centralizer_singleton_iff] at hx
    have hxm : ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * signMat K J =
        signMat K J * ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
      have e := congrArg (fun y : matrixDerived (oQ (diagGL hw)) =>
        ((y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) hx
      simpa only [coe_mul, Units.val_mul, coe_signGL] using e
    have hcJ := (commute_signMat_iff h2 J _).1 hxm.symm
    have hcI : compInd K I * ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * compInd K I := by
      rcases hI with rfl | rfl
      · exact hcJ
      · exact commute_compInd_compl hcJ
    have hxI : (x : GL (Fin d) K) ∈ CatalogueBGraphForm.isometryGroup d K (diagGL hw) :=
      (mem_matrixIsometries_oQ h2 _ (diagGL_transpose hw) _).1 (matrixDerived_le_isometries _ x.2)
    simpa only [coe_mul, coe_inv] using conj_mem_oBlock hw hxI hcI hn
  have hcomm : ∀ i, ∀ l ∈ L i, (g' : GL (Fin d) K) * l = l * g' := by
    intro i l hl
    have hLS : L i ≤ matrixDerived (oQ (diagGL hw)) := (hL i).2.1.trans hIS
    have hq : IsQuasisimple ((L i).subgroupOf (matrixDerived (oQ (diagGL hw)))) :=
      LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hLS).symm (hL i).1
    have key := lift_commute_of_subnormal π hπ hker ⟨signGL K J, hJ⟩ hq
      (N := (oBlock K hw I).subgroupOf (matrixDerived (oQ (diagGL hw))))
      (fun x hx => by rw [mem_subgroupOf] at hx ⊢; exact (hL i).2.1 hx)
      (fun x hx y hy => by
        rw [mem_subgroupOf] at hx hy ⊢
        simpa only [coe_mul, coe_inv] using (hL i).2.2 _ hx _ hy)
      hNC hNn hg hg' ⟨l, hLS hl⟩ (by rw [mem_subgroupOf]; exact hl)
    exact congrArg Subtype.val key
  have hle : oBlock K hw I ≤ centralizer ({(g' : GL (Fin d) K)} : Set (GL (Fin d) K)) := by
    rw [← hsup]
    refine iSup_le fun i l hl => ?_
    rw [mem_centralizer_singleton_iff]
    exact (hcomm i l hl).symm
  intro h hh
  have e := congrArg Units.val (mem_centralizer_singleton_iff.1 (hle hh))
  simp only [Units.val_mul] at e
  exact e.symm

theorem lift_eq_blkScal (hK : ringChar K ≠ 2) (hK3 : Nat.card K ≠ 3) {w : Fin d → K}
    (hw : ∀ i, w i ≠ 0) {J I : Finset (Fin d)} (hI : I = J ∨ I = Jᶜ) (hI3 : 3 ≤ I.card)
    (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw))) {X : Type} [Group X] [Finite X]
    (π : matrixDerived (oQ (diagGL hw)) →* X) (hπ : Function.Surjective π)
    (hker : ∀ s, π s = 1 → s ∈ center (matrixDerived (oQ (diagGL hw)))) {g : X}
    (hg : ∀ L : Subgroup (centralizer ({π ⟨signGL K J, hJ⟩} : Set X)), IsComponent L →
      Even (Nat.card L) → ∀ k ∈ L, (k : X) * g = g * k)
    {g' : matrixDerived (oQ (diagGL hw))} (hg' : π g' = g) :
    ∃ (Y : Matrix (Fin Iᶜ.card) (Fin Iᶜ.card) K) (c : K),
      ((g' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = blkScal K Iᶜ Y c ∧
        Yᵀ * diagonal (wRes w Iᶜ) * Y = diagonal (wRes w Iᶜ) ∧ c ^ 2 = 1 ∧
          Y.det * c ^ I.card = 1 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨c, hc⟩ := eq_of_commute_oBlock hK hw hI3
    (commute_oBlock_of_lift hK hK3 hw hI hI3 hJ π hπ hker hg hg')
  have hD := eq_blkScal (J := Iᶜ) (D := ((g' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) (c := c)
    (fun x hx y hy => by
      rw [Finset.mem_compl] at hx
      rw [Finset.mem_compl, not_not] at hy
      have hxy : y ≠ x := fun h => hx (h ▸ hy)
      obtain ⟨h1, h2⟩ := hc y hy x
      rw [ite_eq_right hxy] at h1
      rw [ite_eq_right (Ne.symm hxy)] at h2
      exact ⟨h2, h1⟩)
    (fun x hx y _ => by
      rw [Finset.mem_compl, not_not] at hx
      exact (hc x hx y).1)
  refine ⟨_, c, hD, ?_⟩
  have hiso : ((g' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)ᵀ * diagonal w *
      ((g' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal w := by
    have e := (CatalogueBGraphForm.mem_isometryGroup _ _ _ _).1
      ((mem_matrixIsometries_oQ h2 _ (diagGL_transpose hw) _).1
        (matrixDerived_le_isometries _ g'.2))
    rwa [coe_diagGL] at e
  rw [hD] at hiso
  have hIne : Iᶜᶜ.Nonempty := by
    rw [compl_compl]
    exact Finset.card_pos.1 (by omega)
  obtain ⟨hY, hc2⟩ := blkScal_isometry hIne hw hiso
  refine ⟨hY, hc2, ?_⟩
  have hdet : ((g' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).det = 1 :=
    det_eq_one_of_mem_commutator (I := matrixIsometries (oQ (diagGL hw))) g'.2
  rwa [hD, det_blkScal, compl_compl] at hdet

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
