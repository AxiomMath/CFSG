module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyTorus
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidDescent

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne
  CFSG.HardMathSupport.Timmesfeld.CrossChar

set_option linter.unusedSectionVars false


section Conj

variable {τ : Tag} {L : Type} [Field L]

theorem conj_rootDiagUnit_of_mapsRootLines {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L)
    {w : WeylGroup τ} (hw : MapsRootLines n w) (a b : Fin τ.rank → Lˣ)
    (h : ∀ v, rootChar a (w • v) = rootChar b v) :
    n * rootDiagUnit τ b * n⁻¹ = rootDiagUnit τ a := by
  set c := canonicalRep (coxeterSystem τ) L w with hcdef
  have hc : MapsRootLines c w := mapsRootLines_canonicalRep w
  have hcM : c ∈ monomialSubgroup τ L := canonicalRep_mem_monomialSubgroup L w
  have h1 : MapsRootLines (c⁻¹ * n) 1 := by
    have := hc.inv.mul hw
    rwa [inv_mul_cancel] at this
  have ht : c⁻¹ * n ∈ torusGroup τ L :=
    mem_torusGroup_of_mapsRootLines_one (mul_mem (inv_mem hcM) hn) h1
  obtain ⟨t, ht'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hn' : n = c * rootDiagUnit τ t := by
    rw [← ht']
    group
  have hca : rootDiagUnit τ a = c * rootDiagUnit τ b * c⁻¹ :=
    (rootDiagUnit_eq_conj_canonicalRep_iff a b w).2 h
  rw [hn', hca]
  have : rootDiagUnit τ t * rootDiagUnit τ b = rootDiagUnit τ b * rootDiagUnit τ t := by
    rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  calc c * rootDiagUnit τ t * rootDiagUnit τ b * (c * rootDiagUnit τ t)⁻¹
      = c * (rootDiagUnit τ t * rootDiagUnit τ b * (rootDiagUnit τ t)⁻¹) * c⁻¹ := by group
    _ = c * rootDiagUnit τ b * c⁻¹ := by rw [this]; group

theorem conj_Hel {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L) {w : WeylGroup τ}
    (hw : MapsRootLines n w) (x : Fin τ.rank → ℤ) (u : Lˣ) :
    n * Hel x u * n⁻¹ = Hel (w • x) u := by
  refine conj_rootDiagUnit_of_mapsRootLines hn hw _ _ fun v => ?_
  rw [rootChar_Hchar, rootChar_Hchar, iform_smul]

end Conj

section SL2

open CFSG.RankThree.Classical
open scoped MatrixGroups

variable {L : Type} [Field L]

theorem conjSL_eq_of {M : GL (Fin 2) L} {A B : SL(2, L)}
    (h : (M : Matrix (Fin 2) (Fin 2) L) * A = B * M) : conjSL M A = B := by
  apply Subtype.ext
  rw [coe_conjSL, h, Matrix.mul_assoc]
  rw [Units.mul_inv, Matrix.mul_one]

theorem map_nSL (σ : L →+* L) (c : Lˣ) :
    Matrix.SpecialLinearGroup.map σ (nSL c) = nSL (Units.map σ.toMonoidHom c) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nSL, RingHom.mapMatrix_apply]

theorem conjSL_diagUnitOne_nSL (s c : Lˣ) : conjSL (diagUnitOne s) (nSL c) = nSL (s * c) := by
  apply conjSL_eq_of
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nSL, coe_diagUnitOne, Matrix.mul_apply, Fin.sum_univ_two]

theorem conjSL_swap_nSL (a c : Lˣ) :
    conjSL (CFSG.RankThree.Classical.swapGL * diagUnitOne a) (nSL c) = nSL (-(a * c)⁻¹) := by
  apply conjSL_eq_of
  rw [coe_swapGL_mul_diagUnitOne]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem nSL_mul_HSL (c t : Lˣ) : nSL c * HSL t = nSL (c * t⁻¹) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [nSL, HSL, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [nSL, HSL, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [nSL, HSL, Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
  · simp [nSL, HSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem nSL_inv_mul_nSL (c c' : Lˣ) : (nSL c)⁻¹ * nSL c' = HSL (c * c'⁻¹) := by
  rw [inv_mul_eq_iff_eq_mul, nSL_mul_HSL, mul_inv_rev, inv_inv]
  congr 1
  rw [mul_left_comm, mul_inv_cancel, mul_one]

end SL2

section Step

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
  {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) L w)

include hFr hΦ hn

theorem LangSetup.units_map_frob (u : Lˣ) : Units.map Fr.toMonoidHom u = u ^ S.D.q :=
  Units.ext (by simp [hFr])

theorem LangSetup.step_Hel (x : Fin τ.rank → ℤ) (u : Lˣ) :
    S.D.step (Hel x u) = Hel (w • x) (u ^ S.D.q) := by
  have h1 : S.D.Φ (Hel x u) = Hel x (u ^ S.D.q) := by
    rw [hΦ]
    unfold Hel
    rw [CrossChar.units_map_entrywiseHom_rootDiagUnit]
    congr 1
    funext i
    simp only [Hchar, map_zpow]
    rw [S.units_map_frob hFr hΦ hn, ← zpow_natCast, ← zpow_mul]
  have h2 : S.D.step (Hel x u) = S.D.n * Hel x (u ^ S.D.q) * S.D.n⁻¹ := by
    show S.D.n * S.D.Φ (Hel x u) * S.D.n⁻¹ = _
    rw [h1]
  rw [h2, hn]
  exact conj_Hel (canonicalRep_mem_monomialSubgroup L w) (mapsRootLines_canonicalRep w) x _

theorem LangSetup.step_rootSL2 {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    ∃ s : Lˣ, ∀ A : SL2 L, S.D.step (rootSL2 τ L β A) =
      rootSL2 τ L (w • β) (CFSG.RankThree.Classical.conjSL
        (CFSG.RankThree.Classical.diagUnitOne s) (Matrix.SpecialLinearGroup.map Fr A)) := by
  obtain ⟨s, hs⟩ := CFSG.RankThree.Chevalley.exists_conj_rootSL2_eq
    (canonicalRep_mem_monomialSubgroup L w) (mapsRootLines_canonicalRep w) hβ rfl
  refine ⟨s, fun A => ?_⟩
  let σ : L ≃+* L := RingEquiv.ofBijective Fr (S.frobenius_bijective hFr)
  have hσ : σ.toRingHom = Fr := RingHom.ext fun c => rfl
  have h1' : Units.map (entrywiseHom σ.toRingHom) (rootSL2 τ L β A) =
      rootSL2 τ L β (Matrix.SpecialLinearGroup.map σ.toRingHom A) := frobGL_rootSL2 σ hβ A
  rw [hσ] at h1'
  show S.D.n * S.D.Φ (rootSL2 τ L β A) * S.D.n⁻¹ = _
  rw [hΦ, h1', hn]
  exact hs _

theorem LangSetup.step_nSL {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    ∃ s : Lˣ, ∀ c : Lˣ, S.D.step (rootSL2 τ L β (nSL c)) =
      rootSL2 τ L (w • β) (nSL (s * c ^ S.D.q)) := by
  obtain ⟨s, hs⟩ := S.step_rootSL2 hFr hΦ hn hβ
  refine ⟨s, fun c => ?_⟩
  rw [hs, map_nSL, conjSL_diagUnitOne_nSL, S.units_map_frob hFr hΦ hn]

end Step

section RankOne

variable {τ : Tag} {L : Type} [Field L]

theorem conj_rootSL2_nSL {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L) {w : WeylGroup τ}
    (hw : MapsRootLines n w) {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : w • β = γ) :
    ∃ s : Lˣ, ∀ c : Lˣ,
      n * rootSL2 τ L β (nSL c) * n⁻¹ = rootSL2 τ L γ (nSL (s * c)) := by
  obtain ⟨s, hs⟩ := CFSG.RankThree.Chevalley.exists_conj_rootSL2_eq hn hw hβ hγ
  exact ⟨s, fun c => by rw [hs, conjSL_diagUnitOne_nSL]⟩

theorem rootSL2_neg_nSL {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    ∃ a : Lˣ, ∀ c : Lˣ, rootSL2 τ L (-β) (nSL c) = rootSL2 τ L β (nSL (-(a * c)⁻¹)) := by
  obtain ⟨a, ha⟩ := CFSG.RankThree.PartOne.KGD.exists_rootSL2_neg_eq (L := L) hβ
  exact ⟨a, fun c => by rw [ha, conjSL_swap_nSL]⟩

theorem rootSL2_nSL_inv_mul (hτ : SimplyLacedTag τ) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (c c' : Lˣ) :
    (rootSL2 τ L β (nSL c))⁻¹ * rootSL2 τ L β (nSL c') = Hel β (c * c'⁻¹) := by
  rw [← map_inv, ← map_mul, nSL_inv_mul_nSL, Hel_root_eq_rootSL2 hτ hβ]

end RankOne

end CFSG.HardMathSupport.Timmesfeld.LangTorus
