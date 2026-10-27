module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyRho
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyStep

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open scoped Matrix
open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.AlgebraicGroups

set_option linter.unusedSectionVars false


section TwistForm

variable {t : TwistTag}

theorem permLattice_form (x : Fin t.tag.rank → ℤ) (i : Fin t.tag.rank) :
    iform (permLattice t.perm x) (Pi.single i 1) = iform x (Pi.single (t.perm.symm i) 1) := by
  have h := iform_latticePerm (τ := t.tag) (symmetrizedCartan_perm t) x
    (Pi.single (t.perm.symm i) 1)
  rw [latticePerm_apply, latticePerm_apply, permLattice_single, Equiv.apply_symm_apply] at h
  exact h

end TwistForm

section TwistStep

variable {t : TwistTag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup t.tag L p)
  {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = twistHom t L Fr)
  {v : WeylGroup t.tag} (hn : S.D.n = canonicalRep (coxeterSystem t.tag) L v)

include hFr hΦ hn

theorem twist_step_eq (g : ModGL t.tag L) :
    S.D.step g = (S.D.n * diagramMap t L) * Units.map (entrywiseHom Fr) g *
      (S.D.n * diagramMap t L)⁻¹ := by
  show S.D.n * S.D.Φ g * S.D.n⁻¹ = _
  rw [hΦ, twistHom_apply]
  group

theorem twist_hel (x : Fin t.tag.rank → ℤ) (u : Lˣ) :
    S.D.step (Hel x u) = Hel (v • permLattice t.perm x) (u ^ S.D.q) := by
  have hFu : Units.map Fr.toMonoidHom u = u ^ S.D.q := Units.ext (by simp [hFr])
  have h1 : Units.map (entrywiseHom Fr) (Hel x u) = Hel x (u ^ S.D.q) := by
    unfold Hel
    rw [CrossChar.units_map_entrywiseHom_rootDiagUnit]
    congr 1
    funext i
    simp only [Hchar, map_zpow]
    rw [hFu, ← zpow_natCast, ← zpow_mul]
  have h2 : diagramMap t L * Hel x (u ^ S.D.q) * (diagramMap t L)⁻¹ =
      Hel (permLattice t.perm x) (u ^ S.D.q) := by
    unfold Hel
    rw [diagramMap_mul_rootDiagUnit, mul_assoc, mul_inv_cancel, mul_one]
    congr 1
    funext i
    simp only [Hchar]
    rw [permLattice_form]
  have h3 : S.D.n * Hel (permLattice t.perm x) (u ^ S.D.q) * S.D.n⁻¹ =
      Hel (v • permLattice t.perm x) (u ^ S.D.q) := by
    rw [hn]
    exact conj_Hel (canonicalRep_mem_monomialSubgroup L v) (mapsRootLines_canonicalRep v) _ _
  rw [twist_step_eq S hFr hΦ hn, h1]
  rw [← h3, ← h2]
  group

theorem twist_nsl {β : Fin t.tag.rank → ℤ} (hβ : IsRoot t.tag β) :
    ∃ s : Lˣ, ∀ c : Lˣ, S.D.step (rootSL2 t.tag L β (nSL c)) =
      rootSL2 t.tag L (v • permLattice t.perm β) (nSL (s * c ^ S.D.q)) := by
  have hmono : S.D.n ∈ monomialSubgroup t.tag L := by
    rw [hn]; exact canonicalRep_mem_monomialSubgroup L v
  have hmaps : MapsRootLines S.D.n v := by rw [hn]; exact mapsRootLines_canonicalRep v
  obtain ⟨s, hs⟩ := CFSG.RankThree.PartOne.KGD.exists_conj_rootSL2_eq_twist (t := t) hmono hβ
  have hw : weylQuotientHom t.tag L ⟨S.D.n, hmono⟩ = v := weylQuotientHom_eq hmaps
  refine ⟨s, fun c => ?_⟩
  let σ : L ≃+* L := RingEquiv.ofBijective Fr (S.frobenius_bijective hFr)
  have hσ : σ.toRingHom = Fr := RingHom.ext fun _ => rfl
  have hFu : Units.map Fr.toMonoidHom c = c ^ S.D.q := Units.ext (by simp [hFr])
  have h1' : Units.map (entrywiseHom σ.toRingHom) (rootSL2 t.tag L β (nSL c)) =
      rootSL2 t.tag L β (Matrix.SpecialLinearGroup.map σ.toRingHom (nSL c)) :=
    frobGL_rootSL2 σ hβ (nSL c)
  rw [hσ, map_nSL, hFu] at h1'
  rw [twist_step_eq S hFr hΦ hn, h1', hs, conjSL_diagUnitOne_nSL, hw]

theorem twist_rho {β : Fin t.tag.rank → ℤ} (hβ : IsRoot t.tag β) :
    S.ρ β = v • permLattice t.perm β := by
  have hmono : S.D.n ∈ monomialSubgroup t.tag L := by
    rw [hn]; exact canonicalRep_mem_monomialSubgroup L v
  have hmaps : MapsRootLines S.D.n v := by rw [hn]; exact mapsRootLines_canonicalRep v
  have hw : weylQuotientHom t.tag L ⟨S.D.n, hmono⟩ = v := weylQuotientHom_eq hmaps
  have hπβ : IsRoot t.tag (permLattice t.perm β) := hβ.permLattice t.cartan_perm
  have hAroot : IsRoot t.tag (v • permLattice t.perm β) := IsRoot.smul hπβ v
  obtain ⟨μ, hμ0, hμ⟩ := step_pinnedX S hβ
  obtain ⟨e, he, hP⟩ := diagramMap_conj_pinnedX (K := L) t hβ
  obtain ⟨μ₂, hμ₂⟩ := monomial_conj_pinnedX hmono hπβ
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq μ⁻¹ S.q_pos
  have hstep : S.D.step (pinnedX t.tag L β c) =
      pinnedX t.tag L (v • permLattice t.perm β) ((μ₂ : L) * (e * Fr c)) := by
    have hX : Units.map (entrywiseHom Fr) (pinnedX t.tag L β c) = pinnedX t.tag L β (Fr c) :=
      Units.ext (by rw [Units.coe_map]; exact entrywise_pinnedX Fr β c)
    rw [twist_step_eq S hFr hΦ hn, hX]
    have : S.D.n * diagramMap t L * pinnedX t.tag L β (Fr c) *
        (S.D.n * diagramMap t L)⁻¹ =
        S.D.n * (diagramMap t L * pinnedX t.tag L β (Fr c) * (diagramMap t L)⁻¹) *
          S.D.n⁻¹ := by
      rw [mul_inv_rev]
      simp only [mul_assoc]
    rw [this, hP, hμ₂, hw]
  have h1 : pinnedX t.tag L (S.ρ β) 1 = pinnedX t.tag L (v • permLattice t.perm β)
      ((μ₂ : L) * (e * Fr c)) := by
    rw [← hstep, hμ c, hc, mul_inv_cancel₀ hμ0]
  have hmem : pinnedX t.tag L (S.ρ β) 1 ∈ rootSubgroup t.tag L (v • permLattice t.perm β) := by
    rw [h1]
    exact mem_rootSubgroup.2 ⟨_, rfl⟩
  exact eq_of_pinnedX_one_mem_rootSubgroup ((S.frob.isRoot_iff β).2 hβ) hAroot hmem

end TwistStep


section TwistHex

variable {t : TwistTag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup t.tag L p)
  {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = twistHom t L Fr)
  {v : WeylGroup t.tag} (hn : S.D.n = canonicalRep (coxeterSystem t.tag) L v)
  {M : Matrix (Fin t.tag.rank) (Fin t.tag.rank) ℤ}
  (hv : ∀ x, v • x = M *ᵥ permLattice t.perm x)
  (hinv : ∀ x, permLattice t.perm (permLattice t.perm x) = x) (hM : M * M = M - 1)

include hFr hΦ hn hv hinv

theorem twist_rho_mulVec {β : Fin t.tag.rank → ℤ} (hβ : IsRoot t.tag β) : S.ρ β = M *ᵥ β := by
  rw [twist_rho S hFr hΦ hn hβ, hv, hinv]

include hM

theorem hexStep_of_twist : S.HexStep where
  hel x hx u := by
    rw [twist_hel S hFr hΦ hn x u, twist_rho S hFr hΦ hn hx]
  nsl β hβ := by
    obtain ⟨s, hs⟩ := twist_nsl S hFr hΦ hn hβ
    exact ⟨s, fun c => by rw [hs c, twist_rho S hFr hΦ hn hβ]⟩
  rel6 δ hδ := by
    have hδ' : IsRoot t.tag (S.ρ δ) := (S.frob.isRoot_iff δ).2 hδ
    have h1 := twist_rho_mulVec S hFr hΦ hn hv hinv hδ
    rw [twist_rho_mulVec S hFr hΦ hn hv hinv hδ', h1, Matrix.mulVec_mulVec, hM,
      Matrix.sub_mulVec, Matrix.one_mulVec, ← h1]

end TwistHex

end CFSG.HardMathSupport.Timmesfeld.LangTorus
