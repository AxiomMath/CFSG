module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHsyl
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2Position
public import CFSG.RankThree.OrthogonalInvolutions.Witt

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_perfect le_perfectCore_of_perfect)


section Conj

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem map_conj_orthDerived {A : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hA : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    (orthDerived Q).map (MulAut.conj A : ((Fin d → K) ≃ₗ[K] (Fin d → K)) →*
      ((Fin d → K) ≃ₗ[K] (Fin d → K))) = orthDerived Q := by
  have hO : (TauCeti.QuadraticMap.orthogonalGroup Q).map (MulAut.conj A :
      ((Fin d → K) ≃ₗ[K] (Fin d → K)) →* ((Fin d → K) ≃ₗ[K] (Fin d → K))) =
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    ext g
    constructor
    · rintro ⟨h, hh, rfl⟩
      change A * h * A⁻¹ ∈ _
      exact mul_mem (mul_mem hA hh) (inv_mem hA)
    · intro hg
      refine ⟨A⁻¹ * g * A, mul_mem (mul_mem (inv_mem hA) hg) hA, ?_⟩
      change A * (A⁻¹ * g * A) * A⁻¹ = g
      group
  change (⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ :
    Subgroup _).map _ = _
  rw [Subgroup.map_commutator, hO]

@[expose] noncomputable def conjOrthDerived {A : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hA : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q) : MulAut (orthDerived Q) :=
  ((MulAut.conj A).subgroupMap (orthDerived Q)).trans
    (MulEquiv.subgroupCongr (map_conj_orthDerived hA))

theorem coe_conjOrthDerived {A : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hA : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (X : orthDerived Q) :
    ((conjOrthDerived hA X : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) = A * X * A⁻¹ :=
  rfl

variable [CharP K 2]

@[expose] noncomputable def conjProj (hQ : ∃ v, Q v ≠ 0) {A : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hA : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q) : MulAut (matrixProjectiveDerived Q) :=
  ((MulEquiv.ofBijective (projHom Q) ⟨projHom_injective hQ, projHom_surjective Q⟩).symm.trans
    (conjOrthDerived hA)).trans
    (MulEquiv.ofBijective (projHom Q) ⟨projHom_injective hQ, projHom_surjective Q⟩)

theorem conjProj_projHom (hQ : ∃ v, Q v ≠ 0) {A : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hA : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (X : orthDerived Q) :
    conjProj hQ hA (projHom Q X) = projHom Q (conjOrthDerived hA X) := by
  change MulEquiv.ofBijective (projHom Q) ⟨projHom_injective hQ, projHom_surjective Q⟩
      (conjOrthDerived hA ((MulEquiv.ofBijective (projHom Q)
        ⟨projHom_injective hQ, projHom_surjective Q⟩).symm
        (MulEquiv.ofBijective (projHom Q) ⟨projHom_injective hQ, projHom_surjective Q⟩ X))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

omit [CharP K 2] in
theorem linearIndependent_of_hyp {u v : Fin d → K} (hu : Q u = 0) (hv : Q v = 0)
    (huv : polar Q u v = 1) : LinearIndependent K ![u, v] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 := congrArg (fun z => polar Q z v) hst
  have h2 := congrArg (fun z => polar Q z u) hst
  simp only [polar_add_left, polar_smul_left_eq, huv, polar_self_eq_zero hv, polar_zero_left,
    polar_comm Q v u] at h1 h2
  rw [polar_self_eq_zero hu] at h2
  exact ⟨by simpa using h1, by simpa using h2⟩

omit [CharP K 2] in
theorem eq_conj_torusLin_of_apply {a b : Fin d} (h : IsHypCoord Q a b)
    {A : (Fin d → K) ≃ₗ[K] (Fin d → K)} (hA : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {u v : Fin d → K} (hAu : A (Pi.single a 1) = u) (hAv : A (Pi.single b 1) = v)
    {g : (Fin d → K) ≃ₗ[K] (Fin d → K)} {c : Kˣ} (hgu : g u = (c : K) • u)
    (hgv : g v = ((c⁻¹ : Kˣ) : K) • v) (hgx : ∀ x, polar Q x u = 0 → polar Q x v = 0 → g x = x) :
    g = A * torusLin a b c * A⁻¹ := by
  have key : A⁻¹ * g * A = torusLin a b c := by
    refine h.linearEquiv_ext ?_ ?_ fun x hx => ?_
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hAu, hgu, map_smul, ← hAu,
        LinearEquiv.inv_apply_apply', torusLin_single_left h.ne]
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hAv, hgv, map_smul, ← hAv,
        LinearEquiv.inv_apply_apply', torusLin_single_right h.ne]
    · have h1 : polar Q (A x) u = 0 := by
        rw [← hAu, polar_map_of_mem hA, polar_comm, h.polar_left, hx.2]
      have h2 : polar Q (A x) v = 0 := by
        rw [← hAv, polar_map_of_mem hA, polar_comm, h.polar_right, hx.1]
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hgx _ h1 h2,
        LinearEquiv.inv_apply_apply', torusLin_eq_self_of hx.1 hx.2]
  calc g = A * (A⁻¹ * g * A) * A⁻¹ := by group
    _ = A * torusLin a b c * A⁻¹ := by rw [key]

end Conj

section Torus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {a b : Fin d}

theorem exists_mulAut_eq_map_pairTorusOf (hQ : (polarBilin Q).Nondegenerate)
    (h : IsHypCoord Q a b) {Y : Subgroup (matrixProjectiveDerived Q)} {u v : Fin d → K}
    (hu : Q u = 0) (hv : Q v = 0) (huv : polar Q u v = 1)
    (hY : ∀ g : orthDerived Q, projHom Q g ∈ Y → ∃ c : Kˣ,
      (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) u = (c : K) • u ∧
      (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) v = ((c⁻¹ : Kˣ) : K) • v ∧
      ∀ x, polar Q x u = 0 → polar Q x v = 0 → (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) x = x)
    (hcard : Nat.card Y = Nat.card (pairTorusOf Q a b)) :
    ∃ α : MulAut (matrixProjectiveDerived Q), Y = (pairTorusOf Q a b).map α.toMonoidHom := by
  have hab : polar Q (Pi.single a 1) (Pi.single b 1) = 1 := by
    rw [h.polar_left, Pi.single_eq_same]
  have hli := linearIndependent_of_hyp h.map_left h.map_right hab
  have hli' := linearIndependent_of_hyp hu hv huv
  obtain ⟨A, hA, hAuv⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_mem_orthogonalGroup_apply_eq
    hQ ![Pi.single a 1, Pi.single b 1] ![u, v] hli hli'
    (by
      intro i
      fin_cases i
      · simp [hu, h.map_left]
      · simp [hv, h.map_right])
    (by
      intro i j
      fin_cases i <;> fin_cases j
      · simp [polar_self_eq_zero hu, polar_self_eq_zero h.map_left]
      · simp [huv, hab]
      · simp [polar_comm Q v u, huv, polar_comm Q (Pi.single b 1) (Pi.single a 1), hab]
      · simp [polar_self_eq_zero hv, polar_self_eq_zero h.map_right])
  have hAu : A (Pi.single a 1) = u := hAuv 0
  have hAv : A (Pi.single b 1) = v := hAuv 1
  set α := conjProj h.exists_ne_zero hA with hα
  refine ⟨α, ?_⟩
  have hle : Y ≤ (pairTorusOf Q a b).map α.toMonoidHom := by
    intro y hy
    obtain ⟨g, rfl⟩ := projHom_surjective Q y
    obtain ⟨c, hgu, hgv, hgx⟩ := hY g hy
    have hg := eq_conj_torusLin_of_apply h hA hAu hAv hgu hgv hgx
    set t : orthDerived Q := ⟨torusLin a b c, h.torusLin_mem_orthDerived c⟩
    have hgt : g = conjOrthDerived hA t := Subtype.ext (by rw [coe_conjOrthDerived]; exact hg)
    refine ⟨projHom Q t, ⟨t, mem_subgroupOf.mpr ⟨c, rfl⟩, rfl⟩, ?_⟩
    rw [hgt]
    exact conjProj_projHom h.exists_ne_zero hA t
  refine eq_of_le_of_card_ge hle ?_
  rw [card_map_of_injective α.injective, hcard]

theorem perfectCore_centralizer_pairTorusOf (h : IsHypCoord Q a b) (hq : 4 ≤ Nat.card K)
    (hD : ⁅pairPerpOf Q a b, pairPerpOf Q a b⁆ = pairPerpOf Q a b) :
    perfectCore (centralizer (pairTorusOf Q a b : Set (matrixProjectiveDerived Q))) =
      pairPerpOf Q a b := by
  rw [h.centralizer_pairTorusOf hq]
  exact F4Pilot.perfectCore_sup_eq_of_le_centralizer
    (F4Pilot.le_centralizer_self_of_isCyclic h.isCyclic_pairTorusOf)
    h.pairTorusOf_le_centralizer_pairPerpOf hD

theorem nonempty_perfectCore_centralizer_mulEquiv_pairPerpOf (hQ : (polarBilin Q).Nondegenerate)
    (h : IsHypCoord Q a b) (hq : 4 ≤ Nat.card K)
    (hD : ⁅pairPerpOf Q a b, pairPerpOf Q a b⁆ = pairPerpOf Q a b)
    {Y : Subgroup (matrixProjectiveDerived Q)} {u v : Fin d → K}
    (hu : Q u = 0) (hv : Q v = 0) (huv : polar Q u v = 1)
    (hY : ∀ g : orthDerived Q, projHom Q g ∈ Y → ∃ c : Kˣ,
      (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) u = (c : K) • u ∧
      (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) v = ((c⁻¹ : Kˣ) : K) • v ∧
      ∀ x, polar Q x u = 0 → polar Q x v = 0 → (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) x = x)
    (hcard : Nat.card Y = Nat.card (pairTorusOf Q a b)) :
    Nonempty (perfectCore (centralizer (Y : Set (matrixProjectiveDerived Q))) ≃*
      pairPerpOf Q a b) := by
  obtain ⟨α, rfl⟩ := exists_mulAut_eq_map_pairTorusOf hQ h hu hv huv hY hcard
  obtain ⟨e⟩ := F4Pilot.nonempty_perfectCore_centralizer_map_mulAut α (pairTorusOf Q a b)
  rw [perfectCore_centralizer_pairTorusOf h hq hD] at e
  exact ⟨e⟩

end Torus

end CFSG.SeitzReduction.OmegaPilot
