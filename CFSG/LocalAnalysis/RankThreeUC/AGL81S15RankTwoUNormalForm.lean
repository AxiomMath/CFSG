module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoUDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S218Borel
public import CFSG.LocalAnalysis.UniquenessCase.UC22S218BorelDiag

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open
open scoped commutatorElement

private theorem normalizer_inv_mul_conj_mem {Y : Type} [Group Y] {U H : Subgroup Y}
    {F : Subgroup (MulAut Y)} (D : CFSG.Quasithin.H13.Sec53F.BA.BorelAutData U H F)
    {g b : Y} (hg : g ∈ Subgroup.normalizer (U : Set Y))
    (hb : b ∈ Subgroup.normalizer (U : Set Y)) :
    b⁻¹ * MulAut.conj g b ∈ U := by
  have hcomm : IsMulCommutative
      (Subgroup.normalizer (U : Set Y) ⧸
        U.subgroupOf (Subgroup.normalizer (U : Set Y))) :=
    IsMulCommutative.of_comm fun q r => D.quot_comm q r
  have hle : _root_.commutator (Subgroup.normalizer (U : Set Y)) ≤
      U.subgroupOf (Subgroup.normalizer (U : Set Y)) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcomm
  have hmem : ⁅(⟨g, hg⟩ : Subgroup.normalizer (U : Set Y)),
      (⟨b, hb⟩ : Subgroup.normalizer (U : Set Y))⁆ ∈
      U.subgroupOf (Subgroup.normalizer (U : Set Y)) :=
    hle (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  have hc : ⁅g, b⁆ ∈ U := by
    simpa [commutatorElement_def] using (Subgroup.mem_subgroupOf.mp hmem)
  have hbc : b⁻¹ * ⁅g, b⁆ * b ∈ U := by
    simpa using (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (U : Set Y)).inv_mem hb) (⁅g, b⁆)).mp hc
  have heq : b⁻¹ * MulAut.conj g b = b⁻¹ * ⁅g, b⁆ * b := by
    rw [commutatorElement_def, MulAut.conj_apply]
    group
  rw [heq]
  exact hbc

private theorem mul_conj_mul_inv_mem_map {Y : Type} [Group Y] {U H : Subgroup Y}
    {F : Subgroup (MulAut Y)} (D : CFSG.Quasithin.H13.Sec53F.BA.BorelAutData U H F)
    {σ : MulAut Y} (hσ : σ ∈ F) {g : Y}
    (hg : g ∈ Subgroup.normalizer (U : Set Y)) :
    σ * MulAut.conj g * σ⁻¹ ∈
      (Subgroup.normalizer (U : Set Y)).map
        (MulAut.conj : Y →* MulAut Y) := by
  have hσg : σ g ∈ Subgroup.normalizer (U : Set Y) := (D.F_B σ hσ g).mpr hg
  refine Subgroup.mem_map.mpr ⟨σ g, hσg, ?_⟩
  rw [CFSG.Quasithin.H13.Sec53F.BA.aut_mul_conj_mul_inv]

theorem isScalarTorus_of_normalForm {Y : Type} [Group Y] {U H A : Subgroup Y}
    {F D : Subgroup (MulAut Y)} {q : ℕ}
    (hHU : H ≤ Subgroup.normalizer (U : Set Y)) (hUH : ∀ x ∈ U, x ∈ H → x = 1)
    (hAH : A ≤ H) (hA : IsElemAbelian q A) (hcard : Nat.card A = q ^ 2)
    (hFH : ∀ σ ∈ F, ∀ x ∈ H, σ x ∈ H) (hFfaith : ∀ σ ∈ F, (∀ x ∈ H, σ x = x) → σ = 1)
    (hDtriv : ∀ e ∈ D, ∀ b ∈ Subgroup.normalizer (U : Set Y), b⁻¹ * e b ∈ U)
    (hFD : ∀ σ ∈ F, ∀ e ∈ D, σ * e * σ⁻¹ ∈ D)
    (hnf : ∀ α : MulAut Y, (∀ x, α x ∈ U ↔ x ∈ U) → ∃ e ∈ D, ∃ σ ∈ F, α = e * σ)
    (hpow : ∀ α : MulAut Y, U.map α.toMonoidHom = U →
      ∃ k : ℕ, ∀ b ∈ Subgroup.normalizer (U : Set Y), α b * (b ^ k)⁻¹ ∈ U)
    (hFinv : ∀ σ ∈ F, σ * σ = 1 → ∀ x ∈ A, σ x = x) : IsScalarTorus q U A := by
  refine ⟨fun x hx => hHU (hAH hx), hA, hcard, ?_⟩
  intro α hα
  constructor
  · obtain ⟨k, hk⟩ := hpow α hα
    exact ⟨k, fun x hx => hk x (hHU (hAH hx))⟩
  · intro hα2
    obtain ⟨e, he, σ, hσ, hαeσ⟩ := hnf α fun x => by
      have h : α x ∈ U.map α.toMonoidHom ↔ x ∈ U :=
        CFSG.Quasithin.H13.Sec53F.BA.mem_map_equiv_iff' α U x
      rwa [hα] at h
    have hσ2F : σ * σ ∈ F := F.mul_mem hσ hσ
    have heD : e * (σ * e * σ⁻¹) ∈ D := D.mul_mem he (hFD σ hσ e he)
    have hσ2D : σ * σ ∈ D := by
      have hα2' : e * (σ * e * σ⁻¹) * (σ * σ) = 1 := by
        rw [← hα2]
        rw [hαeσ]
        group
      rw [eq_inv_of_mul_eq_one_right hα2']
      exact D.inv_mem heD
    have hσ2fix : ∀ x ∈ H, (σ * σ) x = x := by
      intro x hx
      have hxN : x ∈ Subgroup.normalizer (U : Set Y) := hHU hx
      have h1 : x⁻¹ * (σ * σ) x ∈ U := hDtriv (σ * σ) hσ2D x hxN
      have h2 : (σ * σ) x ∈ H := hFH (σ * σ) hσ2F x hx
      have h3 : x⁻¹ * (σ * σ) x ∈ H := H.mul_mem (H.inv_mem hx) h2
      exact (inv_mul_eq_one.mp (hUH _ h1 h3)).symm
    have hσ2 : σ * σ = 1 := hFfaith (σ * σ) hσ2F hσ2fix
    have hσfixA : ∀ x ∈ A, σ x = x := fun x hx => hFinv σ hσ hσ2 x hx
    intro x hx
    have hxH : x ∈ H := hAH hx
    have hxN : x ∈ Subgroup.normalizer (U : Set Y) := hHU hxH
    have hαx : α x = e x := by
      rw [hαeσ, MulAut.mul_apply, hσfixA x hx]
    rw [hαx]
    have h1 : x⁻¹ * e x ∈ U := hDtriv e he x hxN
    have h2 : x * (x⁻¹ * e x) * x⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp hxN (x⁻¹ * e x)).mp h1
    have h3 : x * (x⁻¹ * e x) * x⁻¹ = e x * x⁻¹ := by group
    rwa [h3] at h2

theorem isScalarTorus_of_fieldBorelData {Y : Type} [Group Y] {n e q : ℕ}
    {U H A : Subgroup Y} {F : Subgroup (MulAut Y)}
    (D : CFSG.LocalAnalysis.UniquenessCase.UC22.FieldBorelData n e U H F)
    (hAH : A ≤ H) (hA : IsElemAbelian q A) (hcard : Nat.card A = q ^ 2)
    (hFinv : ∀ σ ∈ F, σ * σ = 1 → ∀ x ∈ A, σ x = x) : IsScalarTorus q U A := by
  let Eset : Subgroup (MulAut Y) :=
    (Subgroup.normalizer (U : Set Y)).map (MulAut.conj : Y →* MulAut Y)
  refine isScalarTorus_of_normalForm (F := F) (D := Eset) D.borel.H_le D.borel.U_inf_H
    hAH hA hcard D.borel.F_H D.borel.F_faithful ?_ ?_ ?_ ?_ hFinv
  · rintro e he b hb
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp he
    exact normalizer_inv_mul_conj_mem D.borel hg hb
  · rintro σ hσ e he
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp he
    exact mul_conj_mul_inv_mem_map D.borel hσ hg
  · intro α hα
    obtain ⟨g, hg, σ, hσ, hασ⟩ := D.borel.normal_form α hα
    exact ⟨MulAut.conj g, Subgroup.mem_map.mpr ⟨g, hg, rfl⟩, σ, hσ, hασ⟩
  · exact fun α hα => D.pow_action hα

theorem isScalarTorus_of_fieldBorelDiagData {Y : Type} [Group Y] {n e q : ℕ}
    {U H A : Subgroup Y} {F Eg : Subgroup (MulAut Y)}
    (D : CFSG.LocalAnalysis.UniquenessCase.UC22.FieldBorelDiagData n e U H F Eg)
    (hAH : A ≤ H) (hA : IsElemAbelian q A) (hcard : Nat.card A = q ^ 2)
    (hFinv : ∀ σ ∈ F, σ * σ = 1 → ∀ x ∈ A, σ x = x) : IsScalarTorus q U A :=
  isScalarTorus_of_normalForm (F := F) (D := Eg) D.borel.H_le D.borel.U_inf_H
    hAH hA hcard D.borel.F_H D.borel.F_faithful D.borel.E_triv D.borel.F_E
    D.borel.normal_form (fun α hα => D.pow_action hα) hFinv

end CFSG.LocalAnalysis.RankThreeUC.S15

end
