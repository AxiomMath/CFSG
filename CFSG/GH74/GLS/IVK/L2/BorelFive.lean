module

public import CFSG.GH74.GLS.IVK.L2.BorelStd

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG.PSL2Table
open scoped MatrixGroups Pointwise

namespace L2Borel

section Conj

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K]

@[expose] noncomputable def eConj (e : K ≃* L2 F) (c : PSL(2, F)) : K ≃* L2 F :=
  ((toPSL e).trans (MulAut.conj c⁻¹)).trans (L2.equivPSL F).symm

omit [Finite F] in
theorem toPSL_eConj (e : K ≃* L2 F) (c : PSL(2, F)) (k : K) :
    toPSL (eConj e c) k = c⁻¹ * toPSL e k * c := by
  simp [toPSL, eConj]

theorem innDiagHom_eConj (e : K ≃* L2 F) (c : PSL(2, F)) (g : PGL(2, F)) :
    innDiagHom (eConj e c) g =
      innDiagHom e (Matrix.ProjectiveSpecialLinearGroup.toPGL c * g *
        (Matrix.ProjectiveSpecialLinearGroup.toPGL c)⁻¹) := by
  ext x
  apply (toPSL e).injective
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  have h := toPGL_toPSL_innDiagHom (eConj e c) g x
  rw [toPSL_eConj, toPSL_eConj] at h
  simp only [map_mul, map_inv] at h
  rw [toPGL_toPSL_innDiagHom]
  set C := Matrix.ProjectiveSpecialLinearGroup.toPGL c
  set L := Matrix.ProjectiveSpecialLinearGroup.toPGL (toPSL e (innDiagHom (eConj e c) g x))
  set X := Matrix.ProjectiveSpecialLinearGroup.toPGL (toPSL e x)
  calc L = C * (C⁻¹ * L * C) * C⁻¹ := by group
    _ = C * (g * (C⁻¹ * X * C) * g⁻¹) * C⁻¹ := by rw [h]
    _ = C * g * C⁻¹ * X * (C * g * C⁻¹)⁻¹ := by group

theorem innDiagSub_eConj (e : K ≃* L2 F) (c : PSL(2, F)) :
    innDiagSub (eConj e c) = innDiagSub e := by
  ext α
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨_, (innDiagHom_eConj e c g).symm⟩
  · rintro ⟨g, rfl⟩
    refine ⟨(Matrix.ProjectiveSpecialLinearGroup.toPGL c)⁻¹ * g *
      Matrix.ProjectiveSpecialLinearGroup.toPGL c, ?_⟩
    rw [innDiagHom_eConj]
    congr 1
    group

theorem exists_isStd {p n : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ n) [Finite K]
    (e : K ≃* L2 F) (W : Sylow p K) :
    ∃ c : PSL(2, F), IsStd (eConj e c) (W : Subgroup K) ∧
      (W : Subgroup K) = (unipotent F).map (psiEquiv e c).toMonoidHom := by
  obtain ⟨c, hc⟩ := exists_psiEquiv_eq e hp hF W
  refine ⟨c, fun k => ?_, hc⟩
  rw [toPSL_eConj, hc, Subgroup.mem_map_equiv, psiEquiv_symm_apply]

theorem le_innDiagSub_of_cyclic_sylow {p n : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ n) [Finite K]
    (e : K ≃* L2 F) (h2 : (2 : F) ≠ 0) (W : Sylow p K) {D : Subgroup (MulAut K)}
    (hD : D ≤ MulAction.stabilizer (MulAut K) (W : Subgroup K)) (hcyc : IsCyclic D)
    (hDcard : Nat.card D = Nat.card F - 1) : D ≤ innDiagSub e := by
  obtain ⟨c, hstd, -⟩ := exists_isStd hp hF e W
  rw [← innDiagSub_eConj e c]
  exact le_innDiagSub_of_cyclic hstd h2 hD hcyc hDcard

theorem not_le_innAut {p n : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ n) (hodd : Odd (Nat.card F))
    [Finite K] (e : K ≃* L2 F) (h2 : (2 : F) ≠ 0) (W : Sylow p K) {D : Subgroup (MulAut K)}
    (hD : D ≤ MulAction.stabilizer (MulAut K) (W : Subgroup K))
    (hDcard : Nat.card D = Nat.card F - 1) : ¬ D ≤ innAut K := by
  intro hle
  obtain ⟨c, -, hc⟩ := exists_isStd hp hF e W
  have hDN : D ≤ (Subgroup.normalizer ((W : Subgroup K) : Set K)).map
      (MulAut.conj : K →* MulAut K) := by
    intro α hα
    obtain ⟨k, rfl⟩ := hle hα
    refine Subgroup.mem_map.2 ⟨k, ?_, rfl⟩
    have := mem_stabilizer_iff_forall.1 (hD hα)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h := this x
    simpa [MulAut.conj_apply] using h.symm
  have hdvd : Nat.card D ∣ Nat.card ((Subgroup.normalizer ((W : Subgroup K) : Set K)).map
      (MulAut.conj : K →* MulAut K)) := Subgroup.card_dvd_of_le hDN
  have hNcard : Nat.card (Subgroup.normalizer ((W : Subgroup K) : Set K)) =
      Nat.card (borel F) := by
    have : Subgroup.normalizer ((W : Subgroup K) : Set K) =
        (borel F).map (psiEquiv e c).toMonoidHom := by
      rw [hc, normalizer_map_equiv, normalizer_unipotent_eq h2]
    rw [this, Subgroup.card_map_of_injective (psiEquiv e c).injective]
  rw [Subgroup.card_map_of_injective (conj_injective_of_L2 e), hNcard, hDcard] at hdvd
  have := Fintype.ofFinite F
  have hB := card_borel h2 (F := F)
  rw [← Nat.card_eq_fintype_card] at hB
  obtain ⟨m, hm⟩ := hdvd
  obtain ⟨r, hr⟩ := hodd
  have hq2 : 2 ≤ Nat.card F := by
    have : 1 < Nat.card F := Finite.one_lt_card
    omega
  have hpos : 0 < Nat.card F - 1 := by omega
  have h3 : (Nat.card F - 1) * (2 * m) = (Nat.card F - 1) * Nat.card F := by
    rw [← hB, hm]
    ring
  have h4 : 2 * m = Nat.card F := Nat.eq_of_mul_eq_mul_left hpos h3
  omega

noncomputable def innDiagEquivPGL (e : K ≃* L2 F) : innDiagSub e ≃* PGL(2, F) :=
  (MonoidHom.ofInjective (innDiagHom_injective e)).symm

end Conj

end L2Borel

open L2Borel


theorem ivk_1_5e : IVK_1_5e := by
  intro F _ _ hF K _ _ e p n hp hcard W D hD hcyc hDcard
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hF.1
  have hDstab : D ≤ MulAction.stabilizer (MulAut K) (W : Subgroup K) := fun x hx => (hD hx).2
  have hDle := le_innDiagSub_of_cyclic_sylow hp hcard e h2 W hDstab hcyc hDcard
  have hDnot := not_le_innAut hp hcard hF.1 e h2 W hDstab hDcard
  obtain ⟨t, htD, htInn⟩ := IsConcreteLE.not_le_iff_exists.1 hDnot
  have hsup : innAut K ⊔ D = innDiagSub e := by
    apply le_antisymm (sup_le (innAut_le_innDiagSub e) hDle)
    rw [← innAut_sup_zpowers_eq e hF (hDle htD) htInn]
    exact sup_le_sup_left ((Subgroup.zpowers_le).2 htD) _
  exact ⟨(MulEquiv.subgroupCongr hsup).trans (innDiagEquivPGL e)⟩

end CFSG.GH74.GLS.IVK
