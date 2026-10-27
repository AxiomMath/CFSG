module

public import CFSG.LargeExtraspecial.S14SMKTransInner
public import CFSG.LargeExtraspecial.S14SMKTransOrbit

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.SMK

open Subgroup Module QuadraticMap CFSG.Open CFSG.Fischer CFSG.SmithE
  CFSG.LargeExtraspecial.SMod20 CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem Phi_conj_tvEquiv
    {ψ : Mbar0 S ≃* T46} {φ : S.Qt ≃ₗ[ZMod 2] V}
    (hψ : ∀ m : S.M, ∀ h0 : rhoM S m ∈ Mbar0 S, Phi S φ m = rhoMod (ψ ⟨rhoM S m, h0⟩))
    (x : S.M) (p : Fin 693) :
    Phi S φ x * tvEquiv p.val * (Phi S φ x)⁻¹ = tvEquiv (piM S ψ (rhoM S x) p).val := by
  obtain ⟨m, h0, hm⟩ := exists_rhoM_mem_Mbar0 ψ ⟨tvP p, tvP_mem p⟩
  have h1 : tvEquiv p.val = Phi S φ m := by rw [hψ m h0, hm, rhoMod_tvP]
  have h0' : rhoM S (x * m * x⁻¹) ∈ Mbar0 S := by
    rw [map_mul, map_mul, map_inv]
    exact (timmesfeldFStar_normal S.Mbar).conj_mem _ h0 _
  have e1 : (⟨rhoM S (x * m * x⁻¹), h0'⟩ : Mbar0 S) =
      mbarConj S (rhoM S x) ⟨rhoM S m, h0⟩ := by
    apply Subtype.ext
    rw [coe_mbarConj]
    simp only [map_mul, map_inv]
  have h2 : ψ ⟨rhoM S (x * m * x⁻¹), h0'⟩ = ⟨tvP (piM S ψ (rhoM S x) p), tvP_mem _⟩ := by
    rw [e1, ← mbarHom_apply, hm]
    exact Subtype.ext (autPerm_tvP _ p)
  have e2 : Phi S φ x * Phi S φ m * (Phi S φ x)⁻¹ = Phi S φ (x * m * x⁻¹) := by
    simp only [map_mul, map_inv]
  have e3 : Phi S φ x * tvEquiv p.val * (Phi S φ x)⁻¹ = Phi S φ (x * m * x⁻¹) := by
    rw [← e2, h1]
  exact e3.trans ((hψ _ h0').trans ((congrArg rhoMod h2).trans (rhoMod_tvP _)))

section Main

variable
  [IsSimpleGroup G]

theorem smithEClause4_of (I : Inputs10) (hInv : InvolutionFacts) (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) {φ : S.Qt ≃ₗ[ZMod 2] V}
    (hφ : SmithEClauses1235 S φ) : SmithEClause4 S φ := by
  obtain ⟨ψ, hmod, hψ⟩ := exists_isModelPhi_of_clauses I hw hU hφ
  obtain ⟨c, hc, hcQ, hcw⟩ := hφ.2.1 0 (by norm_num)
  obtain ⟨g₀, rfl⟩ := isConj_iff.mp hc
  have hane : g₀ * S.z * g₀⁻¹ ≠ S.z := by
    intro h
    rw [h, S.cl_z, map_zero] at hcw
    exact SMG.wt_ne_zero (show (0 : ℕ) < 891 by norm_num) (hcw.symm.trans (by decide))
  intro x hxc hxM hxQ
  obtain ⟨g, rfl⟩ := isConj_iff.mp hxc
  suffices h : ∃ v, IsConj S.z v ∧ v ∈ S.QG ⊓ S.Qa g by
    obtain ⟨v, hv, hvD⟩ := h
    obtain ⟨k, rfl⟩ := isConj_iff.mp hv
    obtain ⟨p, -, hp⟩ := acts_tv_of_mem_Qa I hmod hw hxM hxQ hvD
    exact ⟨p.val, p.2, (acts_iff hxM p.2).mpr hp⟩
  have hx2 : (g * S.z * g⁻¹) ^ 2 = 1 := by rw [conj_pow, S.z_sq, mul_one, mul_inv_cancel]
  have hπN := piM_mem_normalizer ψ (rhoM S ⟨g * S.z * g⁻¹, hxM⟩)
  have hAt := Phi_conj_tvEquiv hψ ⟨g * S.z * g⁻¹, hxM⟩
  have hAA : Phi S φ ⟨g * S.z * g⁻¹, hxM⟩ * Phi S φ ⟨g * S.z * g⁻¹, hxM⟩ = 1 := by
    rw [← map_mul, Phi_eq_one_iff]
    have e : ((⟨g * S.z * g⁻¹, hxM⟩ * ⟨g * S.z * g⁻¹, hxM⟩ : S.M) : G) = 1 := by
      rw [Subgroup.coe_mul, ← pow_two, hx2]
    rw [e]
    exact S.QG.one_mem
  have hA1 : Phi S φ ⟨g * S.z * g⁻¹, hxM⟩ ≠ 1 := fun h => hxQ ((Phi_eq_one_iff _).mp h)
  obtain ⟨hl5, hts⟩ := hInv _ _ ⟨hπN, hAt, hAA, hA1⟩
  have hint : ∀ v, Phi S φ ⟨g * S.z * g⁻¹, hxM⟩ (φ v) =
      φ ((S.ρ ⟨g * S.z * g⁻¹, hxM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := fun v => by
    rw [Phi_apply, LinearEquiv.symm_apply_apply]
  have hdim : finrank (ZMod 2) (commSpace (Phi S φ ⟨g * S.z * g⁻¹, hxM⟩)) =
      finrank (ZMod 2) (S.commQt (g * S.z * g⁻¹)) := by
    rw [S.commQt_of_mem hxM]
    exact finrank_commSpace_of_intertwine φ hint
  by_cases hxz : IsConj S.z (g * S.z * g⁻¹ * S.z)
  · exact exists_isConj_mem_Dl ψ hw hxM hxQ (hdim ▸ hl5) hxz
  have hsing := S.q_eq_zero_of_mem_commQt hxM hx2 (fixQt_eq_of_not_isConj S hxM hxz)
  have hpol : ∀ u v, polar (S.q.comp (φ.symm : V →ₗ[ZMod 2] S.Qt)) u v = fModel u v := by
    intro u v
    have e : polar (S.q.comp (φ.symm : V →ₗ[ZMod 2] S.Qt)) u v =
        polar S.q (φ.symm u) (φ.symm v) := by
      simp only [polar, comp_apply, LinearEquiv.coe_coe, map_add]
    rw [e, ← hmod.isometry I hw hcQ hane, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
  have hwt : ∀ i < 891, S.q.comp (φ.symm : V →ₗ[ZMod 2] S.Qt) (wtV i) = 0 := by
    intro i hi
    obtain ⟨h, hbQ, hbne, hpl⟩ := exists_planeOf_eq ψ hw hcQ hane ⟨i, hi⟩
    have e : φ.symm (wtV i) = S.cl (h * S.z * h⁻¹) := by
      rw [cl_eq_xcl I ψ hw hbQ hbne, hpl, ← hmod.symm_wtV ⟨i, hi⟩]
    rw [comp_apply, LinearEquiv.coe_coe, e, S.q_cl_eq_zero_iff hbQ, conj_pow, S.z_sq, mul_one,
      mul_inv_cancel]
  have hts' : ∀ v ∈ commSpace (Phi S φ ⟨g * S.z * g⁻¹, hxM⟩),
      S.q.comp (φ.symm : V →ₗ[ZMod 2] S.Qt) v = 0 := by
    intro v hv
    rw [commSpace_eq_map_of_intertwine φ hint] at hv
    obtain ⟨w, hw', rfl⟩ := hv
    rw [comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact hsing w (by rw [S.commQt_of_mem hxM]; exact hw')
  rcases hts _ hpol hwt hts' with ⟨i, hi, hUi⟩ | ⟨hl8, hF⟩
  · exact exists_isConj_mem_Dl_of_mem_UA I hmod hw hcQ hane hxM hxQ hxz hi hUi
  · exact (false_of_outer ψ hw hU hxM hxQ hxz (hdim ▸ hl8) hF).elim

end Main

theorem smithEClause4Stmt_of
    (I : Inputs10)
    (hInv : InvolutionFacts) : SmithEClause4Stmt :=
  fun _ _ _ _ _ hw hU _ hφ => smithEClause4_of I hInv hw hU hφ

theorem smithEClause4Stmt
    (I : Inputs10) : SmithEClause4Stmt :=
  smithEClause4Stmt_of I involutionFacts

end CFSG.LargeExtraspecial.S14.SMK

namespace CFSG.LargeExtraspecial.S14

open CFSG.Open

theorem smithEModel_of_inputs
    (hRI : RootInvolutionComponentsInput.{0})
    (hARS : CFSG.Timmesfeld.ARSInput) (hTri : FischerTrialityInput)
    (hFischer : S12FischerStatement) (hInsp : Insp5Input)
    (h36 : Timmesfeld36Input) (hSL : S12SL4ModuleInput) (hDW : DW.DW37Statement)
    (hAS : AschbacherSmithWideInput) : SmithEModel :=
  smithEModel_of_clause4 hRI hARS hTri hFischer hInsp h36 hSL hDW hAS
    (SMK.smithEClause4Stmt ⟨hRI, hARS, hTri, hFischer, hInsp, h36, hSL, hDW⟩)

end CFSG.LargeExtraspecial.S14
