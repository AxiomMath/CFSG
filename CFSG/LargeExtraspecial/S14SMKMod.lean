module

public import CFSG.LargeExtraspecial.S14SMKGramPhi
public import CFSG.LargeExtraspecial.S14SMKGramDefs
public import CFSG.LargeExtraspecial.S14SMKModCert

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.SMK

open Subgroup CFSG.Open CFSG.Fischer CFSG.SmithE CFSG.LargeExtraspecial.SMod20 QuadraticMap
  Module

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem finrank_clSub_QG_inf_Qa_le (hw : S.width = 10) {h : G} (haQ : h * S.z * h⁻¹ ∈ S.QG)
    (hne : h * S.z * h⁻¹ ≠ S.z) : finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa h)) ≤ 10 := by
  have hz : S.z ∈ S.QG ⊓ S.Qa h := ⟨S.z_mem_QG, S.z_mem_Qa haQ hne⟩
  have h1 := S.card_clPre (S.clSub (S.QG ⊓ S.Qa h))
  rw [S.clPre_clSub inf_le_left hz, S.card_submodule] at h1
  have h2 := S.card_QG_inf_Qa_le hne
  rw [hw, h1, show 10 + 1 = 1 + 10 from rfl, pow_add, pow_one] at h2
  have h3 := Nat.le_of_mul_le_mul_left h2 (by norm_num)
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h3

section Mod

variable
  [IsSimpleGroup G] (I : Inputs10) {ψ : Mbar0 S ≃* T46}
  {φ : S.Qt ≃ₗ[ZMod 2] V}

include I in
theorem tvDiff_mem_clSub (hφ : IsModelPhi S ψ φ) (hw : S.width = 10) {h : G}
    (haQ : h * S.z * h⁻¹ ∈ S.QG) (hne : h * S.z * h⁻¹ ≠ S.z) {p : Fin 693}
    (hp : p ∈ planeSet (planeOf S ψ h)) {k : Fin 891} (hk : ¬ Opp (planeOf S ψ h) k) :
    φ.symm (tvEquiv p (wtV k) + wtV k) ∈ S.clSub (S.QG ⊓ S.Qa h) := by
  classical
  have hpU : tvP p ∈ UA (planeOf S ψ h).val :=
    tvP_mem_UA (by rw [wPlane_eq_planeSet (planeOf S ψ h).2]; exact hp)
  rw [← planeOf_spec ψ hw haQ hne] at hpU
  obtain ⟨ℓ, hℓL, hℓp⟩ := hpU
  have hℓL' : (ℓ : S.O) ∈ S.Lbar h := mem_subgroupOf.mp hℓL
  obtain ⟨m₀, hm₀, hm₀ℓ⟩ := Lbar_le_Mbar0 ψ hw haQ hne hℓL'
  obtain ⟨y, hyL, hyℓ⟩ := S.mem_Lbar_iff.mp hℓL'
  have hyM : rhoM S y = ℓ := Subtype.ext hyℓ
  have hℓ0 : ℓ ∈ Mbar0 S := by
    have : m₀ = ℓ := Subtype.ext hm₀ℓ
    exact this ▸ hm₀
  have hy0 : rhoM S y ∈ Mbar0 S := hyM ▸ hℓ0
  have hψ : ψ ⟨rhoM S y, hy0⟩ = ⟨tvP p, tvP_mem p⟩ := by
    apply Subtype.ext
    rw [← piM_of_mem]
    show piM S ψ (rhoM S y) = tvP p
    rw [hyM, hℓp]
  have hPhi : Phi S φ y = tvEquiv p := by
    rw [hφ.Phi_eq_rhoMod I hw haQ hne y hy0, hψ, rhoMod_tvP]
  obtain ⟨c, hcQ, hcne, hck⟩ := exists_planeOf_eq ψ hw haQ hne k
  have hcl : S.cl (c * S.z * c⁻¹) = xcl S ψ k := by
    rw [cl_eq_xcl I ψ hw hcQ hcne, hck]
  have hva : c * S.z * c⁻¹ * (h * S.z * h⁻¹) = h * S.z * h⁻¹ * (c * S.z * c⁻¹) := by
    rw [← S.polar_cl_eq_zero_iff hcQ haQ, hcl, cl_eq_xcl I ψ hw haQ hne,
      gram_eq_opp I ψ hw haQ hne k.2 (planeOf S ψ h).2]
    have hk' : ¬ Opp k (planeOf S ψ h) := fun ho => hk ho.symm
    simp [hk']
  have hyLa : (y : G) ∈ S.La h := (le_sup_right : S.Qa h ⊓ S.M ≤ S.La h) hyL
  have hmem := S.commutator_mem_QG_inf_Qa haQ hne hyLa hcQ hva
  have hx : S.cl ((y : G) * (c * S.z * c⁻¹) * (y : G)⁻¹ * (c * S.z * c⁻¹)⁻¹) =
      φ.symm (tvEquiv p (wtV k) + wtV k) := by
    have hconj : (y : G) * (c * S.z * c⁻¹) * (y : G)⁻¹ ∈ S.QG := S.conj_mem_QG y.2 hcQ
    rw [S.cl_mul hconj (S.QG.inv_mem hcQ), S.cl_inv hcQ, ← S.ρ_cl y hcQ, hcl, map_add,
      ← hPhi, Phi_apply, ← hφ k, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  rw [← hx]
  exact S.cl_mem_clSub hmem hmem.1

include I in
theorem mem_clSub_iff_adjW (hφ : IsModelPhi S ψ φ) (hw : S.width = 10) {h : G}
    (haQ : h * S.z * h⁻¹ ∈ S.QG) (hne : h * S.z * h⁻¹ ≠ S.z) (j : Fin 891) :
    φ.symm (wtV j) ∈ S.clSub (S.QG ⊓ S.Qa h) ↔ adjW (planeOf S ψ h) j = true := by
  obtain ⟨v, hli, hv, hadj⟩ := exists_qaBasis (planeOf S ψ h).2
  set C := S.clSub (S.QG ⊓ S.Qa h) with hC
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hle : Submodule.span (ZMod 2) (Set.range v) ≤ C.map (φ : S.Qt →ₗ[ZMod 2] V) := by
    rw [Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    obtain ⟨p, hp, k, hk, hvs⟩ := hv s
    refine ⟨φ.symm (v s), ?_, by simp⟩
    rw [hvs]
    exact tvDiff_mem_clSub I hφ hw haQ hne hp hk
  have heq : Submodule.span (ZMod 2) (Set.range v) = C.map (φ : S.Qt →ₗ[ZMod 2] V) := by
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    rw [LinearEquiv.finrank_map_eq, finrank_span_eq_card hli, Fintype.card_fin]
    exact finrank_clSub_QG_inf_Qa_le hw haQ hne
  rw [← hadj j, heq, Submodule.mem_map_equiv]

include I in
theorem mem_Qa_iff_adjW (hφ : IsModelPhi S ψ φ) (hw : S.width = 10) {h c : G}
    (haQ : h * S.z * h⁻¹ ∈ S.QG) (hne : h * S.z * h⁻¹ ≠ S.z) (hbQ : c * S.z * c⁻¹ ∈ S.QG)
    (hbne : c * S.z * c⁻¹ ≠ S.z) :
    c * S.z * c⁻¹ ∈ S.Qa h ↔ adjW (planeOf S ψ h) (planeOf S ψ c) = true := by
  have hz : S.z ∈ S.QG ⊓ S.Qa h := ⟨S.z_mem_QG, S.z_mem_Qa haQ hne⟩
  rw [← mem_clSub_iff_adjW I hφ hw haQ hne, ← hφ.cl I hw hbQ hbne,
    LinearEquiv.symm_apply_apply]
  constructor
  · intro hb
    exact S.cl_mem_clSub ⟨hbQ, hb⟩ hbQ
  · intro hb
    have := (S.clPre_clSub inf_le_left hz).le ⟨hbQ, hb⟩
    exact this.2

include I in
theorem clauses1235_of_isModelPhi (hφ : IsModelPhi S ψ φ) (hw : S.width = 10) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) : SmithEClauses1235 S φ := by
  have hcode : ∀ {h : G}, h * S.z * h⁻¹ ∈ S.QG → h * S.z * h⁻¹ ≠ S.z →
      SMG.code (φ (S.cl (h * S.z * h⁻¹))) = wt (planeOf S ψ h) := fun hbQ hbne => by
    rw [hφ.cl I hw hbQ hbne, wtV, code_decode (wt_lt (planeOf S ψ _).2)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc hcQ hcz
    obtain ⟨h, rfl⟩ := isConj_iff.mp hc
    exact ⟨_, (planeOf S ψ h).2, hcode hcQ hcz⟩
  · intro i hi
    obtain ⟨h, hbQ, hbne, hpl⟩ := exists_planeOf_eq ψ hw haQ hne ⟨i, hi⟩
    refine ⟨h * S.z * h⁻¹, isConj_iff.mpr ⟨h, rfl⟩, hbQ, ?_⟩
    rw [hcode hbQ hbne, hpl]
  · intro h b haQ' hne' hb hbQ hbz i j hi hj hai hbj
    obtain ⟨c, rfl⟩ := isConj_iff.mp hb
    rw [hcode haQ' hne'] at hai
    rw [hcode hbQ hbz] at hbj
    have e1 := Aut.wt_injective (planeOf S ψ h).2 hi hai
    have e2 := Aut.wt_injective (planeOf S ψ c).2 hj hbj
    rw [← e1, ← e2]
    exact mem_Qa_iff_adjW I hφ hw haQ' hne' hbQ hbz
  · intro k hk
    obtain ⟨m, hm⟩ := hφ.exists_Phi_eq_tvEquiv I hw haQ hne hk
    exact ⟨m, m.2, (acts_iff m.2 hk).mpr hm⟩

end Mod

theorem clauses1235
    [IsSimpleGroup G] (I : Inputs10)
    (hAS : AschbacherSmithWideInput) (S : Setting G) (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) :
    ∃ φ : S.Qt ≃ₗ[ZMod 2] (Fin 20 → ZMod 2), SmithEClauses1235 S φ := by
  obtain ⟨ψ⟩ := nonempty_mbar0_equiv_T46 S hU
  obtain ⟨g, haQ, hne⟩ := exists_conj_mem_QG hAS hw hU
  obtain ⟨φ, hφ⟩ := exists_isModelPhi I ψ hw haQ hne
  exact ⟨φ, clauses1235_of_isModelPhi I hφ hw haQ hne⟩

end CFSG.LargeExtraspecial.S14.SMK

namespace CFSG.LargeExtraspecial.S14

open CFSG.Open

theorem smithEModel_of_clause4
    (hRI : RootInvolutionComponentsInput.{0})
    (hARS : CFSG.Timmesfeld.ARSInput) (hTri : FischerTrialityInput)
    (hFischer : S12FischerStatement) (hInsp : Insp5Input)
    (h36 : Timmesfeld36Input) (hSL : S12SL4ModuleInput) (hDW : DW.DW37Statement)
    (hAS : AschbacherSmithWideInput) (h4 : SmithEClause4Stmt) : SmithEModel :=
  smithEModel_of_clauses (fun _ _ _ _ S hw hU =>
    SMK.clauses1235 ⟨hRI, hARS, hTri, hFischer, hInsp, h36, hSL, hDW⟩ hAS S hw hU) h4

end CFSG.LargeExtraspecial.S14
