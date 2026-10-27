module

public import CFSG.LargeExtraspecial.GLW4Config
public import CFSG.LargeExtraspecial.GLW4Elim
public import CFSG.LargeExtraspecial.S14W4LocFin
public import CFSG.LargeExtraspecial.GLW4Stmt
public import CFSG.LargeExtraspecial.S12InspP4Plus
public import CFSG.LargeExtraspecial.GLW4FusH
public import CFSG.LargeExtraspecial.GLW4Inst

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.GLW4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S14 CFSG.LargeExtraspecial.GLR

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O} {c : Config}

theorem fusion_of (h : W4Hyp S g t c) [IsSimpleGroup G]
    (hCE : CentralExtInput.{0}) (hNQ : NQIrredStmt) (hNQ6 : NQPlus6Stmt)
    {A B : Submodule (ZMod 2) h.S₀.Qt} (L : LatData h.S₀ h.R₀ A B) {g₀ : ↥(Mbar0 S)}
    (hX : Nonempty (h.S₀.Xbar12 g₀ ≃* Matrix.SpecialLinearGroup (Fin h.S₀.width) (ZMod 2)))
    (k : ↥(Mbar0 S)) (hk : k * h.S₀.z * k⁻¹ ∈ h.S₀.QG) :
    h.S₀.cl (k * h.S₀.z * k⁻¹) ∈ A ∨ h.S₀.cl (k * h.S₀.z * k⁻¹) ∈ B := by
  have : FiniteDimensional (ZMod 2) (Vt S g t) := Module.Finite.of_finite
  have hR : ∀ γ ∈ omegaGroup h.qf h.qf_nondeg, ∃ r ∈ (h.R₀ : Set ↥(Mbar0 S)), ∀ v : Vt S g t,
      ((γ v : Vt S g t) : S.Qt) = ((ι S r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by
    intro γ hγ
    rw [← h.RmodN_eq] at hγ
    obtain ⟨x, hx, hxγ⟩ := hγ
    have hR₀ := h.exists_R₀ hx
    obtain ⟨r, hr, rfl⟩ := hR₀
    exact ⟨r, hr, hxγ⟩
  exact (lev_of h hCE).fusion (L.pair_Xbar12 h.width_S₀ g₀ hX) Setting.Xbar12_le_Mbar
    h.finrank_Vt h.qf_nondeg (R := (h.R₀ : Set ↥(Mbar0 S))) (fun r hr => h.R₀_le_M hr)
    (fun r hr a ha => L.inv₁ ⟨r, h.R₀_le_M hr⟩ hr a ha)
    (fun r hr b hb => L.inv₂ ⟨r, h.R₀_le_M hr⟩ hr b hb) hR
    (fun m hm hm' => three_le_finrank h hNQ hNQ6 hm hm') k hk

omit [Finite G] in
theorem ρ_mem_Lbar_of_mem_La {X : Type*} [Group X] [Finite X] {T : Setting X} {g₀ : X}
    {α : T.M} (hα : (α : X) ∈ T.La g₀) : T.ρ α ∈ T.Lbar g₀ := by
  rw [← T.map_La_eq_Lbar g₀]
  exact ⟨α, mem_subgroupOf.mpr hα, rfl⟩

omit [Finite G] in
theorem LatData.map_symm_of_map {K : Type*} [Group K] [Finite K] {T : Setting K}
    {R : Subgroup K} {A B : Submodule (ZMod 2) T.Qt} (L : LatData T R A B) {k : T.M}
    (hswap : A.map ((T.ρ k : T.O) : T.Qt →ₗ[ZMod 2] T.Qt) = B) :
    B.map ((T.ρ k : T.O) : T.Qt →ₗ[ZMod 2] T.Qt) = A := by
  have hm := L.map_eq k
  rcases hm with ⟨h1, -⟩ | ⟨-, h2⟩
  · exfalso
    have hi := L.inf
    rw [← hswap, h1, inf_idem] at hi
    have h4 := L.finrank₁
    rw [hi, finrank_bot] at h4
    omega
  · exact h2

omit [Finite G] in
theorem false_of_residual_core {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {T : Setting X} (hw : T.width = 4) {R : Subgroup X} {A B : Submodule (ZMod 2) T.Qt}
    (L : LatData T R A B) {k : T.M}
    (hswap : A.map ((T.ρ k : T.O) : T.Qt →ₗ[ZMod 2] T.Qt) = B) {g₀ : X}
    (ha : g₀ * T.z * g₀⁻¹ ∈ T.QG) (hne : g₀ * T.z * g₀⁻¹ ≠ T.z)
    (hclA : T.cl (g₀ * T.z * g₀⁻¹) ∈ A) {t₁ : T.O} (hΓ : T.S12GammaLResidual g₀ t₁)
    (hfus : ∀ x : X, x * T.z * x⁻¹ ∈ T.QG → T.cl (x * T.z * x⁻¹) ∈ A ∨ T.cl (x * T.z * x⁻¹) ∈ B) :
    False := by
  obtain ⟨-, hC1, -, hidx, ⟨e⟩, -⟩ := hΓ
  have hcard : Nat.card (T.Lbar g₀) = 2 ^ (T.width - 1) := by
    have hmod := hC1.model
    obtain ⟨m, -, -, hm⟩ := hmod
    rcases hm with ⟨hL, hidx', hC⟩ | ⟨-, hL8, -⟩
    · have hfin := Setting.case1_finrank ha hne (by rw [hw]; omega) hL hidx' hC
      rw [hL, hfin.1]
    · rw [hL8, hw]
      norm_num
  have hD : Data T (T.Xbar12 g₀) A B g₀ :=
    ⟨L.pair_Xbar12 hw g₀ ⟨e⟩, le_of_eq hw.symm, Setting.Xbar12_le_Mbar, hidx,
      fun σ hσ hσX => L.map_eq_of_not_mem hidx hswap hσ hσX, ha, hne, hclA, hcard, hfus⟩
  have hC := nonempty_config_of_data hD ⟨e⟩
  obtain ⟨C⟩ := hC
  exact false_of_config_four C hw

omit [Finite G] in
theorem false_of_residual_of {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {T : Setting X}
    (hw : T.width = 4) {R : Subgroup X} {A B : Submodule (ZMod 2) T.Qt} (L : LatData T R A B)
    {k : T.M} (hswap : A.map ((T.ρ k : T.O) : T.Qt →ₗ[ZMod 2] T.Qt) = B) {g₀ : X}
    (ha : g₀ * T.z * g₀⁻¹ ∈ T.QG) (hne : g₀ * T.z * g₀⁻¹ ≠ T.z) {t₁ : T.O}
    (hΓ : T.S12GammaLResidual g₀ t₁)
    (hfus : Nonempty (T.Xbar12 g₀ ≃* Matrix.SpecialLinearGroup (Fin T.width) (ZMod 2)) →
      ∀ x : X, x * T.z * x⁻¹ ∈ T.QG → T.cl (x * T.z * x⁻¹) ∈ A ∨ T.cl (x * T.z * x⁻¹) ∈ B) :
    False := by
  have hX := hΓ.2.2.2.2.1
  have hf := hfus hX
  rcases hf g₀ ha with hcl | hcl
  · exact false_of_residual_core hw L hswap ha hne hcl hΓ hf
  · exact false_of_residual_core hw L.symm (L.map_symm_of_map hswap) ha hne hcl hΓ
      fun x hx => (hf x hx).symm

theorem false_of_outer (h : W4Hyp S g t c) [IsSimpleGroup G]
    (hRI : RootInvolutionComponentsInput.{0}) (hARS : CFSG.Timmesfeld.ARSInput)
    (hTri : FischerTrialityInput) (hFischer : S12FischerStatement)
    (hInsp : Insp4PlusInput) (h36 : Timmesfeld36Input)
    (hSL : S12SL4ModuleInput) (hTI : WeaklyClosedTITransitive.{0}) (hCE : CentralExtInput.{0})
    (hNQ : NQIrredStmt) (hNQ6 : NQPlus6Stmt) (hp : c = .omegaPlus6) {k : h.S₀.M}
    (hk : ∀ r : h.S₀.M, (r : ↥(Mbar0 S)) ∈ h.R₀ → h.π (r⁻¹ * k) ≠ 1) {g₀ : ↥(Mbar0 S)}
    (ha : g₀ * h.S₀.z * g₀⁻¹ ∈ h.S₀.QG) (hne : g₀ * h.S₀.z * g₀⁻¹ ≠ h.S₀.z) : False := by
  have : IsSimpleGroup ↥(Mbar0 S) := h.simple
  have hlat := exists_lat4 h hNQ6 hp
  obtain ⟨W₁, W₂, hl⟩ := hlat
  have L := latData_of h hl
  have hswap := swap_of_outer h hl hk
  have hirr : ¬ h.S₀.IsReducible := L.not_isReducible_of_swap hswap
  by_cases hA : h.S₀.HasTypeAInL g₀
  · obtain ⟨α, hαL, -, hαA⟩ := hA
    have ht := ρ_mem_Lbar_of_mem_La hαL
    have h1216 := Setting.timmesfeld_12_16_of_insp4Plus hRI hARS hTri hFischer hInsp h36 hSL
      h.width_S₀ (fun P hP => h.card_le_of_isPGroup hNQ hNQ6 P hP)
      (fun P hab h2 => h.card_le_of_elemAbelian hNQ hNQ6 P hab h2)
      (fun N hN => dvd_card_or_dvd_index_of_plus h hNQ6 hp N hN) ha hne ht hαA
    rcases h1216 with hred | h8 | hΓ | hSp
    · exact hirr hred
    · exact h.not_omegaPlusEight hNQ hNQ6 h8
    · exact false_of_residual_of h.width_S₀ L hswap ha hne hΓ
        fun hX => fusion_of h hCE hNQ hNQ6 L hX
    · exact h.not_spSixSpin hNQ hNQ6 g₀ hSp
  · exact h.false_of_noA2 hNQ hNQ6 hTI ha hne hA hirr

theorem ι_inv_mul {M' : Subgroup ↥(Mbar0 S)} (r k : M') :
    ι S ((r⁻¹ * k : M') : ↥(Mbar0 S)) = (ι S r)⁻¹ * ι S k :=
  (map_mul ((ι S).comp M'.subtype) r⁻¹ k).trans
    (congrArg (· * ((ι S).comp M'.subtype) k) (map_inv ((ι S).comp M'.subtype) r))

theorem centPlus6Stmt_of (hRI : RootInvolutionComponentsInput.{0})
    (hARS : CFSG.Timmesfeld.ARSInput) (hTri : FischerTrialityInput)
    (hFischer : S12FischerStatement) (hInsp : Insp4PlusInput)
    (h36 : Timmesfeld36Input) (hSL : S12SL4ModuleInput) (hTI : WeaklyClosedTITransitive.{0})
    (hCE : CentralExtInput.{0}) (hNQ : NQIrredStmt) (hNQ6 : NQPlus6Stmt) : CentPlus6Stmt := by
  intro G _ _ _ S g t hSt hocc hext hsimp h7 hle hF hx k hk hkt
  by_contra hcon
  push Not at hcon
  have h : W4Hyp S g t .omegaPlus6 := ⟨hSt, Or.inr rfl, hocc, hext, hsimp, h7, hle, hF⟩
  have hk' := exists_ι_eq hk
  obtain ⟨k₀, rfl⟩ := hk'
  have hk₀M : k₀ ∈ h.S₀.M := h.mem_S₀_M.mpr hkt
  obtain ⟨x, hxM, hxN, hxne⟩ := hx
  have hx' := exists_ι_eq hxM
  obtain ⟨x₀, rfl⟩ := hx'
  have hι : ι S (x₀ * h.S₀.z * x₀⁻¹) = ι S x₀ * t * (ι S x₀)⁻¹ := ι_conj S x₀ h.S₀.z
  have ha : x₀ * h.S₀.z * x₀⁻¹ ∈ h.S₀.QG := h.mem_S₀_QG.mpr (by rw [hι]; exact hxN)
  have hne : x₀ * h.S₀.z * x₀⁻¹ ≠ h.S₀.z := fun he => hxne (by
    rw [← hι, he]
    rfl)
  refine false_of_outer h hRI hARS hTri hFischer hInsp h36 hSL hTI hCE hNQ hNQ6 rfl
    (k := ⟨k₀, hk₀M⟩) (fun r hr hπ => ?_) ha hne
  have hv' := hcon (ι S r) hr
  obtain ⟨v, hv, hne'⟩ := hv'
  apply hne'
  have h1 := (h.π_eq_one_iff _).mp hπ v hv
  rw [ι_inv_mul r ⟨k₀, hk₀M⟩] at h1
  exact h1

end CFSG.LargeExtraspecial.GLW4
