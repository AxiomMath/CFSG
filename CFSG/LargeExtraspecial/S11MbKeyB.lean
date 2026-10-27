module

public import CFSG.LargeExtraspecial.S11MbKeyA
public import CFSG.LargeExtraspecial.S11MbBasic
public import CFSG.LargeExtraspecial.S11MbEichler

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.ClassicalGroups.Orthogonal (eichler)

universe u_G

variable {G : Type u_G} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O} {τ : S.M}
  {u : G} {kb σ u₁ : G}

theorem YData.mem_Qa (hy : Hyp S g) (Y : YData S g t τ u kb σ u₁) : σ ∈ S.Qa g := by
  have hne : g * S.z * g⁻¹ ≠ u₁ * S.z * u₁⁻¹ := fun h =>
    Y.not_mem_QG (by rw [Y.conj_eq, ← h]; exact hy.hyp4.conj_mem)
  rw [Y.conj_eq]
  exact S.mem_Qa_symm hne Y.a_mem

theorem YData.rho_mem_Lbar (hy : Hyp S g) (Y : YData S g t τ u kb σ u₁) :
    S.ρ ⟨σ, Y.mem_M⟩ ∈ S.Lbar g :=
  S.ρ_mem_Lbar ⟨Y.mem_Qa hy, Y.mem_M⟩

theorem YData.rho_ne_one (Y : YData S g t τ u kb σ u₁) : S.ρ ⟨σ, Y.mem_M⟩ ≠ 1 :=
  fun h => Y.not_mem_QG ((S.ρ_eq_one_iff _).mp h)

theorem YData.rho_ne (K : Conf S g t τ u) (Y : YData S g t τ u kb σ u₁) :
    S.ρ ⟨σ, Y.mem_M⟩ ≠ t := by
  intro h
  apply Y.mul_tau_not_mem
  have h1 : S.ρ (⟨σ, Y.mem_M⟩ * τ) = 1 := by
    rw [map_mul, h, ← K.rho_eq, ← map_mul, show τ * τ = 1 from Subtype.ext K.tau_mul_self,
      map_one]
  exact (S.ρ_eq_one_iff _).mp h1

theorem YData.polar_eq_zero (Y : YData S g t τ u kb σ u₁) {f c : S.Qt}
    (hf : f ∈ S.clSub (S.QG ⊓ S.Qa u₁))
    (hc : c ∈ S.clSub (S.QG ⊓ centralizer ({σ} : Set G))) : polar S.q f c = 0 := by
  obtain ⟨f₀, hf₀, hf₀Q, rfl⟩ := S.mem_clSub_iff.mp hf
  obtain ⟨c₀, hc₀, hc₀Q, rfl⟩ := S.mem_clSub_iff.mp hc
  have hcσ : c₀ * σ = σ * c₀ := mem_centralizer_singleton_iff.mp (mem_inf.mp hc₀).2
  rw [S.polar_cl_eq_zero_iff hf₀Q hc₀Q]
  exact commute_of_mem_QG_inf_Qa (τ := ⟨σ, Y.mem_M⟩) Y.rho_ne_one rfl Y.conj_eq hf₀ hc₀Q hcσ

variable (hy : Hyp S g) (K : Conf S g t τ u) (hm : finrank (ZMod 2) (Vt S g t) = 2)
  (Y : YData S g t τ u kb σ u₁)
  (hcase : ∀ w ∈ Wt S g t, (S.ρ ⟨σ, Y.mem_M⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈
    (ZMod 2) ∙ S.cl (g * S.z * g⁻¹))
include hy K hm hcase

theorem YData.mem_pointRadical :
    (S.ρ ⟨σ, Y.mem_M⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹)) := by
  set s := S.ρ ⟨σ, Y.mem_M⟩ with hs
  set c := S.cl (g * S.z * g⁻¹) with hc
  have hsL : s ∈ S.Lbar g := Y.rho_mem_Lbar hy
  have hs2 : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) * s = 1 :=
    congrArg Subtype.val (mul_self_of_mem_Lbar S hy.hyp4.conj_mem hsL)
  have hsO : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ orthogonalGroup S.q := s.2
  have hsc : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) c = c := Lbar_apply_cl hy.hyp4 hsL
  have hc0 : c ≠ 0 := cl_conj_z_ne_zero S hy.hyp4.conj_mem hy.hyp4.conj_ne
  set H := LinearMap.BilinForm.orthogonal S.q.polarBilin ((ZMod 2) ∙ c) with hH
  have hmemH : ∀ x, x ∈ H ↔ polar S.q c x = 0 := fun x => mem_orthogonal_span_singleton_iff
  have hWH : Wt S g t ≤ H := fun x hx =>
    (hmemH x).mpr (mem_Wt.mp hx c (cl_a_mem_Vt K.mem_Lbar))
  have hdH := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate ((ZMod 2) ∙ c)
  rw [finrank_span_singleton hc0, ← hH] at hdH
  have hdW := finrank_Wt (S := S) (g := g) (t := t)
  have hQt := S.finrank_Qt_eq_two_mul_width
  have hw := hy.hyp4.two_lt_width
  obtain ⟨p, hpH, hle⟩ := exists_le_sup_span_singleton hWH (by omega)
  have hsing : ∀ x ∈ H, S.q ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x) = 0 := fun x hx =>
    S.q_eq_zero_of_mem_clSub_QG_inf_Qa hy.hyp4.conj_ne
      (Lbar_sub_mem_clSub hy.hyp4 hy.cons hsL ((hmemH x).mp hx))
  have hT : ∀ x ∈ Wt S g t, ∀ x' ∈ H, polar S.q ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x) x' = 0 := by
    intro x hx x' hx'
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp (hcase x hx)
    rw [← hr, polar_smul_left, (hmemH x').mp hx', smul_zero]
  have hvan := polar_sub_eq_zero_of_le hsO hs2 hpH hpH
    (by rw [Set.pair_eq_singleton]; exact hle) hsing hT
    (by rw [polar_sub_self_eq hsO]; exact hsing p hpH)
  refine CFSG.LargeExtraspecial.mem_pointRadical.mpr ⟨hsO, hsc, fun x hx => ?_, fun v => ?_⟩
  · rw [← LinearMap.BilinForm.orthogonal_orthogonal S.q_nondegenerate S.polarBilin_isRefl
      ((ZMod 2) ∙ c)]
    refine LinearMap.BilinForm.mem_orthogonal_iff.mpr fun x' hx' => ?_
    change S.q.polarBilin x' ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x) = 0
    rw [polarBilin_apply_apply, polar_comm]
    exact hvan x ((hmemH x).mpr hx) x' hx'
  · have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hsO c v
    rw [hsc] at h1
    rw [polar_sub_right, h1, sub_self]

theorem YData.exists_commSpace :
    ∃ w₀ ∈ commSpace (S.ρ ⟨σ, Y.mem_M⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt), S.q w₀ = 1 ∧
      finrank (ZMod 2) (commSpace (S.ρ ⟨σ, Y.mem_M⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 2 := by
  set s := S.ρ ⟨σ, Y.mem_M⟩ with hs
  set c := S.cl (g * S.z * g⁻¹) with hc
  have hc0 : c ≠ 0 := cl_conj_z_ne_zero S hy.hyp4.conj_mem hy.hyp4.conj_ne
  have hcq : S.q c = 0 := (S.q_cl_eq_zero_iff hy.hyp4.conj_mem).mpr (by
    rw [pow_two]; exact conj_z_mul_self S g)
  obtain ⟨w₀, hw₀, hsw⟩ := (mem_pointRadical_iff S.q_nondegenerate hc0 hcq).mp
    (Y.mem_pointRadical hy K hm hcase)
  have hs1 : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ≠ 1 := fun h =>
    Y.rho_ne_one (Subtype.ext (by rw [← hs]; exact h))
  have hw₀c : w₀ ∉ (ZMod 2) ∙ c := fun h =>
    hs1 (by rw [hsw]; exact (eichler_eq_one_iff S.q_nondegenerate hc0 hcq hw₀).mpr h)
  obtain ⟨hcomm, hA, -⟩ := eichler_type_of_not_mem_span S.q_nondegenerate hc0 hcq hw₀ hw₀c
  have hq1 : S.q w₀ = 1 := by
    rcases zmod2_eq_zero_or_eq_one (S.q w₀) with h | h
    · exfalso
      have h2 := hA h
      rw [← hsw] at h2
      exact hy.not_isTypeA_of_mem_Lbar (Y.rho_mem_Lbar hy) Y.rho_ne_one h2
    · exact h
  have hw₀0 : w₀ ≠ 0 := fun h => hw₀c (h ▸ zero_mem _)
  have hcw : c ≠ w₀ := fun h => hw₀c (h ▸ Submodule.mem_span_singleton_self _)
  refine ⟨w₀, ?_, hq1, ?_⟩
  · rw [hsw, hcomm]
    exact Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  · rw [hsw, hcomm]
    exact finrank_span_pair (linearIndependent_pair_iff.mpr ⟨hc0, hw₀0, hcw⟩)

theorem YData.cl_mem_span_of_conj {j : G} (hj : j * S.z * j⁻¹ ∈ S.QG ⊓ S.Qa u₁) :
    S.cl (j * S.z * j⁻¹) ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
  by_contra hds
  have hjQ : j * S.z * j⁻¹ ∈ S.QG := (mem_inf.mp hj).1
  have hjz : j * S.z * j⁻¹ ≠ S.z := fun h => hds (by rw [h, S.cl_z]; exact zero_mem _)
  have hσj : σ ∈ S.Qa j := by
    have hne : j * S.z * j⁻¹ ≠ u₁ * S.z * u₁⁻¹ := fun h =>
      Y.not_mem_QG (by rw [Y.conj_eq, ← h]; exact hjQ)
    rw [Y.conj_eq]
    exact S.mem_Qa_symm hne (mem_inf.mp hj).2
  have hsj : S.ρ ⟨σ, Y.mem_M⟩ ∈ S.Lbar j := S.ρ_mem_Lbar ⟨hσj, Y.mem_M⟩
  have hR := hy.Rbar_ne_of_mem_Lbar hjQ hjz hsj hds
  have K' := hy.conf (τ := ⟨σ, Y.mem_M⟩) Y.conj_eq Y.not_mem_QG (Y.mem_Qa hy) hR
  have h1 := finrank_commSpace_eq hy.hyp4 K'.mem_Lbar K'.ne_one
  have h2 := Submodule.finrank_mono (Vt_le_Tt hy.hyp4 hy.noA2' K'.ne_one K'.lin)
  have h3 := K'.lin.two_le_finrank
  obtain ⟨-, -, -, h4⟩ := Y.exists_commSpace hy K hm hcase
  omega

theorem YData.finrank_clSub_centralizer :
    2 * S.width ≤ finrank (ZMod 2) (S.clSub (S.QG ⊓ centralizer ({σ} : Set G))) + 3 := by
  have h1 := finrank_fixSpace_le (t := S.ρ ⟨σ, Y.mem_M⟩) (τ := ⟨σ, Y.mem_M⟩) rfl
  have h2 := finrank_commSpace_add_finrank_fixSpace
    (S.ρ ⟨σ, Y.mem_M⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt)
  obtain ⟨-, -, -, h4⟩ := Y.exists_commSpace hy K hm hcase
  have h5 := S.finrank_Qt_eq_two_mul_width
  change finrank (ZMod 2) (fixSpace (S.ρ ⟨σ, Y.mem_M⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt)) ≤
    finrank (ZMod 2) (S.clSub (S.QG ⊓ centralizer ({σ} : Set G))) + 1 at h1
  omega

theorem YData.finrank_clSub_le_two :
    finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa u₁)) ≤ 2 := by
  have hd2 := Y.finrank_clSub_centralizer hy K hm hcase
  have hd1 := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate
    (S.clSub (S.QG ⊓ centralizer ({σ} : Set G)))
  set C := S.clSub (S.QG ⊓ centralizer ({σ} : Set G)) with hC
  set F := S.clSub (S.QG ⊓ S.Qa u₁) with hF
  set s := S.ρ ⟨σ, Y.mem_M⟩ with hs
  have hFC : F ≤ LinearMap.BilinForm.orthogonal S.q.polarBilin C := fun f hf =>
    LinearMap.BilinForm.mem_orthogonal_iff.mpr fun c hc => by
      change S.q.polarBilin c f = 0
      rw [polarBilin_apply_apply, polar_comm]
      exact Y.polar_eq_zero hf hc
  have hQt := S.finrank_Qt_eq_two_mul_width
  obtain ⟨w₀, hw₀, hq1, -⟩ := Y.exists_commSpace hy K hm hcase
  have hCfix : C ≤ fixSpace (s : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    have := S.clSub_centralizer_le_fixQt Y.mem_M
    rwa [S.fixQt_of_mem Y.mem_M] at this
  have hw₀C : w₀ ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin C := by
    rw [commSpace_eq_orthogonal_fixSpace_of_mem S.q_nondegenerate s.2] at hw₀
    exact LinearMap.BilinForm.orthogonal_le hCfix hw₀
  have hne : u₁ * S.z * u₁⁻¹ ≠ S.z := fun h => Y.not_mem_QG (by
    rw [Y.conj_eq, h]; exact S.z_mem_QG)
  by_contra h3
  push Not at h3
  have heq : F = LinearMap.BilinForm.orthogonal S.q.polarBilin C :=
    Submodule.eq_of_le_of_finrank_le hFC (by omega)
  rw [← heq] at hw₀C
  have := S.q_eq_zero_of_mem_clSub_QG_inf_Qa hne hw₀C
  rw [hq1] at this
  exact absurd this (by decide)

end CFSG.LargeExtraspecial.S11
