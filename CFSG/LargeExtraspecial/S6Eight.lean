module

public import CFSG.LargeExtraspecial.S3bTenB
public import CFSG.LargeExtraspecial.S4FiveMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.OrthoF2

theorem mul_self_mem_of_relIndex_le_two {X : Type*} [Group X] [Finite X] {H K : Subgroup X}
    (h : H.relIndex K ≤ 2) {r : X} (hr : r ∈ K) : r * r ∈ H := by
  have hne : H.relIndex K ≠ 0 := by
    intro h0
    have h1 := Subgroup.relIndex_mul_card H K
    rw [h0, zero_mul] at h1
    exact (Nat.card_pos (α := K)).ne h1
  obtain h1 | h2 : H.relIndex K = 1 ∨ H.relIndex K = 2 := by omega
  · exact Subgroup.relIndex_eq_one.mp h1 (mul_mem hr hr)
  · have h2' : (H.subgroupOf K).index = 2 := h2
    have := (Subgroup.mul_mem_iff_of_index_two h2' (a := ⟨r, hr⟩) (b := ⟨r, hr⟩)).mpr Iff.rfl
    exact Subgroup.mem_subgroupOf.mp this

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

variable (S g) in
@[expose] def FusionCtl : Prop :=
  ∀ k : G, k * S.z * k⁻¹ ∈ S.QG → k * S.z * k⁻¹ ≠ S.z →
    ∃ m ∈ S.M, m * (g * S.z * g⁻¹) * m⁻¹ = k * S.z * k⁻¹

theorem fusionCtl_of_lemma_3_13 (H : Hyp4 S g)
    (hno : ∀ g' : G, g' * S.z * g'⁻¹ ∈ S.QG → g' * S.z * g'⁻¹ ≠ S.z → ¬ S.HasTypeAInL g') :
    FusionCtl S g := by
  intro k hkQ hkz
  have h2 : 2 ≤ S.width := by
    have := H.two_lt_width
    omega
  have e : k * g⁻¹ * (g * S.z * g⁻¹) * (k * g⁻¹)⁻¹ = k * S.z * k⁻¹ := by group
  obtain ⟨m, hm, hmx⟩ := S.lemma_3_13 h2 hno H.conj_mem (conj_z_ne_one S g) H.conj_ne
    (k := k * g⁻¹) (by rw [e]; exact hkQ) (by rw [e]; exact hkz)
  exact ⟨m, hm, hmx.trans e⟩

theorem exists_mem_Rbar_sq {t : S.O} {ht : t ∈ S.Lbar g} (H : Hyp4 S g) (hL : LinCase S g ht)
    {v : Vt S g t} (hv : v ∉ (ZMod 2) ∙ aV ht) :
    ∃ r ∈ Rbar S g t, (r : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (S.cl (g * S.z * g⁻¹))) = S.cl (g * S.z * g⁻¹) + v := by
  set A := aV ht with hA
  have hA0 : A ≠ 0 := aV_ne_zero H ht
  obtain ⟨φ₂, hφ₂v, hφ₂A⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
  have hφ₂A' : φ₂ A = 0 := by
    have : φ₂ A ∈ ((ZMod 2) ∙ A).map φ₂ := ⟨A, Submodule.mem_span_singleton_self A, rfl⟩
    rw [hφ₂A] at this
    exact this
  have hφ₂v' : φ₂ v = 1 := zmod2_eq_one_of_ne_zero hφ₂v
  have hAv : A ∉ (ZMod 2) ∙ v := by
    intro hmem
    rcases mem_span_singleton_iff.mp hmem with h0 | h0
    · exact hA0 h0
    · exact hv (h0 ▸ Submodule.mem_span_singleton_self A)
  obtain ⟨ψ, hψA, hψv⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hAv inferInstance
  have hψv' : ψ v = 0 := by
    have : ψ v ∈ ((ZMod 2) ∙ v).map ψ := ⟨v, Submodule.mem_span_singleton_self v, rfl⟩
    rw [hψv] at this
    exact this
  have hψA' : ψ A = 1 := zmod2_eq_one_of_ne_zero hψA
  set φ₁ := ψ + φ₂ with hφ₁
  have hφ₁A : φ₁ A = 1 := by
    rw [hφ₁, LinearMap.add_apply, hψA', hφ₂A', add_zero]
  have hφ₁v : φ₁ v = 1 := by
    rw [hφ₁, LinearMap.add_apply, hψv', hφ₂v', zero_add]
  have h1 : φ₁ (A + v) = 0 := by
    rw [map_add, hφ₁A, hφ₁v]
    rfl
  set σ := LinearEquiv.transvection h1 * LinearEquiv.transvection hφ₂A' with hσ
  have e2A : LinearEquiv.transvection hφ₂A' A = A := by
    rw [LinearEquiv.transvection.apply, hφ₂A', zero_smul, add_zero]
  have e2v : LinearEquiv.transvection hφ₂A' v = v + A := by
    rw [LinearEquiv.transvection.apply, hφ₂v', one_smul]
  have hσA : σ A = v := by
    rw [hσ, LinearEquiv.mul_apply, e2A, LinearEquiv.transvection.apply, hφ₁A, one_smul,
      ← add_assoc, vec_add_self, zero_add]
  have hσv : σ v = A + v := by
    rw [hσ, LinearEquiv.mul_apply, e2v, LinearEquiv.transvection.apply, map_add, hφ₁v, hφ₁A,
      show (1 : ZMod 2) + 1 = 0 from rfl, zero_smul, add_zero, add_comm]
  have hσR : σ ∈ RmodN S g t := by
    rw [hL.eq_top]
    exact Subgroup.mem_top _
  obtain ⟨r, hr, hrσ⟩ := mem_RmodN.mp hσR
  refine ⟨r, hr, ?_⟩
  have e1 : (r : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = (v : S.Qt) := by
    have := hrσ A
    rw [hσA] at this
    exact this.symm
  rw [e1]
  have := hrσ v
  rw [hσv] at this
  rw [← this]
  rfl

theorem Vt_le_clSub_of_not_conj (H : Hyp4 S g) {t : S.O} {ht : t ∈ S.Lbar g}
    (hL : LinCase S g ht) {τ : S.M} (hτ : S.ρ τ = t) {u : G} (hτu : (τ : G) = u * S.z * u⁻¹)
    (haQt : g * S.z * g⁻¹ ∈ S.Qa u)
    (hα : ¬ ∃ q ∈ S.QG, q * (τ : G) * q⁻¹ = (τ : G) * S.z) :
    Vt S g t ≤ S.clSub (S.QG ⊓ S.Qa u) := by
  have hτ2 : (τ : G) ^ 2 = 1 := by
    rw [hτu]
    exact (S.conjBy u).z_sq
  have hfix : S.fixQt (τ : G) = S.clSub (S.QG ⊓ centralizer ({(τ : G)} : Set G)) := by
    by_contra hne
    exact hα (S.lemma_3_2_1 τ.2 hne)
  have hidx := S.lemma_3_2_index τ.2 hτ2 hfix
  set K := ((S.M ⊓ centralizer ({(τ : G)} : Set G)).subgroupOf S.M).map S.ρ with hK
  have hRle : Rbar S g t ≤ S.Mbar ⊓ centralizer ({S.ρ ⟨(τ : G), τ.2⟩} : Set S.O) := by
    intro x hx
    refine Subgroup.mem_inf.mpr ⟨Rbar_le_Mbar hx, ?_⟩
    rw [mem_centralizer_singleton_iff, show S.ρ ⟨(τ : G), τ.2⟩ = t from hτ]
    exact commute_of_mem_Rbar H.conj_mem hx
  have hne : K.relIndex (S.Mbar ⊓ centralizer ({S.ρ ⟨(τ : G), τ.2⟩} : Set S.O)) ≠ 0 := by
    intro h0
    have h1 := Subgroup.relIndex_mul_card K
      (S.Mbar ⊓ centralizer ({S.ρ ⟨(τ : G), τ.2⟩} : Set S.O))
    rw [h0, zero_mul] at h1
    exact (Nat.card_pos (α := ↥(S.Mbar ⊓ centralizer ({S.ρ ⟨(τ : G), τ.2⟩} : Set S.O)))).ne h1
  have hidxR : K.relIndex (Rbar S g t) ≤ 2 :=
    (Subgroup.relIndex_le_of_le_right hRle hne).trans hidx
  have hKinv : ∀ x ∈ K, ∀ w ∈ S.clSub (S.QG ⊓ S.Qa u),
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ S.clSub (S.QG ⊓ S.Qa u) := by
    rintro _ ⟨m, hm, rfl⟩ w hw
    obtain ⟨p, ⟨hpQ, hpu⟩, -, rfl⟩ := S.mem_clSub_iff.mp hw
    have hmτ : (m : G) * τ = τ * m := mem_centralizer_singleton_iff.mp (mem_subgroupOf.mp hm).2
    rw [S.ρ_cl m hpQ]
    refine S.cl_mem_clSub ⟨S.conj_mem_QG m.2 hpQ, ?_⟩ (S.conj_mem_QG m.2 hpQ)
    have h1 := conj_mem_Qa_mul S (h := (m : G)) hpu
    rwa [S.Qa_eq_of_conj_eq (g := (m : G) * u) (h := u) (by
      rw [show (m : G) * u * S.z * ((m : G) * u)⁻¹ = (m : G) * (u * S.z * u⁻¹) * (m : G)⁻¹ by
        group, ← hτu, hmτ, mul_inv_cancel_right])] at h1
  have haP : S.cl (g * S.z * g⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa u) :=
    S.cl_mem_clSub ⟨H.conj_mem, haQt⟩ H.conj_mem
  intro v hv
  by_cases hva : (⟨v, hv⟩ : Vt S g t) ∈ (ZMod 2) ∙ aV ht
  · rcases mem_span_singleton_iff.mp hva with h0 | h0
    · rw [show v = 0 from congrArg Subtype.val h0]
      exact zero_mem _
    · rw [show v = S.cl (g * S.z * g⁻¹) from congrArg Subtype.val h0]
      exact haP
  obtain ⟨r, hr, hrr⟩ := exists_mem_Rbar_sq H hL hva
  have hsq := mul_self_mem_of_relIndex_le_two hidxR hr
  have h1 := hKinv _ hsq _ haP
  rw [coe_mul_apply, hrr] at h1
  have h2 := add_mem h1 haP
  rwa [add_comm, ← add_assoc, vec_add_self, zero_add] at h2

end CFSG.LargeExtraspecial.S6
