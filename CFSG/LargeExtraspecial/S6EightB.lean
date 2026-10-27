module

public import CFSG.LargeExtraspecial.S6Eight
public import CFSG.LargeExtraspecial.S6Seven
public import CFSG.LargeExtraspecial.S6Six

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.OrthoF2

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

section Tau

variable {t : S.O} (ht1 : t ≠ 1) {τ : S.M} (hτ : S.ρ τ = t) {u : G}
  (hτu : (τ : G) = u * S.z * u⁻¹)

include ht1 hτ in
theorem tau_not_mem_QG : (τ : G) ∉ S.QG := fun h => ht1 (by rw [← hτ, (S.ρ_eq_one_iff τ).mpr h])

include ht1 hτ hτu in
theorem z_not_mem_Qa_of_tau : S.z ∉ S.Qa u := by
  intro hz
  have hne : (1 : G) * S.z * (1 : G)⁻¹ ≠ u * S.z * u⁻¹ := by
    rw [← hτu]
    intro h
    exact tau_not_mem_QG ht1 hτ (by rw [← h]; simpa using S.z_mem_QG)
  have h1 := S.mem_Qa_symm hne (by simpa using hz)
  rw [S.Qa_one, ← hτu] at h1
  exact tau_not_mem_QG ht1 hτ h1

omit [Finite G] in
include hτu in
theorem commute_of_mem_Qa_tau {x : G} (hx : x ∈ S.Qa u) : x * τ = τ * x := by
  have := (S.conjBy u).mem_M_iff.mp ((S.conjBy u).QG_le_M hx)
  rwa [Setting.conjBy_z, ← hτu] at this

omit [Finite G] in
include hτu in
theorem conj_mem_Qa_of_commute {x y : G} (hx : x ∈ S.Qa u) (hy : y * τ = τ * y) :
    y * x * y⁻¹ ∈ S.Qa u := by
  have hyM : y ∈ (S.conjBy u).M := by
    rw [(S.conjBy u).mem_M_iff, Setting.conjBy_z, ← hτu]
    exact hy
  exact (S.conjBy u).conj_mem_QG hyM hx

include ht1 hτ hτu in
theorem commute_of_mem_QG_inf_Qa {p y : G} (hp : p ∈ S.QG ⊓ S.Qa u) (hyQ : y ∈ S.QG)
    (hy : y * τ = τ * y) : p * y = y * p := by
  have h1 : p * y * p⁻¹ * y⁻¹ ∈ S.Qa u := by
    rw [show p * y * p⁻¹ * y⁻¹ = p * (y * p⁻¹ * y⁻¹) by group]
    exact mul_mem hp.2 (conj_mem_Qa_of_commute hτu (inv_mem hp.2) hy)
  rcases S.commutator_eq_one_or_z hp.1 hyQ with h | h
  · calc p * y = p * y * p⁻¹ * y⁻¹ * (y * p) := by group
      _ = y * p := by rw [h, one_mul]
  · exact absurd (h ▸ h1) (z_not_mem_Qa_of_tau ht1 hτ hτu)

include hτ in
theorem finrank_fixSpace_le :
    finrank (ZMod 2) (fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) ≤
      finrank (ZMod 2) (S.clSub (S.QG ⊓ centralizer ({(τ : G)} : Set G))) + 1 := by
  have hfixeq : fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) = S.fixQt (τ : G) := by
    rw [S.fixQt_of_mem τ.2, ← hτ]
  have hle : S.clSub (S.QG ⊓ centralizer ({(τ : G)} : Set G)) ≤
      fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := hfixeq ▸ S.clSub_centralizer_le_fixQt τ.2
  have key : ∀ x ∈ S.QG, S.cl x ∈ fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) →
      S.cl x ∉ S.clSub (S.QG ⊓ centralizer ({(τ : G)} : Set G)) →
        (τ : G) * x * (τ : G)⁻¹ = x * S.z := by
    intro x hx hfx hnx
    have h1 : S.cl ((τ : G) * x * (τ : G)⁻¹) = S.cl x := by
      rw [← S.ρ_cl τ hx, hτ]
      exact mem_fixSpace.mp hfx
    rcases (S.cl_eq_cl_iff hx (S.conj_mem_QG τ.2 hx)).mp h1.symm with h2 | h2
    · exfalso
      apply hnx
      refine S.cl_mem_clSub ⟨hx, mem_centralizer_singleton_iff.mpr ?_⟩ hx
      calc x * (τ : G) = (τ : G) * x * (τ : G)⁻¹ * τ := by rw [h2]
        _ = τ * x := by group
    · exact h2
  refine finrank_le_finrank_add_one_of_add_mem hle fun v hv w hw hv0 hw0 => ?_
  obtain ⟨x, hx, rfl⟩ := S.exists_cl v
  obtain ⟨y, hy, rfl⟩ := S.exists_cl w
  have h1 := key x hx hv hv0
  have h2 := key y hy hw hw0
  rw [← S.cl_mul hx hy]
  refine S.cl_mem_clSub ⟨S.QG.mul_mem hx hy, mem_centralizer_singleton_iff.mpr ?_⟩
    (S.QG.mul_mem hx hy)
  have e : (τ : G) * (x * y) * (τ : G)⁻¹ = x * y := by
    calc (τ : G) * (x * y) * (τ : G)⁻¹ = ((τ : G) * x * (τ : G)⁻¹) * ((τ : G) * y * (τ : G)⁻¹) := by
          group
      _ = x * (S.z * y) * S.z := by rw [h1, h2]; group
      _ = x * y := by rw [← S.z_comm_QG hy, mul_assoc, mul_assoc, S.z_mul_z, mul_one]
  calc x * y * (τ : G) = (τ : G) * (x * y) * (τ : G)⁻¹ * τ := by rw [e]
    _ = τ * (x * y) := by group

end Tau

section Beta

variable (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) {τ : S.M}
  (hτ : S.ρ τ = t) {u : G} (hτu : (τ : G) = u * S.z * u⁻¹)
include H ht ht1 hτ hτu

theorem finrank_clSub_le :
    finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa u)) ≤
      finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa u) ⊓ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) + 1 := by
  set Pt := S.clSub (S.QG ⊓ S.Qa u) with hPt
  set F0 := S.clSub (S.QG ⊓ centralizer ({(τ : G)} : Set G)) with hF0
  set F := fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) with hF
  have htt := mul_self_of_mem_Lbar S H.conj_mem ht
  have hF0F : F0 ≤ F := by
    have hfixeq : F = S.fixQt (τ : G) := by rw [hF, S.fixQt_of_mem τ.2, ← hτ]
    rw [hfixeq]
    exact S.clSub_centralizer_le_fixQt τ.2
  have hPF0 : Pt ≤ LinearMap.BilinForm.orthogonal S.q.polarBilin F0 := by
    intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    obtain ⟨p, hp, hpQ, rfl⟩ := S.mem_clSub_iff.mp hv
    obtain ⟨y, hy, hyQ, rfl⟩ := S.mem_clSub_iff.mp hw
    rw [polarBilin_apply_apply, S.polar_cl_eq_zero_iff hyQ hpQ]
    exact (commute_of_mem_QG_inf_Qa ht1 hτ hτu hp hyQ
      (mem_centralizer_singleton_iff.mp hy.2)).symm
  have hUF0 : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤
      LinearMap.BilinForm.orthogonal S.q.polarBilin F0 := by
    rw [← orthogonal_fixSpace htt]
    exact LinearMap.BilinForm.orthogonal_le hF0F
  have hdimF0 := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate F0
  have hA : finrank (ZMod 2) F ≤ finrank (ZMod 2) F0 + 1 := finrank_fixSpace_le hτ
  have hsup := Submodule.finrank_mono (sup_le hPF0 hUF0)
  have hsi := Submodule.finrank_sup_add_finrank_inf_eq Pt
    (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt))
  have hcf : finrank (ZMod 2) (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) + finrank (ZMod 2) F =
      finrank (ZMod 2) S.Qt := finrank_commSpace_add_finrank_fixSpace _
  have hF0le := Submodule.finrank_mono hF0F
  have hFle := Submodule.finrank_le F
  omega

omit H ht in
theorem inf_commSpace_le_Vt (hF : FusionCtl S g)
    (hβ : ∃ q ∈ S.QG, q * (τ : G) * q⁻¹ = (τ : G) * S.z) :
    S.clSub (S.QG ⊓ S.Qa u) ⊓ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ Vt S g t := by
  rintro v ⟨hvP, hvU⟩
  by_cases hv0 : v = 0
  · rw [hv0]
    exact zero_mem _
  obtain ⟨α, ⟨hαQ, hαu⟩, -, rfl⟩ := S.mem_clSub_iff.mp hvP
  have hα1 : α ≠ 1 := fun h => hv0 (by rw [h, S.cl_one])
  have hαz : α ≠ S.z := fun h => hv0 (by rw [h, S.cl_z])
  have hατ : α ≠ τ := fun h => tau_not_mem_QG ht1 hτ (h ▸ hαQ)
  have hαc : α * τ = τ * α := commute_of_mem_Qa_tau hτu hαu
  have hvU' : S.cl α ∈ S.commQt (τ : G) := by
    rw [S.commQt_of_mem τ.2]
    exact hτ ▸ hvU
  obtain ⟨y, hyQ, hy⟩ := (S.mem_commQt_iff' τ.2).mp hvU'
  have hyτQ : y * τ * y⁻¹ * (τ : G)⁻¹ ∈ S.QG := S.commutator_mem_QG' τ.2 hyQ
  obtain ⟨w, hw⟩ : ∃ w : G, w * τ * w⁻¹ = τ * α := by
    rcases (S.cl_eq_cl_iff hyτQ hαQ).mp hy with h | h
    · refine ⟨y, ?_⟩
      calc y * τ * y⁻¹ = (y * τ * y⁻¹ * (τ : G)⁻¹) * τ := by group
        _ = α * τ := by rw [← h]
        _ = τ * α := hαc
    · obtain ⟨q, -, hq⟩ := hβ
      refine ⟨y * q, ?_⟩
      calc (y * q) * τ * (y * q)⁻¹ = y * (q * τ * q⁻¹) * y⁻¹ := by group
        _ = y * τ * y⁻¹ * (y * S.z * y⁻¹) := by rw [hq]; group
        _ = y * τ * y⁻¹ * S.z := by rw [S.z_comm_QG hyQ]; group
        _ = y * τ * y⁻¹ * (τ : G)⁻¹ * S.z * τ := by
          rw [mul_assoc (y * τ * y⁻¹ * (τ : G)⁻¹) S.z τ, ← S.z_comm τ.2]
          group
        _ = α * τ := by rw [← h]
        _ = τ * α := hαc
  set T := S.conjBy u with hT
  have hTz : T.z = τ := hτu.symm
  obtain ⟨r, -, hr⟩ := T.exists_conj_eq_mul_z hαu hα1 (by rw [hTz]; exact hατ)
  rw [hTz] at hr
  set k := r⁻¹ * w * u with hk
  have hkα : k * S.z * k⁻¹ = α := by
    calc k * S.z * k⁻¹ = r⁻¹ * (w * (u * S.z * u⁻¹) * w⁻¹) * r := by rw [hk]; group
      _ = r⁻¹ * (α * τ) * r := by rw [← hτu, hw, hαc]
      _ = α := by rw [← hr]; group
  obtain ⟨m, hm, hma⟩ := hF k (by rw [hkα]; exact hαQ) (by rw [hkα]; exact hαz)
  have hmα : (m * g) * S.z * (m * g)⁻¹ = α := by
    rw [← hkα, ← hma]
    group
  have hne : (m * g) * S.z * (m * g)⁻¹ ≠ u * S.z * u⁻¹ := by
    rw [hmα, ← hτu]
    exact hατ
  have hτα : u * S.z * u⁻¹ ∈ S.Qa (m * g) := S.mem_Qa_symm hne (by rw [hmα]; exact hαu)
  have htL : t ∈ S.Lbar (((⟨m, hm⟩ : S.M) : G) * g) := by
    rw [← hτ]
    exact ρ_mem_Lbar S ⟨by rw [hτu]; exact hτα, τ.2⟩
  have := cl_mem_Vt htL
  rwa [show ((⟨m, hm⟩ : S.M) : G) * g * S.z * (((⟨m, hm⟩ : S.M) : G) * g)⁻¹ = α from hmα]
    at this

end Beta

end CFSG.LargeExtraspecial.S6
