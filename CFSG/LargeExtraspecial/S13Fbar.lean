module

public import CFSG.LargeExtraspecial.S13Basic
public import CFSG.LargeExtraspecial.S13Lin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G} {K : Subgroup S.O}

variable (S) in
@[expose] noncomputable def Fbar (g : G) (K : Subgroup S.O) : Submodule (ZMod 2) S.Qt :=
  fixSub S (Ebar S g K)

theorem mem_Fbar {v : S.Qt} :
    v ∈ Fbar S g K ↔ ∀ x ∈ Ebar S g K, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := Iff.rfl

theorem Lbar_apply_cl (H : Hyp4 S g) {x : S.O} (hx : x ∈ S.Lbar g) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) := by
  have h : S.cl (g * S.z * g⁻¹) ∈ fixSub S (S.Lbar g) := by
    rw [H.fixSub_eq]; exact Submodule.mem_span_singleton_self _
  exact h x hx

theorem cl_mem_Fbar (H : Hyp4 S g) : S.cl (g * S.z * g⁻¹) ∈ Fbar S g K :=
  fun _ hx => Lbar_apply_cl H (Ebar_le_Lbar hx)

theorem apply_mem_Fbar_of_mem_K {k : S.O} (hk : k ∈ K) {v : S.Qt} (hv : v ∈ Fbar S g K) :
    (k : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Fbar S g K := by
  intro x hx
  have hc := ((mem_Ebar).mp hx).2 k hk
  rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, ← hc, Subgroup.coe_mul,
    LinearEquiv.mul_apply, hv x hx]

theorem apply_mem_Fbar_of_mem_Lbar (H : Hyp4 S g) {l : S.O} (hl : l ∈ S.Lbar g) {v : S.Qt}
    (hv : v ∈ Fbar S g K) : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Fbar S g K := by
  intro x hx
  have hc := S4.Lbar_comm S H.conj_mem hl (Ebar_le_Lbar hx)
  rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, ← hc, Subgroup.coe_mul,
    LinearEquiv.mul_apply, hv x hx]

section Card

variable (H : Hyp4 S g) (hK3 : Nat.card K = 3) (hN : NormalInMbar S K) (hfpf : FixFree S K)
include H hK3 hN hfpf

theorem card_Lbar_eq_two_mul : Nat.card (S.Lbar g) = 2 * Nat.card (Ebar S g K) := by
  obtain ⟨x₀, hx₀, hx₀E⟩ := exists_not_mem_Ebar H hfpf (K := K)
  have hidx : ((Ebar S g K).subgroupOf (S.Lbar g)).index = 2 := by
    rw [index_eq_two_iff]
    refine ⟨⟨x₀, hx₀⟩, fun b => ?_⟩
    rw [mem_subgroupOf, mem_subgroupOf]
    by_cases hb : (b : S.O) ∈ Ebar S g K
    · refine Or.inr ⟨hb, fun h => hx₀E ?_⟩
      have e : x₀ = (b : S.O)⁻¹ * ((b * ⟨x₀, hx₀⟩ : S.Lbar g) : S.O) := by simp
      rw [e]
      exact mul_mem (inv_mem hb) h
    · exact Or.inl ⟨mul_mem_Ebar hK3 hN b.2 hb hx₀ hx₀E, hb⟩
  have h1 := card_mul_index ((Ebar S g K).subgroupOf (S.Lbar g))
  rw [hidx, Nat.card_congr (subgroupOfEquivOfLe Ebar_le_Lbar).toEquiv] at h1
  omega

end Card

section Dim

variable (H : Hyp4 S g) (hK3 : Nat.card K = 3) (hN : NormalInMbar S K) (hfpf : FixFree S K)
include H hK3 hN hfpf

theorem finrank_Fbar_le : finrank (ZMod 2) (Fbar S g K) ≤ 2 := by
  obtain ⟨x₀, hx₀, hx₀E⟩ := exists_not_mem_Ebar H hfpf (K := K)
  set f : S.Qt ≃ₗ[ZMod 2] S.Qt := (x₀ : S.Qt ≃ₗ[ZMod 2] S.Qt) with hf
  have hff : ∀ v, f (f v) = v := fun v => by
    have := S4.mul_self_of_mem_Lbar S H.conj_mem hx₀
    have h2 := congrArg (fun y : S.O => (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v) this
    simpa [hf] using h2
  have hfix : ∀ v ∈ Fbar S g K, f v = v → v ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
    intro v hv hfv
    rw [← H.fixSub_eq]
    intro l hl
    by_cases hlE : l ∈ Ebar S g K
    · exact hv l hlE
    · have h1 := hv _ (mul_mem_Ebar hK3 hN hl hlE hx₀ hx₀E)
      rw [Subgroup.coe_mul, LinearEquiv.mul_apply] at h1
      rw [← hf, hfv] at h1
      exact h1
  set ψ : Fbar S g K →ₗ[ZMod 2] S.Qt := ((f : S.Qt →ₗ[ZMod 2] S.Qt) - 1).comp
    (Fbar S g K).subtype with hψ
  have hrange : LinearMap.range ψ ≤ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
    rintro _ ⟨v, rfl⟩
    refine hfix _ ?_ ?_
    · simp only [hψ, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.sub_apply,
        LinearEquiv.coe_coe, Module.End.one_apply]
      exact sub_mem (apply_mem_Fbar_of_mem_Lbar H hx₀ v.2) v.2
    · simp only [hψ, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.sub_apply,
        LinearEquiv.coe_coe, Module.End.one_apply, map_sub, hff]
      rw [← neg_sub, zmod2_neg_eq]
  have hker : (LinearMap.ker ψ).map (Fbar S g K).subtype ≤ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
    rintro _ ⟨v, hv, rfl⟩
    refine hfix _ v.2 ?_
    have : ψ v = 0 := hv
    simp only [hψ, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.sub_apply,
      LinearEquiv.coe_coe, Module.End.one_apply, sub_eq_zero] at this
    exact this
  have h1 := LinearMap.finrank_range_add_finrank_ker ψ
  have h2 := Submodule.finrank_mono hrange
  have h3 := Submodule.finrank_mono hker
  rw [Submodule.finrank_map_subtype_eq] at h3
  have h4 := finrank_span_singleton (K := ZMod 2) (cl_conj_z_ne_zero S H.conj_mem H.conj_ne)
  omega

omit H hK3 hN hfpf in
theorem linearIndependent_pair_zmod2 {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {u v : V}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) : LinearIndependent (ZMod 2) ![u, v] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases h01 s with rfl | rfl <;> rcases h01 t with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · simp only [zero_smul, one_smul, zero_add] at hst
    exact absurd hst hv
  · simp only [zero_smul, one_smul, add_zero] at hst
    exact absurd hst hu
  · exfalso
    simp only [one_smul] at hst
    apply huv
    have := congrArg (· + v) hst
    simp only [zero_add] at this
    rw [add_assoc, ← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul,
      add_zero] at this
    exact this

theorem Fbar_eq_span {k : S.O} (hk : k ∈ K) (hk1 : k ≠ 1) :
    Fbar S g K = Submodule.span (ZMod 2)
      (Set.range ![S.cl (g * S.z * g⁻¹), (k : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))]) := by
  have ha0 := cl_conj_z_ne_zero S H.conj_mem H.conj_ne
  have hka0 : (k : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ≠ 0 := fun h =>
    ha0 (by simpa using congrArg (k : S.Qt ≃ₗ[ZMod 2] S.Qt).symm h)
  have hne : S.cl (g * S.z * g⁻¹) ≠ (k : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) :=
    fun h => ha0 (fix_eq_zero hK3 hfpf hk hk1 _ h.symm)
  have hli := linearIndependent_pair_zmod2 ha0 hka0 hne
  have hle : Submodule.span (ZMod 2)
      (Set.range ![S.cl (g * S.z * g⁻¹), (k : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))]) ≤
        Fbar S g K := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact cl_mem_Fbar H
    · exact apply_mem_Fbar_of_mem_K hk (cl_mem_Fbar H)
  have h2 := finrank_span_eq_card hli
  simp only [Fintype.card_fin] at h2
  have h3 := finrank_Fbar_le H hK3 hN hfpf (K := K)
  exact (Submodule.eq_of_le_of_finrank_le hle (by omega)).symm

theorem finrank_Fbar {k : S.O} (hk : k ∈ K) (hk1 : k ≠ 1) :
    finrank (ZMod 2) (Fbar S g K) = 2 := by
  rw [Fbar_eq_span H hK3 hN hfpf hk hk1]
  have ha0 := cl_conj_z_ne_zero S H.conj_mem H.conj_ne
  have hka0 : (k : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) ≠ 0 := fun h =>
    ha0 (by simpa using congrArg (k : S.Qt ≃ₗ[ZMod 2] S.Qt).symm h)
  have hne : S.cl (g * S.z * g⁻¹) ≠ (k : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) :=
    fun h => ha0 (fix_eq_zero hK3 hfpf hk hk1 _ h.symm)
  have h2 := finrank_span_eq_card (linearIndependent_pair_zmod2 ha0 hka0 hne)
  simpa using h2

end Dim

end CFSG.LargeExtraspecial.S13
