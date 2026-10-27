module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellHull

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG CFSG.Quasithin CFSG.Quasithin.BlueprintB2
open scoped LinearAlgebra.Projectivization

section TwoTools

variable {G : Type*} [Group G]

theorem aimg_eq_bot_iff [Finite G] {S₀ : Subgroup G} (α : S₀ ≃* S₀) {B : Subgroup G} (hB : B ≤ S₀) :
    aimg S₀ α B = ⊥ ↔ B = ⊥ := by
  constructor
  · intro h
    have h1 : Nat.card B = 1 := by
      rw [← card_aimg (α := α) hB, h]; exact Subgroup.card_bot
    exact Subgroup.card_eq_one.mp h1
  · intro h
    rw [h, aimg_bot]

theorem adm_aimg {S₀ Y : Subgroup G} [Finite G] (α : S₀ ≃* S₀) (h : Adm S₀ Y) :
    Adm S₀ (aimg S₀ α Y) := by
  obtain ⟨A, hA, hYA⟩ := h
  exact ⟨aimg S₀ α A, isMaxElemAbelian_aimg α hA, aimg_mono hYA⟩

open Pointwise in
theorem exists_conj_mem_sylow [Finite G] {x : G} (hx : ∃ n : ℕ, x ^ (2 ^ n) = 1) (S : Sylow 2 G) :
    ∃ c : G, c⁻¹ * x * c ∈ (S : Subgroup G) := by
  obtain ⟨n, hn⟩ := hx
  have hP : IsPGroup 2 (Subgroup.zpowers x) := by
    rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := hg
    refine ⟨n, Subtype.ext ?_⟩
    show (x ^ m) ^ (2 ^ n) = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hn, one_zpow]
  obtain ⟨P, hP'⟩ := hP.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G S P
  refine ⟨c, ?_⟩
  have hxP : x ∈ ((c • S : Sylow 2 G) : Subgroup G) := by
    rw [hc]; exact hP' (Subgroup.mem_zpowers x)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxP
  simpa [MulAut.inv_apply] using hxP

section Seed

variable {k : Type*} [Field k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}

namespace IsSeed

variable [Finite G] [Finite k] (h : IsSeed S ρ (Ecore G) ψ)
include h

theorem sylow_eq_sup_of_card {Y : Subgroup G} (hY : Y ≤ (S : Subgroup G))
    (hcard : Nat.card Y = Nat.card (Vmod G))
    (hint : Nat.card (Y ⊓ CFSG.pCore 2 G : Subgroup G) = Nat.card (Zfix S)) :
    (S : Subgroup G) = Y ⊔ CFSG.pCore 2 G := by
  obtain ⟨ℓ, hℓ⟩ := h.exists_rootGrp_eq
  have hker : Y ⊓ ρ.ker = Y ⊓ CFSG.pCore 2 G := by
    apply le_antisymm
    · rintro y ⟨hyY, hyk⟩
      exact ⟨hyY, by rw [← h.sylow_inf_ker]; exact ⟨hY hyY, hyk⟩⟩
    · rintro y ⟨hyY, hyQ⟩
      exact ⟨hyY, h.core_le hyQ⟩
  have hc := card_eq_card_map_mul_card_inf_ker ρ Y
  rw [hker, hint, hcard, ← h.card_k_mul_card_Zfix] at hc
  have hpos : 0 < Nat.card (Zfix S) := Nat.card_pos
  have hmapcard : Nat.card (Y.map ρ) = Nat.card k :=
    (Nat.eq_of_mul_eq_mul_right hpos hc).symm
  have hle : Y.map ρ ≤ (S : Subgroup G).map ρ := Subgroup.map_mono hY
  have hmap : Y.map ρ = (S : Subgroup G).map ρ := by
    rw [hℓ] at hle ⊢
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_rootGrp, hmapcard])
  exact h.sylow_eq_sup_of_map_eq hY hmap

theorem tr_sylow_not_core_comm_Vmod (α : (S : Subgroup G) ≃* (S : Subgroup G)) (g : G) {s w : G}
    (hs : s ∈ cj (S : Subgroup G) g) (hsQ : s ∉ tr (S : Subgroup G) α g (CFSG.pCore 2 G))
    (hw : w ∈ tr (S : Subgroup G) α g (Vmod G)) (hc : s * w = w * s) :
    w ∈ tr (S : Subgroup G) α g (Zfix S) := by
  have hs1 : g * s * g⁻¹ ∈ (S : Subgroup G) := mem_cj.mp hs
  have hw1 : g * w * g⁻¹ ∈ aimg (S : Subgroup G) α (Vmod G) := mem_cj.mp hw
  have hw1S : g * w * g⁻¹ ∈ (S : Subgroup G) := aimg_le hw1
  have hsQ' : ((α.symm ⟨g * s * g⁻¹, hs1⟩ : (S : Subgroup G)) : G) ∉ CFSG.pCore 2 G := by
    intro hQ
    apply hsQ
    have h1 : ((α (α.symm ⟨g * s * g⁻¹, hs1⟩) : (S : Subgroup G)) : G) ∈
        aimg (S : Subgroup G) α (CFSG.pCore 2 G) := mem_aimg_of_mem hQ
    rw [α.apply_symm_apply] at h1
    exact mem_cj.mpr h1
  have hwV' : ((α.symm ⟨g * w * g⁻¹, hw1S⟩ : (S : Subgroup G)) : G) ∈ Vmod G :=
    (mem_aimg_symm_iff hw1S).mp hw1
  have hcomm : (α.symm ⟨g * s * g⁻¹, hs1⟩ : (S : Subgroup G)) * α.symm ⟨g * w * g⁻¹, hw1S⟩ =
      α.symm ⟨g * w * g⁻¹, hw1S⟩ * α.symm ⟨g * s * g⁻¹, hs1⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show g * s * g⁻¹ * (g * w * g⁻¹) = g * w * g⁻¹ * (g * s * g⁻¹)
    calc g * s * g⁻¹ * (g * w * g⁻¹) = g * (s * w) * g⁻¹ := by group
      _ = g * (w * s) * g⁻¹ := by rw [hc]
      _ = g * w * g⁻¹ * (g * s * g⁻¹) := by group
  have hZ := h.sylow_not_core_comm_Vmod (α.symm ⟨g * s * g⁻¹, hs1⟩).2 hsQ' hwV'
    (congrArg Subtype.val hcomm)
  have h2 : ((α (α.symm ⟨g * w * g⁻¹, hw1S⟩) : (S : Subgroup G)) : G) ∈
      aimg (S : Subgroup G) α (Zfix S) := mem_aimg_of_mem hZ
  rw [α.apply_symm_apply] at h2
  exact mem_cj.mpr h2

omit [Field k] [Finite G] [Finite k] h in
theorem tr_core_commute_tr_Vmod (α : (S : Subgroup G) ≃* (S : Subgroup G)) (g : G) {q w : G}
    (hq : q ∈ tr (S : Subgroup G) α g (CFSG.pCore 2 G))
    (hw : w ∈ tr (S : Subgroup G) α g (Vmod G)) : q * w = w * q := by
  obtain ⟨qt, hqq, hqe⟩ := mem_tr.mp hq
  obtain ⟨wt, hwV', hwe⟩ := mem_tr.mp hw
  have h1 : qt * wt = wt * qt := Subtype.ext (Ecore_commute_core hqq (Vmod_le_Ecore hwV'))
  have h2 := congrArg α h1
  rw [map_mul, map_mul] at h2
  have h3 := congrArg Subtype.val h2
  simp only [Subgroup.coe_mul] at h3
  rw [hqe, hwe] at h3
  have : g * (q * w) * g⁻¹ = g * (w * q) * g⁻¹ := by
    calc g * (q * w) * g⁻¹ = g * q * g⁻¹ * (g * w * g⁻¹) := by group
      _ = g * w * g⁻¹ * (g * q * g⁻¹) := h3
      _ = g * (w * q) * g⁻¹ := by group
  simpa using this

end IsSeed

end Seed

end TwoTools

end CFSG.QuasithinUnique.Setup.Campbell
