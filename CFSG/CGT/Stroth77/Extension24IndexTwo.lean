module

public import CFSG.CGT.Stroth77.Extension24Basic

public section

namespace CFSG.CGT.Stroth77

theorem false_of_index_two_t300_of_data {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S} {n : ℕ}
    (D : StrothTypeData B (StrothTypeIndex.t300 n)) (_hn : 1 ≤ n)
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False := by
  classical
  obtain ⟨d, hdC, hdB⟩ : ∃ d, d ∈ C ∧ d ∉ B := by
    by_contra hcon
    push Not at hcon
    have hle := Subgroup.card_le_of_le (fun x hx => hcon x hx : C ≤ B)
    have hpos : 0 < Nat.card B := Nat.card_pos
    omega
  have hindex : (B.subgroupOf C).index = 2 := index_two_of_relIndex hBC hrel
  have hdH : (⟨d, hdC⟩ : C) ∉ B.subgroupOf C := fun h => hdB (Subgroup.mem_subgroupOf.mp h)
  have hd2H : (⟨d, hdC⟩ : C) * ⟨d, hdC⟩ ∈ B.subgroupOf C :=
    (Subgroup.mul_mem_iff_of_index_two hindex).mpr (by simp [hdH])
  have hd2B : d * d ∈ B := by
    simpa using Subgroup.mem_subgroupOf.mp hd2H
  let sB : B := ⟨d * d, hd2B⟩
  have hcommB : ∀ β : B, (β : S) * d = d * (β : S) := fun β =>
    Subgroup.mem_centralizer_iff.mp (hC hdC) (β : S) β.2
  have hfix : ∀ {g : S} (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B),
      ∃ z : Torus (StrothTypeIndex.t300 n).k, 2 • z = D.ec (conjBy hgB sB * sB⁻¹) := by
    intro g hgC hgB
    obtain ⟨β, hβ⟩ := exists_conj_eq hBC hrel hdC hdB g hgC hgB
    have hβS : g⁻¹ * d * g = d * (β : S) := by
      simpa [conjBy_val] using congrArg Subtype.val hβ
    have hconj : conjBy hgB sB * sB⁻¹ = β * β := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjBy_val]
      change g⁻¹ * (d * d) * g * (d * d)⁻¹ = (β : S) * β
      have h1 : g⁻¹ * (d * d) * g = (g⁻¹ * d * g) * (g⁻¹ * d * g) := by group
      rw [h1, hβS]
      have h2 : d * (β : S) * (d * (β : S)) = d * d * ((β : S) * β) := by
        rw [mul_assoc d, ← mul_assoc (β : S) d, hcommB β]
        group
      rw [h2]
      have h3 : (β : S) * β * d = d * ((β : S) * β) := by
        rw [mul_assoc, hcommB β, ← mul_assoc, hcommB β, mul_assoc]
      calc d * d * ((β : S) * β) * (d * d)⁻¹
          = d * (d * ((β : S) * β)) * (d * d)⁻¹ := by group
        _ = d * ((β : S) * β * d) * (d * d)⁻¹ := by rw [h3]
        _ = d * ((β : S) * β) * d * (d * d)⁻¹ := by group
        _ = (β : S) * β * d * d * (d * d)⁻¹ := by rw [← h3]
        _ = (β : S) * β := by group
    exact ⟨D.ec β, by rw [hconj, D.ec_mul, two_nsmul]⟩
  obtain ⟨z, hz⟩ := t300_fixed_rho_t_mod_two_of_mem D (hfix (hL D.ρ_mem_L) D.ρ_mem)
    (hfix (hL D.t_mem_L) D.t_mem)
  let σ : B := Additive.toMul (D.e.symm z)
  have hσz : D.ec σ = z := D.e.apply_symm_apply z
  have hσ : σ * σ = sB := by
    apply D.ec_injective
    rw [D.ec_mul, ← two_nsmul, hσz, hz]
  have hσS : (σ : S) * σ = d * d := by
    simpa [sB] using congrArg Subtype.val hσ
  have hσC : (σ : S) ∈ C := hBC σ.2
  let w : S := d * (σ : S)⁻¹
  have hwC : w ∈ C := C.mul_mem hdC (C.inv_mem hσC)
  have hww : w * w = 1 := by
    have hcσ : (σ : S)⁻¹ * d = d * (σ : S)⁻¹ := by
      have h := hcommB σ⁻¹
      simpa using h
    calc w * w = d * ((σ : S)⁻¹ * d) * (σ : S)⁻¹ := by simp only [w]; group
      _ = d * (d * (σ : S)⁻¹) * (σ : S)⁻¹ := by rw [hcσ]
      _ = (d * d) * ((σ : S) * σ)⁻¹ := by group
      _ = 1 := by rw [hσS, mul_inv_cancel]
  have hwB : w ∈ B := hH w (hcS hwC) hww (hC hwC)
  apply hdB
  have hd : d = w * (σ : S) := by simp only [w]; group
  rw [hd]
  exact B.mul_mem hwB σ.2

theorem false_of_index_two_t300 {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S} {n : ℕ}
    (hB : HasStrothType B (StrothTypeIndex.t300 n)) (_hn : 1 ≤ n)
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') : False :=
  false_of_index_two_t300_of_data hB.data _hn hBC hC hrel hL hH hcS

end CFSG.CGT.Stroth77
