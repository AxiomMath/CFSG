module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29D2
public import CFSG.GH74.Generic.BProg.B3.S3Sec29D3

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools CFSG.GH74.Generic.S45
open scoped commutatorElement

namespace S3Sec29D8

section Abstract

variable {X : Type*} [Group X]

theorem normalizes_diag {J : Subgroup X} {g e : X} (hc : S3Sec29D3.CommConj J g) (hg2 : g * g = 1)
    (heg : e * g = g * e) (hcase : e ∈ normalizer (J : Set X) ∨ e * g ∈ normalizer (J : Set X))
    {d : X} (hd : d ∈ (S3Sec29D3.diagHom J g hc).range) :
    e * d * e⁻¹ ∈ (S3Sec29D3.diagHom J g hc).range := by
  obtain ⟨c, rfl⟩ := hd
  have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  rcases hcase with hN | hN
  · have hc' : e * c * e⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 hN c).1 c.2
    refine ⟨⟨e * c * e⁻¹, hc'⟩, ?_⟩
    rw [S3Sec29D3.diagHom_apply, S3Sec29D3.diagHom_apply]
    have h4 : g * (e * c * e⁻¹) * g⁻¹ = e * (g * c * g⁻¹) * e⁻¹ := by
      calc g * (e * c * e⁻¹) * g⁻¹ = (g * e) * c * (g * e)⁻¹ := by group
        _ = (e * g) * c * (e * g)⁻¹ := by rw [heg]
        _ = e * (g * c * g⁻¹) * e⁻¹ := by group
    rw [h4]; group
  · obtain ⟨f, hf⟩ : ∃ f : X, f = e * g := ⟨_, rfl⟩
    rw [← hf] at hN
    have hc' : f * c * f⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 hN c).1 c.2
    refine ⟨⟨f * c * f⁻¹, hc'⟩, ?_⟩
    rw [S3Sec29D3.diagHom_apply, S3Sec29D3.diagHom_apply]
    have hfg : f * g = g * f := by
      calc f * g = (e * g) * g := by rw [hf]
        _ = (g * e) * g := by rw [heg]
        _ = g * (e * g) := by group
        _ = g * f := by rw [hf]
    have h1 := hc (f * c * f⁻¹) hc' (f * c * f⁻¹) hc'
    have he : e = f * g := by rw [hf, mul_assoc, hg2, mul_one]
    have h2 : e * c * e⁻¹ = g * (f * c * f⁻¹) * g⁻¹ := by
      calc e * c * e⁻¹ = (f * g) * c * (f * g)⁻¹ := by rw [he]
        _ = (g * f) * c * (g * f)⁻¹ := by rw [hfg]
        _ = g * (f * c * f⁻¹) * g⁻¹ := by group
    have h3 : e * (g * c * g⁻¹) * e⁻¹ = f * c * f⁻¹ := by
      calc e * (g * c * g⁻¹) * e⁻¹ = (f * g) * (g * c * g⁻¹) * (f * g)⁻¹ := by rw [he]
        _ = f * (g * g) * c * (g * g)⁻¹ * f⁻¹ := by group
        _ = f * c * f⁻¹ := by rw [hg2]; group
    calc f * c * f⁻¹ * (g * (f * c * f⁻¹) * g⁻¹) = (g * (f * c * f⁻¹) * g⁻¹) * (f * c * f⁻¹) := h1
      _ = (e * c * e⁻¹) * (e * (g * c * g⁻¹) * e⁻¹) := by rw [h2, h3]
      _ = e * ((c : X) * (g * c * g⁻¹)) * e⁻¹ := by group

end Abstract

section GLevel

variable {G : Type} [Group G] [Finite G] {x y : G} {K A B Q D J R : Subgroup G}

theorem mul_mem_normalizer_of_not (h : Ctx29w G x K A B Q y y D J) (hO : Obs52 B y D J) {g e : G}
    (hgB : g ∈ B) (hgN : g ∉ normalizer (J : Set G)) (heB : e ∈ B) (heN : e ∉ normalizer (J : Set G)) :
    e * g ∈ normalizer (J : Set G) := by
  have h8 := S3Sec29D2.eight_le_card_normalizer h hO
  obtain ⟨E, hEK, hAE, -, hEel, hE4, -⟩ := S3Sec29D2.exists_E h
  obtain ⟨-, -, -, hB16, -⟩ := S3Sec29D2.B_decomp h ⟨hEK, hAE, hEel, hE4⟩
  set H : Subgroup ↥B := (B ⊓ normalizer (J : Set G)).subgroupOf B with hH
  have hcardH : Nat.card ↥H = Nat.card ↥(B ⊓ normalizer (J : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hidx : H.index * Nat.card ↥H = Nat.card ↥B := Subgroup.index_mul_card H
  rw [hB16, hcardH] at hidx
  have hmemH : ∀ (a : G) (ha : a ∈ B), (⟨a, ha⟩ : ↥B) ∈ H ↔ a ∈ normalizer (J : Set G) := by
    intro a ha
    rw [hH, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h1 => h1.2, fun h1 => ⟨ha, h1⟩⟩
  have hne : H.index ≠ 1 := by
    intro h1
    rw [Subgroup.index_eq_one] at h1
    apply hgN
    rw [← hmemH g hgB, h1]
    trivial
  have h2 : H.index = 2 := by
    by_contra hne2
    have h3 : 3 ≤ H.index := by
      have h0 : H.index ≠ 0 := by
        intro h0; rw [h0, zero_mul] at hidx; omega
      omega
    have := Nat.mul_le_mul h3 h8
    omega
  have key := Subgroup.mul_mem_iff_of_index_two h2 (a := ⟨e, heB⟩) (b := ⟨g, hgB⟩)
  have hab : (⟨e, heB⟩ : ↥B) * ⟨g, hgB⟩ ∈ H :=
    key.2 ⟨fun h1 => absurd ((hmemH e heB).1 h1) heN, fun h1 => absurd ((hmemH g hgB).1 h1) hgN⟩
  exact (hmemH (e * g) (mul_mem heB hgB)).1 hab

end GLevel

end S3Sec29D8

variable {G : Type} [Group G] [Finite G]

end CFSG.GH74.Generic.BProg.B3
