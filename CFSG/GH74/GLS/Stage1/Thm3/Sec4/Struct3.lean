module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Struct2

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec4.M

open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] {O : Subgroup G → Subgroup G}
  {FA : G → Subgroup G → Prop} {SD : Subgroup G → Prop} {z : G} {S K₁ K₂ : Subgroup G}

namespace M4

theorem E_le_C : Em O z K₁ K₂ ≤ centralizer ({z} : Set G) := by
  intro x hx; exact hx.2

theorem E_norm [Finite G] (h : M4 O FA SD z S K₁ K₂) {c e : G}
    (hc : c ∈ centralizer ({z} : Set G)) (he : e ∈ Em O z K₁ K₂) : c * e * c⁻¹ ∈ Em O z K₁ K₂ := by
  obtain ⟨⟨heK, heO, hcm⟩, heC⟩ := he
  obtain ⟨he1, he2⟩ := mem_normalizer_comp heK
  obtain ⟨heO1, heO2⟩ := mem_normalizer_comp heO
  have heC' : e ∈ centralizer ({z} : Set G) := heC
  have hcC : c * e * c⁻¹ ∈ centralizer ({z} : Set G) := mul_mem (mul_mem hc heC') (inv_mem hc)
  refine ⟨⟨?_, ?_, ?_⟩, hcC⟩
  · refine mem_normalizer_of_both (fun x hx => ?_) (fun x hx => ?_)
    · have h1 := h.C_norm_K' hc hx
      have h2 := he1 _ h1
      have h3 := h.C_norm_K hc h2
      have e : c * e * c⁻¹ * x * (c * e * c⁻¹)⁻¹ = c * (e * (c⁻¹ * x * c) * e⁻¹) * c⁻¹ := by group
      rw [e]; exact h3
    · have h1 := h.C_norm_K' hc hx
      have h2 := he2 _ h1
      have h3 := h.C_norm_K hc h2
      have e : (c * e * c⁻¹)⁻¹ * x * (c * e * c⁻¹) = c * (e⁻¹ * (c⁻¹ * x * c) * e) * c⁻¹ := by group
      rw [e]; exact h3
  · refine mem_normalizer_of_both (fun x hx => ?_) (fun x hx => ?_)
    · have h1 := h.C_norm_OK (inv_mem hc) hx
      have h1' : c⁻¹ * x * c ∈ O (K₁ ⊔ K₂) := by simpa using h1
      have h2 := heO1 _ h1'
      have h3 := h.C_norm_OK hc h2
      have e : c * e * c⁻¹ * x * (c * e * c⁻¹)⁻¹ = c * (e * (c⁻¹ * x * c) * e⁻¹) * c⁻¹ := by group
      rw [e]; exact h3
    · have h1 := h.C_norm_OK (inv_mem hc) hx
      have h1' : c⁻¹ * x * c ∈ O (K₁ ⊔ K₂) := by simpa using h1
      have h2 := heO2 _ h1'
      have h3 := h.C_norm_OK hc h2
      have e : (c * e * c⁻¹)⁻¹ * x * (c * e * c⁻¹) = c * (e⁻¹ * (c⁻¹ * x * c) * e) * c⁻¹ := by group
      rw [e]; exact h3
  · intro k hk
    have hk' : c⁻¹ * k * c ∈ K₁ ⊔ K₂ := h.C_norm_K' hc hk
    have h1 := hcm _ hk'
    have h2 := h.C_norm_OK hc h1
    have e : ⁅k, c * e * c⁻¹⁆ = c * ⁅c⁻¹ * k * c, e⁆ * c⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]; exact h2

theorem R_char [Finite G] (h : M4 O FA SD z S K₁ K₂) {w : G} (hwS : w ∈ S)
    (hw : w ∈ (K₁ ⊔ K₂) ⊔ Em O z K₁ K₂) : w ∈ Rm O S K₁ K₂ := by
  set A := K₁ ⊔ K₂ with hA
  set B := Em O z K₁ K₂ with hB
  have hHC : A ⊔ B ≤ centralizer ({z} : Set G) := sup_le h.K_le_C E_le_C
  have hBA : B ≤ normalizer (A : Set G) := fun e he => he.1.1
  have hset : (↑(B ⊔ A) : Set G) = (B : Set G) * (A : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right B A hBA
  have hnormH : ∀ c ∈ centralizer ({z} : Set G), ∀ x ∈ A ⊔ B, c * x * c⁻¹ ∈ A ⊔ B := by
    intro c hc x hx
    have hx' : x ∈ (↑(B ⊔ A) : Set G) := by rw [sup_comm]; exact hx
    rw [hset] at hx'
    obtain ⟨b, hb, a, ha, rfl⟩ := Set.mem_mul.1 hx'
    have e : c * (b * a) * c⁻¹ = (c * b * c⁻¹) * (c * a * c⁻¹) := by group
    rw [e]
    exact mul_mem (mem_sup_right (h.E_norm hc hb)) (mem_sup_left (h.C_norm_K hc ha))
  have hsyl : Syl2In (S ⊓ (A ⊔ B)) (A ⊔ B) := h.S_syl.inf_normal hHC hnormH
  have hres := Syl2In.eq_sup_of_normalizing (A := A) (B := B) hBA
    (fun x hx n hn => h.C_norm_K (hHC hx) hn) (fun x hx n hn => h.E_norm (hHC hx) hn) hsyl
    (fun a ha b hb => by
      have haP : a ∈ Pm S K₁ K₂ := ⟨ha.1.1, ha.2⟩
      have hbQ : b ∈ Qm O S K₁ K₂ := ⟨hb.1.1, hb.2.1⟩
      exact (h.Q_comm_P hbQ haP).symm)
  have hwH : w ∈ S ⊓ (A ⊔ B) := ⟨hwS, hw⟩
  rw [hres] at hwH
  have hle : (S ⊓ (A ⊔ B)) ⊓ A ⊔ (S ⊓ (A ⊔ B)) ⊓ B ≤ Pm S K₁ K₂ ⊔ Qm O S K₁ K₂ := by
    refine sup_le_sup ?_ ?_
    · intro x hx; exact ⟨hx.1.1, hx.2⟩
    · intro x hx; exact ⟨hx.1.1, hx.2.1⟩
  exact hle hwH

end M4

end CFSG.GH74.GLS.Stage1.Thm3.Sec4.M
