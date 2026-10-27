module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Struct

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec4.M

open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] {O : Subgroup G → Subgroup G}
  {FA : G → Subgroup G → Prop} {SD : Subgroup G → Prop} {z : G} {S K₁ K₂ : Subgroup G}

theorem exists_conj_inv {z t : G} (h : IsConj z t) : ∃ g : G, g⁻¹ * z * g = t := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  exact ⟨c⁻¹, by simpa using hc⟩

theorem mem_normalizer_cj {K : Subgroup G} {g w : G} (hw : w ∈ normalizer (cj K g : Set G)) :
    g * w * g⁻¹ ∈ normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hw ⊢
  intro x
  have h1 := hw (g⁻¹ * x * g)
  simp only [mem_cj] at h1 ⊢
  have e1 : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
  have e2 : g * (w * (g⁻¹ * x * g) * w⁻¹) * g⁻¹ = g * w * g⁻¹ * x * (g * w * g⁻¹)⁻¹ := by group
  rw [e1, e2] at h1
  exact h1

theorem isPGroup_zpowers_conj [Finite G] {w : G} (g : G) (hw : IsPGroup 2 ↥(zpowers w)) :
    IsPGroup 2 ↥(zpowers (g * w * g⁻¹)) := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hw
  have hord : orderOf (g * w * g⁻¹) = orderOf w := by
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective w
    simpa using this
  refine IsPGroup.of_card (n := n) ?_
  rw [Nat.card_zpowers, hord, ← Nat.card_zpowers]
  exact hn

theorem isPGroup_zpowers_of_mem {w u : G} (hu : IsPGroup 2 ↥(zpowers u)) (hw : w ∈ zpowers u) :
    IsPGroup 2 ↥(zpowers w) :=
  hu.to_le (zpowers_le.2 hw)

namespace M4

variable [Finite G]

theorem secCent_of_gen (h : M4 O FA SD z S K₁ K₂) {c : G} (hc : c ∈ centralizer ({z} : Set G))
    (h1 : ∀ x ∈ K₁, ⁅x, c⁆ ∈ O (K₁ ⊔ K₂)) (h2 : ∀ y ∈ K₂, ⁅y, c⁆ ∈ O (K₁ ⊔ K₂)) :
    c ∈ secCent (K₁ ⊔ K₂) (O (K₁ ⊔ K₂)) := by
  refine ⟨mem_normalizer_of_both (fun x hx => h.C_norm_K hc hx)
    (fun x hx => h.C_norm_K' hc hx), mem_normalizer_of_both (fun x hx => h.C_norm_OK hc hx)
    (fun x hx => ?_), ?_⟩
  · have := h.C_norm_OK (inv_mem hc) hx
    simpa using this
  · intro k hk
    obtain ⟨x, hx, y, hy, rfl⟩ := h.mem_sup hk
    have e : ⁅x * y, c⁆ = x * ⁅y, c⁆ * x⁻¹ * ⁅x, c⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact mul_mem (h.coreK.normal x (mem_sup_left hx) _ (h2 y hy)) (h1 x hx)

theorem not_mem_ZsK (h : M4 O FA SD z S K₁ K₂) {t : G} (htS : t ∈ S)
    (ht1 : t ≠ 1) (htz : t ≠ z) : t ∉ ZsM O (K₁ ⊔ K₂) := by
  intro htZ
  have : t ∈ S ⊓ ZsM O (K₁ ⊔ K₂) := ⟨htS, htZ⟩
  rw [h.S_inf_Zs] at this
  rcases (mem_zpowers_of_sq h.z_sq).1 this with h1 | h1
  · exact ht1 h1
  · exact htz h1

end M4

end CFSG.GH74.GLS.Stage1.Thm3.Sec4.M
