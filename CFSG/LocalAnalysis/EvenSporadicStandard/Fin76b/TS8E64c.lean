module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8E64b
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13HE64a

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OI13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B S : Subgroup G} {α σ : G}
  (c : OI13Ctx L z t T E B β S α σ) {b₁ b₂ w₀ : G}

structure PData (P : Subgroup G) : Prop where
  le : P ≤ c.W1
  alpha_mem : α ∈ P
  inj : ∀ p ∈ P, ∀ p' ∈ P, p * (z * p * z⁻¹) = p' * (z * p' * z⁻¹) → p = p'
  surj : ∀ e ∈ E, ∃ p ∈ P, p * (z * p * z⁻¹) = e

section P1

variable (k : OE64.IsKlein B b₁ b₂) (hw₀ : w₀ ∈ c.W1)

include c k hw₀

theorem P1_le_W1 : OE64.P1 α b₁ b₂ w₀ ≤ c.W1 := by
  rw [OE64.P1, closure_le]
  rintro y (hy | hy)
  · rw [Set.mem_singleton_iff.1 hy]
    exact c.Zs_le_W1 c.alpha_mem_Zs
  · rw [Set.mem_ofPred_eq, OE64.mem_genP] at hy
    obtain ⟨g, hg, rfl⟩ := hy
    have hgB : g ∈ B := by
      rcases hg with rfl | rfl | rfl | rfl
      exacts [B.one_mem, k.mem₁, k.mem₂, k.prod_mem]
    exact c.N1_W1 (c.B_le_N1 hgB) hw₀

omit hw₀ in
theorem P1_conj {b : G} (hb : b ∈ closure ({b₁, b₂} : Set G)) {p : G}
    (hp : p ∈ OE64.P1 α b₁ b₂ w₀) : b * p * b⁻¹ ∈ OE64.P1 α b₁ b₂ w₀ := by
  refine I13HE64.conj_mem_closure b ?_ p hp
  rintro s (hs | hs)
  · rw [Set.mem_singleton_iff.1 hs]
    have : b * α * b⁻¹ = α := by
      rw [c.B_comm_alpha (k.grp_le hb)]; group
    rw [this]
    exact OE64.alpha_mem_P1 α b₁ b₂ w₀
  · rw [Set.mem_ofPred_eq, OE64.mem_genP] at hs
    obtain ⟨g, hg, rfl⟩ := hs
    have hgm : g ∈ closure ({b₁, b₂} : Set G) := by
      rcases hg with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact OE64.IsKlein.b₁_mem_grp
      · exact OE64.IsKlein.b₂_mem_grp
      · exact mul_mem OE64.IsKlein.b₁_mem_grp OE64.IsKlein.b₂_mem_grp
    have e : b * (g * w₀ * g⁻¹) * b⁻¹ = (b * g) * w₀ * (b * g)⁻¹ := by group
    rw [e]
    exact OE64.omega_mem_P1 k α w₀ (mul_mem hb hgm)

theorem card_P1_le : Nat.card ↥(OE64.P1 α b₁ b₂ w₀) ≤ 32 := by
  have hα2 : α * α = 1 := c.hα.sq
  have hcomm : ∀ x ∈ c.W1, ∀ y ∈ c.W1, x * y * x⁻¹ * y⁻¹ ∈ zpowers α := by
    intro x hx y hy
    rcases c.W1_comm hx hy with h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact mem_zpowers α
  have hsq : ∀ x ∈ c.W1, x * x ∈ zpowers α := by
    intro x hx
    rcases c.W1_sq hx with h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact mem_zpowers α
  have hl : ∀ y ∈ OE64.genP b₁ b₂ w₀, y ∈ c.W1 := by
    intro y hy
    rw [OE64.mem_genP] at hy
    obtain ⟨g, hg, rfl⟩ := hy
    have hgB : g ∈ B := by
      rcases hg with rfl | rfl | rfl | rfl
      exacts [B.one_mem, k.mem₁, k.mem₂, k.prod_mem]
    exact c.N1_W1 (c.B_le_N1 hgB) hw₀
  have := I13HE64.card_closure_le_of_list c.W1 (c.Zs_le_W1 c.alpha_mem_Zs) hα2 hcomm hsq
    (OE64.genP b₁ b₂ w₀) hl
  simpa [OE64.P1, OE64.genP] using this

end P1

theorem exists_PData {b₁ b₂ : G} (k : OE64.IsKlein B b₁ b₂) (kE : c.KleinE b₁ b₂) :
    ∃ P : Subgroup G, c.PData P ∧
      ∀ b ∈ closure ({b₁, b₂} : Set G), ∀ p ∈ P, b * p * b⁻¹ ∈ P := by
  obtain ⟨e₀, hb₁, hb₂, hgen⟩ := kE.gen
  obtain ⟨w₀, hw₀⟩ := c.thetaHom_surjective e₀
  have hw₀W : (w₀ : G) ∈ c.W1 := w₀.2
  have hle : OE64.P1 α b₁ b₂ (w₀ : G) ≤ c.W1 := c.P1_le_W1 k hw₀W
  let f : ↥(OE64.P1 α b₁ b₂ (w₀ : G)) →* ↥E := c.thetaHom.comp (Subgroup.inclusion hle)
  have hf : ∀ p : ↥(OE64.P1 α b₁ b₂ (w₀ : G)), ((f p : ↥E) : G) = p * (z * p * z⁻¹) :=
    fun p => rfl
  have hfe : ∀ (g : G) (hg : g ∈ closure ({b₁, b₂} : Set G)) (hgB : g ∈ B),
      c.kappa ⟨g, hgB⟩ e₀ ∈ f.range := by
    intro g hg hgB
    refine ⟨⟨g * w₀ * g⁻¹, OE64.omega_mem_P1 k α w₀ hg⟩, ?_⟩
    show c.thetaHom ⟨g * w₀ * g⁻¹, _⟩ = _
    rw [← hw₀]
    exact c.theta_conj_B ⟨g, hgB⟩ w₀
  have hsurj : Function.Surjective f := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, closure_le]
    rintro e (rfl | rfl | rfl | rfl)
    · have := hfe 1 (one_mem _) B.one_mem
      have h1 : c.kappa (⟨1, B.one_mem⟩ : ↥B) = 1 := map_one c.kappa
      rwa [h1, MulAut.one_apply] at this
    · exact hfe b₁ OE64.IsKlein.b₁_mem_grp k.mem₁
    · exact hfe b₂ OE64.IsKlein.b₂_mem_grp k.mem₂
    · have := hfe (b₁ * b₂) (mul_mem OE64.IsKlein.b₁_mem_grp OE64.IsKlein.b₂_mem_grp) k.prod_mem
      have h1 : c.kappa (⟨b₁ * b₂, k.prod_mem⟩ : ↥B) =
          c.kappa ⟨b₁, k.mem₁⟩ * c.kappa ⟨b₂, k.mem₂⟩ := by
        rw [← map_mul]; rfl
      rwa [h1, MulAut.mul_apply] at this
  have hbij : Function.Bijective f := by
    refine hsurj.bijective_of_nat_card_le ?_
    rw [c.h.wf.card_E]
    exact c.card_P1_le k hw₀W
  refine ⟨OE64.P1 α b₁ b₂ (w₀ : G), ⟨hle, OE64.alpha_mem_P1 α b₁ b₂ w₀, ?_, ?_⟩, ?_⟩
  · intro p hp p' hp' h
    have := hbij.1 (a₁ := ⟨p, hp⟩) (a₂ := ⟨p', hp'⟩) (Subtype.ext (by rw [hf, hf]; exact h))
    exact congrArg Subtype.val this
  · intro e he
    obtain ⟨⟨p, hp⟩, hpe⟩ := hbij.2 ⟨e, he⟩
    exact ⟨p, hp, by rw [← hf ⟨p, hp⟩, hpe]⟩
  · intro b hb p hp
    exact c.P1_conj k hb hp

end OI13Ctx

end CFSG.EvenSporadicStandard.Fin76b
