module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARemCls
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private theorem conj_mem_L (h : Hyp G t L) {g : G} (hg : g ∈ invCent t) {x : G}
    (hx : x ∈ L) : g * x * g⁻¹ ∈ L := by
  have hxH : x ∈ invCent t := L_le_invCent h hx
  have hmem : (⟨g, hg⟩ : ↥(invCent t)) * (⟨x, hxH⟩ : ↥(invCent t)) *
      (⟨g, hg⟩ : ↥(invCent t))⁻¹ ∈ L.subgroupOf (invCent t) :=
    h.normal.conj_mem ⟨x, hxH⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨g, hg⟩
  simpa using (Subgroup.mem_subgroupOf.mp hmem)

private theorem mem_zpowers_t_eq_one_or (h : Hyp G t L) {p : G} (hp : p ∈ zpowers t) :
    p = 1 ∨ p = t := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hp
  have ht : t * t = 1 := t_mul_self h
  have ht2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ht]
  rcases Int.even_or_odd' k with ⟨m, hm | hm⟩
  · left
    rw [← hk, hm, zpow_mul, ht2, one_zpow]
  · right
    rw [← hk, hm, zpow_add, zpow_mul, ht2, one_zpow, one_mul, zpow_one]

private theorem zpowers_t_sq (h : Hyp G t L) {p : G} (hp : p ∈ zpowers t) : p * p = 1 := by
  rcases mem_zpowers_t_eq_one_or h hp with rfl | rfl
  · rw [one_mul]
  · exact t_mul_self h

private theorem isElemAbelian_sup_zpowers_of_le_invCent {E : Subgroup G}
    (h : Ctx t L S x₁ x₂ lam rho tau) (hEH : E ≤ invCent t)
    (hE : CFSG.Open.IsElemAbelian 2 E) :
    CFSG.Open.IsElemAbelian 2 (E ⊔ zpowers t) := by
  have hcomm : ∀ a ∈ E, ∀ b ∈ zpowers t, a * b = b * a := by
    intro a ha b hb
    have hat : Commute a t := mem_invCent_iff.mp (hEH ha)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← hk]
    exact (hat.zpow_right k).eq
  refine ⟨?_, ?_⟩
  · exact isMulCommutative_sup_of_commute hcomm hE.1 inferInstance
  · intro x hx
    obtain ⟨v, hv, p, hp, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp hx
    have hv2 : v ^ 2 = 1 := hE.2 v hv
    have hp2 : p ^ 2 = 1 := by simpa [pow_two] using zpowers_t_sq h.hyp hp
    have hvp : Commute v p := hcomm v hv p hp
    rw [hvp.mul_pow 2, hv2, hp2, mul_one]

private theorem card_sup_zpowers_of_t_not_mem_of_le_invCent {E : Subgroup G}
    (h : Ctx t L S x₁ x₂ lam rho tau) (hEH : E ≤ invCent t) (htE : t ∉ E) :
    Nat.card (E ⊔ zpowers t : Subgroup G) = 2 * Nat.card E := by
  have hcomm : ∀ a ∈ E, ∀ b ∈ zpowers t, a * b = b * a := by
    intro a ha b hb
    have hat : Commute a t := mem_invCent_iff.mp (hEH ha)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← hk]
    exact (hat.zpow_right k).eq
  have hinf : E ⊓ zpowers t = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    rcases mem_zpowers_t_eq_one_or h.hyp hx.2 with hx1 | hxt
    · rw [hx1]
    · exact absurd (hxt ▸ hx.1) htE
  have hcard := card_sup_of_commute (P := E) (Q := zpowers t) hcomm hinf
  rw [hcard, Nat.card_zpowers, h.hyp.ord_t, Nat.mul_comm]

theorem false_of_E8_avoiding_tG (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) (htau : ∃ g : G, g * t * g⁻¹ = tau)
    (httau : ∃ g : G, g * t * g⁻¹ = t * tau)
    (htz : ∃ g : G, g * t * g⁻¹ = t * (x₁ * x₂) ^ 2) {E : Subgroup G} (hEH : E ≤ invCent t)
    (hEe : CFSG.Open.IsElemAbelian 2 E) (hEc : Nat.card E = 8)
    (hno : ∀ g : G, ∀ e ∈ E, g * t * g⁻¹ ≠ e) : False := by
  have hEsub : E ≤ twoCore t ⊔ L := by
    intro e he
    by_cases he1 : e = 1
    · rw [he1]
      exact Subgroup.mem_sup_left (twoCore t).one_mem
    · have heH : e ∈ invCent t := hEH he
      have hee : e * e = 1 := by simpa [pow_two] using hEe.2 e he
      obtain ⟨k, hkH, hconj⟩ := (five_classes_of h h43 h44).1 e heH hee he1
      rcases hconj with h1 | h1 | h1 | h1 | h1
      ·
        exact absurd (by rw [← h1]; group) (hno k⁻¹ e he)
      ·
        have heq : e = k⁻¹ * (x₁ * x₂) ^ 2 * k := by rw [← h1]; group
        rw [heq]
        exact Subgroup.mem_sup_right (by
          simpa using conj_mem_L h.hyp ((invCent t).inv_mem hkH) (y_z_mem_L h.toCtx0).2)
      · obtain ⟨g, hg⟩ := htau
        exact absurd (by
          rw [show (k⁻¹ * g) * t * (k⁻¹ * g)⁻¹ = k⁻¹ * (g * t * g⁻¹) * k by group, hg]
          rw [← h1]; group) (hno (k⁻¹ * g) e he)
      · obtain ⟨g, hg⟩ := htz
        exact absurd (by
          rw [show (k⁻¹ * g) * t * (k⁻¹ * g)⁻¹ = k⁻¹ * (g * t * g⁻¹) * k by group, hg]
          rw [← h1]; group) (hno (k⁻¹ * g) e he)
      · obtain ⟨g, hg⟩ := httau
        exact absurd (by
          rw [show (k⁻¹ * g) * t * (k⁻¹ * g)⁻¹ = k⁻¹ * (g * t * g⁻¹) * k by group, hg]
          rw [← h1]; group) (hno (k⁻¹ * g) e he)
  have htE : t ∉ E := by
    intro ht
    exact (hno 1 t ht) (by group)
  have hYP : (E ⊔ zpowers t : Subgroup G) ≤ twoCore t ⊔ L := by
    refine sup_le hEsub ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_sup_left h.hyp.mem_twoCore
  have hYH : (E ⊔ zpowers t : Subgroup G) ≤ invCent t :=
    hYP.trans (sup_le (twoCore_le_invCent t) (L_le_invCent h.hyp))
  have hYe : CFSG.Open.IsElemAbelian 2 (E ⊔ zpowers t) :=
    isElemAbelian_sup_zpowers_of_le_invCent h hEH hEe
  have hYcard : Nat.card (E ⊔ zpowers t : Subgroup G) = 16 := by
    rw [card_sup_zpowers_of_t_not_mem_of_le_invCent h hEH htE, hEc]
  obtain ⟨k, hkH, hkS⟩ := exists_conj_le_of_isPGroup (H := invCent t) (S := S)
    (Q := E ⊔ zpowers t) hYH hYe.isPGroup h.toCtx0.le_invCent h.toCtx0.isPGroup
    h.toCtx0.relIndex_odd
  have hconjPL : ∀ y ∈ (E ⊔ zpowers t : Subgroup G), k * y * k⁻¹ ∈ twoCore t ⊔ L := by
    intro y hy
    obtain ⟨p, hp, l, hl, rfl⟩ :=
      (mem_sup_iff_of_commute (P := twoCore t) (Q := L) (twoCore_commute h.hyp)).mp (hYP hy)
    rw [show k * (p * l) * k⁻¹ = (k * p * k⁻¹) * (k * l * k⁻¹) by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (twoCore_conj_mem t hkH hp))
      (Subgroup.mem_sup_right (conj_mem_L h.hyp hkH hl))
  let f : G →* G := (MulAut.conj k).toMonoidHom
  have hf : ∀ x, f x = k * x * k⁻¹ := fun x => by simp [f, MulAut.conj_apply]
  have hfinj : Function.Injective f := by
    intro x y hxy
    apply (MulAut.conj k).injective
    simpa [f] using hxy
  have hY'le : (E ⊔ zpowers t).map f ≤ twoCore t ⊔ wreathGrp x₁ x₂ lam := by
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    have haS : f a ∈ S := by rw [hf]; exact hkS a ha
    have haPL : f a ∈ twoCore t ⊔ L := by rw [hf]; exact hconjPL a ha
    have hmem : f a ∈ S ⊓ (twoCore t ⊔ L) := ⟨haS, haPL⟩
    rwa [h.inf_PL] at hmem
  have hY'e : CFSG.Open.IsElemAbelian 2 ((E ⊔ zpowers t).map f) :=
    CFSG.Open.IsElemAbelian.map hYe f
  have hY'card : Nat.card ((E ⊔ zpowers t).map f) = 16 := by
    rw [Subgroup.card_map_of_injective (f := f) hfinj, hYcard]
  have hle8 := h.m2_PT ((E ⊔ zpowers t).map f) hY'le hY'e
  omega

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
