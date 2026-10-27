module

public import CFSG.GH74.Generic.S1.CompIdent
public import CFSG.GH74.Generic.S1.SL2Facts
public import CFSG.GH74.Generic.S1.Exo.NbDefs
public import CFSG.GH74.KGroups.L3EpsOuterLin

public section

namespace CFSG.GH74.Generic.S1.Exo

theorem NbhdHyp.two_subgroup_le {H : Type} [Group H] [Finite H] {q : ℕ} {w y : H}
    {J₂ J₄ : Subgroup H} (h : NbhdHyp H q w y J₂ J₄) {T : Subgroup H} (hT : IsPGroup 2 T)
    (hc₂ : ∀ t ∈ T, ∀ a ∈ J₂, t * a = a * t) (hc₄ : ∀ t ∈ T, ∀ b ∈ J₄, t * b = b * t) :
    ∀ t ∈ T, t = 1 ∨ t = w ∨ t = y ∨ t = w * y := by
  obtain ⟨ψ₂, hψ₂i, hψ₂m⟩ := exists_q8_of_hasSL2Model h.odd h.sl₂
  obtain ⟨ψ₄, hψ₄i, hψ₄m⟩ := exists_q8_of_hasSL2Model h.odd h.sl₄
  obtain ⟨t₂, -, -, ht₂inv, -⟩ := sl2_involution_facts h.odd h.sl₂
  obtain ⟨t₄, -, -, ht₄inv, -⟩ := sl2_involution_facts h.odd h.sl₄
  have hw : w = t₂ := (ht₂inv w h.w_mem h.w_sq).resolve_left h.w_ne_one
  have hy : y = t₄ := (ht₄inv y h.y_mem h.y_sq).resolve_left h.y_ne_one
  have hzz : (QuaternionGroup.a 2 : QuaternionGroup 2) * QuaternionGroup.a 2 = 1 := by decide
  have hz1 : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 := by decide
  have hz2 : ψ₂ (QuaternionGroup.a 2) = w := by
    have hsq : ψ₂ (QuaternionGroup.a 2) * ψ₂ (QuaternionGroup.a 2) = 1 := by
      rw [← map_mul, hzz, map_one]
    rcases ht₂inv _ (hψ₂m _) hsq with h1 | h1
    · exact absurd (hψ₂i (h1.trans (map_one ψ₂).symm)) hz1
    · rw [h1, hw]
  have hz4 : ψ₄ (QuaternionGroup.a 2) = y := by
    have hsq : ψ₄ (QuaternionGroup.a 2) * ψ₄ (QuaternionGroup.a 2) = 1 := by
      rw [← map_mul, hzz, map_one]
    rcases ht₄inv _ (hψ₄m _) hsq with h1 | h1
    · exact absurd (hψ₄i (h1.trans (map_one ψ₄).symm)) hz1
    · rw [h1, hy]
  have hinter : ∀ u : H, u ∈ J₂ → u ∈ J₄ → u = 1 := by
    intro u hu2 hu4
    rcases h.cent₂ u hu2 (fun b hb => (h.comm b hb u hu4).symm) with h2 | h2
    · exact h2
    · rcases h.cent₄ u hu4 (fun b hb => h.comm u hu2 b hb) with h4 | h4
      · exact h4
      · exact absurd (h2.symm.trans h4) h.w_ne_y
  let φ : QuaternionGroup 2 × QuaternionGroup 2 →* H :=
    ψ₂.noncommCoprod ψ₄ fun m n => h.comm _ (hψ₂m m) _ (hψ₄m n)
  have hφ : ∀ g, φ g = ψ₂ g.1 * ψ₄ g.2 := fun g => rfl
  have hker : ∀ g, φ g = 1 → g = 1 ∨
      g = ((QuaternionGroup.a 2 : QuaternionGroup 2), (QuaternionGroup.a 2 : QuaternionGroup 2)) := by
    intro g hg
    left
    have hg' : ψ₂ g.1 * ψ₄ g.2 = 1 := hg
    have hu : ψ₂ g.1 = 1 := by
      apply hinter _ (hψ₂m _)
      rw [eq_inv_of_mul_eq_one_left hg']
      exact J₄.inv_mem (hψ₄m _)
    have hv : ψ₄ g.2 = 1 := by
      rw [hu, one_mul] at hg'
      exact hg'
    exact Prod.ext (hψ₂i (hu.trans (map_one ψ₂).symm)) (hψ₄i (hv.trans (map_one ψ₄).symm))
  have hcomm : ∀ (a : QuaternionGroup 2 × QuaternionGroup 2) (t : H), t ∈ T →
      φ a * t = t * φ a := by
    intro a t ht
    have e2 := hc₂ t ht _ (hψ₂m a.1)
    have e4 := hc₄ t ht _ (hψ₄m a.2)
    rw [hφ, mul_assoc, ← e4, ← mul_assoc, ← e2, mul_assoc]
  intro t ht
  obtain ⟨g, hg, hgc⟩ := q8q8_commuting_two_subgroup_le' h.gen4 φ hker T hT hcomm t ht
  have h1 := CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices.quaternion_center g.1
    (fun x => by
      have := congrArg Prod.fst (hgc (x, 1))
      simpa using this)
  have h2 := CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices.quaternion_center g.2
    (fun x => by
      have := congrArg Prod.snd (hgc (1, x))
      simpa using this)
  rw [← hg, hφ]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · left
    rw [h1, h2, map_one, map_one, mul_one]
  · right; right; left
    rw [h1, h2, map_one, hz4, one_mul]
  · right; left
    rw [h1, h2, map_one, hz2, mul_one]
  · right; right; right
    rw [h1, h2, hz2, hz4]

end CFSG.GH74.Generic.S1.Exo
