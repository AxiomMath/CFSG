module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.Fam
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpDichotomy
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpArrCls
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpInputs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G}

theorem cp_member_unique (hG : Gen2A) (h : F5Std a z) {b x : G} (hbA : IsConj a b)
    (hx : IsConj a x) (hbx : b ∈ orb2A a x) {β : G → G'} (ℬ ℬ' : Fam b β) :
    (∀ u ∈ Gx x, ℬ.app x u = ℬ'.app x u) ∨ ∀ u ∈ Gx x, ℬ.app x u = ℬ'.app x (b * u * b⁻¹) := by
  obtain ⟨c₁, c₂, g, hc₁, hc₂, h1x, h1b, h1xb, h2x, h2b, h2xb, hg, hbg, hgen⟩ :=
    hG h x hx b hbx
  have hbF : F5Std b z := h.of_isConj hbA (IsConj.refl z)
  have hbG : b ∈ Gx x := h.mem_Gx_of_orb2A hx hbx
  have hxb : x * b = b * x := mem_Gx.1 hbG
  have hxInv : x ∈ InvIn (Gx b) := ⟨mem_Gx.2 hxb.symm, h.orderOf_eq_two (Or.inl hx)⟩
  have hbxA : IsConj b x := hbA.symm.trans hx
  have hxbA : IsConj a (b * x) := by rw [← hxb]; exact hbx.2
  have hx2A : x ∈ orb2A b b := ⟨hbxA, hbA.symm.trans hxbA⟩
  have hxne : x ≠ b :=
    (cp_ne_self_of_orb2A (h.of_isConj hx (IsConj.refl z))
      ⟨hx.symm.trans hbx.1, hx.symm.trans hbx.2⟩).symm
  have key : ∀ c, c ∈ InvIn (Gxy x b) → c ≠ x → c ≠ b → c ≠ x * b →
      (∀ u ∈ Gxy x c, ℬ.app x u = ℬ'.app x u) ∨
        ∀ u ∈ Gxy x c, ℬ.app x u = ℬ'.app x (b * u * b⁻¹) := by
    intro c hc hcx hcb hcxb
    have hcInv : c ∈ InvIn (Gxy b x) :=
      ⟨mem_Gxy.2 ⟨(mem_Gxy.1 hc.1).2, (mem_Gxy.1 hc.1).1⟩, hc.2⟩
    have hcGx : c ∈ Gx x := (mem_Gxy.1 hc.1).1
    have hβc : ℬ.app x c = β c := ℬ.restrict x hxInv c hcInv.1
    have hβc' : ℬ'.app x c = β c := ℬ'.restrict x hxInv c hcInv.1
    have h₁ : IsIsoOn (Gxy x c) (Gx (β x) ⊓ Gx (β c)) (ℬ.app x) := by
      have := (ℬ.iso x hxInv).restrict_cent hcGx
      rw [hβc] at this
      rwa [Gxy_eq_inf]
    have h₂ : IsIsoOn (Gxy x c) (Gx (β x) ⊓ Gx (β c)) (ℬ'.app x) := by
      have := (ℬ'.iso x hxInv).restrict_cent hcGx
      rw [hβc'] at this
      rwa [Gxy_eq_inf]
    have hS : ∀ u ∈ Gxyz b x c, ℬ.app x u = ℬ'.app x u := by
      intro u hu
      obtain ⟨hub, hux, -⟩ := mem_Gxyz.1 hu
      have hu' : u ∈ Gxy b x := mem_Gxy.2 ⟨hub, hux⟩
      rw [ℬ.restrict x hxInv u hu', ℬ'.restrict x hxInv u hu']
    exact cp_dichotomy hbF hxInv hbxA hxne (Or.inl hx2A) hcInv hcb hcx
      (by rw [← hxb]; exact hcxb) h₁ h₂ hS
  have hiso : IsIsoOn (Gx x) (Gx (β x)) (ℬ.app x) := ℬ.iso x hxInv
  have hiso' : IsIsoOn (Gx x) (Gx (β x)) (ℬ'.app x) := ℬ'.iso x hxInv
  have hiso'' : IsIsoOn (Gx x) (Gx (β x)) (fun u => ℬ'.app x (b * u * b⁻¹)) :=
    (isIsoOn_conj hbG).comp hiso'
  have hsub : ((Gxy x c₁ : Set G) ∪ (Gxy x c₂ : Set G)) ⊆ Gx x := by
    rintro u (hu | hu)
    exacts [(mem_Gxy.1 hu).1, (mem_Gxy.1 hu).1]
  have hgx : g ∈ Gx x := (mem_Gxyz.1 hg).1
  have hg₁ : g ∈ Gxy x c₁ := mem_Gxy.2 ⟨hgx, (mem_Gxyz.1 hg).2.1⟩
  have hg₂ : g ∈ Gxy x c₂ := mem_Gxy.2 ⟨hgx, (mem_Gxyz.1 hg).2.2⟩
  have hbgb : b * g * b⁻¹ ∈ Gx x :=
    (Gx x).mul_mem ((Gx x).mul_mem hbG hgx) ((Gx x).inv_mem hbG)
  have hbad : ℬ'.app x g = ℬ'.app x (b * g * b⁻¹) → False := by
    intro e
    have e' : g = b * g * b⁻¹ := hiso'.injOn g hgx _ hbgb e
    apply hbg
    calc b * g = b * g * b⁻¹ * b := by group
      _ = g * b := by rw [← e']
  rcases key c₁ hc₁ h1x h1b h1xb with e₁ | e₁ <;> rcases key c₂ hc₂ h2x h2b h2xb with e₂ | e₂
  · left
    intro u hu
    rw [← hgen] at hu
    exact IsIsoOn.agree_on_closure hiso hiso' hsub (fun v hv => hv.elim (e₁ v) (e₂ v)) u hu
  · exact (hbad ((e₁ g hg₁).symm.trans (e₂ g hg₂))).elim
  · exact (hbad ((e₂ g hg₂).symm.trans (e₁ g hg₁))).elim
  · right
    intro u hu
    rw [← hgen] at hu
    exact IsIsoOn.agree_on_closure hiso hiso'' hsub (fun v hv => hv.elim (e₁ v) (e₂ v)) u hu

end CFSG.EvenSporadicStandard.HNRecog.Section4
