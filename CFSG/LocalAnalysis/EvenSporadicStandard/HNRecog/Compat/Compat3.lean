module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.Fam
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpDichotomy

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'} {α : G → G'}

theorem compat_three (h : F5Std a z) (h' : F5Std a' z') (hα : IsIsoOn (Gx a) (Gx a') α)
    (F : Fam a α) {b t : G} (hb : b ∈ InvIn (Gx a)) (hbA : IsConj a b) (hba : b ≠ a)
    (hcase : b ∈ orb2A a a ∨ t ∈ orb2A a b) (ht : t ∈ InvIn (Gxy a b)) (hta : t ≠ a)
    (htb : t ≠ b) (htab : t ≠ a * b) :
    (∀ x ∈ Gxy b t, F.app b x = F.app t x) ∨
      ∀ x ∈ Gxy b t, F.app b x = F.app t (a * x * a⁻¹) := by
  have hbtG : t ∈ Gx b := (mem_Gxy.1 ht.1).2
  have htG : t ∈ InvIn (Gx a) := ⟨(mem_Gxy.1 ht.1).1, ht.2⟩
  have hbGt : b ∈ Gx t := mem_Gx.2 (mem_Gx.1 hbtG).symm
  have hFb : F.app b t = α t := F.restrict b hb t ht.1
  have hFt : F.app t b = α b := F.restrict t htG b (mem_Gxy.2 ⟨hb.1, hbGt⟩)
  have h₁ : IsIsoOn (Gxy b t) (Gx (α b) ⊓ Gx (α t)) (F.app b) := by
    have := (F.iso b hb).restrict_cent hbtG
    rw [hFb] at this
    rwa [Gxy_eq_inf]
  have h₂ : IsIsoOn (Gxy b t) (Gx (α b) ⊓ Gx (α t)) (F.app t) := by
    have := (F.iso t htG).restrict_cent hbGt
    rw [hFt, inf_comm (Gx t) (Gx b), inf_comm (Gx (α t)) (Gx (α b))] at this
    rwa [Gxy_eq_inf]
  have hS : ∀ x ∈ Gxyz a b t, F.app b x = F.app t x := by
    intro x hx
    obtain ⟨hxa, hxb, hxt⟩ := mem_Gxyz.1 hx
    rw [F.restrict b hb x (mem_Gxy.2 ⟨hxa, hxb⟩), F.restrict t htG x (mem_Gxy.2 ⟨hxa, hxt⟩)]
  exact cp_dichotomy h hb hbA hba hcase ht hta htb htab h₁ h₂ hS

theorem compat_three_eq (h : F5Std a z) (h' : F5Std a' z') (hα : IsIsoOn (Gx a) (Gx a') α)
    (F : Fam a α) {b t : G} (hb : b ∈ InvIn (Gx a)) (hbA : IsConj a b) (hba : b ≠ a)
    (hcase : b ∈ orb2A a a ∨ t ∈ orb2A a b) (ht : t ∈ InvIn (Gxy a b)) (hta : t ≠ a)
    (htb : t ≠ b) (htab : t ≠ a * b) {x : G} (hx : x ∈ Gxy b t) (hx' : x ∉ Gxyz a b t)
    (hxe : F.app t x = F.app b x) : ∀ y ∈ Gxy b t, F.app b y = F.app t y := by
  rcases compat_three h h' hα F hb hbA hba hcase ht hta htb htab with h1 | h1
  · exact h1
  · exfalso
    have htG : t ∈ InvIn (Gx a) := ⟨(mem_Gxy.1 ht.1).1, ht.2⟩
    have hbtG : t ∈ Gx b := (mem_Gxy.1 ht.1).2
    have hat : a ∈ Gx t := mem_Gx.2 (mem_Gx.1 htG.1).symm
    obtain ⟨hxb, hxt⟩ := mem_Gxy.1 hx
    have hax : a * x * a⁻¹ ∈ Gx t := (Gx t).mul_mem ((Gx t).mul_mem hat hxt) ((Gx t).inv_mem hat)
    have hxx : F.app t x = F.app t (a * x * a⁻¹) := hxe.trans (h1 x hx)
    have hxeq : x = a * x * a⁻¹ := (F.iso t htG).injOn x hxt _ hax hxx
    have hcomm : a * x = x * a := by
      have := congrArg (fun w => w * a) hxeq
      simpa [mul_assoc] using this.symm
    exact hx' (mem_Gxyz.2 ⟨mem_Gx.2 hcomm, hxb, hxt⟩)

end CFSG.EvenSporadicStandard.HNRecog.Section4
