module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.Fam
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpDihedral

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'} {α : G → G'}

theorem exists_inv_vertex (h : F5Std a z) {x : G} (hx : IsConj a x) :
    ∃ t, t ∈ InvIn (Gxy a x) := by
  have hxmem : x ∈ gammaSet a z a :=
    h.loc.gamma.self.eq_gamma a x (IsConj.refl a) hx
  simp only [gammaSet, Set.mem_union, Set.mem_singleton_iff] at hxmem
  rcases hxmem with
    (((((((hxa | hx2A) | hx2B) | hx3A) | hx4A) | hx4B) | hx5A) | hx5E) | hx6A
  · rw [hxa]
    exact ⟨a, mem_Gxy.mpr ⟨self_mem_Gx a, self_mem_Gx a⟩, h.typ.orderOf_a⟩
  · exact ⟨x, mem_Gxy.mpr ⟨h.mem_Gx_of_orb2A (IsConj.refl a) hx2A, self_mem_Gx x⟩,
      h.orderOf_eq_two (Or.inl hx)⟩
  · exact ⟨x, mem_Gxy.mpr ⟨h.mem_Gx_of_orb2B (IsConj.refl a) hx2B, self_mem_Gx x⟩,
      h.orderOf_eq_two (Or.inl hx)⟩
  · obtain ⟨t, ht⟩ := hx3A.2.2
    exact ⟨t, mem_Gxy.mpr ⟨h.mem_Gx_of_orb2A (IsConj.refl a) ht.1,
      h.mem_Gx_of_orb2A hx ht.2⟩, h.orderOf_eq_two (Or.inl ht.1.1)⟩
  · exact ⟨(a * x) ^ 2, (cp_central_inv h hx (k := 2) (Or.inr hx4A.2)).1⟩
  · exact ⟨(a * x) ^ 2, (cp_central_inv h hx (k := 2) (Or.inl hx4B.2)).1⟩
  · obtain ⟨t, ht⟩ := (h.loc.lines.self.five_A x hx5A).1.nonempty
    exact ⟨t, ht⟩
  · obtain ⟨t, -, htA, -, -, htG, -, -⟩ := h.loc.five.self.klein_E x hx5E
    exact ⟨t, htG, h.orderOf_eq_two (Or.inl htA)⟩
  · exact ⟨(a * x) ^ 3, (cp_central_inv h hx (k := 3) (Or.inl hx6A.2.2)).1⟩

structure IsTheta (a : G) (F : Fam a α) (θ : G → G') : Prop where
  eq_app : ∀ x, IsConj a x → ∀ t ∈ InvIn (Gxy a x), θ x = F.app t x

theorem IsTheta.typed (h : F5Std a z) (h' : F5Std a' z') (hα : IsIsoOn (Gx a) (Gx a') α)
    {F : Fam a α} {θ : G → G'} (hθ : IsTheta a F θ) {x : G} (hx : IsConj a x) :
    IsConj a' (θ x) := by
  obtain ⟨t, ht⟩ := exists_inv_vertex h hx
  have htGxa : t ∈ Gx a := (mem_Gxy.mp ht.1).1
  have htInv : t ∈ InvIn (Gx a) := ⟨htGxa, ht.2⟩
  have hxt : x ∈ Gx t := mem_Gx.2 (mem_Gx.1 (mem_Gxy.mp ht.1).2).symm
  have ha' : IsConj a' (α a) :=
    Eq.mpr (congrArg (fun y => IsConj a' y) (iso_apply_self h h' hα)) (IsConj.refl a')
  have hαa : IsIsoOn (Gx a) (Gx (α a)) α :=
    Eq.mpr (congrArg (fun y => IsIsoOn (Gx a) (Gx y) α) (iso_apply_self h h' hα)) hα
  rw [hθ.eq_app x hx t ht]
  exact Fam.typed h h' (IsConj.refl a) ha' hαa F htInv hxt hx

theorem IsTheta.equivariant (h : F5Std a z) {F : Fam a α} {θ : G → G'} (hθ : IsTheta a F θ)
    {g x : G} (hg : g ∈ Gx a) (hx : IsConj a x) :
    θ (g * x * g⁻¹) = α g * θ x * (α g)⁻¹ := by
  obtain ⟨t, ht⟩ := exists_inv_vertex h hx
  have htGxa : t ∈ Gx a := (mem_Gxy.mp ht.1).1
  have htInv : t ∈ InvIn (Gx a) := ⟨htGxa, ht.2⟩
  have hxt : x ∈ Gx t := mem_Gx.2 (mem_Gx.1 (mem_Gxy.mp ht.1).2).symm
  have hx' : IsConj a (g * x * g⁻¹) := hx.trans (isConj_iff.2 ⟨g, rfl⟩)
  have hgt : g * t * g⁻¹ ∈ Gx a :=
    (Gx a).mul_mem ((Gx a).mul_mem hg htGxa) ((Gx a).inv_mem hg)
  have hcomm : (g * x * g⁻¹) * (g * t * g⁻¹) = (g * t * g⁻¹) * (g * x * g⁻¹) := by
    calc (g * x * g⁻¹) * (g * t * g⁻¹) = g * (x * t) * g⁻¹ := by group
      _ = g * (t * x) * g⁻¹ := by rw [← mem_Gx.1 hxt]
      _ = (g * t * g⁻¹) * (g * x * g⁻¹) := by group
  have hgt' : g * t * g⁻¹ ∈ Gx (g * x * g⁻¹) := mem_Gx.2 hcomm
  have ht1ord : orderOf (g * t * g⁻¹) = 2 := by
    simpa [MulAut.conj_apply] using
      (MulEquiv.orderOf_eq (MulAut.conj g) t).trans ht.2
  have ht₁ : g * t * g⁻¹ ∈ InvIn (Gxy a (g * x * g⁻¹)) :=
    ⟨mem_Gxy.mpr ⟨hgt, hgt'⟩, ht1ord⟩
  calc θ (g * x * g⁻¹) = F.app (g * t * g⁻¹) (g * x * g⁻¹) :=
        hθ.eq_app (g * x * g⁻¹) hx' (g * t * g⁻¹) ht₁
    _ = α g * F.app t x * (α g)⁻¹ := F.equivariant t htInv g hg x hxt
    _ = α g * θ x * (α g)⁻¹ := by rw [← hθ.eq_app x hx t ht]

theorem IsTheta.orderOf_mul (h : F5Std a z) (h' : F5Std a' z') (hα : IsIsoOn (Gx a) (Gx a') α)
    {F : Fam a α} {θ : G → G'} (hθ : IsTheta a F θ) {x : G} (hx : IsConj a x) :
    orderOf (a' * θ x) = orderOf (a * x) := by
  obtain ⟨t, ht⟩ := exists_inv_vertex h hx
  have htGxa : t ∈ Gx a := (mem_Gxy.mp ht.1).1
  have htInv : t ∈ InvIn (Gx a) := ⟨htGxa, ht.2⟩
  have hat : a ∈ Gx t := mem_Gx.2 (mem_Gx.1 htGxa).symm
  have hxt : x ∈ Gx t := mem_Gx.2 (mem_Gx.1 (mem_Gxy.mp ht.1).2).symm
  have hax : a * x ∈ Gx t := (Gx t).mul_mem hat hxt
  have hia : F.app t a = a' :=
    (F.restrict t htInv a (mem_Gxy.mpr ⟨self_mem_Gx a, hat⟩)).trans (iso_apply_self h h' hα)
  rw [← hia, hθ.eq_app x hx t ht, ← (F.iso t htInv).map_mul a hat x hxt]
  exact (F.iso t htInv).orderOf_eq hax

end CFSG.EvenSporadicStandard.HNRecog.Section4
