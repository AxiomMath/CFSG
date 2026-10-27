module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.Dict

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

section Congr

variable {H : Type} [Group H]

theorem hIsA_congr {a z x b : H} (ha : ∀ g : H, g * a = a * g) (hx : IsConj z x) (y : H) :
    HIsA a x b y ↔ HIsA a z b y := by
  have hconj : IsConj (a * z) (a * x) := by
    obtain ⟨c, hc⟩ := isConj_iff.1 hx
    refine isConj_iff.2 ⟨c, ?_⟩
    calc c * (a * z) * c⁻¹
        = (c * a) * z * c⁻¹ := by group
      _ = (a * c) * z * c⁻¹ := by rw [ha c]
      _ = a * (c * z * c⁻¹) := by group
      _ = a * x := by rw [hc]
  unfold HIsA
  constructor
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl (hconj.trans h))
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl (hconj.symm.trans h))
    · exact Or.inr (Or.inr h)

theorem hIsB_congr {z x z₁ : H} (hx : IsConj z x) (y : H) : HIsB x z₁ y ↔ HIsB z z₁ y := by
  unfold HIsB
  constructor
  · rintro (h | h)
    · exact Or.inl (hx.trans h)
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl (hx.symm.trans h)
    · exact Or.inr h

end Congr

variable {G : Type} [Group G]

private lemma xOrderOf_eq_of_isConj {x y : G} (h : IsConj x y) : orderOf x = orderOf y := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  exact (MulEquiv.orderOf_eq (MulAut.conj c) x).symm.trans
    (congrArg orderOf (MulAut.conj_apply c x))

private lemma xData_of_cross {p w : G} {x : ↥(Gx p)} (hp2 : p ^ 2 = 1) (hw2 : w ^ 2 = 1)
    (hpx : IsConj p (p * (x : G))) {c : G} (hpc : IsConj p c) (hppc : IsConj p (p * c))
    (hcross : IsConj p ((p * (x : G)) * c) ∨ IsConj w ((p * (x : G)) * c)) :
    ∃ hcp : c ∈ Gx p, (⟨c, hcp⟩ : ↥(Gx p)) ∈ Gx x := by
  have hcp : c ∈ Gx p :=
    mem_Gx_of_isConj_mul (x := p) (y := p) hp2 hp2 (IsConj.refl p) hpc (Or.inl hppc)
  refine ⟨hcp, ?_⟩
  have hcpx : c ∈ Gx (p * (x : G)) :=
    mem_Gx_of_isConj_mul (x := p) (y := w) hp2 hw2 hpx hpc hcross
  have hcp' : p * c = c * p := mem_Gx.1 hcp
  have hcpx' : (p * (x : G)) * c = c * (p * (x : G)) := mem_Gx.1 hcpx
  rw [mem_Gx]
  apply Subtype.ext
  change (x : G) * c = c * (x : G)
  have h1 : p * (x * c) = p * (c * x) := by
    calc p * (x * c) = (p * x) * c := by group
      _ = c * (p * x) := hcpx'
      _ = (c * p) * x := by group
      _ = (p * c) * x := by rw [hcp']
      _ = p * (c * x) := by group
  exact mul_left_cancel h1

theorem orb2A_inter_orb2A_eq {a p w : G} {z₀ b₀ u₀ x : ↥(Gx p)} (L : HLab p w z₀ b₀ u₀)
    (hap : IsConj a p) (hx : IsConj z₀ x) :
    orb2A a p ∩ orb2A a (p * (x : G)) = Subtype.val '' tabXSet (GxSelf p) x b₀ u₀ 0 := by
  have hp2 : p ^ 2 = 1 := by
    have ho : orderOf p = 2 := by
      simpa [GxSelf] using (Subgroup.orderOf_coe (GxSelf p)).trans L.facts.orderOf_a
    have h := pow_orderOf_eq_one p
    rw [ho] at h
    exact h
  have hw2 : w ^ 2 = 1 := by
    have hz0 : orderOf (z₀ : G) = 2 := by
      simpa [GxSelf] using (Subgroup.orderOf_coe z₀).trans L.facts.orderOf_z
    have ho : orderOf w = 2 := (xOrderOf_eq_of_isConj L.z₀_B).trans hz0
    have h := pow_orderOf_eq_one w
    rw [ho] at h
    exact h
  have hxW : IsConj w (x : G) :=
    L.z₀_B.trans (MonoidHom.map_isConj (Gx p).subtype hx)
  have hpx : IsConj p (p * (x : G)) := (HLab.isConj_z₀_iff L hxW).1 hx
  have hpA : ∀ c : G, IsConj a c ↔ IsConj p c :=
    fun c => ⟨fun h => hap.symm.trans h, fun h => hap.trans h⟩
  have hcentral : ∀ g : ↥(Gx p), g * GxSelf p = GxSelf p * g := by
    intro g
    apply Subtype.ext
    exact (mem_Gx.1 g.2).symm
  ext c
  constructor
  · rintro ⟨hcA, hcpxA⟩
    have hpc : IsConj p c := (hpA c).1 hcA.1
    have hppc : IsConj p (p * c) := (hpA (p * c)).1 hcA.2
    have hpxc : IsConj p ((p * (x : G)) * c) := (hpA ((p * (x : G)) * c)).1 hcpxA.2
    obtain ⟨hcp, hcomm⟩ :=
      xData_of_cross (p := p) (w := w) (x := x) hp2 hw2 hpx hpc hppc (Or.inl hpxc)
    let c' : ↥(Gx p) := ⟨c, hcp⟩
    have hc'x : c' ∈ Gx x := hcomm
    have hconjb₀ : IsConj b₀ c' := (HLab.isConj_b₀_iff L c').2 ⟨hpc, hppc⟩
    have hIsA : HIsA (GxSelf p) x b₀ (GxSelf p * x * c') :=
      (hIsA_congr hcentral hx (GxSelf p * x * c')).2
        ((HLab.isA_iff L (GxSelf p * x * c')).2 hpxc)
    exact ⟨c', ⟨hconjb₀, hc'x, hIsA⟩, rfl⟩
  · rintro ⟨c', hc', hc'eq⟩
    obtain ⟨hconjb₀, hc'x, hIsA⟩ := hc'
    obtain ⟨hpc, hppc⟩ := (HLab.isConj_b₀_iff L c').1 hconjb₀
    have hpxc : IsConj p ((p * (x : G)) * (c' : G)) :=
      (HLab.isA_iff L (GxSelf p * x * c')).1
        ((hIsA_congr hcentral hx (GxSelf p * x * c')).1 hIsA)
    rw [hc'eq] at hpc hppc hpxc
    exact ⟨⟨hap.trans hpc, hap.trans hppc⟩, hap.trans hpc, hap.trans hpxc⟩

theorem orb2A_inter_orb2B_eq {a p w : G} {z₀ b₀ u₀ x : ↥(Gx p)} (L : HLab p w z₀ b₀ u₀)
    (hap : IsConj a p) (hx : IsConj z₀ x) :
    orb2A a p ∩ orb2B a w (p * (x : G)) = Subtype.val '' tabXSet (GxSelf p) x b₀ u₀ 1 := by
  have hp2 : p ^ 2 = 1 := by
    have ho : orderOf p = 2 := by
      simpa [GxSelf] using (Subgroup.orderOf_coe (GxSelf p)).trans L.facts.orderOf_a
    have h := pow_orderOf_eq_one p
    rw [ho] at h
    exact h
  have hw2 : w ^ 2 = 1 := by
    have hz0 : orderOf (z₀ : G) = 2 := by
      simpa [GxSelf] using (Subgroup.orderOf_coe z₀).trans L.facts.orderOf_z
    have ho : orderOf w = 2 := (xOrderOf_eq_of_isConj L.z₀_B).trans hz0
    have h := pow_orderOf_eq_one w
    rw [ho] at h
    exact h
  have hxW : IsConj w (x : G) :=
    L.z₀_B.trans (MonoidHom.map_isConj (Gx p).subtype hx)
  have hpx : IsConj p (p * (x : G)) := (HLab.isConj_z₀_iff L hxW).1 hx
  have hpA : ∀ c : G, IsConj a c ↔ IsConj p c :=
    fun c => ⟨fun h => hap.symm.trans h, fun h => hap.trans h⟩
  have hcentral : ∀ g : ↥(Gx p), g * GxSelf p = GxSelf p * g := by
    intro g
    apply Subtype.ext
    exact (mem_Gx.1 g.2).symm
  ext c
  constructor
  · rintro ⟨hcA, hcxB⟩
    have hpc : IsConj p c := (hpA c).1 hcA.1
    have hppc : IsConj p (p * c) := (hpA (p * c)).1 hcA.2
    have hpxw : IsConj w ((p * (x : G)) * c) := hcxB.2
    obtain ⟨hcp, hcomm⟩ :=
      xData_of_cross (p := p) (w := w) (x := x) hp2 hw2 hpx hpc hppc (Or.inr hpxw)
    let c' : ↥(Gx p) := ⟨c, hcp⟩
    have hc'x : c' ∈ Gx x := hcomm
    have hconjb₀ : IsConj b₀ c' := (HLab.isConj_b₀_iff L c').2 ⟨hpc, hppc⟩
    have hIsB : HIsB x u₀ (GxSelf p * x * c') :=
      (hIsB_congr hx (GxSelf p * x * c')).2
        ((HLab.isB_iff L (GxSelf p * x * c')).2 hpxw)
    exact ⟨c', ⟨hconjb₀, hc'x, hIsB⟩, rfl⟩
  · rintro ⟨c', hc', hc'eq⟩
    obtain ⟨hconjb₀, hc'x, hIsB⟩ := hc'
    obtain ⟨hpc, hppc⟩ := (HLab.isConj_b₀_iff L c').1 hconjb₀
    have hpxw : IsConj w ((p * (x : G)) * (c' : G)) :=
      (HLab.isB_iff L (GxSelf p * x * c')).1
        ((hIsB_congr hx (GxSelf p * x * c')).1 hIsB)
    rw [hc'eq] at hpc hppc hpxw
    exact ⟨⟨hap.trans hpc, hap.trans hppc⟩, hap.trans hpc, hpxw⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
