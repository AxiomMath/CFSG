module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.TableAt

public section

namespace CFSG.EvenSporadicStandard.HNRecog.AutGamma

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type} [Group G] {a z : G}

theorem not_centralizes_of_mem_kinds [Finite G] (hF : IsF5Type a z) (hL : F5Local G a z)
    (hnc : ¬ IsConj a z) {x : G} (hx : x ∈ orb3A a a) {y : G}
    (hy : y ∈ orb4A a z a ∪ orb4B a a ∪ orb6A a a ∪ orb5A a a ∪ orb5E a a) :
    ¬ ∀ s ∈ Gxy a x, y * s = s * y := by
  intro hc
  have hcardx : Nat.card ↥(Gxy a x) = 5040 := by
    rw [Gxy_eq_inf]
    exact hL.tableVII.self.card_3A x hx
  have hle : Gxy a x ≤ Gxy a y := by
    intro s hs
    exact mem_Gxy.2 ⟨(mem_Gxy.1 hs).1, mem_Gx.2 (hc s hs)⟩
  have hdvd : 5040 ∣ Nat.card ↥(Gxy a y) := by
    have h := Subgroup.card_dvd_of_le hle
    rwa [hcardx] at h
  simp only [Set.mem_union] at hy
  rcases hy with (((hy4A | hy4B) | hy6A) | hy5A) | hy5E
  · have hstab : Nat.card ↥(Gx a ⊓ Gx y) = 640 := by
      simpa using hL.tableV.self.card_stab 2 y (by simpa [tab5Set] using hy4A)
    rw [Gxy_eq_inf, hstab] at hdvd
    norm_num at hdvd
  · have hstab : Nat.card ↥(Gx a ⊓ Gx y) = 1440 := by
      simpa using hL.tableV.self.card_stab 3 y (by simpa [tab5Set] using hy4B)
    rw [Gxy_eq_inf, hstab] at hdvd
    norm_num at hdvd
  · have hstab : Nat.card ↥(Gx a ⊓ Gx y) = 240 := by
      simpa using hL.tableV.self.card_stab 4 y (by simpa [tab5Set] using hy6A)
    rw [Gxy_eq_inf, hstab] at hdvd
    norm_num at hdvd
  · obtain ⟨t, ht⟩ := ((hL.s7.self.classes x hx).orbit 0).nonempty
    have htS : t ∈ orb2A a a ∩ orb2A a x := ht
    have htSub := (hL.s7.self.classes x hx).subset 0 ht
    have htGxy : t ∈ Gxy a y := hle htSub.1
    have hEq := (hL.lines.self.five_A y hy5A).2
    have ht2B : t ∈ orb2B a z a ∩ orb2B a z y := by
      rw [← hEq]
      exact ⟨htGxy, htSub.2⟩
    exact hnc (htS.1.2.trans (ht2B.1.2).symm)
  · have hcard : Nat.card ↥(Gxy a y) = 500 :=
      card_Gxy_orb5E_at hL (IsConj.refl a) hy5E
    rw [hcard] at hdvd
    norm_num at hdvd

end CFSG.EvenSporadicStandard.HNRecog.AutGamma
