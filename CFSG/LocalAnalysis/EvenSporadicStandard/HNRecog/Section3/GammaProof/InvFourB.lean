module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.Rows
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.Seg27Cases
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.Orders

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] [Finite G] {a z : G}

private lemma gamma_inf_Gxy_Gxyz_le_Gxyz (a b y t : G) :
    Gxy a y ⊓ Gxyz b y t ≤ Gxyz a y t := by
  intro g hg
  rw [Subgroup.mem_inf] at hg
  rw [mem_Gxyz] at hg ⊢
  exact ⟨(mem_Gxy.mp hg.1).1, hg.2.2⟩

theorem gamma_inv_fourB (H : GammaHyps a z) {y t : G} (hy : y ∈ orb4B a a)
    (ht : t ∈ orb2A a y) : ∃ s : G, orderOf s = 2 ∧ s ∈ Gxyz a y t := by
  obtain ⟨-, hbm⟩ := H.sq_mem_orb2A (IsConj.refl a) hy
  set b : G := (a * y) ^ 2 with hb
  have hbA : IsConj a b := hbm.1.1
  have hyb : y ∈ orb2A a b := H.orb2A_symm hy.1 hbm.2
  have hab : a * b = b * a := H.comm_of_orb2A (IsConj.refl a) hbm.1
  have hyb_comm : y * b = b * y := H.comm_of_orb2A hy.1 hbm.2
  have hyb' : y ∈ orb2A b b := (gamma_orb2A_eq hbA b).symm ▸ hyb
  have hXZ : Gxy a y ≤ Gxy b y := by
    intro g hg
    rw [mem_Gxy] at hg ⊢
    obtain ⟨hga, hgy⟩ := hg
    have hga' : Commute a g := mem_Gx.mp hga
    have hgy' : Commute y g := mem_Gx.mp hgy
    refine ⟨?_, hgy⟩
    rw [mem_Gx, hb]
    exact ((hga'.mul_left hgy').pow_left 2).eq
  have hS6a : IsShapeZ2TimesSym 6 ↥(Gxy a y) := (H.hT5.self).shape_4B y hy
  have hcard_a : Nat.card ↥(Gxy a y) = 1440 := by
    have hmem : y ∈ tab5Set a z 3 := by simpa [tab5Set] using hy
    rw [Gxy_eq_inf]
    simpa using (H.hT5.self).card_stab 3 y hmem
  have hcard_b : Nat.card ↥(Gxy b y) = 80640 := by
    have hmem : y ∈ tab5Set b z 0 := by simpa [tab5Set] using hyb'
    rw [Gxy_eq_inf]
    simpa using (H.hT5 b z hbA (IsConj.refl z)).card_stab 0 y hmem
  have hY : Gxyz b y t ≤ Gxy b y := by
    rw [Gxyz_eq_inf]
    exact inf_le_left
  rcases gamma_rows H hbA hyb ht with hcomm | ⟨-, hS6'⟩ | ⟨-, hcard64⟩ | ⟨c, hc, hc3, hle⟩
  · exact ⟨b, H.orderOf_a hbA, mem_Gxyz.mpr
      ⟨mem_Gx.mpr hab, mem_Gx.mpr hyb_comm, mem_Gx.mpr hcomm⟩⟩
  · obtain ⟨s, hs, hso⟩ :=
      gamma_seg27_S6_S6 (L := Gxy a y) (L' := Gxyz b y t) H hbA hyb hXZ hS6a hY hS6'
    exact ⟨s, hso, gamma_inf_Gxy_Gxyz_le_Gxyz a b y t hs⟩
  · have hlt : Nat.card ↥(Gxy b y) <
        Nat.card ↥(Gxy a y) * Nat.card ↥(Gxyz b y t) := by
      rw [hcard_b, hcard_a, hcard64]
      norm_num
    have hk : Nat.gcd (Nat.card ↥(Gxy a y)) (Nat.card ↥(Gxyz b y t)) ∣ 2 ^ 5 := by
      rw [hcard_a, hcard64]
      norm_num
    obtain ⟨s, hs, hso⟩ :=
      gamma_exists_inv_of_card_lt (X := Gxy a y) (Y := Gxyz b y t) (Z := Gxy b y)
        hXZ hY hlt (k := 5) hk
    exact ⟨s, hso, gamma_inf_Gxy_Gxyz_le_Gxyz a b y t hs⟩
  · obtain ⟨s, hs, hso⟩ :=
      gamma_seg27_S5b_S6 (L := Gxy a y) H hbA hyb hc hc3 hXZ hS6a
    exact ⟨s, hso, gamma_inf_Gxy_Gxyz_le_Gxyz a b y t ⟨hs.2, hle hs.1⟩⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
