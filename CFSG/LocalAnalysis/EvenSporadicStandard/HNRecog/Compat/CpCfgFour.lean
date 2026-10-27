module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVProof.TableVBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpDihedral

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G : Type} [Group G] {a z : G}

private theorem commute_pow_of_mem_Gxy {x y c : G} (hc : c ∈ Gxy x y) (k : ℕ) :
    Commute c ((x * y) ^ k) := by
  have hx : Commute c x := (mem_Gx.1 (mem_Gxy.1 hc).1).symm
  have hy : Commute c y := (mem_Gx.1 (mem_Gxy.1 hc).2).symm
  exact (hx.mul_right hy).pow_right k

theorem cp_four_pair_B (h : F5Std a z) :
    ∃ t t' x : G, t ∈ orb2A a a ∧ t' ∈ orb2A a a ∧ t * t' ∈ orb2AB a z a ∧ x ∈ orb4B a a ∧
      x ∈ Gxy t t' := by
  obtain ⟨x, hx⟩ := (h.loc.tableV.self.partition.orbit 3).nonempty
  have hx4B : x ∈ orb4B a a := hx
  have hb : (a * x) ^ 2 ∈ orb2A a a := (tableV_orb4B_row h.typ hx4B).1
  have hbInv : (a * x) ^ 2 ∈ InvIn (Gxy a x) :=
    (cp_central_inv h hx4B.1 (k := 2) (Or.inl hx4B.2)).1
  have hb2 : (a * x) ^ 2 * (a * x) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one ((a * x) ^ 2)
    rw [hbInv.2] at h
    simpa [pow_two] using h
  have hbGxx : (a * x) ^ 2 ∈ Gx x := (mem_Gxy.1 hbInv.1).2
  have hfb := h.loc.fourB.self
  have hcl := hfb.classes x hx4B
  obtain ⟨w, hw⟩ := (hcl.orbit 4).nonempty
  have hw4 : w ∈ orb2AB a z a ∩ orb2BB a z x := hw
  have hwG : w ∈ Gxy a x := (hcl.subset 4 hw).1
  have hcomm_wb : Commute w ((a * x) ^ 2) := commute_pow_of_mem_Gxy hwG 2
  have hbw : (a * x) ^ 2 * w = w * (a * x) ^ 2 := hcomm_wb.eq.symm
  have hcase : w * (a * x) ^ 2 ∈ orb2A a a := (hfb.case_ii x hx4B w hw4).1.1
  have hprod : (a * x) ^ 2 * (w * (a * x) ^ 2) = w := by
    calc (a * x) ^ 2 * (w * (a * x) ^ 2)
        = ((a * x) ^ 2 * w) * (a * x) ^ 2 := by rw [← mul_assoc]
      _ = (w * (a * x) ^ 2) * (a * x) ^ 2 := by rw [hbw]
      _ = w * ((a * x) ^ 2 * (a * x) ^ 2) := by rw [mul_assoc]
      _ = w * 1 := by rw [hb2]
      _ = w := mul_one w
  have hbx_comm : Commute ((a * x) ^ 2) x := (mem_Gx.1 hbGxx).symm
  have hwx_comm : Commute w x := (mem_Gx.1 (mem_Gxy.1 hwG).2).symm
  have hxGxy : x ∈ Gxy ((a * x) ^ 2) (w * (a * x) ^ 2) :=
    mem_Gxy.2 ⟨mem_Gx.2 hbx_comm, mem_Gx.2 (hwx_comm.mul_left hbx_comm)⟩
  exact ⟨(a * x) ^ 2, w * (a * x) ^ 2, x, hb, hcase, by simpa [hprod] using hw4.1,
    hx4B, hxGxy⟩

theorem cp_four_pair_A (h : F5Std a z) :
    ∃ t t' y : G, t ∈ orb2A a a ∧ t' ∈ orb2A a a ∧ t * t' ∈ orb2AB a z a ∧ y ∈ orb4A a z a ∧
      y ∈ Gxy t t' ∧ t ∈ orb2A a y ∧ t' ∈ orb2A a y ∧ t * t' = (a * y) ^ 2 := by
  obtain ⟨b₀, hb₀⟩ := (h.loc.tableV.self.partition.orbit 0).nonempty
  have hb₀A : b₀ ∈ orb2A a a := hb₀
  obtain ⟨y, hy⟩ := ((h.loc.tableIV.self.partition b₀ hb₀A).orbit 3).nonempty
  have hy3 : y ∈ sBase a b₀ ∧ IsConj z ((a * y) ^ 2) := hy
  obtain ⟨hyA, hyb, -, -⟩ := hy3.1
  have hy4A : y ∈ orb4A a z a := ⟨hyA, hy3.2⟩
  have hcomm : b₀ * y = y * b₀ :=
    h.mul_comm (Or.inl hb₀A.1) (Or.inl hyA) (Or.inl hyb)
  have hb₀y : b₀ ∈ orb2A a y := ⟨hb₀A.1, by rw [← hcomm]; exact hyb⟩
  have hb₀Gxa : b₀ ∈ Gx a := h.mem_Gx_of_orb2A (IsConj.refl a) hb₀A
  have hb₀Gy : b₀ ∈ Gx y := mem_Gx.2 hcomm.symm
  have hb₀2 : b₀ * b₀ = 1 := by
    rw [← pow_two, ← h.orderOf_eq_two (Or.inl hb₀A.1)]
    exact pow_orderOf_eq_one b₀
  have hz1Inv : (a * y) ^ 2 ∈ InvIn (Gxy a y) :=
    (cp_central_inv h hyA (k := 2) (Or.inr hy3.2)).1
  have hz1Gy : (a * y) ^ 2 ∈ Gx y := (mem_Gxy.1 hz1Inv.1).2
  have hyz1 : y * (a * y) ^ 2 = (a * y) ^ 2 * y := mem_Gx.1 hz1Gy
  have hz1y_comm : Commute ((a * y) ^ 2) y := hyz1.symm
  have hb₀Gxy_ay : b₀ ∈ Gxy a y := mem_Gxy.2 ⟨hb₀Gxa, hb₀Gy⟩
  have hb₀z1 : Commute b₀ ((a * y) ^ 2) := commute_pow_of_mem_Gxy hb₀Gxy_ay 2
  have hb₀y_comm : Commute b₀ y := (mem_Gx.1 hb₀Gy).symm
  have hfig := h.loc.lines.self.fig14_a y hy4A b₀ ⟨hb₀A, hb₀y⟩
  have hta' : a * ((a * y) ^ 2 * b₀) = a * b₀ * (a * y) ^ 2 := by
    rw [hb₀z1.eq.symm, mul_assoc]
  have hty' : y * ((a * y) ^ 2 * b₀) = (a * y) ^ 2 * y * b₀ := by
    rw [← mul_assoc, hyz1, mul_assoc]
  have ht' : (a * y) ^ 2 * b₀ ∈ orb2A a a :=
    ⟨hfig.1, by rw [hta']; exact hfig.2.2.2.2⟩
  have ht'y : (a * y) ^ 2 * b₀ ∈ orb2A a y :=
    ⟨hfig.1, by rw [hty']; exact hfig.2.2.1⟩
  have hprod : b₀ * ((a * y) ^ 2 * b₀) = (a * y) ^ 2 := by
    calc b₀ * ((a * y) ^ 2 * b₀)
        = (b₀ * (a * y) ^ 2) * b₀ := by rw [← mul_assoc]
      _ = ((a * y) ^ 2 * b₀) * b₀ := by rw [hb₀z1.eq]
      _ = (a * y) ^ 2 * (b₀ * b₀) := by rw [mul_assoc]
      _ = (a * y) ^ 2 * 1 := by rw [hb₀2]
      _ = (a * y) ^ 2 := mul_one _
  have htprod : b₀ * ((a * y) ^ 2 * b₀) ∈ orb2AB a z a := by
    rw [hprod]
    exact ⟨hy3.2, hfig.2.2.2.1⟩
  have hyGxy : y ∈ Gxy b₀ ((a * y) ^ 2 * b₀) :=
    mem_Gxy.2 ⟨mem_Gx.2 hcomm, mem_Gx.2 (hz1y_comm.mul_left hb₀y_comm)⟩
  exact ⟨b₀, (a * y) ^ 2 * b₀, y, hb₀A, ht', htprod, hy4A, hyGxy, hb₀y, ht'y, hprod⟩

end CFSG.EvenSporadicStandard.HNRecog.Section4
