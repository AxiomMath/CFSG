module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.Arrange

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'} {α : G → G'}

theorem const_self (F : Fam a α) {t t' : G} (ht : t ∈ InvIn (Gxy a a))
    (ht' : t' ∈ InvIn (Gxy a a)) : F.app t a = F.app t' a := by
  have htGx : t ∈ InvIn (Gx a) := ⟨(mem_Gxy.1 ht.1).1, ht.2⟩
  have ht'Gx : t' ∈ InvIn (Gx a) := ⟨(mem_Gxy.1 ht'.1).1, ht'.2⟩
  have hat : a ∈ Gxy a t :=
    mem_Gxy.2 ⟨self_mem_Gx a, mem_Gx.2 (mem_Gx.1 (mem_Gxy.1 ht.1).1).symm⟩
  have hat' : a ∈ Gxy a t' :=
    mem_Gxy.2 ⟨self_mem_Gx a, mem_Gx.2 (mem_Gx.1 (mem_Gxy.1 ht'.1).1).symm⟩
  rw [F.restrict t htGx a hat, F.restrict t' ht'Gx a hat']

theorem const_2A_2B (h : F5Std a z) (F : Fam a α) {x : G}
    (hx : x ∈ orb2A a a ∨ x ∈ orb2B a z a) {t t' : G} (ht : t ∈ InvIn (Gxy a x))
    (ht' : t' ∈ InvIn (Gxy a x)) : F.app t x = F.app t' x := by
  have hxa : x ∈ Gx a := by
    rcases hx with hx | hx
    · exact h.mem_Gx_of_orb2A (IsConj.refl a) hx
    · exact h.mem_Gx_of_orb2B (IsConj.refl a) hx
  have htGx : t ∈ InvIn (Gx a) := ⟨(mem_Gxy.1 ht.1).1, ht.2⟩
  have ht'Gx : t' ∈ InvIn (Gx a) := ⟨(mem_Gxy.1 ht'.1).1, ht'.2⟩
  have hxt : x ∈ Gxy a t :=
    mem_Gxy.2 ⟨hxa, mem_Gx.2 (mem_Gx.1 (mem_Gxy.1 ht.1).2).symm⟩
  have hxt' : x ∈ Gxy a t' :=
    mem_Gxy.2 ⟨hxa, mem_Gx.2 (mem_Gx.1 (mem_Gxy.1 ht'.1).2).symm⟩
  rw [F.restrict t htGx x hxt, F.restrict t' ht'Gx x hxt']

theorem const_6A (h : F5Std a z) (F : Fam a α) (hF : Arranged a F) {x : G} (hx : x ∈ orb6A a a)
    {t t' : G} (ht : t ∈ InvIn (Gxy a x)) (ht' : t' ∈ InvIn (Gxy a x)) :
    F.app t x = F.app t' x := by
  let b : G := (a * x) ^ 3
  have hbA : IsConj a b := hx.2.2
  obtain ⟨hbInv, -⟩ := cp_central_inv h hx.1 (k := 3) (Or.inl hbA)
  have hb2 : b * b = 1 := by
    rw [← pow_two, ← hbInv.2]
    exact pow_orderOf_eq_one b
  have hbGxa : b ∈ Gx a := (mem_Gxy.1 hbInv.1).1
  have hbx3 : b * x ∈ orb3A a a :=
    cp_orb6A_cube_mul_mem h hx
  have htGxa : t ∈ Gx a := (mem_Gxy.1 ht.1).1
  have htx : t ∈ Gx x := (mem_Gxy.1 ht.1).2
  have hcomm_ta : Commute t a := (mem_Gx.1 htGxa).symm
  have hcomm_tx : Commute t x := (mem_Gx.1 htx).symm
  have hcomm_tb : Commute t b := (hcomm_ta.mul_right hcomm_tx).pow_right 3
  have hbGxt : b ∈ Gx t := mem_Gx.2 hcomm_tb.eq
  have hbxGxt : b * x ∈ Gx t := mem_Gx.2 (hcomm_tb.mul_right hcomm_tx).eq
  have hbGxyat : b ∈ Gxy a t := mem_Gxy.2 ⟨hbGxa, hbGxt⟩
  have ht_inv_bx : t ∈ InvIn (Gxy a (b * x)) := by
    refine ⟨mem_Gxy.2 ⟨htGxa, ?_⟩, ht.2⟩
    exact mem_Gx.2 (hcomm_tb.mul_right hcomm_tx).symm.eq
  have ht'Gxa : t' ∈ Gx a := (mem_Gxy.1 ht'.1).1
  have ht'x : t' ∈ Gx x := (mem_Gxy.1 ht'.1).2
  have hcomm_t'a : Commute t' a := (mem_Gx.1 ht'Gxa).symm
  have hcomm_t'x : Commute t' x := (mem_Gx.1 ht'x).symm
  have hcomm_t'b : Commute t' b := (hcomm_t'a.mul_right hcomm_t'x).pow_right 3
  have hbGxt' : b ∈ Gx t' := mem_Gx.2 hcomm_t'b.eq
  have hbxGxt' : b * x ∈ Gx t' := mem_Gx.2 (hcomm_t'b.mul_right hcomm_t'x).eq
  have hbGxyat' : b ∈ Gxy a t' := mem_Gxy.2 ⟨hbGxa, hbGxt'⟩
  have ht'_inv_bx : t' ∈ InvIn (Gxy a (b * x)) := by
    refine ⟨mem_Gxy.2 ⟨ht'Gxa, ?_⟩, ht'.2⟩
    exact mem_Gx.2 (hcomm_t'b.mul_right hcomm_t'x).symm.eq
  have hrestb : F.app t b = α b := F.restrict t ⟨htGxa, ht.2⟩ b hbGxyat
  have hrestb' : F.app t' b = α b := F.restrict t' ⟨ht'Gxa, ht'.2⟩ b hbGxyat'
  have harr : F.app t (b * x) = F.app t' (b * x) :=
    hF (b * x) (Or.inl hbx3) t ht_inv_bx t' ht'_inv_bx
  have hmul_t : F.app t x = F.app t b * F.app t (b * x) := by
    have hxeq : b * (b * x) = x := by rw [← mul_assoc, hb2, one_mul]
    calc F.app t x = F.app t (b * (b * x)) := by rw [hxeq]
      _ = F.app t b * F.app t (b * x) :=
        (F.iso t ⟨htGxa, ht.2⟩).map_mul b hbGxt (b * x) hbxGxt
  have hmul_t' : F.app t' x = F.app t' b * F.app t' (b * x) := by
    have hxeq : b * (b * x) = x := by rw [← mul_assoc, hb2, one_mul]
    calc F.app t' x = F.app t' (b * (b * x)) := by rw [hxeq]
      _ = F.app t' b * F.app t' (b * x) :=
        (F.iso t' ⟨ht'Gxa, ht'.2⟩).map_mul b hbGxt' (b * x) hbxGxt'
  rw [hmul_t, hmul_t', hrestb, hrestb', harr]

end CFSG.EvenSporadicStandard.HNRecog.Section4
