module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co1Native
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2Engine
public import Certificates.Certificate1037002

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.Sporadic.Co1Patterson CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier CFSG.Blueprint
  CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

theorem co1_heisCfg_of_emb {s : NativeSporadic.Co1} {X Y : GL24}
    (hX : X ∈ GA) (hY : Y ∈ GA) (hX5 : X ^ 5 = 1) (hY5 : Y ^ 5 = 1)
    (hW5 : (X⁻¹ * Y⁻¹ * X * Y) ^ 5 = 1) (hW1 : X⁻¹ * Y⁻¹ * X * Y ≠ 1)
    (hXW : X * (X⁻¹ * Y⁻¹ * X * Y) = X⁻¹ * Y⁻¹ * X * Y * X)
    (hYW : Y * (X⁻¹ * Y⁻¹ * X * Y) = X⁻¹ * Y⁻¹ * X * Y * Y)
    (hs : nativeEmb s * X * (nativeEmb s)⁻¹ = X⁻¹) :
    ∃ (x y : Fin (0 + 1) → NativeSporadic.Co1) (w : NativeSporadic.Co1),
      HeisCfg 5 (0 + 1) x y w ∧ (∀ i, y i ^ 5 = 1) ∧ s * x 0 * s⁻¹ = (x 0)⁻¹ := by
  obtain ⟨x, hxe⟩ := exists_nativeEmb_eq hX
  obtain ⟨y, hye⟩ := exists_nativeEmb_eq hY
  have hz : nativeEmb (x⁻¹ * y⁻¹ * x * y) = X⁻¹ * Y⁻¹ * X * Y := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hxe, hye]
  have hxp : x ^ 5 = 1 := emb_pow (by rw [hxe]; exact hX5)
  have hyp : y ^ 5 = 1 := emb_pow (by rw [hye]; exact hY5)
  have hzp : (x⁻¹ * y⁻¹ * x * y) ^ 5 = 1 := emb_pow (by rw [hz]; exact hW5)
  have hzx : x * (x⁻¹ * y⁻¹ * x * y) = (x⁻¹ * y⁻¹ * x * y) * x :=
    emb_comm_eq (by rw [hz, hxe]; exact hXW)
  have hzy : y * (x⁻¹ * y⁻¹ * x * y) = (x⁻¹ * y⁻¹ * x * y) * y :=
    emb_comm_eq (by rw [hz, hye]; exact hYW)
  have hz1 : x⁻¹ * y⁻¹ * x * y ≠ 1 := emb_ne (by rw [hz, map_one]; exact hW1)
  refine ⟨fun _ => x, fun _ => y, x⁻¹ * y⁻¹ * x * y, ?_, fun _ => hyp, ?_⟩
  · exact
    { xp := fun _ => hxp
      zp := hzp
      zx := fun _ => hzx
      zy := fun _ => hzy
      yx := fun _ => heis_yx x y
      xx := fun _ _ => rfl
      yy := fun i j hij => absurd (Fin.eq_of_val_eq (by have := i.2; have := j.2; omega)) hij
      xy := fun i j hij => absurd (Fin.eq_of_val_eq (by have := i.2; have := j.2; omega)) hij
      z1 := hz1 }
  · show s * x * s⁻¹ = x⁻¹
    refine emb_conj_eq ?_
    rw [map_inv, hxe]
    exact hs

theorem co1_heisCfg_of_heisInvCheck {s : NativeSporadic.Co1}
    {rt rx ry : Native.Rows} {X Y : GL24} (ht : MRep rt (nativeEmb s)) (hX : MRep rx X)
    (hY : MRep ry Y) (hXG : X ∈ GA) (hYG : Y ∈ GA) (h : heisInvCheck rt rx ry = true) :
    ∃ (x y : Fin (0 + 1) → NativeSporadic.Co1) (w : NativeSporadic.Co1),
      HeisCfg 5 (0 + 1) x y w ∧ (∀ i, y i ^ 5 = 1) ∧ s * x 0 * s⁻¹ = (x 0)⁻¹ := by
  unfold heisInvCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hXi, hYi⟩, hX5⟩, hY5⟩, hW5⟩, hW1⟩, hvW⟩, hXW⟩, hYW⟩, htt⟩, htX⟩ := h
  have hXi' : MRep (Native.inv rx) X⁻¹ := hX.inv hXi
  have hYi' : MRep (Native.inv ry) Y⁻¹ := hY.inv hYi
  have hW : MRep (Native.mul (Native.mul (Native.mul (Native.inv rx) (Native.inv ry)) rx) ry)
      (X⁻¹ * Y⁻¹ * X * Y) := ((hXi'.mul hYi').mul hX).mul hY
  have hX5' : X ^ 5 = 1 := (hX.pow 5).eq (hX5 ▸ MRep.one)
  have hY5' : Y ^ 5 = 1 := (hY.pow 5).eq (hY5 ▸ MRep.one)
  have hW5' : (X⁻¹ * Y⁻¹ * X * Y) ^ 5 = 1 := (hW.pow 5).eq (hW5 ▸ MRep.one)
  have hW1' : X⁻¹ * Y⁻¹ * X * Y ≠ 1 := by
    intro h1
    apply hW1
    rw [h1] at hW
    exact CFSG.Sporadic.Co1.Module.rowsMatrix_injective_of_valid hvW validRows_one
      (hW.trans MRep.one.symm)
  have hXW' : X * (X⁻¹ * Y⁻¹ * X * Y) = X⁻¹ * Y⁻¹ * X * Y * X :=
    (hX.mul hW).eq (hXW ▸ hW.mul hX)
  have hYW' : Y * (X⁻¹ * Y⁻¹ * X * Y) = X⁻¹ * Y⁻¹ * X * Y * Y :=
    (hY.mul hW).eq (hYW ▸ hW.mul hY)
  have htt' : nativeEmb s * nativeEmb s = 1 := (ht.mul ht).eq (htt ▸ MRep.one)
  have htX' : nativeEmb s * X * nativeEmb s = X⁻¹ := ((ht.mul hX).mul ht).eq (htX ▸ hXi')
  have hti : (nativeEmb s)⁻¹ = nativeEmb s := inv_eq_of_mul_eq_one_right htt'
  exact co1_heisCfg_of_emb hXG hYG hX5' hY5' hW5' hW1' hXW' hYW'
    ((congrArg (nativeEmb s * X * ·) hti).trans htX')

theorem heisBC_Y :
    (∃ (x y : Fin (0 + 1) → NativeSporadic.Co1) (w : NativeSporadic.Co1),
      HeisCfg 5 (0 + 1) x y w ∧ (∀ i, y i ^ 5 = 1) ∧ bNC * x 0 * bNC⁻¹ = (x 0)⁻¹) ∧
    (∃ (x y : Fin (0 + 1) → NativeSporadic.Co1) (w : NativeSporadic.Co1),
      HeisCfg 5 (0 + 1) x y w ∧ (∀ i, y i ^ 5 = 1) ∧ cNC * x 0 * cNC⁻¹ = (x 0)⁻¹) := by
  have hc := Certificates.certificate1037002
  unfold dispBCCheck at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hD, hB⟩, hC⟩ := hc
  have hbase : List.Forall₂ MRep [Native.aR, Native.bR, iotaARows] [A₁, A₂, (iotaA : GL24)] :=
    .cons rep_A₁ (.cons rep_A₂ (.cons rep_iotaA .nil))
  have hdag := dag_rep hbase (dispHeis ++ dispBC) hD
  have hmem := dagG_mem (H := GA) (derivs := dispHeis ++ dispBC)
    (base := [A₁, A₂, (iotaA : GL24)]) (fun g hg => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with h | h | h <;> rw [h]
      exacts [A₁_mem, A₂_mem, iotaA_mem_GA])
  have htB : MRep Native.aR (nativeEmb bNC) := by rw [nativeEmb_bNC]; exact rep_A₁
  have htC : MRep iotaCRows (nativeEmb cNC) := by rw [nativeEmb_cNC]; exact rep_iotaC
  exact ⟨co1_heisCfg_of_heisInvCheck htB (getD_rep hdag MRep.one (dispIXB - 1))
      (getD_rep hdag MRep.one (dispIYB - 1)) (getD_mem_of_forall hmem _)
      (getD_mem_of_forall hmem _) hB,
    co1_heisCfg_of_heisInvCheck htC (getD_rep hdag MRep.one (dispIXC - 1))
      (getD_rep hdag MRep.one (dispIYC - 1)) (getD_mem_of_forall hmem _)
      (getD_mem_of_forall hmem _) hC⟩

theorem co1_heis_inv
    (t : NativeSporadic.Co1) (ht : orderOf t = 2) :
    ∃ (x y : Fin (0 + 1) → NativeSporadic.Co1) (w : NativeSporadic.Co1),
      HeisCfg 5 (0 + 1) x y w ∧ (∀ i, y i ^ 5 = 1) ∧ t * x 0 * t⁻¹ = (x 0)⁻¹ := by
  obtain ⟨hB, hC⟩ := heisBC_Y
  have hA : ∃ (x y : Fin (0 + 1) → NativeSporadic.Co1) (w : NativeSporadic.Co1),
      HeisCfg 5 (0 + 1) x y w ∧ (∀ i, y i ^ 5 = 1) ∧ aNC * x 0 * aNC⁻¹ = (x 0)⁻¹ := by
    obtain ⟨X, Y, hX, hY, hX5, hY5, hW5, hW1, hXW, hYW, haX⟩ := heis_facts
    exact co1_heisCfg_of_emb hX hY hX5 hY5 hW5 hW1 hXW hYW (by rw [nativeEmb_aNC]; exact haX)
  rcases Y_classes t ht with h | h | h
  · exact Co2Engine.heis_conj h.symm hA
  · exact Co2Engine.heis_conj h.symm hC
  · exact Co2Engine.heis_conj h.symm hB

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
