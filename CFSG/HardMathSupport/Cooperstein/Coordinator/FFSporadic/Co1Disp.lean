module

public import CFSG.Sporadic.Co1Block.Co1Equiv
public import Certificates.Certificate129071
public import CFSG.Sporadic.Co1.Module.InvSpec

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier

theorem heis_facts :
    ∃ X Y : GL24, X ∈ GA ∧ Y ∈ GA ∧ X ^ 5 = 1 ∧ Y ^ 5 = 1 ∧
      (X⁻¹ * Y⁻¹ * X * Y) ^ 5 = 1 ∧ X⁻¹ * Y⁻¹ * X * Y ≠ 1 ∧
      X * (X⁻¹ * Y⁻¹ * X * Y) = (X⁻¹ * Y⁻¹ * X * Y) * X ∧
      Y * (X⁻¹ * Y⁻¹ * X * Y) = (X⁻¹ * Y⁻¹ * X * Y) * Y ∧
      (iotaA : GL24) * X * (iotaA : GL24)⁻¹ = X⁻¹ := by
  have hc := Certificates.certificate129071
  unfold dispCheck at hc
  rw [Bool.and_eq_true] at hc
  have hH := hc.1
  unfold dispHeisCheck at hH
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hH
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hD, hXi⟩, hYi⟩, hX5⟩, hY5⟩, hW5⟩, hW1⟩, hvW⟩, hXW⟩, hYW⟩, haa⟩, haX⟩ := hH
  have ha : MRep iotaARows (iotaA : GL24) := rep_iotaA
  have hbase : List.Forall₂ MRep [Native.aR, Native.bR, iotaARows] [A₁, A₂, (iotaA : GL24)] :=
    .cons rep_A₁ (.cons rep_A₂ (.cons ha .nil))
  have hdag := dag_rep hbase dispHeis hD
  have hmem := dagG_mem (H := GA) (derivs := dispHeis) (base := [A₁, A₂, (iotaA : GL24)])
    (fun g hg => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with h | h | h <;> rw [h]
      exacts [A₁_mem, A₂_mem, iotaA_mem_GA])
  set XG : GL24 := (dagG [A₁, A₂, (iotaA : GL24)] dispHeis).getD (dispIX - 1) 1 with hXG
  set YG : GL24 := (dagG [A₁, A₂, (iotaA : GL24)] dispHeis).getD (dispIY - 1) 1 with hYG
  have hX : MRep ((Native.dag [Native.aR, Native.bR, iotaARows] dispHeis).1.getD (dispIX - 1)
      Native.one) XG := getD_rep hdag MRep.one _
  have hY : MRep ((Native.dag [Native.aR, Native.bR, iotaARows] dispHeis).1.getD (dispIY - 1)
      Native.one) YG := getD_rep hdag MRep.one _
  obtain ⟨rx, hrx⟩ : ∃ r, (Native.dag [Native.aR, Native.bR, iotaARows] dispHeis).1.getD
      (dispIX - 1) Native.one = r := ⟨_, rfl⟩
  obtain ⟨ry, hry⟩ : ∃ r, (Native.dag [Native.aR, Native.bR, iotaARows] dispHeis).1.getD
      (dispIY - 1) Native.one = r := ⟨_, rfl⟩
  rw [hrx] at hX hXi hX5 hW5 hW1 hvW hXW haX hYW
  rw [hry] at hY hYi hY5 hW5 hW1 hvW hXW hYW
  have hXi' : MRep (Native.inv rx) XG⁻¹ := hX.inv hXi
  have hYi' : MRep (Native.inv ry) YG⁻¹ := hY.inv hYi
  have hW : MRep (Native.mul (Native.mul (Native.mul (Native.inv rx) (Native.inv ry)) rx) ry)
      (XG⁻¹ * YG⁻¹ * XG * YG) := ((hXi'.mul hYi').mul hX).mul hY
  have hX5' : XG ^ 5 = 1 := (hX.pow 5).eq (hX5 ▸ MRep.one)
  have hY5' : YG ^ 5 = 1 := (hY.pow 5).eq (hY5 ▸ MRep.one)
  have hW5' : (XG⁻¹ * YG⁻¹ * XG * YG) ^ 5 = 1 := (hW.pow 5).eq (hW5 ▸ MRep.one)
  have hW1' : XG⁻¹ * YG⁻¹ * XG * YG ≠ 1 := by
    intro h
    apply hW1
    rw [h] at hW
    exact CFSG.Sporadic.Co1.Module.rowsMatrix_injective_of_valid hvW validRows_one
      (hW.trans MRep.one.symm)
  have hXW' : XG * (XG⁻¹ * YG⁻¹ * XG * YG) = (XG⁻¹ * YG⁻¹ * XG * YG) * XG :=
    (hX.mul hW).eq (hXW ▸ hW.mul hX)
  have hYW' : YG * (XG⁻¹ * YG⁻¹ * XG * YG) = (XG⁻¹ * YG⁻¹ * XG * YG) * YG :=
    (hY.mul hW).eq (hYW ▸ hW.mul hY)
  have haa' : (iotaA : GL24) * (iotaA : GL24) = 1 := (ha.mul ha).eq (haa ▸ MRep.one)
  have haX' : (iotaA : GL24) * XG * (iotaA : GL24) = XG⁻¹ := ((ha.mul hX).mul ha).eq (haX ▸ hXi')
  refine ⟨XG, YG, getD_mem_of_forall hmem _, getD_mem_of_forall hmem _, hX5', hY5', hW5', hW1',
    hXW', hYW', ?_⟩
  rw [← haX']
  have : (iotaA : GL24)⁻¹ = (iotaA : GL24) := inv_eq_of_mul_eq_one_right haa'
  rw [this]

theorem dih_facts :
    (∃ cc : GL24, cc ∈ GA ∧
      orderOf ((iotaC : GL24) * (cc * (iotaC : GL24) * cc⁻¹)) = 13) ∧
    (∃ ca : GL24, ca ∈ GA ∧ orderOf (A₁ * (ca * A₁ * ca⁻¹)) = 13) := by
  have hc := Certificates.certificate129071
  unfold dispCheck at hc
  rw [Bool.and_eq_true] at hc
  have hH := hc.2
  unfold dispDihCheck at hH
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hH
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hD, hcc⟩, hca⟩, hpC13⟩, hpC1⟩, hvC⟩, hpA13⟩, hpA1⟩, hvA⟩ := hH
  have hC : MRep iotaCRows (iotaC : GL24) := rep_iotaC
  have hbase : List.Forall₂ MRep [Native.aR, Native.bR, iotaCRows] [A₁, A₂, (iotaC : GL24)] :=
    .cons rep_A₁ (.cons rep_A₂ (.cons hC .nil))
  have hdag := dag_rep hbase dispDihD hD
  have hmem := dagG_mem (H := GA) (derivs := dispDihD) (base := [A₁, A₂, (iotaC : GL24)])
    (fun g hg => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with h | h | h <;> rw [h]
      exacts [A₁_mem, A₂_mem, iotaC_mem_GA])
  set cG : GL24 := (dagG [A₁, A₂, (iotaC : GL24)] dispDihD).getD (dispIC - 1) 1 with hcG
  set aG' : GL24 := (dagG [A₁, A₂, (iotaC : GL24)] dispDihD).getD (dispIA1 - 1) 1 with haG'
  have hrc : MRep ((Native.dag [Native.aR, Native.bR, iotaCRows] dispDihD).1.getD (dispIC - 1)
      Native.one) cG := getD_rep hdag MRep.one _
  have hra : MRep ((Native.dag [Native.aR, Native.bR, iotaCRows] dispDihD).1.getD (dispIA1 - 1)
      Native.one) aG' := getD_rep hdag MRep.one _
  obtain ⟨rc, hrcd⟩ : ∃ r, (Native.dag [Native.aR, Native.bR, iotaCRows] dispDihD).1.getD
      (dispIC - 1) Native.one = r := ⟨_, rfl⟩
  obtain ⟨ra, hrad⟩ : ∃ r, (Native.dag [Native.aR, Native.bR, iotaCRows] dispDihD).1.getD
      (dispIA1 - 1) Native.one = r := ⟨_, rfl⟩
  rw [hrcd] at hrc hcc hpC13 hpC1 hvC
  rw [hrad] at hra hca hpA13 hpA1 hvA
  have hci : MRep (Native.inv rc) cG⁻¹ := hrc.inv hcc
  have hai : MRep (Native.inv ra) aG'⁻¹ := hra.inv hca
  have hpC : MRep (Native.mul iotaCRows (Native.mul rc (Native.mul iotaCRows (Native.inv rc))))
      ((iotaC : GL24) * (cG * ((iotaC : GL24) * cG⁻¹))) := hC.mul (hrc.mul (hC.mul hci))
  have hpA : MRep (Native.mul Native.aR (Native.mul ra (Native.mul Native.aR (Native.inv ra))))
      (A₁ * (aG' * (A₁ * aG'⁻¹))) := rep_A₁.mul (hra.mul (rep_A₁.mul hai))
  have hpC13' : ((iotaC : GL24) * (cG * ((iotaC : GL24) * cG⁻¹))) ^ 13 = 1 :=
    (hpC.pow 13).eq (hpC13 ▸ MRep.one)
  have hpA13' : (A₁ * (aG' * (A₁ * aG'⁻¹))) ^ 13 = 1 := (hpA.pow 13).eq (hpA13 ▸ MRep.one)
  have hpC1' : (iotaC : GL24) * (cG * ((iotaC : GL24) * cG⁻¹)) ≠ 1 := by
    intro h
    apply hpC1
    rw [h] at hpC
    exact CFSG.Sporadic.Co1.Module.rowsMatrix_injective_of_valid hvC validRows_one
      (hpC.trans MRep.one.symm)
  have hpA1' : A₁ * (aG' * (A₁ * aG'⁻¹)) ≠ 1 := by
    intro h
    apply hpA1
    rw [h] at hpA
    exact CFSG.Sporadic.Co1.Module.rowsMatrix_injective_of_valid hvA validRows_one
      (hpA.trans MRep.one.symm)
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  refine ⟨⟨cG, getD_mem_of_forall hmem _, ?_⟩, ⟨aG', getD_mem_of_forall hmem _, ?_⟩⟩
  · have := orderOf_eq_prime hpC13' hpC1'
    simpa [mul_assoc] using this
  · have := orderOf_eq_prime hpA13' hpA1'
    simpa [mul_assoc] using this

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
