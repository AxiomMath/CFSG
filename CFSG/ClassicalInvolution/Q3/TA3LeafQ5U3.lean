module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5U3Frame
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L3U3
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L5U5
public import CFSG.ClassicalInvolution.Q3.TA3SmallModels

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution Q5GL2
open CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

theorem smallSimpleLeaf_u3Ne3 : SmallSimpleLeaf SmallU3Ne3 := by
  intro Y _ _ _ _ hnab _ hPF R S t hD hc _
  obtain ⟨p, f, hp, hp2, hf, h3, hm⟩ := hPF
  have : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  have hC : Subgroup.centralizer ((genFittingFStar Y : Subgroup Y) : Set Y) = ⊥ :=
    Nobq.centralizer_genFittingFStar_eq_bot hnab
  have hg : Odd (Nat.gcd 3 (p ^ f + 1)) :=
    (by decide : Odd 3).of_dvd_nat (Nat.gcd_dvd_left 3 _)
  obtain ⟨htN, s, hsR, hsN, hs4⟩ :=
    TightDatum.exists_cyclic4_of_outTwoCyclic hD hC (outTwoCyclic_PSU hm hg)
  obtain ⟨⟨hℓ, hm1, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have h : UnitaryFieldData p f K := ⟨hℓ, hm1, by rw [hK, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := h.charP
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have h5 : 5 ≤ p ^ f := by
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hle : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    obtain ⟨k, hk⟩ := hodd
    omega
  have hq := LieType.Steinberg.card_fixedSubfield h.card_eq_sq
  obtain ⟨π, hrange, hk, hπ1⟩ := Q5U3.exists_frame h hp2 e htN hD.order
  obtain ⟨eJ⟩ := Q5U3.nonempty_slPart_equiv h
  exact Or.inl (TightDatum.tightEx_of_gl2 hD hc hrange hk (Q5U3.slCentScalar_GU2 h)
    (N1 := ⟨-1, Q5U3.neg_one_mem_GU2 h⟩) rfl hπ1 (by rw [hq]; exact hodd) (by rw [hq]; omega)
    eJ hsR hsN hs4)

end CFSG.ClassicalInvolution.Q3.TA3
