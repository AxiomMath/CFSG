module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupJ1Max
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupTransfer
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupConj
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.OvergroupDefs
public import CFSG.Sporadic.Bridge.J1
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupA5

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupJ1

open CFSG.Sporadic.J1 CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupTransfer


theorem N_isSolvable : Group.IsSolvable N := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hHN : H ≤ N := Subgroup.le_normalizer
  let H' : Subgroup N := H.subgroupOf N
  haveI : H'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hHN).2 le_rfl
  have hH'card : Nat.card H' = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHN).toEquiv, H, Nat.card_zpowers, orderOf_b]
  have hq : Nat.card (N ⧸ H') = 20 := by
    have := H'.card_eq_card_quotient_mul_card_subgroup
    rw [card_N.1, hH'card] at this
    omega
  have hQ : Group.IsSolvable (N ⧸ H') :=
    OvergroupA5.isSolvable_of_card_eq_pow_mul_pow (p := 2) (q := 5) (a := 2) (b := 1)
      Nat.prime_two Nat.prime_five (by norm_num) (by rw [hq]; norm_num)
  have hcyc : IsCyclic H' := isCyclic_of_prime_card hH'card
  have hH'solv : Group.IsSolvable H' :=
    Group.isSolvable_of_comm fun x y => IsMulCommutative.is_comm.comm x y
  exact Group.isSolvable_of_ker_le_range H'.subtype (QuotientGroup.mk' H')
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem eqTop_normalizer (W : Subgroup J) (hNW : N ≤ W) (hW : ¬ CFSG.HallHigman.IsPSolvable 3 W) :
    W = ⊤ := by
  rcases eq_or_eq_top hNW with h | h
  · exfalso
    apply hW
    rw [h]
    exact OvergroupA5.isPSolvable_of_isSolvable Nat.prime_three N_isSolvable
  · exact h

theorem overgroupEqTop_J : OvergroupEqTop J := by
  intro hcyc A W hA hNW hW
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hHcard : Nat.card H = 3 := by rw [H, Nat.card_zpowers, orderOf_b]
  obtain ⟨g, hg⟩ := OvergroupConj.exists_conj_eq_of_card_three hcyc hHcard hA
  exact eqTop_of_map_eq (MulAut.conj g) hg hNW hW fun W' hN' hW' => eqTop_normalizer W' hN' hW'

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupJ1

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811

open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

theorem kFactOvergroupJ1 :
    KFactOvergroupJ1 := by
  intro K _ _ ⟨e⟩ _ hcyc A W hA hNW hW _
  obtain ⟨c⟩ := CFSG.Sporadic.Bridge.J1.nonempty_mulEquiv
  have eJ : K ≃* CFSG.Sporadic.J1.J := (e.trans c.symm).trans CFSG.Sporadic.J1.nativeEquiv
  have htop := OvergroupTransfer.overgroupEqTop_of_mulEquiv eJ OvergroupJ1.overgroupEqTop_J
    hcyc A W hA hNW hW
  rw [htop, Subgroup.index_top]
  exact odd_one

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811
