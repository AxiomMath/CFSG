module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTStmt
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M22
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.Schreier.J1Outer
public import CFSG.Sporadic.Schreier.PairJ2Pairs
public import CFSG.Sporadic.Schreier.PairJ3Pairs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

namespace OutS

theorem OutTwoNilp.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : OutTwoNilp Y') : OutTwoNilp Y := by
  obtain ⟨O, hOn, hIO, hodd, h2⟩ := h
  refine ⟨O.comap (MulAut.congr e).toMonoidHom, Subgroup.Normal.comap hOn _, ?_, ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩
    rw [mem_comap, MulEquiv.coe_toMonoidHom, congr_conj]
    exact hIO ⟨e y, rfl⟩
  · intro w hw
    obtain ⟨m, hm, y', hy'⟩ := hodd _ hw
    refine ⟨m, hm, e.symm y', (MulAut.congr e).injective ?_⟩
    rw [congr_conj, MulEquiv.apply_symm_apply, hy', MulEquiv.coe_toMonoidHom, map_pow]
  · intro y
    obtain ⟨n, hn⟩ := h2 (MulAut.congr e y)
    exact ⟨n, by rw [mem_comap, MulEquiv.coe_toMonoidHom, map_pow]; exact hn⟩

theorem outTwoNilp_of_card_outer_dvd {Y : Type} [Group Y] {k : ℕ}
    (h : Nat.card (Outer Y) ∣ 2 ^ k) : OutTwoNilp Y := by
  refine ⟨inner Y, inferInstance, le_rfl, fun w hw => ⟨1, odd_one, by rw [pow_one]; exact hw⟩,
    fun y => ⟨k, ?_⟩⟩
  have h1 : ((y : Outer Y)) ^ 2 ^ k = 1 := by
    obtain ⟨c, hc⟩ := h
    rw [hc, pow_mul, pow_card_eq_one', one_pow]
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem outTwoNilp_of_odd_card_outer {Y : Type} [Group Y] (h : Odd (Nat.card (Outer Y))) :
    OutTwoNilp Y := by
  refine ⟨⊤, inferInstance, le_top, fun w _ => ⟨Nat.card (Outer Y), h, ?_⟩,
    fun y => ⟨0, by simp⟩⟩
  have h1 : ((w : Outer Y)) ^ Nat.card (Outer Y) = 1 := pow_card_eq_one'
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem finite_outer {Y : Type} [Group Y] [Finite Y] : Finite (Outer Y) := by
  have : Finite (MulAut Y) :=
    Finite.of_injective (fun α : MulAut Y => (α : Y → Y)) DFunLike.coe_injective
  infer_instance

theorem outTwoNilp_of_card_outer_le_six {Y : Type} [Group Y] [Finite Y]
    (h : Nat.card (Outer Y) ≤ 6) : OutTwoNilp Y := by
  have := finite_outer (Y := Y)
  have hpos : 0 < Nat.card (Outer Y) := Nat.card_pos
  interval_cases hc : Nat.card (Outer Y)
  · exact outTwoNilp_of_card_outer_dvd (k := 0) (by rw [hc]; norm_num)
  · exact outTwoNilp_of_card_outer_dvd (k := 1) (by rw [hc]; norm_num)
  · exact outTwoNilp_of_odd_card_outer (by rw [hc]; decide)
  · exact outTwoNilp_of_card_outer_dvd (k := 2) (by rw [hc]; norm_num)
  · exact outTwoNilp_of_odd_card_outer (by rw [hc]; decide)
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Outer Y) 3 (by rw [hc]; norm_num)
    set N : Subgroup (Outer Y) := zpowers x with hN
    have hidx : N.index = 2 := by
      have e := Subgroup.card_mul_index N
      rw [Nat.card_zpowers, hx, hc] at e
      omega
    have hNn : N.Normal := Subgroup.normal_of_index_eq_two hidx
    refine ⟨N.comap (QuotientGroup.mk' (inner Y)), Subgroup.Normal.comap hNn _, ?_, ?_, ?_⟩
    · intro w hw
      rw [mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff (N := inner Y) w).mpr hw]
      exact N.one_mem
    · intro w hw
      refine ⟨3, by decide, ?_⟩
      have h3 : ((w : Outer Y)) ^ 3 = 1 := by
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hw
        rw [show ((w : Outer Y)) = QuotientGroup.mk' (inner Y) w from rfl, ← hj, ← zpow_natCast,
          ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hx, pow_orderOf_eq_one, one_zpow]
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h3
      exact h3
    · intro y
      refine ⟨1, ?_⟩
      rw [mem_comap, pow_one, map_pow]
      exact Subgroup.sq_mem_of_index_two hidx _

theorem outTwoNilp_of_equiv_le_six {Y Z : Type} [Group Y] [Finite Y] [Group Z] (e : Y ≃* Z)
    (h : Nat.card (Outer Z) ≤ 6) : OutTwoNilp Y :=
  outTwoNilp_of_card_outer_le_six (by rw [Nat.card_congr (equivalence e).toEquiv]; exact h)

theorem outTwoNilp_of_isSporadic {Y : Type} [Group Y] [Finite Y] {s : TauCeti.SporadicName}
    (h : NativeSporadic.IsSporadic Y s) (hle : Nat.card (Outer (NativeSporadic.Carrier s)) ≤ 6) :
    OutTwoNilp Y := by
  have h' : Nonempty (Y ≃* NativeSporadic.Carrier s) := h
  obtain ⟨e⟩ := h'
  exact outTwoNilp_of_equiv_le_six e hle

end OutS

open OutS

theorem outCell_alt : OutCell FAlt := by
  rintro Y _ _ - ⟨n, h7, -, ⟨e⟩⟩
  exact outTwoNilp_of_equiv_le_six e (by
    rw [ProperTwoGeneratedCore.BenderFacts.card_outer_alternatingGroup (by omega) (by omega)]
    norm_num)

theorem outCell_spor : OutCell FSpor := by
  intro Y _ _ _ hY
  rcases hY with h | h | h | h | h | h | h
  · exact outTwoNilp_of_isSporadic h (Sporadic.Schreier.at_m11_schreier.1.trans (by norm_num))
  · exact outTwoNilp_of_isSporadic h (Sporadic.Schreier.at_m12_schreier.1.trans (by norm_num))
  · exact outTwoNilp_of_isSporadic h (Sporadic.Schreier.at_m22_schreier.1.trans (by norm_num))
  · exact outTwoNilp_of_isSporadic h (Sporadic.Schreier.at_m23_schreier.1.trans (by norm_num))
  · exact outTwoNilp_of_isSporadic h (by
      change Nat.card (Outer NativeSporadic.J1) ≤ 6
      rw [Sporadic.Schreier.at_j1_schreier.1]
      norm_num)
  · exact outTwoNilp_of_isSporadic h (Sporadic.Schreier.AT_J2_Schreier.1.trans (by norm_num))
  · exact outTwoNilp_of_isSporadic h Sporadic.Schreier.AT_J3_Schreier.1

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
