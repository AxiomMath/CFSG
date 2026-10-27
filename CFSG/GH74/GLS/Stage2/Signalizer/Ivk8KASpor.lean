module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAOdd
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87QuotTools
public import CFSG.Sporadic.Schreier.J1OddCore
public import CFSG.Sporadic.Schreier.J1Outer
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.Schreier.MathieuOddCore
public import CFSG.Sporadic.SmallOddCore.J2
public import CFSG.Sporadic.SmallOddCore.J3Aut

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped commutatorElement

theorem kaAll_of_M11
    {Y : Type} [Group Y] [Finite Y] (hs : IsSimpleGroup Y)
    (hYs : NativeSporadic.IsSporadic Y .M11) {α : MulAut Y} (hα2 : α * α = 1)
    (hα1 : α ≠ 1) : KAAll α := by
  obtain ⟨e⟩ := hYs
  have hc : Nat.card Y = 7920 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Schreier.m11_card
  have hY : OddCoreAut Y := fun X _ _ S _ hS hC t ht => by
    obtain ⟨ψ⟩ := hS
    exact CFSG.Sporadic.Schreier.ctuc_mathieu_almost_simple_involution_centralizer_odd_core_trivial
      S (Or.inl ⟨ψ.trans e⟩) hC t ht
  obtain ⟨hcard, hcomm, -⟩ := CFSG.Sporadic.Schreier.at_m11_schreier
  have hfinC : Finite (NativeSporadic.Carrier .M11) := Finite.of_equiv Y e.toEquiv
  have hOutCyc : KAOutCyc Y :=
    kaOutCyc_of_mulEquiv e.symm (kaOutCyc_of_card_outer_le_four (le_trans hcard (by norm_num)))
  have hOut : OutAbelian Y := outAbelian_of_mulEquiv e.symm (outAbelian_of_outer_comm hcomm)
  exact kaAll_of_oddCore_aut hs (exists_noncomm_of_simple_of_not_prime hs (by rw [hc]; norm_num))
    hY hOutCyc hOut hα2 hα1

theorem kaAll_of_M12
    {Y : Type} [Group Y] [Finite Y] (hs : IsSimpleGroup Y)
    (hYs : NativeSporadic.IsSporadic Y .M12) {α : MulAut Y} (hα2 : α * α = 1)
    (hα1 : α ≠ 1) : KAAll α := by
  obtain ⟨e⟩ := hYs
  have hc : Nat.card Y = 95040 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Schreier.m12_card
  have hY : OddCoreAut Y := fun X _ _ S _ hS hC t ht => by
    obtain ⟨ψ⟩ := hS
    exact CFSG.Sporadic.Schreier.ctuc_mathieu_almost_simple_involution_centralizer_odd_core_trivial
      S (Or.inr (Or.inl ⟨ψ.trans e⟩)) hC t ht
  obtain ⟨hcard, hcomm, -⟩ := CFSG.Sporadic.Schreier.at_m12_schreier
  have hfinC : Finite (NativeSporadic.Carrier .M12) := Finite.of_equiv Y e.toEquiv
  have hOutCyc : KAOutCyc Y :=
    kaOutCyc_of_mulEquiv e.symm (kaOutCyc_of_card_outer_le_four (le_trans hcard (by norm_num)))
  have hOut : OutAbelian Y := outAbelian_of_mulEquiv e.symm (outAbelian_of_outer_comm hcomm)
  exact kaAll_of_oddCore_aut hs (exists_noncomm_of_simple_of_not_prime hs (by rw [hc]; norm_num))
    hY hOutCyc hOut hα2 hα1

theorem kaAll_of_M22
    {Y : Type} [Group Y] [Finite Y] (hs : IsSimpleGroup Y)
    (hYs : NativeSporadic.IsSporadic Y .M22) {α : MulAut Y} (hα2 : α * α = 1)
    (hα1 : α ≠ 1) : KAAll α := by
  obtain ⟨e⟩ := hYs
  have hc : Nat.card Y = 443520 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Schreier.m22_card
  have hY : OddCoreAut Y := fun X _ _ S _ hS hC t ht => by
    obtain ⟨ψ⟩ := hS
    exact CFSG.Sporadic.Schreier.ctuc_mathieu_almost_simple_involution_centralizer_odd_core_trivial
      S (Or.inr (Or.inr (Or.inl ⟨ψ.trans e⟩))) hC t ht
  obtain ⟨hcard, hcomm, -⟩ := CFSG.Sporadic.Schreier.at_m22_schreier
  have hfinC : Finite (NativeSporadic.Carrier .M22) := Finite.of_equiv Y e.toEquiv
  have hOutCyc : KAOutCyc Y :=
    kaOutCyc_of_mulEquiv e.symm (kaOutCyc_of_card_outer_le_four (le_trans hcard (by norm_num)))
  have hOut : OutAbelian Y := outAbelian_of_mulEquiv e.symm (outAbelian_of_outer_comm hcomm)
  exact kaAll_of_oddCore_aut hs (exists_noncomm_of_simple_of_not_prime hs (by rw [hc]; norm_num))
    hY hOutCyc hOut hα2 hα1

theorem kaAll_of_M23
    {Y : Type} [Group Y] [Finite Y] (hs : IsSimpleGroup Y)
    (hYs : NativeSporadic.IsSporadic Y .M23) {α : MulAut Y} (hα2 : α * α = 1)
    (hα1 : α ≠ 1) : KAAll α := by
  obtain ⟨e⟩ := hYs
  have hc : Nat.card Y = 10200960 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Schreier.m23_card
  have hY : OddCoreAut Y := fun X _ _ S _ hS hC t ht => by
    obtain ⟨ψ⟩ := hS
    exact CFSG.Sporadic.Schreier.ctuc_mathieu_almost_simple_involution_centralizer_odd_core_trivial
      S (Or.inr (Or.inr (Or.inr (Or.inl ⟨ψ.trans e⟩)))) hC t ht
  obtain ⟨hcard, hcomm, -⟩ := CFSG.Sporadic.Schreier.at_m23_schreier
  have hfinC : Finite (NativeSporadic.Carrier .M23) := Finite.of_equiv Y e.toEquiv
  have hOutCyc : KAOutCyc Y :=
    kaOutCyc_of_mulEquiv e.symm (kaOutCyc_of_card_outer_le_four (le_trans hcard (by norm_num)))
  have hOut : OutAbelian Y := outAbelian_of_mulEquiv e.symm (outAbelian_of_outer_comm hcomm)
  exact kaAll_of_oddCore_aut hs (exists_noncomm_of_simple_of_not_prime hs (by rw [hc]; norm_num))
    hY hOutCyc hOut hα2 hα1

theorem kaAll_of_J1
    {Y : Type} [Group Y] [Finite Y] (hs : IsSimpleGroup Y)
    (hYs : NativeSporadic.IsSporadic Y .J1) {α : MulAut Y} (hα2 : α * α = 1)
    (hα1 : α ≠ 1) : KAAll α := by
  obtain ⟨e⟩ := hYs
  have hc : Nat.card Y = 175560 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J1.card_J1
  have hna : ∃ a b : Y, a * b ≠ b * a :=
    exists_noncomm_of_simple_of_not_prime hs (by rw [hc]; norm_num)
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) :=
    conj_injective_of_center_eq_bot
      (CFSG.GH74.GLS.Stage2.Bender.Thm2.P911.center_eq_bot_of_simple hs hna)
  have hinnerT : ∀ φ : MulAut NativeSporadic.J1, ∃ g : NativeSporadic.J1, φ = MulAut.conj g :=
    CFSG.Sporadic.Schreier.at_j1_schreier.2.1
  have hinner : ∀ φ : MulAut Y, ∃ g : Y, φ = MulAut.conj g := fun φ =>
    exists_conj_of_equiv e hinnerT φ
  refine kaAll_of_allInner hinj hinner (fun t ht2 ht1 => ?_) hα2 hα1
  have hto : orderOf t = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [sq]; exact ht2) ht1
  exact kaNoP_of_oddCore_inner
    (CFSG.Sporadic.Schreier.ctugs_j1_involution_centralizer_odd_core_free ⟨e⟩ t hto).2.2.2

theorem kaAll_of_J2
    {Y : Type} [Group Y] [Finite Y] (hs : IsSimpleGroup Y)
    (hYs : NativeSporadic.IsSporadic Y .J2) {α : MulAut Y} (hα2 : α * α = 1)
    (hα1 : α ≠ 1) : KAAll α := by
  obtain ⟨e⟩ := hYs
  have hc : Nat.card Y = 604800 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J2.card_J2
  have hY : OddCoreAut Y := fun X _ _ S _ hS hC t ht => by
    obtain ⟨ψ⟩ := hS
    exact CFSG.Sporadic.SmallOddCore.ctuc_j2_almost_simple_involution_centralizer_odd_core_trivial
      S ⟨ψ.trans e⟩ hC t ht
  obtain ⟨hcard, hcomm, -⟩ := CFSG.Sporadic.Schreier.AT_J2_Schreier
  have hfinC : Finite (NativeSporadic.Carrier .J2) := Finite.of_equiv Y e.toEquiv
  have hOutCyc : KAOutCyc Y :=
    kaOutCyc_of_mulEquiv e.symm (kaOutCyc_of_card_outer_le_four (le_trans hcard (by norm_num)))
  have hOut : OutAbelian Y := outAbelian_of_mulEquiv e.symm (outAbelian_of_outer_comm hcomm)
  exact kaAll_of_oddCore_aut hs (exists_noncomm_of_simple_of_not_prime hs (by rw [hc]; norm_num))
    hY hOutCyc hOut hα2 hα1

theorem kaAll_of_J3
    {Y : Type} [Group Y] [Finite Y] (hs : IsSimpleGroup Y)
    (hYs : NativeSporadic.IsSporadic Y .J3) {α : MulAut Y} (hα2 : α * α = 1)
    (hα1 : α ≠ 1) : KAAll α := by
  obtain ⟨e⟩ := hYs
  have hc : Nat.card Y = 50232960 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J3.card_J3
  have hY : OddCoreAut Y := fun X _ _ S _ hS hC t ht => by
    obtain ⟨ψ⟩ := hS
    exact CFSG.Sporadic.SmallOddCore.ctuc_j3_almost_simple_involution_centralizer_odd_core_trivial
      S ⟨ψ.trans e⟩ hC t ht
  have hcard := CFSG.Sporadic.SmallOddCore.j3_outer_card_le
  let e' : Y ≃* CFSG.Sporadic.Schreier.j3P := e.trans CFSG.Sporadic.Schreier.j3PermEquiv
  have hfinP : Finite CFSG.Sporadic.Schreier.j3P := Finite.of_equiv Y e'.toEquiv
  have hcard4 : Nat.card (Outer CFSG.Sporadic.Schreier.j3P) ≤ 4 := hcard.trans (by norm_num)
  have hOutCyc : KAOutCyc Y :=
    kaOutCyc_of_mulEquiv e'.symm (kaOutCyc_of_card_outer_le_four hcard4)
  have hcomm : IsMulCommutative (Outer CFSG.Sporadic.Schreier.j3P) :=
    CFSG.ComponentClassification.CatalogueSchreierAlternating.commutative_of_card_le_four hcard4
  have hOut : OutAbelian Y := outAbelian_of_mulEquiv e'.symm (outAbelian_of_outer_comm hcomm)
  exact kaAll_of_oddCore_aut hs (exists_noncomm_of_simple_of_not_prime hs (by rw [hc]; norm_num))
    hY hOutCyc hOut hα2 hα1

theorem kay_Spor :
    KAY FSpor := by
  refine kay_of_kaAll ?_
  intro Y _ _ hF hs α hα2 hα1
  rcases hF with h | h | h | h | h | h | h
  · exact kaAll_of_M11 hs h hα2 hα1
  · exact kaAll_of_M12 hs h hα2 hα1
  · exact kaAll_of_M22 hs h hα2 hα1
  · exact kaAll_of_M23 hs h hα2 hα1
  · exact kaAll_of_J1 hs h hα2 hα1
  · exact kaAll_of_J2 hs h hα2 hα1
  · exact kaAll_of_J3 hs h hα2 hα1

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
