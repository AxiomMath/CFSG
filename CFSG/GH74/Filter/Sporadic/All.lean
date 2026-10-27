module

public import CFSG.GH74.Filter.Sporadic.M24
public import CFSG.GH74.Filter.Sporadic.J4
public import CFSG.GH74.Filter.Sporadic.HS
public import CFSG.GH74.Filter.Sporadic.He
public import CFSG.GH74.Filter.Sporadic.Ru
public import CFSG.GH74.Filter.Sporadic.Suz
public import CFSG.GH74.Filter.Sporadic.ON
public import CFSG.GH74.Filter.Sporadic.Co1
public import CFSG.GH74.Filter.Sporadic.Co2
public import CFSG.GH74.Filter.Sporadic.Co3
public import CFSG.GH74.Filter.Sporadic.Fi22
public import CFSG.GH74.Filter.Sporadic.Fi23
public import CFSG.GH74.Filter.Sporadic.Fi24prime
public import CFSG.GH74.Filter.Sporadic.HN
public import CFSG.GH74.Filter.Sporadic.Th
public import CFSG.GH74.Filter.Sporadic.B

public section

namespace CFSG.GH74.Filter

open CFSG.Blueprint

theorem sporadic_of_carrier {s : TauCeti.SporadicName}
    (h : Finite (NativeSporadic.Carrier s) → ¬ Gen4 (NativeSporadic.Carrier s)) :
    S_sporadic s :=
  fun G _ _ _ ⟨e⟩ => not_gen4_of_mulEquiv e.symm (h (Finite.of_equiv G e.toEquiv))

theorem t_sporadic_M24 : S_sporadic .M24 := sporadic_of_carrier fun _ => not_gen4_M24

theorem t_sporadic_J4 :
    S_sporadic .J4 := sporadic_of_carrier fun _ => not_gen4_J4

theorem t_sporadic_HS :
    S_sporadic .HS := sporadic_of_carrier fun _ => not_gen4_HS

theorem t_sporadic_He :
    S_sporadic .He := sporadic_of_carrier fun _ => not_gen4_He

theorem t_sporadic_Ru :
    S_sporadic .Ru := sporadic_of_carrier fun _ => not_gen4_Ru

theorem t_sporadic_Suz :
    S_sporadic .Suz := sporadic_of_carrier fun _ => not_gen4_Suz

theorem t_sporadic_ONan :
    S_sporadic .ONan := sporadic_of_carrier fun _ => not_gen4_ON

theorem t_sporadic_Co1 :
    S_sporadic .Co1 := sporadic_of_carrier fun _ => not_gen4_Co1

theorem t_sporadic_Co2 :
    S_sporadic .Co2 := sporadic_of_carrier fun _ => not_gen4_Co2

theorem t_sporadic_Co3 :
    S_sporadic .Co3 := sporadic_of_carrier fun _ => not_gen4_Co3

theorem t_sporadic_Fi22 :
    S_sporadic .Fi22 := sporadic_of_carrier fun _ => not_gen4_Fi22

theorem t_sporadic_Fi23 :
    S_sporadic .Fi23 := sporadic_of_carrier fun _ => not_gen4_Fi23

theorem t_sporadic_Fi24Prime : S_sporadic .Fi24Prime :=
  sporadic_of_carrier fun _ => not_gen4_Fi24prime

theorem t_sporadic_HN :
    S_sporadic .HN := sporadic_of_carrier fun _ => not_gen4_HN

theorem t_sporadic_Th :
    S_sporadic .Th := sporadic_of_carrier fun _ => not_gen4_Th

theorem t_sporadic_B :
    S_sporadic .B := sporadic_of_carrier fun _ => not_gen4_B

theorem t_sporadic_of_out
    : ∀ s ∈ sporadicOut, s ≠ .M → S_sporadic s := by
  intro s hs hM
  simp only [sporadicOut, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact t_sporadic_M24
  · exact t_sporadic_J4
  · exact t_sporadic_HS
  · exact t_sporadic_He
  · exact t_sporadic_Ru
  · exact t_sporadic_Suz
  · exact t_sporadic_ONan
  · exact t_sporadic_Co1
  · exact t_sporadic_Co2
  · exact t_sporadic_Co3
  · exact t_sporadic_Fi22
  · exact t_sporadic_Fi23
  · exact t_sporadic_Fi24Prime
  · exact t_sporadic_HN
  · exact t_sporadic_Th
  · exact t_sporadic_B
  · exact absurd rfl hM

theorem t_sporadic_all
    (hM : S_sporadic .M) : ∀ s ∈ sporadicOut, S_sporadic s := by
  intro s hs
  by_cases h : s = .M
  · subst h
    exact hM
  · exact t_sporadic_of_out s hs h

end CFSG.GH74.Filter
