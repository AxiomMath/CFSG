module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenElementsParts
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenJInputs
public import CFSG.LieType.Multipliers.L34Data

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native CFSG.Sporadic.Bridge
  CFSG.Sporadic.Bridge.TwoGen CFSG.LieType.Multipliers

@[expose] noncomputable def uB7 : NativeSporadic.B :=
  wordProd (img2 yB7 eB7) (b7JUWord ())

@[expose] noncomputable def vB7 : NativeSporadic.B :=
  yB7 ^ 3

structure B7JParts (a e y u v : NativeSporadic.B) : Prop where
  a_sq : a * a = 1
  y_pow : y ^ 5 = 1
  e_pow : e ^ 3 = 1
  seven : (e * y) ^ 7 = a
  u_sq : u * u = 1
  rels_mem : ∀ w ∈ L34.rels.map (List.map fun l => ((l.1 : ℕ), l.2)),
    wordProd (img2 u v) w ∈ Subgroup.zpowers a
  u_ne_one : u ≠ 1
  u_ne_a : u ≠ a
  e_word : wordProd (img2 u v) (b7JEWord ()) = e

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
