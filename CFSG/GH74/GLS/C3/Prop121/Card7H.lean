module

public import CFSG.GH74.GLS.C3.Prop121.Card7H3

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7

theorem card7HFacts
    : HFacts where
  card_H := HC.card_H
  ord3 := fun τ h3 h1 => HC.ord3_field τ h3 h1
  inv_tau1 := HC.inv_tau1_field
  center := fun c hc => HC.center_field c hc
  card_B0 := HC.card_B0_field
  B0inv := fun b hb hi hy => HC.B0inv_field b hb hi hy
  ry := fun X' h1 h2 h3 h4 h5 _ => HC.ry_field X' h1 h2 h3 h4 h5

end CFSG.GH74.GLS.C3.Prop121.Card7
