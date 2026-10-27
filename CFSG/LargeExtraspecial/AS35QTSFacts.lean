module

public import CFSG.LargeExtraspecial.AS35QTSCode

public section

namespace CFSG.LargeExtraspecial.AS35QTS

open CFSG.Fischer

@[expose] def QtsFacts : Prop :=
  (unitB I3 = true ∧ mulC e0 e0 = e0 ∧ ∀ g ∈ cgens, unitB g.m = true) ∧
  (gu3s.length = 648 ∧ gu3s.Nodup ∧ sl.length = 36 ∧ sl.Nodup) ∧
  (∀ q ∈ codes, q.m = I3 → powC q 4 = e0) ∧
  (∀ c ∈ il, c.m ≠ I3 → ∃ q ∈ codes, q.m = I3 ∧ mulC q q = tau0 ∧ mulC q c = mulC c q) ∧
  (∀ c ∈ il,
    c = tau0 ∨ c ∈ sl ∨ ∃ a ∈ dl, ∃ b ∈ dl, a ≠ b ∧ mulC a b = mulC b a ∧ mulC a b = c) ∧
  (∀ t ∈ sl, ∃ m ∈ codes, mulC m t0c = mulC t m) ∧
  (∀ a ∈ dl, ∀ b ∈ dl, mulC (mulC a b) (mulC a b) = e0 ∨
      mulC (mulC (mulC a b) (mulC a b)) (mulC a b) = e0) ∧
  ((∀ t ∈ sl, (lineIn dl t).length = 5) ∧
    (∀ t ∈ sl, ∀ a ∈ lineIn dl t, ∀ b ∈ lineIn dl t, mulC a b = mulC b a) ∧
    (∀ t ∈ sl, ∀ t' ∈ sl, mulC t t' = mulC t' t → ∀ s ∈ sl,
      (mulC t s = mulC s t ↔ mulC t' s = mulC s t')) ∧
    (∀ t ∈ sl, ∀ a ∈ lineIn dl t, ∀ b ∈ lineIn dl t, ∀ a' ∈ lineIn dl t,
      ∀ b' ∈ lineIn dl t, a ≠ b → a' ≠ b' → mulC a b = mulC a' b' →
        (a = a' ∧ b = b') ∨ (a = b' ∧ b = a')) ∧
    ∀ t ∈ sl, mulC tau0 t ∉ dl) ∧
  ((∀ x ∈ dl, ∀ v ∈ wl, pow72 (mulC x v) = e0) ∧
    ((dl.toFinset ×ˢ wl.toFinset).filter fun p => tau0 ∈ zpowL (mulC p.1 p.2)).card = 1188) ∧
  (((lineIn dl t0c).toFinset ×ˢ (wl.filter (commB t0c)).toFinset).filter
    fun p => mulC tau0 t0c ∈ zpowL (mulC p.1 p.2)).card = 3 ∧
  (∀ p ∈ sl, ∀ p' ∈ sl, p ≠ p' → mulC p p' = mulC p' p →
    (il.toFinset.filter fun v => mulC v p = mulC p' v).card = 16 ∧
      ∀ q ∈ sl, q ≠ p → q ≠ p' → mulC p q = mulC q p → ∀ v ∈ il,
        mulC v p = mulC p' v → mulC v q ≠ mulC q v) ∧
  (codes.filter (commB t0c)).toFinset.card = 2304 ∧
  ∀ c ∈ codes, (∀ g ∈ cgens, mulC c g = mulC g c) → c = e0 ∨ c = tau0

end CFSG.LargeExtraspecial.AS35QTS

end
