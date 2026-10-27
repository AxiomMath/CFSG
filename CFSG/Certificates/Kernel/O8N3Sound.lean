module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitNCData
public import CFSG.Certificates.Kernel.O8MaskProved
public import CFSG.Certificates.Kernel.O8PlusSound

public section

namespace CFSG.KC.O8

open CFSG.EvenSmallLie.OmegaEight.Stage2 CFSG.EvenSmallLie.OmegaEight.N3Split

theorem fixVecs_eq (k : ℕ) :
    fixVecs k = (List.range 4096).filter fun v => mulVec12K k v == v := by
  apply fixVecs_eq_proved

theorem kerOn_eq (E : Enum) (s : ℕ) (vs : List ℕ) : kerOn E s vs =
    ((List.range E.keys.size).filter fun i =>
      mulK (E.keys.getD i 0) s == mulK s (E.keys.getD i 0) &&
        fixesOn vs (E.keys.getD i 0)).length := by
  apply kerOn_eq_proved

theorem fixCountF_eqM {SW : List ℕ} (hSW : SW = swarK) (k : ℕ) :
    fixCountF k = popcM SW (fixMaskW SW k) := by
  apply fixCountF_eqM_proved <;> assumption

@[expose] noncomputable def relPairK (a b c d : ℕ) : Bool :=
  ((mul12K a b == mul12K b a) == (mul12K c d == mul12K d c)) &&
    ((powKK (mul12K a b) 3 == ID12) == (powKK (mul12K c d) 3 == ID12))

theorem relPair_eq (a b c d : ℕ) : relPair a b c d = relPairK a b c d := by
  simp only [relPair, relPairK, mulK_eq, powK_eq, idK_eq]

@[expose] noncomputable def chainAuxK (mem : ℕ → Bool) (R : List ℕ) :
    List ℕ → List ℕ → List (List (ℕ × ℕ)) → Bool
  | _, [], _ => true
  | _, _ :: _, [] => false
  | fx, ρ :: ρs, ks :: kss =>
    (R.all fun σ => !(fx.all fun φ => relPairK φ ρ φ σ) ||
      ks.any fun p => p.1 == σ && mem p.2 && (fx.all fun φ => mul12K p.2 φ == mul12K φ p.2) &&
        mul12K p.2 ρ == mul12K σ p.2) && chainAuxK mem R (fx ++ [ρ]) ρs kss

theorem chainAux_eq (keys : Array ℕ) (R : List ℕ) {mem : ℕ → Bool}
    (hm : ∀ k, memK keys k = mem k) : ∀ (fx ρs : List ℕ) (kss : List (List (ℕ × ℕ))),
    chainAux keys R fx ρs kss = chainAuxK mem R fx ρs kss
  | _, [], _ => by simp [chainAux, chainAuxK]
  | _, _ :: _, [] => by simp [chainAux, chainAuxK]
  | fx, ρ :: ρs, ks :: kss => by
    simp only [chainAux, chainAuxK, relPair_eq, mulK_eq, hm,
      chainAux_eq keys R hm (fx ++ [ρ]) ρs kss]

theorem length_filter_range_add (q : ℕ → Bool) (n k : ℕ) :
    ((List.range (n + k)).filter q).length =
      ((List.range n).filter q).length + ((List.range k).filter fun c => q (n + c)).length := by
  rw [List.range_add, List.filter_append, List.length_append, List.filter_map, List.length_map]
  rfl

theorem length_filter_range_blocks {m s nb : ℕ} {p : ℕ → Bool} (hm : m ≤ nb * 2 ^ s)
    {C : ℕ → ℕ} (hC : ∀ b < nb, ((List.range (2 ^ s)).filter fun c =>
      decide (b * 2 ^ s + c < m) && p (b * 2 ^ s + c)).length = C b) :
    ((List.range m).filter p).length = ((List.range nb).map C).sum := by
  set q : ℕ → Bool := fun i => decide (i < m) && p i with hq
  have h1 : ((List.range m).filter p).length = ((List.range (nb * 2 ^ s)).filter q).length := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hm
    rw [hk, length_filter_range_add]
    have e1 : (List.range m).filter q = (List.range m).filter p :=
      List.filter_congr fun i hi => by simp [hq, List.mem_range.1 hi]
    have e2 : ((List.range k).filter fun c => q (m + c)) = [] :=
      List.filter_eq_nil_iff.2 fun c _ => by simp [hq]
    rw [e1, e2, List.length_nil, Nat.add_zero]
  rw [h1]
  clear h1 hm
  induction nb with
  | zero => simp
  | succ n ih =>
    have hn := hC n (by omega)
    rw [Nat.succ_mul, length_filter_range_add, ih (fun b hb => hC b (by omega)),
      List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
      ← hn]

theorem candB_false_of_zfix {E : Enum} {s : ℕ} {vs : List ℕ} (hlen : 3 ≤ vs.length)
    (hnd : vs.Nodup) (hfix : vs.all (fun v => decide (v < 4096) && mulVecK s v == v) = true)
    (hall : ((List.range E.keys.size).all fun i =>
      !(mulK (E.keys.getD i 0) s == mulK s (E.keys.getD i 0)) ||
        vs.all fun v => mulVecK (E.keys.getD i 0) v == v) = true) :
    candB E s = false := by
  apply candB_false_of_zfix_proved <;> assumption

theorem all_eq_range (l : List ℕ) (f : ℕ → Bool) :
    l.all f = (List.range l.length).all fun i => f (l.getD i 0) := by
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true, List.mem_range]
  constructor
  · intro h i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact h _ (List.getElem_mem hi)
  · intro h x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    have := h i hi
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this

end CFSG.KC.O8

end
