module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsCore
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.AutA6CodeK

public section

namespace CFSG.QuasithinUnique.Unc25G2

namespace A6I

open CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.AutA6K
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.AutA6CodeK

@[expose] def cinvT (c : List Nat) : List Nat := (List.range c.length).map fun j => c.idxOf j

@[expose] def conjT (c k : List Nat) : List Nat := Core.cmul (Core.cmul c k) (cinvT c)

@[expose] def Va : List (List Nat) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [0, 2, 1, 6, 8, 7, 3, 5, 4, 9], [9, 1, 2, 6, 5, 4, 3, 8, 7, 0],
    [9, 2, 1, 3, 7, 8, 6, 4, 5, 0]]

@[expose] def Vb : List (List Nat) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [3, 2, 1, 0, 5, 4, 9, 7, 8, 6], [6, 2, 1, 9, 4, 5, 0, 8, 7, 3],
    [9, 1, 2, 6, 5, 4, 3, 8, 7, 0]]

@[expose] def Ka : List (List Nat) := Core.pslLit.filter fun k => Va.all fun v => Va.contains (conjT k v)

@[expose] def Kb : List (List Nat) := Core.pslLit.filter fun k => Vb.all fun v => Vb.contains (conjT k v)

@[expose] def closedOK (l : List (List Nat)) : Bool :=
  l.contains Core.cid && l.all (fun a => l.all fun b => l.contains (Core.cmul a b)) &&
    l.all fun a => l.contains (cinvT a)

@[expose] def notNormal (K : List (List Nat)) : Bool :=
  K.any fun k => Core.dLit.any fun p => !Core.dLit.contains (conjT k p)

@[expose] def normCent (V K : List (List Nat)) : Bool :=
  K.all (fun k => V.all fun v => V.contains (conjT k v)) &&
    K.all fun k => !(V.all fun v => Core.cmul k v == Core.cmul v k) || V.contains k

@[expose] def subsetOK (X Y : List (List Nat)) : Bool := X.all fun x => Y.contains x

@[expose] def wordA : List (List Nat) :=
  [[0, 3, 6, 2, 5, 8, 1, 4, 7, 9], [0, 7, 8, 9, 5, 4, 6, 1, 2, 3], [6, 9, 0, 1, 5, 7, 2, 4, 8, 3]]

@[expose] def prodT (w : List (List Nat)) : List Nat := w.foldl Core.cmul Core.cid

private theorem cinvT_code (σ : P10) : cinvT (code σ) = code σ⁻¹ := by
  unfold cinvT
  rw [code_length]
  exact (Setup.X3Aut.code_inv σ).symm

private theorem isC_Ka : ∀ c ∈ Ka, IsC c := fun c hc => isC_of_psl (List.mem_filter.1 hc).1

private theorem isC_Kb : ∀ c ∈ Kb, IsC c := fun c hc => isC_of_psl (List.mem_filter.1 hc).1

private theorem Ka_map : Ka.map pk = KaK := by
  have hV : ∀ c ∈ Va, IsC c := fun c hc => isC_of_psl (List.contains_iff_mem.1
    (List.all_eq_true.1 (by decide +kernel : Va.all (fun v => Core.pslLit.contains v) = true) c hc))
  unfold Ka conjT
  rw [normL_pin cinvT cinvT_code hV, beq_iff_eq.1 (by decide +kernel : (Va.map pk == VaK) = true)]
  exact beq_iff_eq.1 KaK_check

private theorem Kb_map : Kb.map pk = KbK := by
  have hV : ∀ c ∈ Vb, IsC c := fun c hc => isC_of_psl (List.contains_iff_mem.1
    (List.all_eq_true.1 (by decide +kernel : Vb.all (fun v => Core.pslLit.contains v) = true) c hc))
  unfold Kb conjT
  rw [normL_pin cinvT cinvT_code hV, beq_iff_eq.1 (by decide +kernel : (Vb.map pk == VbK) = true)]
  exact beq_iff_eq.1 KbK_check

private theorem Ka_eq : Ka = KaL := eq_of_map_pk isC_Ka isC_KaL (by rw [Ka_map, KaL_pin])

private theorem Kb_eq : Kb = KbL := eq_of_map_pk isC_Kb isC_KbL (by rw [Kb_map, KbL_pin])

theorem facts6_D : closedOK Core.dLit = true ∧ subsetOK Core.dLit Core.pslLit = true ∧
    Core.dLit.Nodup ∧ Core.dLit.length = 8 := by
  decide +kernel

theorem facts6_gen : subsetOK wordA (Ka ++ Kb) = true ∧ prodT wordA = Core.pslGenC[0]! ∧
    subsetOK [Core.pslGenC[1]!, Core.pslGenC[2]!] (Ka ++ Kb) = true := by
  rw [Ka_eq, Kb_eq]
  decide +kernel

theorem facts6_closed : closedOK Ka = true ∧ closedOK Kb = true ∧ closedOK Va = true ∧ closedOK Vb = true := by
  rw [Ka_eq, Kb_eq]
  decide +kernel

theorem facts6_card : Ka.Nodup ∧ Ka.length = 24 ∧ Kb.Nodup ∧ Kb.length = 24 ∧ Va.Nodup ∧ Va.length = 4 ∧
    Vb.Nodup ∧ Vb.length = 4 := by
  rw [Ka_eq, Kb_eq]
  decide +kernel

theorem facts6_sub : subsetOK Ka Core.pslLit = true ∧ subsetOK Kb Core.pslLit = true ∧
    subsetOK Core.dLit Ka = true ∧ subsetOK Core.dLit Kb = true ∧
    subsetOK Va Core.dLit = true ∧ subsetOK Vb Core.dLit = true := by
  rw [Ka_eq, Kb_eq]
  decide +kernel

theorem facts6_normal : notNormal Ka = true ∧ notNormal Kb = true ∧ normCent Va Ka = true ∧
    normCent Vb Kb = true := by
  rw [Ka_eq, Kb_eq]
  decide +kernel

set_option synthInstance.maxSize 1024 in
theorem facts6_aut_a : ∀ b ∈ Core.autL, b ∉ Core.pslLit →
    (∀ d ∈ Core.dLit, Core.cmul b d = Core.cmul d b) → ∀ c ∈ Core.autL,
    (∀ d ∈ Core.dLit, conjT c d ∈ Core.dLit) → Core.cmul c b = Core.cmul b c →
    ∀ k ∈ Ka, conjT c k ∈ Ka :=
  aut_norm cinvT cinvT_code isC_Ka (by rw [Ka_map]; exact autN_KaK)

set_option synthInstance.maxSize 1024 in
theorem facts6_aut_b : ∀ b ∈ Core.autL, b ∉ Core.pslLit →
    (∀ d ∈ Core.dLit, Core.cmul b d = Core.cmul d b) → ∀ c ∈ Core.autL,
    (∀ d ∈ Core.dLit, conjT c d ∈ Core.dLit) → Core.cmul c b = Core.cmul b c →
    ∀ k ∈ Kb, conjT c k ∈ Kb :=
  aut_norm cinvT cinvT_code isC_Kb (by rw [Kb_map]; exact autN_KbK)

end A6I

end CFSG.QuasithinUnique.Unc25G2
