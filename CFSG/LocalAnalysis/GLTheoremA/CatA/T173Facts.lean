module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs123

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

@[expose] def T173ClassA : TauCeti.LieTypeIndex → Prop
  | .A _ _ | .twistedA _ _ => True
  | _ => False

@[expose] def T173ClassD : TauCeti.LieTypeIndex → Prop
  | .D _ _ => True
  | _ => False

@[expose] def T173ClassTD : TauCeti.LieTypeIndex → Prop
  | .twistedD _ _ => True
  | _ => False

@[expose] def T173Concl (p : ℕ) {Ω : Type} [Group Ω] [Finite Ω] (S B K N : Subgroup Ω) : Prop :=
  Type126 p S K (closureIn K N) ∨
    ∃ B' U : Subgroup Ω, IsElemAbelian p B' ∧ B' ≤ S ⊔ B ∧ B ≤ B' ∧ B ≠ B' ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ U ≤ K ∧
      B' = (B' ⊓ K) ⊔ (B' ⊓ Subgroup.normalizer (U : Set Ω))

structure Cfg173 (p : ℕ) {Ω : Type} [Group Ω] [Finite Ω] (S B N D K : Subgroup Ω) (x : Ω) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  normal : S.Normal
  qs : CFSG.Open.IsQuasisimple ↥S
  chev : IsChevSimple 2 (PSimple p S)
  top : S ⊔ N = ⊤
  hN : N = Subgroup.normalizer (B : Set Ω) ⊓ Subgroup.centralizer ({x} : Set Ω)
  elem : IsElemAbelian p B
  bmax : GLAIsBmax p B
  four : p ^ 4 ≤ Nat.card B
  mem : x ∈ B
  ne_one : x ≠ 1
  cent : ∀ b ∈ B, b ∈ Subgroup.centralizer (S : Set Ω) ↔ b ∈ Subgroup.zpowers x
  cyc : CycModSylow p S
  split : SplitInnerDiagMarking16 p B S
  std : GLAStdSubPre p B x S D K
  hb : ∃ T : Subgroup Ω, T ≤ S ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set Ω) ∧
    (⁅T, B⁆ : Subgroup Ω) ≠ ⊥
  hc : ∃ T : Subgroup Ω, T ≤ S ∧ IsPGroup 2 T ∧ closureIn K N ⊔ B ≤ Subgroup.normalizer (T : Set Ω) ∧
    (⁅closureIn K N, T⁆ : Subgroup Ω) ≠ ⊥

@[expose] def I173FactA : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B N D K : Subgroup Ω) (x : Ω),
    Cfg173 p S B N D K x → catalogIs (PSimple p S) (onLie T173ClassA) → T173Concl p S B K N

@[expose] def I173FactD : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B N D K : Subgroup Ω) (x : Ω),
    Cfg173 p S B N D K x → catalogIs (PSimple p S) (onLie T173ClassD) → T173Concl p S B K N

@[expose] def I173FactTD : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B N D K : Subgroup Ω) (x : Ω),
    Cfg173 p S B N D K x → catalogIs (PSimple p S) (onLie T173ClassTD) → T173Concl p S B K N

@[expose] def I173FactO : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B N D K : Subgroup Ω) (x : Ω),
    Cfg173 p S B N D K x → ¬ catalogIs (PSimple p S) (onLie T173ClassA) →
      ¬ catalogIs (PSimple p S) (onLie T173ClassD) → ¬ catalogIs (PSimple p S) (onLie T173ClassTD) →
      T173Concl p S B K N

@[expose] def I173FactNoncyc : Prop :=
  ∀ (p : ℕ) (Y : Type) [Group Y] [Finite Y] (S B : Subgroup Y) (x : Y),
    p.Prime → p ≠ 2 → CFSG.Open.IsQuasisimple ↥S → IsChevSimple 2 (PSimple p S) →
    IsElemAbelian p B → p ^ 4 ≤ Nat.card B → x ∈ B → x ≠ 1 → B ≤ Subgroup.normalizer (S : Set Y) →
    (∀ b ∈ B, b ∈ Subgroup.centralizer (S : Set Y) ↔ b ∈ Subgroup.zpowers x) →
    InnerDiagMarking B S →
    ∃ P : Subgroup Y, P ≤ S ∧ IsPGroup p P ∧ ¬ IsCyclic P

end CFSG.LocalAnalysis.GLTheoremA.T173

end
