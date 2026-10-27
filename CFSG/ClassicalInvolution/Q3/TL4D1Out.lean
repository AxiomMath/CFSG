module

public import CFSG.ClassicalInvolution.Q3.TL3T13
public import CFSG.ClassicalInvolution.Q3.TL4D1Pack

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G] {Δ : Set (Subgroup G)}

structure D1Sub (J X : Subgroup G) : Prop where
  le : J ≤ X
  sub : X.IsSubnormal
  span : pSpan {L | ∃ x ∈ X, conjSub x J = L} = X
  pack : D1Pack X
  out : (∃ E : Subgroup G, E8Struct X E) ∨
    ∃ (n : ℕ) (𝒜 : Set (Finset (Fin n))) (M : Subgroup (AE.AEQ n)), 5 ≤ n ∧
      ModelMembers 𝒜 M ∧ Nonempty (AEIdentOn {L | ∃ x ∈ X, conjSub x J = L} n 𝒜 M)

omit [Finite G] in
theorem nonempty_aeIdentOn_of_aeIdent {P : Set (Subgroup G)} {m : ℕ}
    (h : Nonempty (AEIdent P m)) : Nonempty (AEIdentOn P m Set.univ (aeModel m)) := by
  obtain ⟨I⟩ := h
  exact ⟨{ φ := I.φ
           range_eq := I.range_eq
           ker_le := I.ker_le
           label := fun L hL => by
             obtain ⟨α, h, b, hlab⟩ := I.label L hL
             exact ⟨α, Set.mem_univ α, h, b, hlab⟩
           label_surj := fun α _ h b => I.label_surj α h b }⟩

omit [Finite G] in
theorem mem_pCore_of_tightInO2 {u : G} (hu : TightInO2 u) : u ∈ pCore 2 G := by
  obtain ⟨T, hTn, hT2, huT⟩ := hu
  exact (le_sSup ⟨hTn, hT2⟩ : T ≤ pCore 2 G) huT

end CFSG.ClassicalInvolution.Q3.TL4
