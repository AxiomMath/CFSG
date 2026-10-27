module

public import CFSG.LocalAnalysis.AGLEmbedding.JStarElimSporAux
public import CFSG.Open.MonsterDefs
import CFSG.Sporadic.ON
import CFSG.Sporadic.Fi22.Simple
import CFSG.Sporadic.Fi24.Simple
import CFSG.RankThree.PartOne.CTP.SporadicOrders
import CFSG.Monster.Existence.BabyOrder
import CFSG.Sporadic.B
import CFSG.Sporadic.Bridge.Y443Relabel
public import CFSG.Open.MonsterY443Defs
public import CFSG.Sporadic.Co1
public import CFSG.Sporadic.Fi23.Simple
import CFSG.Sporadic.Th.KernelSimple

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.Blueprint CFSG.Sporadic


theorem kFactJStarElimSpor_of
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hOutS : ∀ s : TauCeti.SporadicName, ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group))
    (hMcard : Nat.card Open.MonsterY443Derived = Open.monsterOrder)
    (hMsimple : IsSimpleGroup Open.MonsterY443Derived) : KFactJStarElimSpor := by
  intro p n _ _ hn L _ _ s hs ⟨e⟩
  obtain ⟨f⟩ := hbr s
  have hOut : ∀ q : ℕ, q.Prime → q ≠ 2 → ¬ q ∣ Nat.card (Outer L) := fun q hq hq2 => by
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact hOutS s q hq hq2
  have key {N : ℕ} (hN : Nat.card (NativeSporadic.Carrier s) = N) (hND : N ∣ jStarSporBound)
      (hc : (p = 3 ∧ ((¬ 13 ∣ N ∧ ¬ 41 ∣ N) ∨
          (IsSimpleGroup (NativeSporadic.Carrier s) ∧ 3 ^ 5 ∣ N))) ∨
        (p = 5 ∧ (¬ 31 ∣ N ∨ (IsSimpleGroup (NativeSporadic.Carrier s) ∧ 5 ^ 4 ∣ N))) ∨ p = 7 ∨
        p = 13) :
      ¬ JStarElimData L p n :=
    not_jStarElimData_of_mulEquiv (e.trans f.symm) hn hN hND hOut hc
  have hMc : Nat.card (NativeSporadic.Carrier .M) = Open.monsterOrder :=
    (Nat.card_congr Bridge.Y443.commutatorMulEquiv.toEquiv).trans hMcard
  have hMs : IsSimpleGroup (NativeSporadic.Carrier .M) :=
    Bridge.Y443.commutatorMulEquiv.isSimpleGroup
  rcases hs with ⟨rfl, rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
  · exact key J3.card_J3 (by decide) (Or.inl ⟨rfl, Or.inl ⟨by decide, by decide⟩⟩)
  · exact key McL.card_McL (by decide) (Or.inl ⟨rfl, Or.inl ⟨by decide, by decide⟩⟩)
  · exact key Suz.card_Suz (by decide) (Or.inl ⟨rfl, Or.inr ⟨Suz.isSimpleGroup_Suz, by decide⟩⟩)
  · exact key ON.card_ON (by decide) (Or.inl ⟨rfl, Or.inl ⟨by decide, by decide⟩⟩)
  · exact key Co1.card_Co1 (by decide) (Or.inl ⟨rfl, Or.inr ⟨Co1.isSimpleGroup_Co1, by decide⟩⟩)
  · exact key Co2.card_Co2 (by decide) (Or.inl ⟨rfl, Or.inl ⟨by decide, by decide⟩⟩)
  · exact key Co3.card_Co3 (by decide) (Or.inl ⟨rfl, Or.inl ⟨by decide, by decide⟩⟩)
  · exact key Fi22.card_Fi22 (by decide)
      (Or.inl ⟨rfl, Or.inr ⟨Fi22.isSimpleGroup_Fi22, by decide⟩⟩)
  · exact key Fi23.card_Fi23 (by decide)
      (Or.inl ⟨rfl, Or.inr ⟨Fi23.isSimpleGroup_Fi23, by decide⟩⟩)
  · exact key Fi24.card_Fi24prime (by decide)
      (Or.inl ⟨rfl, Or.inr ⟨Fi24.isSimpleGroup_Fi24prime, by decide⟩⟩)
  · exact key HN.card_HN (by decide) (Or.inl ⟨rfl, Or.inl ⟨by decide, by decide⟩⟩)
  · exact key Ly.card_Ly (by decide) (Or.inl ⟨rfl, Or.inl ⟨by decide, by decide⟩⟩)
  · exact key RankThree.PartOne.CTP.card_Th (by decide)
      (Or.inl ⟨rfl, Or.inr ⟨Th.Kernel.isSimpleGroup_Th Th.th_kernel_facts, by decide⟩⟩)
  · exact key Monster.Existence.card_nativeB (by decide)
      (Or.inl ⟨rfl, Or.inr ⟨B.fam_b_simplicity, by decide⟩⟩)
  · exact key hMc (by decide) (Or.inl ⟨rfl, Or.inr ⟨hMs, by decide⟩⟩)
  · exact key Mathieu.card_M22 (by decide) (Or.inl ⟨rfl, Or.inl ⟨by decide, by decide⟩⟩)
  · exact key Co1.card_Co1 (by decide) (Or.inr (Or.inl ⟨rfl, Or.inl (by decide)⟩))
  · exact key Ly.card_Ly (by decide)
      (Or.inr (Or.inl ⟨rfl, Or.inr ⟨Ly.isSimpleGroup_Ly, by decide⟩⟩))
  · exact key HN.card_HN (by decide) (Or.inr (Or.inl ⟨rfl, Or.inl (by decide)⟩))
  · exact key Monster.Existence.card_nativeB (by decide)
      (Or.inr (Or.inl ⟨rfl, Or.inr ⟨B.fam_b_simplicity, by decide⟩⟩))
  · exact key hMc (by decide) (Or.inr (Or.inl ⟨rfl, Or.inr ⟨hMs, by decide⟩⟩))
  · exact key Fi24.card_Fi24prime (by decide) (Or.inr (Or.inr (Or.inl rfl)))
  · exact key hMc (by decide) (Or.inr (Or.inr (Or.inl rfl)))
  · exact key hMc (by decide) (Or.inr (Or.inr (Or.inr rfl)))

end CFSG.AGLEmbedding
