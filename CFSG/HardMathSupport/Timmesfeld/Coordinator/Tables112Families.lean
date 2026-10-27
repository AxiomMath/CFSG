module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.Tables112
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_6_Defs

public section

namespace CFSG.HardMathSupport.Timmesfeld.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.ComponentBalance

@[expose] def AltCentralQuotient (L : Type) [Group L] : Prop :=
  ∃ n : ℕ, Nonempty ((L ⧸ Subgroup.center L) ≃* ↥(alternatingGroup (Fin n)))

@[expose] def LieCentralQuotient (L : Type) [Group L] : Prop :=
  ∃ idx : TauCeti.ValidLieTypeIndex,
    Nonempty ((L ⧸ Subgroup.center L) ≃* (TauCeti.CFSGIndex.lie idx).Group)

@[expose] def SporCentralQuotient (L : Type) [Group L] : Prop :=
  ∃ name : TauCeti.SporadicName,
    Nonempty ((L ⧸ Subgroup.center L) ≃* (TauCeti.CFSGIndex.sporadic name).Group)

structure Tables112On (F : ∀ (L : Type) [Group L], Prop) : Prop where
  T0 : ∀ (L : Type) [Group L] [Finite L], F L → IsQuasisimple L → CFSG.Open.IsKGroup L →
    ∃ t : L, orderOf t = 2
  T1a : ∀ (L : Type) [Group L] [Finite L], F L → IsQuasisimple L → CFSG.Open.IsKGroup L →
    ∀ p : ℕ, p.Prime → p ≠ 2 →
      pRank p (⊤ : Subgroup (MulAut L)) ≤ pRank p (⊤ : Subgroup L) + 2
  T1b : ∀ (L : Type) [Group L] [Finite L], F L → IsQuasisimple L → CFSG.Open.IsKGroup L →
    ∀ p : ℕ, p.Prime → p ≠ 2 →
      (pRank p (⊤ : Subgroup L) < 7 ∨ p ∣ Nat.card (Subgroup.center L)) →
      pRank p (⊤ : Subgroup (MulAut L)) ≤ pRank p (⊤ : Subgroup L) + 1
  T2 : ∀ (L : Type) [Group L] [Finite L], F L → IsQuasisimple L → CFSG.Open.IsKGroup L →
    ∀ p : ℕ, p.Prime → p ≠ 2 →
      2 * pRank p (Subgroup.center L) ≤ pRank p (⊤ : Subgroup L)
  T3 : ∀ (L : Type) [Group L] [Finite L], F L → IsQuasisimple L → CFSG.Open.IsKGroup L →
    ∀ p : ℕ, p.Prime → p ≠ 2 → IsPGroup p (Subgroup.center L) →
      pRank p (Subgroup.center L) = 1 →
      (p = 3 ∧ Nat.card (Subgroup.center L) = 3) ∨
        p + 2 ≤ (p - 2) * pRank p (⊤ : Subgroup L)
  T11 : ∀ (L : Type) [Group L] [Finite L], F L → IsQuasisimple L → CFSG.Open.IsKGroup L →
    ∀ p : ℕ, p.Prime → p ≠ 2 → IsPGroup p (Subgroup.center L) →
      2 ≤ pRank p (Subgroup.center L) →
      p = 3 ∧ pRank 3 (Subgroup.center L) = 2 ∧ pRank 3 (⊤ : Subgroup L) = 6 ∧
        pRank 3 (⊤ : Subgroup (MulAut L)) ≤ 6
  T9 : ∀ (L : Type) [Group L] [Finite L], F L → IsQuasisimple L → CFSG.Open.IsKGroup L →
    Nat.card (Subgroup.center L) = 1 → pRank 3 (⊤ : Subgroup L) = 2 →
      GLATwoLocalRank 3 L = 0 → pRank 3 (⊤ : Subgroup (MulAut L)) ≤ 2
  TFA_a : ∀ (L : Type) [Group L] [Finite L], F L → IsQuasisimple L → CFSG.Open.IsKGroup L →
    Nat.card (Subgroup.center L) = 1 → pRank 3 (⊤ : Subgroup L) = 1 →
      GLATwoLocalRank 3 L = 1 → ∀ H : Subgroup (MulAut L), IsElemAbelian 3 H →
        Nat.card H = 9 → FieldBonus L 3 H
  TFA_b : ∀ (L : Type) [Group L] [Finite L], F L → IsQuasisimple L → CFSG.Open.IsKGroup L →
    Nat.card (Subgroup.center L) = 3 → pRank 3 (⊤ : Subgroup L) = 2 →
      GLATwoLocalRank 3 L = 1 → ∀ H : Subgroup (MulAut L), IsElemAbelian 3 H →
        Nat.card H = 27 → FieldBonus L 3 H

theorem centralQuotient_family {L : Type} [Group L] [Finite L] (hq : IsQuasisimple L)
    (hK : CFSG.Open.IsKGroup L) :
    AltCentralQuotient L ∨ LieCentralQuotient L ∨ SporCentralQuotient L := by
  obtain ⟨hperf, hsimple⟩ := hq
  have := hsimple
  have hnab : ∃ a b : L ⧸ Subgroup.center L, a * b ≠ b * a := by
    by_contra hab
    push Not at hab
    have hle : commutator L ≤ Subgroup.center L := by
      rw [commutator, Subgroup.commutator_le]
      intro a _ b _
      rw [← QuotientGroup.eq_one_iff, commutatorElement_def]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hab (a : L ⧸ Subgroup.center L) b]
      group
    rw [hperf, top_le_iff] at hle
    have hall : ∀ q : L ⧸ Subgroup.center L, q = 1 := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H x => exact (QuotientGroup.eq_one_iff x).2 (hle ▸ Subgroup.mem_top x)
    obtain ⟨a, b, hab'⟩ := exists_pair_ne (L ⧸ Subgroup.center L)
    exact hab' ((hall a).trans (hall b).symm)
  have hmap : ((Subgroup.center L).subgroupOf (⊤ : Subgroup L)).map
      (Subgroup.topEquiv : (⊤ : Subgroup L) ≃* L).toMonoidHom = Subgroup.center L := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, Subgroup.mem_top x⟩, hx, rfl⟩
  let e : (↥(⊤ : Subgroup L) ⧸ (Subgroup.center L).subgroupOf (⊤ : Subgroup L)) ≃*
      (L ⧸ Subgroup.center L) := QuotientGroup.congr _ _ Subgroup.topEquiv hmap
  have hs' : IsSimpleGroup (↥(⊤ : Subgroup L) ⧸ (Subgroup.center L).subgroupOf (⊤ : Subgroup L)) :=
    e.isSimpleGroup
  have hna' : ∃ a b : ↥(⊤ : Subgroup L) ⧸ (Subgroup.center L).subgroupOf (⊤ : Subgroup L),
      a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this
  obtain ⟨i, ⟨φ⟩⟩ := hK ⊤ (Subgroup.center L) le_top hs' hna'
  let ψ : (L ⧸ Subgroup.center L) ≃* i.Group := e.symm.trans φ
  cases i with
  | cyclic q hq =>
    exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    apply ψ.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  | alternating n hn => exact Or.inl ⟨n, ⟨ψ⟩⟩
  | lie idx => exact Or.inr (Or.inl ⟨idx, ⟨ψ⟩⟩)
  | sporadic name => exact Or.inr (Or.inr ⟨name, ⟨ψ⟩⟩)

theorem tables112_of_families (hA : Tables112On AltCentralQuotient)
    (hL : Tables112On LieCentralQuotient) (hS : Tables112On SporCentralQuotient) : Tables112 := by
  have key : ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L → CFSG.Open.IsKGroup L →
      AltCentralQuotient L ∨ LieCentralQuotient L ∨ SporCentralQuotient L :=
    fun L _ _ hq hK => centralQuotient_family hq hK
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro L _ _ hq hK
    rcases key L hq hK with h | h | h
    · exact hA.T0 L h hq hK
    · exact hL.T0 L h hq hK
    · exact hS.T0 L h hq hK
  · intro L _ _ hq hK
    rcases key L hq hK with h | h | h
    · exact hA.T1a L h hq hK
    · exact hL.T1a L h hq hK
    · exact hS.T1a L h hq hK
  · intro L _ _ hq hK
    rcases key L hq hK with h | h | h
    · exact hA.T1b L h hq hK
    · exact hL.T1b L h hq hK
    · exact hS.T1b L h hq hK
  · intro L _ _ hq hK
    rcases key L hq hK with h | h | h
    · exact hA.T2 L h hq hK
    · exact hL.T2 L h hq hK
    · exact hS.T2 L h hq hK
  · intro L _ _ hq hK
    rcases key L hq hK with h | h | h
    · exact hA.T3 L h hq hK
    · exact hL.T3 L h hq hK
    · exact hS.T3 L h hq hK
  · intro L _ _ hq hK
    rcases key L hq hK with h | h | h
    · exact hA.T11 L h hq hK
    · exact hL.T11 L h hq hK
    · exact hS.T11 L h hq hK
  · intro L _ _ hq hK
    rcases key L hq hK with h | h | h
    · exact hA.T9 L h hq hK
    · exact hL.T9 L h hq hK
    · exact hS.T9 L h hq hK
  · intro L _ _ hq hK
    rcases key L hq hK with h | h | h
    · exact hA.TFA_a L h hq hK
    · exact hL.TFA_a L h hq hK
    · exact hS.TFA_a L h hq hK
  · intro L _ _ hq hK
    rcases key L hq hK with h | h | h
    · exact hA.TFA_b L h hq hK
    · exact hL.TFA_b L h hq hK
    · exact hS.TFA_b L h hq hK

end CFSG.HardMathSupport.Timmesfeld.Coordinator
