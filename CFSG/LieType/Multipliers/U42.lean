module

public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.Blueprint.Catalog
public import Certificates.Certificate10010
public meta import CFSG.LieType.Multipliers.U42Data
public meta import CFSG.Certificates.CosetTableOrders

public section

namespace CFSG.LieType.Multipliers.U42

open CFSG.GH74.Exceptional CFSG.Assembly.LowTwoRank CFSG.Fischer CFSG.Fischer.Classification
  CFSG.CosetTable

theorem nonempty_mulEquiv_PSp43 {X : Type} [Group X] (h : CFSG.Blueprint.LieModel X .PSU 4 2 1) :
    Nonempty (X ≃* PSp43) := by
  rcases h with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
    have : Fintype K := Fintype.ofFinite K
    have : Fintype Blueprint.Fischer.K := Fintype.ofFinite _
    have hc : Fintype.card K = Fintype.card Blueprint.Fischer.K := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, Unitary.card_K]
    exact ⟨(e.trans (Recognition.statedProjSUEquiv (FiniteField.ringEquivOfCardEq hc) 4
      (2 ^ 1))).trans (u2FourEquiv.symm.trans psp43EquivU2.symm)⟩
  all_goals exact absurd h0 (by norm_num)

theorem cover_bounds :
    Finite (PG 2 (coverWords rels fun i => commWords (coverPairs i))) ∧
      Nat.card (PG 2 (coverWords rels fun i => commWords (coverPairs i))) ≤ 51840 ∧
      2 ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin 2) | r ∈ (coverWords rels
        fun i => commWords (coverPairs i)).map FreeGroup.mk} (FreeGroup.mk relZ)) :=
  Certificates.certificate10010

theorem multiplier_PSU_four_two
    (X : Type) [Group X]
    (h : CFSG.Blueprint.LieModel X .PSU 4 2 1) :
    commutator X = ⊤ ∧ Nonempty (CFSG.Open.griessHopfMultiplier X ≃* Multiplicative (ZMod 2)) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_PSp43 h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hperf, hM⟩ := multiplier_eq_zmod_of_bounds (isPresentation_PSp43.mulEquiv e.symm)
    coverPairs (fun i => by rw [lift_mulEquiv, commWord_eval]) (by simp [rels]) cover_bounds.1
    cover_bounds.2.1 cover_bounds.2.2 (by rw [Nat.card_congr e.toEquiv, card_PSp43])
  exact ⟨hperf.commutator_eq_top, hM⟩

end CFSG.LieType.Multipliers.U42
