module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3Coexist
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi23Row

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction.Fi.V3

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78

@[expose] def Fi23TwoSylowMax : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (N L K : Subgroup H) (t u : H), FStarSimple N → N.index ≤ 2 →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → OddCover .Fi23 L →
      SolomonGlobalQ H L K t u → fiLoc (2 * 64561751654400) H L K u →
        ∀ S : Sylow 2 (centralizer (L : Set H)), Nat.card S = 2

@[expose] def Fi23ClaimMax : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (N L K : Subgroup H) (t u : H), FStarSimple N → N.index ≤ 2 →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → OddCover .Fi23 L →
      SolomonGlobalQ H L K t u → fiLoc (2 * 64561751654400) H L K u → Fi23Transposition L u →
        (∃ L₀ : Subgroup H, SolStd L₀ ∧ OddCover .Fi24Prime L₀) →
          (∀ P : Subgroup H, InL P → IsSporadic (↥P ⧸ center ↥P) .Fi23 → Maximal P) →
            (∀ S : Sylow 2 (centralizer (L : Set H)), Nat.card S = 2) →
              ∀ a : H, a ∈ L → orderOf a = 2 → (¬ ∃ l ∈ L, a = l * u * l⁻¹) → ¬ IsConj t (t * a)

@[expose] def Fi23ClaimMaxAt (H : Type) [Group H] [Finite H] : Prop :=
  ∀ (N L K : Subgroup H) (t u : H), FStarSimple N → N.index ≤ 2 →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → OddCover .Fi23 L →
      SolomonGlobalQ H L K t u → fiLoc (2 * 64561751654400) H L K u → Fi23Transposition L u →
        (∃ L₀ : Subgroup H, SolStd L₀ ∧ OddCover .Fi24Prime L₀) →
          (∀ P : Subgroup H, InL P → IsSporadic (↥P ⧸ center ↥P) .Fi23 → Maximal P) →
            (∀ S : Sylow 2 (centralizer (L : Set H)), Nat.card S = 2) →
              ∀ a : H, a ∈ L → orderOf a = 2 → (¬ ∃ l ∈ L, a = l * u * l⁻¹) → ¬ IsConj t (t * a)

@[expose] def Fi23ClaimMaxHered : Prop :=
  ∀ (H : Type) [Group H] [Finite H], Balance.UHered H → Fi23ClaimMaxAt H

@[expose] def Fi23TailMaxAt (H : Type) [Group H] [Finite H] : Prop :=
  ∀ (N L K : Subgroup H) (t u : H), FStarSimple N → N.index ≤ 2 →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → OddCover .Fi23 L →
      SolomonGlobalQ H L K t u → fiLoc (2 * 64561751654400) H L K u →
        (∀ S : Sylow 2 (centralizer (L : Set H)), Nat.card S = 2) → t ∉ N →
          IsSporadic ↥N .Fi24Prime

@[expose] def Fi23TailMaxHered : Prop :=
  ∀ (H : Type) [Group H] [Finite H], Balance.UHered H → Fi23TailMaxAt H

section CertificatesCard

theorem fi23Transposition_of_fiLoc {H : Type} [Group H] [Finite H] {L K : Subgroup H} {u : H}
    (hL : IsSporadic ↥L .Fi23) (hfi : fiLoc (2 * 64561751654400) H L K u) :
    Fi23Transposition L u := by
  obtain ⟨huL, hu2, hKL, hKu, -, hcard⟩ := hfi
  refine ⟨huL, hu2, le_antisymm (fi23_card_inf_centralizer_le hL huL hu2) ?_⟩
  have h1 : Nat.card (↥K ⧸ CFSG.oddCore ↥K) ≤ Nat.card ↥K :=
    Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective
  have h2 : K ≤ L ⊓ Subgroup.centralizer ({u} : Set H) := fun k hk =>
    ⟨hKL hk, Subgroup.mem_centralizer_singleton_iff.2 (hKu k hk)⟩
  have h3 := Subgroup.card_le_of_le h2
  omega

end CertificatesCard

section Certificates

theorem fi23CloseCoexistAt_of_inputs (hmult : OddMultTrivial .Fi23) (h63 : Fi23Lemma63)
    (h65 : Balance.Sol78Lemma65KP) (hS2 : Fi23TwoSylowMax) {H : Type} [Group H] [Finite H]
    (hBal : Fi23BalanceAt H) (hE : Fi23ClaimMaxAt H) (hTail : Fi23TailMaxAt H) :
    Fi23CloseCoexistAt H := by
  intro N L K t u hN hidx hKP hcoex hmax hcov hglob hfi
  obtain ⟨e⟩ := hcov.isSporadic_of_mult hmult
  have hS : ∀ S : Sylow 2 (centralizer (L : Set H)), Nat.card S = 2 :=
    hS2 H N L K t u hN hidx hKP hcov hglob hfi
  have hbal := hBal N L hN hidx hKP hglob.standardL hcov hS t hglob.t_mem hglob.t_order
  have hs : Setting612 H L t :=
    fi23_setting612 hmult hcov hglob.standardL hglob.t_mem hglob.t_order hbal
  have hT : Fi23Transposition L u := fi23Transposition_of_fiLoc ⟨e⟩ hfi
  have hclaim := hE N L K t u hN hidx hKP hcov hglob hfi hT hcoex hmax hS
  obtain ⟨W, hW⟩ := fi23_exists_out_of_setting hN hs hT (h63 H L ⟨e⟩)
    (fun g => h63 H _ (fi23_isSporadic_map_conj ⟨e⟩ g)) hKP h65 hclaim
  obtain ⟨M, hMn, hM2, htM⟩ := fi23_exists_normal_index_two hW
  have hNM : N ≤ M := fi23_le_of_normal_index_two hN hMn hM2
  have htN : t ∉ N := fun h => htM (hNM h)
  exact ⟨⟨e⟩, hTail N L K t u hN hidx hKP hcov hglob hfi hS htN⟩

theorem fiCoexistMax_of_atlas (ho : FiOrders)
    (row : Stage3Row [.Fi23, .Fi24Prime] (fun _ => fiLoc (2 * 64561751654400)))
    (h31 : FiHyp31Max row.IsK) (hmult : OddMultTrivial .Fi23) (h63 : Fi23Lemma63)
    (h65 : Balance.Sol78Lemma65KP) (hS2 : Fi23TwoSylowMax) (hBal : Fi23BalanceHered)
    (hE : Fi23ClaimMaxHered) (hTail : Fi23TailMaxHered) : FiCoexistMax :=
  fiCoexistMax_of_inputs ho row h31 fun H _ _ hH =>
    fi23CloseCoexistAt_of_inputs hmult h63 h65 hS2 (hBal H hH) (hE H hH) (hTail H hH)

end Certificates

end CFSG.EvenSporadicStandard.Induction.Fi.V3
