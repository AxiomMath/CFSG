module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceCommon
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245BaumannSetting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathGate6

public section

namespace CFSG.QuasithinUnique.Setup.Lift.Piece

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.BlueprintB2 CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Wreath CFSG.QuasithinUnique.Setup.Campbell
open scoped commutatorElement

theorem adapter_core {G : Type} [Group G] [Finite G] {k : Type} [Field k] [Finite k] [CharP k 2]
    {S P M W : Subgroup G} (hSP : S ≤ P) (hWS : W ≤ S) (hBaum : baum S = S)
    (hP : P = oddOrderSubgroup P ⊔ S) (hchar : CharTwo P)
    (hnc : ∀ C : Subgroup G, C ≤ S → C ≠ ⊥ → (C.subgroupOf S).Characteristic →
      ¬ P ≤ Subgroup.normalizer (C : Set G))
    {n : ℕ} (hn : 1 ≤ n) (hcard : Nat.card k = 2 ^ n)
    (hset : ∃ (ϱ : ↥P →* Gamma k)
        (ψ : ↥(W.subgroupOf P) →* Multiplicative (Fin 2 → k)),
      IsNatQuotSetting (S.subgroupOf P) (M.subgroupOf P) (W.subgroupOf P) ϱ ψ)
    (hJ : ⁅thompsonJ S, W⁆ ≠ ⊥) :
    IsChi0Block P (oddOrderSubgroup P) ∧
      (1 < n → IsLin2Type (oddOrderSubgroup P) n) ∧
      (n = 1 → IsAltType (oddOrderSubgroup P) 3 ∧
        Nonempty (↥(oddOrderSubgroup P) ≃* alternatingGroup (Fin 4)) ∧
        Nat.card (↥(oddOrderSubgroup P) ⧸ CFSG.pCore 2 ↥(oddOrderSubgroup P)) = 3) ∧
      ⁅blockQ P, oddOrderSubgroup P⁆ = ⁅W, oddOrderSubgroup P⁆ ∧
      blockU (oddOrderSubgroup P) = ⁅blockQ P, oddOrderSubgroup P⁆ ∧
      P ⊓ Subgroup.centralizer ((⁅blockQ P, oddOrderSubgroup P⁆ : Subgroup G) : Set G) =
        blockQ P ∧
      Nat.card ↥(⁅blockQ P, oddOrderSubgroup P⁆ : Subgroup G) =
        Nat.card ↥((⁅blockQ P, oddOrderSubgroup P⁆ : Subgroup G) ⊓
          Subgroup.centralizer (P : Set G)) * Nat.card k ^ 2 := by
  classical
  obtain ⟨ϱ, ψ, hset⟩ := hset
  have hWP : W ≤ P := hWS.trans hSP
  have hchar' : CharTwo (⊤ : Subgroup ↥P) := charTwo_top_of_charTwo hchar
  have hnc' : NoCharNormal (S.subgroupOf P) (⊤ : Subgroup ↥P) :=
    noCharNormal_top_of hSP (fun C h1 h2 h3 => hnc C h2 h1 h3)
  have hJ' : ⁅elemThompsonIn 2 (S.subgroupOf P), W.subgroupOf P⁆ ≠ ⊥ := by
    intro hb
    apply hJ
    have h1 := congrArg (Subgroup.map P.subtype) hb
    rwa [Subgroup.map_commutator, C56.elemThompsonIn_subgroupOf_map hSP,
      Subgroup.map_subgroupOf_eq_of_le hWP, Subgroup.map_bot] at h1
  have hGb : baumannOvergroup (S.subgroupOf P) = ⊤ := by
    apply Subgroup.map_injective P.subtype_injective
    rw [baumannOvergroup, Subgroup.map_sup, oddOrderSubgroup_top_map P,
      C56.elemBaumannIn_subgroupOf_map hSP, hBaum, Subgroup.map_top, Subgroup.range_subtype]
    exact hP.symm
  obtain ⟨hchi, hLin, hAlt, hE, hUK, hcent, hcardU⟩ :=
    natural_chi0_block_ext hset hchar' hnc' hJ' hn hcard hGb
  set L' : Subgroup ↥P := oddOrderSubgroup (⊤ : Subgroup ↥P) with hL'
  have hLmap : L'.map P.subtype = oddOrderSubgroup P := oddOrderSubgroup_top_map P
  have hTmap : (⊤ : Subgroup ↥P).map P.subtype = P := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hQmap : blockQ P = (blockQ (⊤ : Subgroup ↥P)).map P.subtype := by
    have := blockQ_map_injective P.subtype P.subtype_injective (⊤ : Subgroup ↥P)
    rwa [hTmap] at this
  have hWmap : (W.subgroupOf P).map P.subtype = W := Subgroup.map_subgroupOf_eq_of_le hWP
  have hUmap : (⁅blockQ (⊤ : Subgroup ↥P), L'⁆ : Subgroup ↥P).map P.subtype =
      ⁅blockQ P, oddOrderSubgroup P⁆ := by
    rw [Subgroup.map_commutator, ← hQmap, hLmap]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := IsChi0Block.map_of_injective P.subtype P.subtype_injective hchi
    rwa [hTmap, hLmap] at this
  · intro hn1
    have := IsLin2Type.map_of_injective P.subtype P.subtype_injective (hLin hn1)
    rwa [hLmap] at this
  · intro hn1
    obtain ⟨hA, ⟨e⟩, hc3⟩ := hAlt hn1
    refine ⟨?_, ⟨?_⟩, ?_⟩
    · have := IsAltType.map_of_injective P.subtype P.subtype_injective hA
      rwa [hLmap] at this
    · exact ((L'.equivMapOfInjective P.subtype P.subtype_injective).trans
        (MulEquiv.subgroupCongr hLmap)).symm.trans e
    · rw [← hLmap, card_quot_pCore_map_injective P.subtype P.subtype_injective L']
      exact hc3
  · have := congrArg (Subgroup.map P.subtype) hE
    rwa [Subgroup.map_commutator, Subgroup.map_commutator, ← hQmap, hLmap, hWmap] at this
  · have h1 := blockU_map_injective P.subtype P.subtype_injective L'
    rw [hLmap] at h1
    rw [h1, hUK, hUmap]
  · have h1 := map_inf_centralizer_map P.subtype P.subtype_injective (U := (⊤ : Subgroup ↥P))
      (L := (⁅blockQ (⊤ : Subgroup ↥P), L'⁆ : Subgroup ↥P))
    rw [hcent, hTmap, hUmap, ← hQmap] at h1
    exact h1
  · have h1 := map_inf_centralizer_map P.subtype P.subtype_injective (U := (⁅blockQ (⊤ : Subgroup ↥P), L'⁆ : Subgroup ↥P))
      (L := (⊤ : Subgroup ↥P))
    rw [hTmap, hUmap] at h1
    have e1 : Nat.card ↥(⁅blockQ P, oddOrderSubgroup P⁆ : Subgroup G) =
        Nat.card ↥(⁅blockQ (⊤ : Subgroup ↥P), L'⁆ : Subgroup ↥P) := by
      rw [← hUmap]
      exact Subgroup.card_map_of_injective P.subtype_injective
    have e2 : Nat.card ↥((⁅blockQ P, oddOrderSubgroup P⁆ : Subgroup G) ⊓
        Subgroup.centralizer (P : Set G)) =
        Nat.card ↥((⁅blockQ (⊤ : Subgroup ↥P), L'⁆ : Subgroup ↥P) ⊓
          Subgroup.centralizer ((⊤ : Subgroup ↥P) : Set ↥P)) := by
      rw [h1]
      exact Subgroup.card_map_of_injective P.subtype_injective
    rw [e1, e2]
    exact hcardU

end CFSG.QuasithinUnique.Setup.Lift.Piece
