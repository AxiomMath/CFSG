module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootMain
public import CFSG.LocalAnalysis.OddStandard.AltStdSecGenMain
public import CFSG.LocalAnalysis.OddStandard.AltStdSecWreathMain
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.OddStandard.AltStdBalCaseO

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal
open CFSG.ComponentClassification.RestrictedStd.Spor

theorem false_of_inner_ge_twelve (hlookup : AltComponentLookup) (hHN : HNLocalComponentsInput)
    (hFour : FourExactOuterInput) {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ}
    {Q : Subgroup G} {z : G} (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (hE : centralizer ({z} : Set G) ≤ L ⊔ Q) (hn : 12 ≤ n) : False := by
  obtain ⟨e⟩ := h.iso
  have hF := fusionAll_of_shape_one' hlookup hHN hFour h d hQ2 hE hn
  let S₀ : Finset (Fin n) := {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩}
  have hS₀ : S₀.card = 3 := by
    simp only [S₀]
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · simp [Fin.ext_iff]
    · simp [Fin.ext_iff]
  have hIII : CaseIIIAt e z S₀ :=
    wreath_of_fusionAll hlookup hHN hFour h d hQ2 hE e hn hF (Or.inl hS₀) (by omega)
  obtain ⟨H, hH⟩ := stageMRootStmt G L n Q z h d hQ2 e hn S₀ hS₀ hIII
  exact false_of_wreathPair h d hQ2 hE hH

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

theorem altStdBalancedOrder2Inner_ge_twelve (hlookup : AltComponentLookup)
    (hHN : HNLocalComponentsInput) (hFour : FourExactOuterInput) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
      ∀ n : ℕ, 12 ≤ n → Nonempty (L ≃* alternatingGroup (Fin n)) →
        ∀ S : Sylow 2 (centralizer (L : Set G)),
          IsCyclic (S : Subgroup (centralizer (L : Set G))) → Nat.card S = 2 →
            (∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥) →
            (∀ z : G, z ∈ centralizer (L : Set G) → orderOf z = 2 →
              centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G)) → False := by
  intro G _ _ L hS n hn hθ S hcyc h2 hbal hinner
  have h : Setting G L n := ⟨hS, by omega, hθ, ⟨S, hcyc⟩, hbal⟩
  obtain ⟨z, d⟩ := Cyc.of_sylow h S hcyc
  have hQ2 : Nat.card (sylowSub S) = 2 := (card_sylowSub S).trans h2
  have hE : centralizer ({z} : Set G) ≤ L ⊔ sylowSub S := fun c hc =>
    mem_sup_of_mem_sup_centralizer h d hc (hinner z (d.le d.mem) d.order hc)
  exact false_of_inner_ge_twelve hlookup hHN hFour h d hQ2 hE hn

end CFSG.OddStandard.AltStdSec
