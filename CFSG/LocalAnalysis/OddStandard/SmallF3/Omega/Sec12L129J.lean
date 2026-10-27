module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L129
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L129JA1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L129JA2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L129JBase
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Steps

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Open CFSG.Blueprint

theorem asc82Lemma129J_of (hp : Asc82Pre11) (h122 : Asc82Lemma122) (h124 : Asc82Lemma124)
    (h125a : Asc82Lemma125a) (h128 : Asc82Lemma128) : Asc82Lemma129J := by
  intro G _ _ t L S z K1 K2 E hctx R0 hSR0 hR0
  have hV : IsElemAb2 (secV t S L E) 8 := h124 G t L S z K1 K2 E hctx
  have hCV : centralizer (secV t S L E : Set G) =
      secV t S L E ⊔ oddCoreIn (secN (secV t S L E)) := h125a G t L S z K1 K2 E hctx
  obtain ⟨X, hX⟩ := h122 G t L S z K1 K2 E hctx
  have hΩ := h128 G t L S z K1 K2 E X hctx hX
  have hbd := sec10BData_of hp.basic hp.facts.b5 hctx.toSec10Z
  set V := secV t S L E with hVdef
  have hV2 : ∀ v ∈ V, v * v = 1 := fun v hv => by
    rw [← pow_two]
    exact hV.1.2 v hv
  have hO : oddCoreIn (secN V) ≤ centralizer (V : Set G) := by
    rw [hCV]
    exact le_sup_right
  have hVO : ∀ v ∈ V, ∀ o ∈ oddCoreIn (secN V), v * o = o * v := fun v hv o ho =>
    Subgroup.mem_centralizer_iff.mp (hO ho) v hv
  have hC : ∀ g ∈ centralizer (V : Set G), (∃ m : ℕ, g ^ (2 ^ m) = 1) → g ∈ V :=
    fun g hg hg2 => sec12J_twoElem_mem hV2 hVO (fun o ho => sec10L104_odd_orderOf ho)
      (hCV ▸ hg) hg2
  have hmain : ∀ F : Subgroup G, F ≤ secN V → IsElemAbelian 2 F → F ≤ V ∨ Nat.card F ≤ 128 := by
    intro F hFN hF
    rcases hΩ with h1 | h2
    · exact sec12J_main_alt1 hbd hV hC hO h1 hFN hF
    · exact sec12J_main_alt2 hC h2 hFN hF
  have hVR0 : V ≤ R0 := sec12J_V_le_sylow hV.1.isPGroup hR0
  have hR0N : R0 ≤ secN V := hR0.1
  have hVmax : ∀ A : Subgroup G, A ≤ R0 → IsElemAbelian 2 A → Nat.card A ≤ Nat.card V := by
    intro A hA hAel
    rcases hmain A (hA.trans hR0N) hAel with h | h
    · exact Subgroup.card_le_of_le h
    · rw [hV.2]
      omega
  apply le_antisymm
  · rw [JElem]
    refine (Subgroup.closure_le V).mpr ?_
    rintro x ⟨A, hAmax, hxA⟩
    have hAle : A ≤ R0 := hAmax.1
    have hAel : IsElemAbelian 2 A := hAmax.2.1
    have hcardVA : Nat.card V ≤ Nat.card A := hAmax.2.2 V hVR0 hV.1
    rcases hmain A (hAle.trans hR0N) hAel with h | h
    · exact h hxA
    · rw [hV.2] at hcardVA
      omega
  · rw [JElem]
    intro v hv
    exact Subgroup.subset_closure ⟨V, ⟨hVR0, hV.1, hVmax⟩, hv⟩

end CFSG.OddStandard.SmallF3.Omega
