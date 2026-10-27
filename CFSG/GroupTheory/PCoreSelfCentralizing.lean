module

public import CFSG.Open.LocalVocabulary
import CFSG.LieType.BorelTits.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer

public section

namespace CFSG.GroupTheory

open CFSG.Open Subgroup

variable {G : Type*} [Group G] {p : ℕ}

theorem pCoreOf_ne_bot_of_inf_centralizer_le {P : Subgroup G}
    (hP : P ⊓ centralizer (pCoreOf p P : Set G) ≤ pCoreOf p P) (hne : P ≠ ⊥) :
    pCoreOf p P ≠ ⊥ := fun h => hne (eq_bot_iff.mpr fun x hx => by
  have := hP ⟨hx, mem_centralizer_iff.mpr fun y hy => by simp [h] at hy; simp [hy]⟩
  rwa [h] at this)

theorem centralizer_pCoreOf_le_of_normalizer_le {P : Subgroup G}
    (hP : P ⊓ centralizer (pCoreOf p P : Set G) ≤ pCoreOf p P)
    (hN : normalizer (pCoreOf p P : Set G) ≤ P) :
    centralizer (pCoreOf p P : Set G) ≤ pCoreOf p P :=
  fun _ hx => hP ⟨hN (centralizer_le_normalizer _ hx), hx⟩

theorem pCoreOf_normalizer_pCoreOf_eq [Finite G] [Fact p.Prime] (S : Sylow p G)
    {X : Subgroup G} (hSX : (S : Subgroup G) ≤ X) :
    pCoreOf p (normalizer (pCoreOf p X : Set G)) = pCoreOf p X := by
  have hXY : X ≤ normalizer (pCoreOf p X : Set G) := LieType.BorelTits.le_normalizer_pCoreOf p X
  have hYS : pCoreOf p (normalizer (pCoreOf p X : Set G)) ≤ S := by
    have h0 := CFSG.fitting_pCore_le_sylow (S.subtype (hSX.trans hXY))
    rw [Sylow.coe_subtype] at h0
    exact (map_mono h0).trans (by rw [subgroupOf_map_subtype]; exact inf_le_left)
  refine le_antisymm ?_
    (LieType.BorelTits.le_pCoreOf_normalizer p _ (LieType.BorelTits.pCoreOf_isPGroup p X))
  exact LieType.BorelTits.le_pCoreOf_of_le_normalizer p (hYS.trans hSX)
    (hXY.trans (LieType.BorelTits.le_normalizer_pCoreOf p _))
    (LieType.BorelTits.pCoreOf_isPGroup p _)

theorem pCoreOf_ne_bot_and_centralizer_le_of_isSimpleGroup [Finite G] [Fact p.Prime]
    (hG : IsSimpleGroup G) (S : Sylow p G)
    (h : ∀ Y : Subgroup G, normalizer ((S : Subgroup G) : Set G) ≤ Y → Y ≠ ⊤ →
      Y ⊓ centralizer (pCoreOf p Y : Set G) ≤ pCoreOf p Y)
    {X : Subgroup G} (hX : normalizer ((S : Subgroup G) : Set G) ≤ X) (hXt : X ≠ ⊤) :
    pCoreOf p X ≠ ⊥ ∧ centralizer (pCoreOf p X : Set G) ≤ pCoreOf p X := by
  have hSX : (S : Subgroup G) ≤ X := le_normalizer.trans hX
  have hXb : X ≠ ⊥ := by
    rintro rfl
    have hS : (S : Subgroup G) = ⊥ := le_bot_iff.1 hSX
    have hN : normalizer ((⊥ : Subgroup G) : Set G) = ⊤ := normalizer_eq_top ⊥
    rw [hS, hN] at hX
    exact hXt (top_le_iff.1 hX)
  have h1 := pCoreOf_ne_bot_of_inf_centralizer_le (h X hX hXt) hXb
  have hXY : X ≤ normalizer (pCoreOf p X : Set G) := LieType.BorelTits.le_normalizer_pCoreOf p X
  have hYt : normalizer (pCoreOf p X : Set G) ≠ ⊤ := by
    intro hY
    have := hG
    have hn := normalizer_eq_top_iff.1 hY
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pCoreOf p X) with h0 | h0
    · exact h1 h0
    · exact hXt (top_le_iff.1 (h0.ge.trans (LieType.BorelTits.pCoreOf_le p X)))
  have hYX := pCoreOf_normalizer_pCoreOf_eq S hSX
  refine ⟨h1, ?_⟩
  have h3 := centralizer_pCoreOf_le_of_normalizer_le (h _ (hX.trans hXY) hYt) (by rw [hYX])
  rwa [hYX] at h3

end CFSG.GroupTheory
