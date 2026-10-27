module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Classes
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS

theorem isDoubleCoverOfAlt_of_ker {K : Type} [Group K] {n : ℕ} (hn : 5 ≤ n)
    (hperf : Group.IsPerfect K) (ρ : K →* alternatingGroup (Fin n)) (hρ : Function.Surjective ρ)
    (hkc : ρ.ker ≤ center K) (hk2 : Nat.card ρ.ker = 2) : IsDoubleCoverOfAlt K n := by
  have hcard : 5 ≤ Nat.card (Fin n) := by simpa using hn
  have hsimple : IsSimpleGroup (alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup hcard
  have hcenter : center K = ρ.ker := by
    refine le_antisymm ?_ hkc
    intro c hc
    rw [MonoidHom.mem_ker]
    have h1 : ρ c ∈ center (alternatingGroup (Fin n)) := by
      rw [mem_center_iff]
      intro a
      obtain ⟨u, rfl⟩ := hρ a
      rw [← map_mul, ← map_mul, mem_center_iff.1 hc u]
    rw [alternatingGroup.center_eq_bot (by omega), mem_bot] at h1
    exact h1
  let e : K ⧸ center K ≃* alternatingGroup (Fin n) :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρ hρ)
  refine ⟨⟨hperf, e.isSimpleGroup, ?_⟩, ?_, ⟨e⟩⟩
  · have h4 : 4 ≤ Nat.card (Fin n) := by simpa using (by omega : 4 ≤ n)
    by_contra hcon
    push Not at hcon
    have hcomm : ∀ a b : alternatingGroup (Fin n), a * b = b * a := fun a b => by
      have := hcon (e.symm a) (e.symm b)
      simpa using congrArg e this
    have htop : center (alternatingGroup (Fin n)) = ⊤ := by
      ext a
      simp only [mem_top, iff_true]
      rw [mem_center_iff]
      intro b
      exact hcomm b a
    rw [alternatingGroup.center_eq_bot h4] at htop
    obtain ⟨g, hg⟩ := exists_ne (1 : alternatingGroup (Fin n))
    have hgb : g ∈ (⊥ : Subgroup (alternatingGroup (Fin n))) := htop ▸ mem_top g
    exact hg (mem_bot.1 hgb)
  · rw [hcenter]
    exact hk2

theorem natCard_alternatingGroup_fin {k : ℕ} (hk : 2 ≤ k) :
    Nat.card (alternatingGroup (Fin k)) = k.factorial / 2 := by
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.2 hk
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]

end CFSG.OddStandard.Solomon75
