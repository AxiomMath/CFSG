module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport

public section

namespace CFSG.HardMathSupport.Cooperstein.Proving

variable {G : Type} [Group G]

theorem pCoreOf_two_conj_mem (X : Subgroup G) {x q : G} (hx : x ∈ X)
    (hq : q ∈ CFSG.Open.pCoreOf 2 X) : x * q * x⁻¹ ∈ CFSG.Open.pCoreOf 2 X := by
  obtain ⟨⟨q', hq'X⟩, hmem, rfl⟩ := Subgroup.mem_map.mp hq
  have hn : (CFSG.Open.pCore 2 X).Normal := by
    exact CFSG.pCore_normal
  have hc := hn.conj_mem _ hmem ⟨x, hx⟩
  exact Subgroup.mem_map.mpr ⟨_, hc, by simp⟩

theorem le_pCoreOf_two_of_normal {Y Q : Subgroup G} (hQY : Q ≤ Y)
    (hQ2 : ∀ q ∈ Q, ∃ k : ℕ, q ^ 2 ^ k = 1)
    (hQc : ∀ y ∈ Y, ∀ q ∈ Q, y * q * y⁻¹ ∈ Q) :
    Q ≤ CFSG.Open.pCoreOf 2 Y := by
  have hN : (Q.subgroupOf Y).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hQc g.1 g.2 _ hn⟩
  have hP : IsPGroup 2 (Q.subgroupOf Y) := by
    intro n
    obtain ⟨k, hk⟩ := hQ2 (n : G) (Subgroup.mem_subgroupOf.mp n.2)
    exact ⟨k, by ext; simpa using hk⟩
  intro x hx
  have hxY : x ∈ Y := hQY hx
  have hmem : (⟨x, hxY⟩ : Y) ∈ CFSG.Open.pCore 2 Y := by
    exact (le_sSup ⟨hN, hP⟩ : Q.subgroupOf Y ≤ CFSG.pCore 2 Y) (Subgroup.mem_subgroupOf.mpr hx)
  exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩

theorem pCoreOf_two_pow_eq_one {X : Subgroup G} {q : G} (hq : q ∈ CFSG.Open.pCoreOf 2 X) :
    ∃ k : ℕ, q ^ 2 ^ k = 1 := by
  obtain ⟨⟨q', hq'X⟩, hmem, rfl⟩ := Subgroup.mem_map.mp hq
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := X) ⟨⟨q', hq'X⟩, hmem⟩
  exact ⟨k, by simpa using congrArg (fun z : ↥(CFSG.pCore 2 X) => ((z : ↥X) : G)) hk⟩

theorem charTwo_of_pCoreOf_le {X Y : Subgroup G} (hX : CFSG.QuasithinUnique.CharTwo X)
    (hQY : CFSG.Open.pCoreOf 2 X ≤ Y) (hYX : Y ≤ X) :
    CFSG.QuasithinUnique.CharTwo Y := CFSG.QuasithinUnique.CharTwo.of_pCoreOf_le hX hYX hQY

end CFSG.HardMathSupport.Cooperstein.Proving

end
