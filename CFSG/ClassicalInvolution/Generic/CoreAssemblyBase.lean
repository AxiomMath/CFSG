module

public import CFSG.ClassicalInvolution.Generic.StepMember
public import CFSG.ClassicalInvolution.Reduction
public import CFSG.ClassicalInvolution.RouteD.GenerationA
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Generic.CoreAssembly

open CFSG.Open

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

abbrev conjClass (K : Subgroup G) : Set (Subgroup G) :=
  Set.range fun g : G => conjSub g K

theorem mem_conjClass_self (K : Subgroup G) : K ∈ conjClass K :=
  ⟨1, conjSub_one K⟩

theorem conjugateSet_eq_range (K : Subgroup G) :
    CFSG.ClassicalInvolution.conjugateSet K = conjClass K := by
  ext A
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g⁻¹, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g⁻¹, by simp [conjSub]⟩

theorem single_class (K : Subgroup G) : ∀ L ∈ conjClass K, ∃ g : G, L = conjSub g K :=
  fun _ ⟨g, hg⟩ => ⟨g, hg.symm⟩

theorem exists_single_class (K : Subgroup G) :
    ∃ K' ∈ conjClass K, ∀ L ∈ conjClass K, ∃ g : G, L = conjSub g K' :=
  ⟨K, mem_conjClass_self K, single_class K⟩

theorem deltaConnected_iff (K : Subgroup G) :
    CFSG.ClassicalInvolution.DeltaConnected K ↔
      CFSG.ClassicalInvolution.RouteD.DeltaConnected (conjClass K) := by
  classical
  rw [CFSG.ClassicalInvolution.DeltaConnected, CFSG.ClassicalInvolution.RouteD.DeltaConnected]
  constructor
  · intro h
    have : Nonempty (conjClass K) := ⟨⟨K, mem_conjClass_self K⟩⟩
    refine ⟨fun u v => ?_⟩
    have hu : (u : Subgroup G) ∈ CFSG.ClassicalInvolution.conjugateSet K := by
      rw [conjugateSet_eq_range]; exact u.2
    have hv : (v : Subgroup G) ∈ CFSG.ClassicalInvolution.conjugateSet K := by
      rw [conjugateSet_eq_range]; exact v.2
    have key : ∀ B : Subgroup G, Relation.ReflTransGen
        (CFSG.ClassicalInvolution.commutingAdj K) (u : Subgroup G) B →
        ∀ hB : B ∈ conjClass K, (SimpleGraph.Reachable
          (CFSG.ClassicalInvolution.Models.commGraph (conjClass K)) u ⟨B, hB⟩) := by
      intro B hB
      induction hB with
      | refl => intro hB'; exact SimpleGraph.Reachable.refl _
      | @tail b c _ hbc ih =>
        intro hc
        obtain ⟨hb, -, hne, hcomm⟩ := hbc
        have hb' : b ∈ conjClass K := by rw [← conjugateSet_eq_range]; exact hb
        refine (ih hb').trans (SimpleGraph.Adj.reachable ?_)
        rw [CFSG.ClassicalInvolution.Models.commGraph_adj]
        exact ⟨fun e => hne (congrArg Subtype.val e), hcomm⟩
    exact key v (h u hu v hv) v.2
  · intro h A hA B hB
    rw [conjugateSet_eq_range] at hA hB
    have hreach := h.preconnected ⟨A, hA⟩ ⟨B, hB⟩
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    have key : ∀ v : conjClass K, Relation.ReflTransGen
        (CFSG.ClassicalInvolution.Models.commGraph (conjClass K)).Adj ⟨A, hA⟩ v →
        Relation.ReflTransGen (CFSG.ClassicalInvolution.commutingAdj K) A (v : Subgroup G) := by
      intro v hv
      induction hv with
      | refl => exact Relation.ReflTransGen.refl
      | @tail b c _ hbc ih =>
        refine ih.tail ?_
        obtain ⟨hne, hcomm⟩ := (CFSG.ClassicalInvolution.Models.commGraph_adj).mp hbc
        refine ⟨?_, ?_, fun e => hne (Subtype.ext e), hcomm⟩
        · rw [conjugateSet_eq_range]; exact b.2
        · rw [conjugateSet_eq_range]; exact c.2
    exact key ⟨B, hB⟩ hreach

section Member

variable {K : Subgroup G} {z : G}

omit [Fact p.Prime] in
theorem pos_of_five_le (hq : 5 ≤ p ^ f) : 0 < f := by
  rcases Nat.eq_zero_or_pos f with rfl | h
  · simp at hq
  · exact h

theorem witness_of_isClassicalMember (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (h : IsClassicalMember p f K z) : classicalInvolutionWitness K :=
  Or.inl ⟨p, f, inferInstance, hp2, pos_of_five_le hq, h.nonempty_equiv⟩

theorem not_isSolvable_of_isClassicalMember (h : IsClassicalMember p f K z) :
    ¬ Group.IsSolvable K := by
  have : Group.IsPerfect K := h.perfect
  have : Nontrivial K := ⟨⟨⟨z, h.mem⟩, 1, fun e => h.ne_one (congrArg Subtype.val e)⟩⟩
  exact Group.IsPerfect.not_isSolvable K

end Member

section Simple

variable [IsSimpleGroup G]

theorem center_eq_bot (hnab : ∃ x y : G, x * y ≠ y * x) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    obtain ⟨x, y, hxy⟩ := hnab
    have hx : x ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top x
    exact hxy ((Subgroup.mem_center_iff.mp hx y).symm)

theorem singleton_not_subset_center (hnab : ∃ x y : G, x * y ≠ y * x) {z : G} (hz : z ≠ 1) :
    ¬ ({z} : Set G) ⊆ Subgroup.center G := by
  intro h
  have : z ∈ Subgroup.center G := h (Set.mem_singleton z)
  rw [center_eq_bot hnab, Subgroup.mem_bot] at this
  exact hz this

end Simple

end CFSG.ClassicalInvolution.Generic.CoreAssembly
