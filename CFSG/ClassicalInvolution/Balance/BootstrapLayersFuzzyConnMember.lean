module

public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyClass
public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyEdge

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
open CFSG.ClassicalInvolution.Balance.Theorem5
  (MemberAdj FuzzyMemberConn FuzzyEdgeInFrame FuzzyVertexConn fuzzyVertexConn_of_adj conjMembers
    commuteAdj fuzzyMemberConn_conjMembers)
open scoped commutatorElement

section Adjacency

@[expose] def ActsTrivOnQuot {H : Type} [Group H] (J : Subgroup H) (a : H) : Prop :=
  a ∈ Subgroup.normalizer (J : Set H) ∧ ∀ x ∈ J, ⁅a, x⁆ ∈ oddCoreIn J

theorem mem_trivialOnQuot_iff_actsTrivOnQuot {H : Type} [Group H] [Finite H]
    {J : Subgroup H} {a : H} :
    a ∈ trivialOnQuot J ↔ ActsTrivOnQuot J a :=
  mem_trivialOnQuot_iff

@[expose] def tqAdj (p f : ℕ) [Fact p.Prime] : MemberAdj :=
  fun {H} _ M N => ∃ a u : H, IsClassicalMember p f M a ∧ IsClassicalMember p f N u ∧
    ActsTrivOnQuot M u ∧ ActsTrivOnQuot N a

end Adjacency

section Member

variable {p f : ℕ} [Fact p.Prime]

theorem fuzzyMemberConn_canonClass : FuzzyMemberConn p f (canonClass p f) (tqAdj p f) := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  obtain ⟨hcls, hc⟩ := fuzzyMemberConn_conjMembers G hnab hp2 hq K z hz hBelow hconn hind
  refine ⟨?_, ?_⟩
  · rintro _ ⟨M, -, w, hw, rfl⟩
    exact ⟨w, isClassicalMember_canonMember hw⟩
  · rintro _ ⟨M, hM, zM, hzM, rfl⟩ _ ⟨M', hM', zM', hzM', rfl⟩
    have key : ∀ X, Relation.ReflTransGen
        (fun A B : Subgroup G => B ∈ conjMembers K ∧ commuteAdj A B) M X →
        X ∈ conjMembers K ∧ ∀ zX, IsClassicalMember p f X zX →
          Relation.ReflTransGen
            (fun A B : Subgroup G => B ∈ canonClass p f K ∧ tqAdj p f A B)
            (canonMember M zM) (canonMember X zX) := by
      intro X hX
      induction hX with
      | refl =>
        refine ⟨hM, fun zX hzX => ?_⟩
        have : zX = zM := hzM.eq_of_isCentralInvolution hp2 hf hzX.isCentralInvolution
        rw [this]
      | @tail b c _ hbc ih =>
        obtain ⟨hbK, ih⟩ := ih
        refine ⟨hbc.1, fun zc hzc => ?_⟩
        obtain ⟨zb, hzb⟩ := hcls b hbK
        obtain ⟨h1, h2⟩ := mem_trivialOnQuot_canonMember_of_commutes hzb hzc hbc.2
        exact (ih zb hzb).tail ⟨canonMember_mem_canonClass hbc.1 hzc, zb, zc,
          isClassicalMember_canonMember hzb, isClassicalMember_canonMember hzc,
          mem_trivialOnQuot_iff_actsTrivOnQuot.mp h1, mem_trivialOnQuot_iff_actsTrivOnQuot.mp h2⟩
    exact (key M' (hc M hM M' hM')).2 zM' hzM'

theorem fuzzyVertexConn_canonClass
    (hedge : FuzzyEdgeInFrame p f (canonClass p f) (tqAdj p f)) :
    FuzzyVertexConn p f (canonClass p f) :=
  fuzzyVertexConn_of_adj fuzzyMemberConn_canonClass hedge

end Member

end CFSG.ClassicalInvolution.Balance.Bootstrap
