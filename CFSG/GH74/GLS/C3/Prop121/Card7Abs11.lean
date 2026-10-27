module

public import CFSG.GH74.GLS.C3.Prop121.Card7Abs10

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
open CFSG.ShultStronglyClosedTI.InvolutionCounting

namespace Ctx

variable {G : Type} [Group G] [Finite G] {C : Ctx G}

theorem thompson_fwd (hF : FFacts) (hH : HFacts) (Y : C.Y1) (v : ↥(centralizer ({C.s} : Set G)))
    (hpart : ∀ p ∈ thompsonPairs C.xG Y.yG v, p.1 ∈ centralizer ({v} : Set _) ∧
      p.2 ∈ centralizer ({v} : Set _))
    {p : ↥(centralizer ({C.s} : Set G)) × ↥(centralizer ({C.s} : Set G))}
    (hp : p ∈ thompsonPairs C.xG Y.yG v) :
    (p.1 : G) ∈ centralizer ({(v : G)} : Set G) ∧ (p.2 : G) ∈ centralizer ({(v : G)} : Set G) ∧
      (p.1 : G) ∈ C.Acl ∧ (p.2 : G) ∈ C.Bcl ∧ (v : G) ∈ zpowers ((p.1 : G) * (p.2 : G)) := by
  obtain ⟨hc1, hc2⟩ := hpart p hp
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨?_, ?_, (isConj_xG_iff hF hH Y p.1).1 h1, (isConj_yG_iff hF hH Y p.2).1 h2, ?_⟩
  · exact mem_centralizer_singleton_iff.2 (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hc1))
  · exact mem_centralizer_singleton_iff.2 (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hc2))
  · obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h3
    exact mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem thompson_bwd (hF : FFacts) (hH : HFacts) (Y : C.Y1) (v : ↥(centralizer ({C.s} : Set G)))
    {g1 g2 : G} (hg1 : g1 ∈ centralizer ({C.s} : Set G)) (hg2 : g2 ∈ centralizer ({C.s} : Set G))
    (h1 : g1 ∈ C.Acl) (h2 : g2 ∈ C.Bcl) (hz : (v : G) ∈ zpowers (g1 * g2)) :
    ((⟨g1, hg1⟩, ⟨g2, hg2⟩) : ↥(centralizer ({C.s} : Set G)) × ↥(centralizer ({C.s} : Set G))) ∈
      thompsonPairs C.xG Y.yG v := by
  refine ⟨(isConj_xG_iff hF hH Y ⟨g1, hg1⟩).2 h1, (isConj_yG_iff hF hH Y ⟨g2, hg2⟩).2 h2, ?_⟩
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hz
  exact mem_zpowers_iff.2 ⟨k, Subtype.ext (by simpa using hk)⟩

theorem thompson_card_eq (hF : FFacts) (hH : HFacts) (Y : C.Y1)
    (v : ↥(centralizer ({C.s} : Set G)))
    (hpart : ∀ p ∈ thompsonPairs C.xG Y.yG v, p.1 ∈ centralizer ({v} : Set _) ∧
      p.2 ∈ centralizer ({v} : Set _)) :
    Nat.card ↥(thompsonPairs C.xG Y.yG v) =
      Nat.card {p : G × G // p.1 ∈ centralizer ({(v : G)} : Set G) ∧
        p.2 ∈ centralizer ({(v : G)} : Set G) ∧ p.1 ∈ C.Acl ∧ p.2 ∈ C.Bcl ∧
        (v : G) ∈ zpowers (p.1 * p.2)} := by
  have hs : ∀ g : G, g ∈ C.Acl ∨ g ∈ C.Bcl → g ∈ centralizer ({C.s} : Set G) := by
    rintro g (h | h) <;> exact mem_centralizer_singleton_iff.2 h.1
  refine Nat.card_congr
    { toFun := fun p => ⟨((p.1.1 : G), (p.1.2 : G)), thompson_fwd hF hH Y v hpart p.2⟩
      invFun := fun q => ⟨(⟨q.1.1, hs _ (Or.inl q.2.2.2.1)⟩, ⟨q.1.2, hs _ (Or.inr q.2.2.2.2.1)⟩),
        thompson_bwd hF hH Y v _ _ q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro p; rfl
  · intro q; rfl

end Ctx

end CFSG.GH74.GLS.C3.Prop121.Card7
