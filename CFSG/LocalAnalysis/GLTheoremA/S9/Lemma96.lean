module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma96C

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S9

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

structure Lemma96Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  l94 : Lemma94Inputs G
  i107 : I107At G p
  rank2d4 : Rank2D4At G
  aut : AutRank96At G
  ext : ExtraspecialU5D4At G
  sylow : SylowU38At G
  i314 : I314At
  repA : ExtraspecialRepAt
  repB : ExtraspecialRepCenterAt

theorem L96.isList107_le_isList269 (i : TauCeti.CFSGIndex) (h : isList107 i) : isList269 i := by
  rcases h with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem lemma96 {G : Type} [Group G] [Finite G] {p q : ℕ} {B : Subgroup G} {x : G}
    {L Q₁ : Subgroup G} (hc : S9Ctx G p) (hin : Lemma96Inputs G p) (hC : Contra92 p B x L q Q₁)
    (h95 : GLATwoLocalRank q G ≤ GLATwoLocalRank p G) : Concl96 p B x L Q₁ := by
  obtain ⟨hp3, hlist⟩ := L96.list107_of_inputs hc hin.i107 hC h95
  subst hp3
  have hX : CFSG.Open.IsKGroup ↥(cx x) := isKGroup_cx hc hC.h.ne_one
  have hnoGB : ¬ IsGB 3 B L :=
    notIsGB_of_I269 hc hin.l94.lbal hin.l94.i269 hC.h
      (catalogIs_mono L96.isList107_le_isList269 hlist)
  have hodd_cx : Odd (Nat.card (GLAPPrimeCoreOf 3 (cx x))) :=
    odd_core_of_not_isGB hc hin.l94.l93 hC.h hnoGB
  have hodd : Odd (Nat.card (GLAPPrimeCoreOf 3 L)) := by
    have hle : GLAPPrimeCoreOf 3 L ≤ GLAPPrimeCoreOf 3 (cx x) :=
      glaPPrimeCoreOf_le_of_isSubnormal hc.ctx.prime hC.h.comp.2.1
    exact Odd.of_dvd_nat hodd_cx (Subgroup.card_dvd_of_le hle)
  have h94 := lemma94 hc hin.l94 hC.h
  obtain ⟨i, hi, e⟩ := hlist
  rcases hi with hi | hi | hi | hi | hi | hi
  · exact absurd ⟨i, Or.inl hi, e⟩ h94.1
  · exact absurd ⟨i, Or.inr hi, e⟩ h94.1
  ·
    have hcat : catalogIs (PSimple 3 L) isU5two := ⟨i, hi, e⟩
    have hL94 : catalogIs (PSimple 3 L) isList94 :=
      ⟨i, Or.inr (Or.inr (Or.inr hi)), e⟩
    have hB4 : Nat.card B = 3 ^ 4 := (h94.2 ⟨i, Or.inr hi, e⟩).1
    have hZ : Subgroup.center (PQuot 3 L) = ⊥ :=
      (hin.l94.rank23 (cx x) L hC.h.comp hL94).1
    exact ⟨rfl, hcat, hB4, hodd_cx,
      L96.center_le_of_U5 hc hC h95 hodd hB4 hZ hin.ext hin.repA hcat⟩
  ·
    exact (L96.case_U38 hc hC h95 hodd hin.aut hin.sylow hin.repB hin.i314 ⟨i, hi, e⟩).elim
  ·
    have hB4 : Nat.card B = 3 ^ 4 := (h94.2 ⟨i, Or.inl hi, e⟩).1
    exact (L96.case_D4 hc hC h95 hodd hin.rank2d4 hB4 ⟨i, hi, e⟩).elim
  ·
    exact (L96.case_TD4 hc hC h95 hodd hin.aut hin.ext hin.repA hin.i314 ⟨i, hi, e⟩).elim

end CFSG.LocalAnalysis.GLTheoremA.S9
