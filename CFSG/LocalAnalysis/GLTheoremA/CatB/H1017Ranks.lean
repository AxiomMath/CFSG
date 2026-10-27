module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCo1Five

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA

theorem simpleElemRank_of_model {p r : ℕ} {s : TauCeti.SporadicName} {Q : Type} [Group Q]
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (h : ∃ E : Subgroup Q, IsElemAbelian p E ∧ Nat.card E = p ^ r) : SimpleElemRank p s r := by
  intro K _ _ hcat
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  simp only [S8.sporIs] at hi
  subst hi
  obtain ⟨E, hE, hc⟩ := h
  let φ : Q ≃* K := b.trans e.symm
  refine ⟨E.map φ.toMonoidHom, ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨x, x', hx', rfl⟩ := x
    obtain ⟨y, y', hy', rfl⟩ := y
    show φ x' * φ y' = φ y' * φ x'
    rw [← map_mul, ← map_mul]
    haveI := hE.1
    have := congrArg Subtype.val (mul_comm' (⟨x', hx'⟩ : E) ⟨y', hy'⟩)
    simp only [Subgroup.coe_mul] at this
    rw [this]
  · rintro _ ⟨x, hx, rfl⟩
    show φ x ^ p = 1
    rw [← map_pow, hE.2 x hx, map_one]
  · rw [Subgroup.card_map_of_injective φ.injective, hc]


theorem i1017LyRank_holds : I1017LyRank :=
  simpleElemRank_of_model (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Ly).some
    CFSG.SectionRank.Ly_elementary_three_rank_four

theorem i1017CoTwoRank_holds : I1017CoTwoRank :=
  simpleElemRank_of_model (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Co2).some
    CFSG.SectionRank.Co2_elementary_three_rank_four

theorem i1017SuzRank_holds : I1017SuzRank :=
  simpleElemRank_of_model (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Suz).some
    CFSG.SectionRank.Suz_elementary_three_rank_four

theorem i1017ThRank_holds : I1017ThRank :=
  simpleElemRank_of_model (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Th).some
    CFSG.SectionRank.Th_elementary_three_rank_four

open CFSG.Sporadic.Co1Schreier in
theorem i1017CoOneRank_holds : I1017CoOneRank := by
  obtain ⟨hfin, -, -, ⟨b⟩⟩ := CFSG.HardMathSupport.Dickson.I271.TabCo1.co1_model_five
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  show SimpleElemRank 3 .Co1 5
  refine simpleElemRank_of_model (p := 3) (r := 5) (s := .Co1) (Q := ↥GA) ?_ ?_
  · exact b
  have hEGA : ElemThree.E ≤ GA := by
    refine E_le_K.trans ?_
    rw [ThreeLocal.K, Subgroup.closure_le]
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    exacts [threeLocal_mem.2.1, threeLocal_mem.2.2.1]
  let E' : Subgroup ↥GA := ElemThree.E.subgroupOf GA
  have hE' : IsElemAbelian 3 E' := by
    refine ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · exact (E_comm _ (Subgroup.mem_subgroupOf.1 x.2) _ (Subgroup.mem_subgroupOf.1 y.2)).eq
    · exact E_pow_three _ (Subgroup.mem_subgroupOf.1 hx)
  have hc : Nat.card E' = 3 ^ 6 := by
    rw [show Nat.card E' = Nat.card ElemThree.E from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEGA).toEquiv, card_E]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E'', hle, hE'', hc''⟩ := CFSG.LocalAnalysis.GLTheoremB.exists_le_isElemAbelian_card hE'
    (n := 5) (by rw [hc]; exact pow_dvd_pow 3 (by norm_num))
  exact ⟨E'', hE'', hc''⟩

end CFSG.LocalAnalysis.GLTheoremA.H1017

end
