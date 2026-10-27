module

public import CFSG.LocalAnalysis.GLTheoremA.S11.Prop111
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

structure Cfg116 (G : Type) [Group G] [Finite G] (m p : ℕ) (L : Subgroup G) (p' : ℕ) (B' : Subgroup G) (x' : G)
    (J : Subgroup G) : Prop where
  mu : p' ∈ Mu G m
  cfg : Concl166 G p p' L B' x' J
  e_eq : evenRank ↥L = m
  splits : ∀ lab : GLALabel, LabelOf L lab → GLASplit16 p' lab

namespace S11

variable {G : Type} [Group G] [Finite G] {m p q : ℕ} {B : Subgroup G} {x : G} {L : Subgroup G}

theorem split16_swap (q : ℕ) (r n : ℕ) : GLASplit16 q ⟨.B, r, n⟩ ↔ GLASplit16 q ⟨.C, r, n⟩ := by
  simp [GLASplit16, CFSG.Assembly.LargeEvenSplit16, CFSG.Assembly.LargeEvenUntwisted]

theorem split16_of_label (hu : LabelUniqAt G) {K : Subgroup G} (he : 4 ≤ evenRank ↥K) {lab₁ lab₂ : GLALabel}
    (h1 : LabelOf K lab₁) (h2 : LabelOf K lab₂) (hs : GLASplit16 q lab₁) : GLASplit16 q lab₂ := by
  rcases hu K lab₁ lab₂ he h1 h2 with rfl | ⟨ht1, ht2, hr, hn⟩
  · exact hs
  · obtain ⟨t1, r1, n1⟩ := lab₁
    obtain ⟨t2, r2, n2⟩ := lab₂
    simp only at ht1 ht2 hr hn
    subst hr hn
    rcases ht1 with rfl | rfl <;> rcases ht2 with rfl | rfl
    · exact hs
    · exact (split16_swap q r1 n1).1 hs
    · exact (split16_swap q r1 n1).2 hs
    · exact hs

theorem lemma116 (hctx : ThmACtx G m) (hsf : StageFacts G m) (hin : Inputs111 G) (h166 : I166At G) (hu : LabelUniqAt G)
    (hR : RQuad G m p B x L) (hns : NoSplit16 p L) :
    ∃ (p' : ℕ) (B' : Subgroup G) (x' : G) (J : Subgroup G), Cfg116 G m p L p' B' x' J := by
  have hH := rquad_hyp hsf hR
  have hm : 4 ≤ m := hctx.1.four_le
  have hcor := cor112_full hctx hsf hin hR hns
  have hhalf : HalfSplit16At p L := by
    obtain ⟨lab, hlab, hl⟩ := hcor.half
    exact ⟨lab, hlab, hl.1⟩
  obtain ⟨q, B', x', J, hC⟩ := h166 p hH.prime hH.ne_two L hH.isChev2 hhalf hns (by rw [hcor.e_eq]; exact hm)
    (by rw [hcor.indep.rank, hcor.e_eq]; omega) (fun _ => hcor.not_E62)
  have hqL : GLATwoLocalRank q ↥L = m := by rw [hC.rank_K, hcor.e_eq]
  have hZ : Odd (Nat.card (Subgroup.center ↥L)) := hin.i161b p hH.prime hH.ne_two L hH.isChev2 hhalf hns
  obtain ⟨lab', hlab', hsp⟩ := hin.i163 q hC.prime hC.odd L hH.isChev2 (by omega) (by rw [hqL, hcor.e_eq]) (Or.inl hZ)
  have hmu : q ∈ Mu G m := prop113 hctx hsf hin hR hns hcor.e_eq hC.prime hC.odd hqL
  exact ⟨q, B', x', J, hmu, hC, hcor.e_eq, fun lab hlab =>
    split16_of_label hu (by rw [hcor.e_eq]; exact hm) hlab' hlab hsp⟩

end S11

end CFSG.LocalAnalysis.GLTheoremA
