module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04D3
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04I117Count

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance (isElemAbelian_of_forall)
open CFSG.ComponentClassification.PerfectAutomorphisms
local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

theorem d3_card_le_of_normalizes {G : Type} [Group G] [Finite G] {B E T : Subgroup G}
    (hB : GLAIsBmax 3 B) (hE : IsElemAbelian 3 E) (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hET : E ≤ Subgroup.normalizer (T : Set G)) : Nat.card E ≤ Nat.card B := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hEp : IsPGroup 3 E := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 g.1 g.2)⟩
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  have h1 : k ≤ CFSG.Open.pRank 3 E := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hE hk
  have h2 := pRank_le_glaTwoLocalRank_of_normalizes hp hT hT2 hET
  rw [hk, hB.2.1]
  exact Nat.pow_le_pow_right (by norm_num) (h1.trans h2)

theorem d3_card_le_of_normalizes_image {G : Type} [Group G] [Finite G] {B N : Subgroup G}
    (hB : GLAIsBmax 3 B) (O : Subgroup ↥N) [O.Normal] (hO : ¬ 3 ∣ Nat.card O)
    {E : Subgroup (↥N ⧸ O)} (hE : IsElemAbelian 3 E) {T : Subgroup ↥N} (hT : T ≠ ⊥)
    (hT2 : IsPGroup 2 T)
    (hET : E ≤ Subgroup.normalizer ((T.map (QuotientGroup.mk' O) : Subgroup (↥N ⧸ O)) :
      Set (↥N ⧸ O))) : Nat.card E ≤ Nat.card B := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  by_cases hTb : T.map (QuotientGroup.mk' O) = ⊥
  ·
    have hTO : T ≤ O := by
      intro t ht
      have : QuotientGroup.mk' O t ∈ (T.map (QuotientGroup.mk' O)) := ⟨t, ht, rfl⟩
      rw [hTb, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff t).1 this
    obtain ⟨S, hSel, hSmap, hScard⟩ := exists_elemAbelian_lift O hO hE
    have hSp : IsPGroup 3 S := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hSel.2 g.1 g.2)⟩
    have heven : Even (Nat.card O) := by
      obtain ⟨j, hj⟩ := hT2.exists_card_eq
      have hj1 : j ≠ 0 := by
        rintro rfl
        exact hT (Subgroup.eq_bot_of_card_eq T (by simpa using hj))
      have h2 : 2 ∣ Nat.card T := by rw [hj]; exact dvd_pow_self 2 hj1
      exact even_iff_two_dvd.2 (h2.trans (Subgroup.card_dvd_of_le hTO))
    have hSO : S ≤ Subgroup.normalizer (O : Set ↥N) := by
      rw [Subgroup.normalizer_eq_top_iff.2 inferInstance]
      exact le_top
    obtain ⟨T', hT'ne, -, hT'2, hST'⟩ := exists_twoGroup_normalized_of_coprime_even hp
      (by norm_num) hSp hSO hO heven
    have hT'' : T'.map N.subtype ≠ ⊥ := fun h =>
      hT'ne ((Subgroup.map_eq_bot_iff_of_injective T' N.subtype_injective).1 h)
    have hS'' : IsElemAbelian 3 (S.map N.subtype) := by
      refine isElemAbelian_of_forall ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        change (x : G) * y = y * x
        exact congrArg Subtype.val (isElemAbelian_commute hSel hx hy)
      · rintro _ ⟨x, hx, rfl⟩
        change (x : G) ^ 3 = 1
        exact congrArg Subtype.val (hSel.2 x hx)
    have hnorm : S.map N.subtype ≤ Subgroup.normalizer ((T'.map N.subtype : Subgroup G) : Set G) :=
      (Subgroup.map_mono hST').trans (Subgroup.le_normalizer_map _)
    have := d3_card_le_of_normalizes hB hS'' hT'' (hT'2.map _) hnorm
    rwa [Subgroup.card_map_of_injective N.subtype_injective, hScard] at this
  · exact card_le_of_normalizes_quotient hB O hO hE hTb (hT2.map _) hET

end CFSG.LocalAnalysis.GLTheoremA
