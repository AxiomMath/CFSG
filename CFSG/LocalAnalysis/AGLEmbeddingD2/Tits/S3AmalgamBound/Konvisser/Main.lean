module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser.Induction
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.PurityOfOrderThree

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser

theorem qstmt_four : QStmt 4 :=
  qstmt_succ 3 (by norm_num) le_rfl
    (qstmt_succ 2 (by norm_num) (by norm_num)
      (qstmt_succ 1 le_rfl (by norm_num) qstmt_one))

theorem exists_sub_ea_of_dvd {G : Type} [Group G] [Finite G] {E : Subgroup G} (hE : IsEA3 E)
    {n : ℕ} (hd : 3 ^ n ∣ Nat.card E) :
    ∃ K : Subgroup G, K ≤ E ∧ IsEA3 K ∧ Nat.card K = 3 ^ n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K', hK'⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) 3 (n := n) hd
  refine ⟨K'.map E.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
      exact hE.1 _ x.2 _ y.2
    · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
      exact hE.2 _ x.2
  · rw [Subgroup.card_map_of_injective E.subtype_injective, hK']

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers in
theorem kFactNormalRankFourThree :
    CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.KFactNormalRankFourThree := by
  intro X _ _ P hP h4
  have hp3 : (3 : ℕ).Prime := Nat.prime_three
  obtain ⟨E, hEP, hEe, hEc⟩ := pRank_attained 3 hp3 P
  have hEea : IsEA3 E := ⟨fun a ha b hb =>
    congrArg Subtype.val (isMulCommutative_iff.mp hEe.1 ⟨a, ha⟩ ⟨b, hb⟩), hEe.2⟩
  obtain ⟨K, hKE, hKe, hKc⟩ := exists_sub_ea_of_dvd hEea (n := 4)
    (by rw [hEc]; exact pow_dvd_pow 3 h4)
  have hKP : K ≤ P := hKE.trans hEP
  obtain ⟨N', -, hN'n, hN'e, hN'c⟩ := qstmt_four P hP ⊤ inferInstance
    ⟨K.subgroupOf P, le_top, ⟨fun a ha b hb => Subtype.ext (hKe.1 _ ha _ hb),
      fun a ha => Subtype.ext (hKe.2 _ ha)⟩, by
        rw [← hKc]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKP).toEquiv⟩
  refine ⟨N'.map P.subtype, Subgroup.map_subtype_le _, ?_, ⟨?_, ?_⟩, ?_⟩
  · have : (N'.map P.subtype).subgroupOf P = N' :=
      Subgroup.comap_map_eq_self_of_injective P.subtype_injective N'
    rw [this]
    exact hN'n
  · refine isMulCommutative_iff.mpr fun a b => ?_
    obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp b.2
    apply Subtype.ext
    show (a : X) * b = b * a
    rw [← hxa, ← hyb]
    exact congrArg Subtype.val (hN'e.1 x hx y hy)
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    exact congrArg Subtype.val (hN'e.2 x hx)
  · rw [Subgroup.card_map_of_injective P.subtype_injective, hN'c]

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser
