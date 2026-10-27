module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossLinUni

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC (IsLinearOrUnitaryAt)

@[expose] def I294CrossLargePrime : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L →
    (∃ a b : L, a * b ≠ b * a) → ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic ≠ p →
    Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) → ¬ IsLinearOrUnitaryAt p L →
    (∃ S : Sylow p L, ¬ IsMulCommutative (S : Subgroup L)) →
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup L)

@[expose] def I294CrossThreeRankThree : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic ≠ 3 →
    Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) → ¬ IsLinearOrUnitaryAt 3 L →
    (∃ S : Sylow 3 L, ¬ IsMulCommutative (S : Subgroup L)) → ¬ 3 ^ 5 ∣ Nat.card L →
    CFSG.Open.pRank 3 (⊤ : Subgroup L) = 3 →
    ∀ x : L, orderOf x = 3 → 3 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer ({x} : Set L))

@[expose] def I294CrossThreeRankTwo : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic ≠ 3 →
    Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) → ¬ IsLinearOrUnitaryAt 3 L →
    (∃ S : Sylow 3 L, ¬ IsMulCommutative (S : Subgroup L)) →
    CFSG.Open.pRank 3 (⊤ : Subgroup L) ≤ 2 → ¬ 3 ^ 4 ∣ Nat.card L →
      ∀ α : MulAut L, (∃ k : ℕ, α ^ 3 ^ k = 1) → α ∈ (MulAut.conj : L →* MulAut L).range

section Assembly

variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} [L.Normal]

theorem I294Cross.isSylowOf_top_of_sylow {p : ℕ} [Fact p.Prime] (P : Sylow p Y) :
    CFSG.ABGLocalTools.IsSylowOf p (P : Subgroup Y) (⊤ : Subgroup Y) := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨le_top, P.isPGroup', ?_⟩
  rw [Subgroup.relIndex_top_right]
  exact P.not_dvd_index

theorem I294Cross.isMulCommutative_of_subgroupOf {H K : Subgroup Y} (hHK : H ≤ K)
    (h : IsMulCommutative ↥(H.subgroupOf K)) : IsMulCommutative ↥H :=
  ⟨⟨fun a b => by
    have := h.is_comm.comm ⟨⟨a, hHK a.2⟩, a.2⟩ ⟨⟨b, hHK b.2⟩, b.2⟩
    exact Subtype.ext (congrArg (fun t : ↥(H.subgroupOf K) => ((t : K) : Y)) this)⟩⟩

theorem I294Cfg.exists_sylow_not_comm {p : ℕ} {z g : Y} {D : Subgroup Y} (h : I294Cfg p L z g D)
    (hDL : D ≤ L) {P : Sylow p Y} (hDP : D ≤ (P : Subgroup Y)) :
    ∃ S : Sylow p ↥L, ¬ IsMulCommutative (S : Subgroup ↥L) := by
  haveI := Fact.mk h.prime
  have hSyl : CFSG.ABGLocalTools.IsSylowOf p ((P : Subgroup Y) ⊓ L) L :=
    (I294Cross.isSylowOf_top_of_sylow P).inf_of_le_normalizer le_top (by
      intro y _
      rw [Subgroup.mem_normalizer_iff]
      intro n
      constructor
      · intro hn; exact (inferInstance : L.Normal).conj_mem n hn y
      · intro hn
        have := (inferInstance : L.Normal).conj_mem _ hn y⁻¹
        simpa [mul_assoc] using this)
  obtain ⟨Q, hQ⟩ := hSyl.exists_sylow_eq_subgroupOf
  refine ⟨Q, fun hc => h.not_isMulCommutative_inf hDL hDP ?_⟩
  refine I294Cross.isMulCommutative_of_subgroupOf inf_le_right ?_
  rw [← hQ]
  exact hc

end Assembly

@[expose] def I294InnerLieCrossThree : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y) [L.Normal] (z g : Y) (D : Subgroup Y),
    I294Cfg 3 L z g D → D ≤ L → ∀ d : TauCeti.ValidLieTypeIndex,
      d.1.characteristic ≠ 3 → Nonempty (↥L ≃* (TauCeti.CFSGIndex.lie d).Group) → False

theorem i294InnerLieCrossThree_of_inputs (h3 : I294CrossThreeRankThree)
    (h2 : I294CrossThreeRankTwo) : I294InnerLieCrossThree := by
  intro Y _ _ L _ z g D cfg hDL d hd ⟨e⟩
  by_cases hLU : IsLinearOrUnitaryAt 3 ↥L
  · exact cfg.false_of_linearOrUnitary_three hLU
  · obtain ⟨P, hDP⟩ := cfg.exists_sylow_ge
    have hS := cfg.exists_sylow_not_comm hDL hDP
    have hr3 := cfg.pRank_normal_le_three
    by_cases hrk : CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) = 3
    · exact cfg.false_of_three_le_pRank_centralizer hDL
        (fun x hx => h3 ↥L cfg.simple cfg.nonab d hd ⟨e⟩ hLU hS cfg.not_dvd_pow_five hrk x hx)
    · have hr2 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) ≤ 2 := by omega
      by_cases h81 : 3 ^ 4 ∣ Nat.card ↥L
      · exact cfg.false_of_sylow_le (cfg.le_of_dvd_eightyOne' hDP (by simpa using h81)) hr2
      · exact cfg.false_of_sylow_le
          (cfg.le_of_pAut_inner (h2 ↥L cfg.simple cfg.nonab d hd ⟨e⟩ hLU hS hr2 h81) P.isPGroup')
          hr2

theorem i294InnerLieCross_of_three (h4 : I294CrossLargePrime) (hT : I294InnerLieCrossThree) :
    I294InnerLieCross := by
  intro p Y _ _ L _ z g D cfg hDL d hd ⟨e⟩
  have hp := cfg.prime
  by_cases hp3 : p = 3
  · subst hp3
    exact hT Y L z g D cfg hDL d hd ⟨e⟩
  · have hp5 : 5 ≤ p := by
      have h1 := hp.two_le
      have h2 := cfg.odd
      have h4 : p ≠ 4 := by rintro rfl; exact absurd hp (by decide)
      omega
    by_cases hLU : IsLinearOrUnitaryAt p ↥L
    · obtain ⟨x, hxD, hx1, hxS⟩ := cfg.sylowLine
      exact CFSG.LocalAnalysis.RankFourTheoremC.i294OutDiagExcluded_holds p hp hp5 Y L
        cfg.simple cfg.nonab cfg.catalog cfg.cent D cfg.elem cfg.card cfg.sylow cfg.rank.ge z g
        cfg.mem cfg.ne_one cfg.diag
        ⟨x, hxD, hx1, pRank_centralizer_le_two_of_isSylowOf hp cfg.card hxS⟩ hLU
    · obtain ⟨P, hDP⟩ := cfg.exists_sylow_ge
      have hS := cfg.exists_sylow_not_comm hDL hDP
      have h4' := h4 p hp hp5 ↥L cfg.simple cfg.nonab d hd ⟨e⟩ hLU hS
      have hr3 := cfg.pRank_normal_le_three
      omega

theorem i294InnerLieCross_of_inputs (h4 : I294CrossLargePrime) (h3 : I294CrossThreeRankThree)
    (h2 : I294CrossThreeRankTwo) : I294InnerLieCross :=
  i294InnerLieCross_of_three h4 (i294InnerLieCrossThree_of_inputs h3 h2)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
