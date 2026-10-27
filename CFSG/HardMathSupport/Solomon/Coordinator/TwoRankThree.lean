module

public import CFSG.HardMathSupport.Solomon.Coordinator.TwoRankThreeCritical
public import CFSG.HardMathSupport.Solomon.Proving.UGroupThreePRank
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Subgroup CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal

variable {G : Type} [Group G] [Finite G]

theorem tr3_exists_twoLocal (h : 4 ≤ evenRank G) :
    ∃ (q : ℕ) (H : Subgroup G), q.Prime ∧ q ≠ 2 ∧ IsTwoLocal H ∧ 4 ≤ pRank q H := by
  by_contra hne
  push Not at hne
  have hle : evenRank G ≤ 3 := by
    unfold evenRank
    refine csSup_le' ?_
    rintro k ⟨q, H, hq, hq2, hH, rfl⟩
    have := hne q H hq hq2 hH
    omega
  omega

theorem tr3_three_le_pRank {T F : Subgroup G} (hFT : F ≤ T) (hF : IsElemAbelian 2 F)
    (h8 : 8 ≤ Nat.card F) : 3 ≤ pRank 2 T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF2 : IsPGroup 2 F := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hF.2 x x.2)⟩
  obtain ⟨k, hk⟩ := hF2.exists_card_eq
  have hk3 : 3 ≤ k := by
    by_contra h
    push Not at h
    have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact hk3.trans (CFSG.SectionRank.le_pRank (by norm_num) hFT hF hk)

theorem tr3_exists_elem_of_twoLocal (hchar : IsCharTwoType G) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {H : Subgroup G} (hH : IsTwoLocal H) (h4 : 4 ≤ pRank q H) :
    ∃ F : Subgroup G, F ≤ pCoreOf 2 H ∧ IsElemAbelian 2 F ∧ 8 ≤ Nat.card F := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfq : Fact q.Prime := ⟨hq⟩
  set Q := pCoreOf 2 H with hQ
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  obtain ⟨E, hEH, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hq.one_lt H
  have hEN : E ≤ normalizer (Q : Set G) :=
    hEH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
  have hEq : IsPGroup q E := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 x x.2)⟩
  have hEC : ∀ e ∈ E, e ∈ centralizer (Q : Set G) → e = 1 := by
    intro e he hc
    have heQ : e ∈ Q := hchar H hH ⟨hEH he, hc⟩
    exact Subgroup.disjoint_def.1 (IsPGroup.disjoint_of_ne q 2 hq2 E Q hEq hQ2) he heQ
  let φ : E →* MulAut Q := Q.normalizerMonoidHom.comp (inclusion hEN)
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro e he
    have hk : inclusion hEN e ∈ Q.normalizerMonoidHom.ker := MonoidHom.mem_ker.2 he
    rw [normalizerMonoidHom_ker, mem_subgroupOf] at hk
    exact Subtype.ext (hEC e e.2 hk)
  have hEcomm : ∀ a b : E, a * b = b * a := fun a b => hE.1.is_comm.comm a b
  obtain ⟨F, hFcomm, hFsq, hF8⟩ := tr3_key hQ2 hq hq2 φ.range
    (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul, hEcomm])
    (by
      rintro _ ⟨a, rfl⟩
      rw [← map_pow, show a ^ q = 1 from Subtype.ext (hE.2 a a.2), map_one])
    (by
      rw [← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv, hEcard]
      exact Nat.pow_le_pow_right hq.pos h4)
  have hFel : IsElemAbelian 2 F := ⟨⟨⟨fun a b => Subtype.ext (hFcomm _ a.2 _ b.2)⟩⟩, hFsq⟩
  refine ⟨F.map Q.subtype, map_subtype_le F, CFSG.SectionRank.isElemAbelian_map hFel _, ?_⟩
  rw [card_map_of_injective Q.subtype_injective]
  exact hF8

theorem tr3_three_le_pRank_sylow {Q F : Subgroup G} (hQ : IsPGroup 2 Q) (hFQ : F ≤ Q)
    (hF : IsElemAbelian 2 F) (h8 : 8 ≤ Nat.card F) (P : Sylow 2 G) :
    3 ≤ pRank 2 (P : Subgroup G) := by
  obtain ⟨P', hP'⟩ := (hQ.to_le hFQ).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P' P
  refine tr3_three_le_pRank (F := F.map (MulAut.conj g).toMonoidHom) ?_
    (CFSG.SectionRank.isElemAbelian_map hF _) ?_
  · rintro _ ⟨x, hx, rfl⟩
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hP' hx)
  · rw [card_map_of_injective (MulAut.conj g).injective]
    exact h8

theorem twoRankThreeOfStanding_proved :
    ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), CFSG.LocalAnalysis.GLTheoremB.GLStanding G m p →
      ∀ P : Sylow 2 G, 3 ≤ CFSG.Open.pRank 2 (P : Subgroup G) := by
  intro G _ _ m p hS P
  obtain ⟨q, H, hq, hq2, hH, h4⟩ := tr3_exists_twoLocal hS.evenRank_ge
  obtain ⟨F, hFQ, hF, hF8⟩ := tr3_exists_elem_of_twoLocal hS.charTwo hq hq2 hH h4
  exact tr3_three_le_pRank_sylow (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) hFQ hF hF8 P

theorem inputUExists_proved : InputUExists := by
  intro G _ _ m p hS P
  exact CFSG.HardMathSupport.Solomon.Proving.exists_isUGroup_of_three_le_pRank P.isPGroup'
    (twoRankThreeOfStanding_proved G m p hS P)

end CFSG.HardMathSupport.Solomon.Coordinator

end
