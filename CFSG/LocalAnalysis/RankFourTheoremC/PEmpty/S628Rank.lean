module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S628Common

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (smallRankS smallRankR)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}
  {T : Subgroup G}

theorem s62_commutator_mem_centralizer_of_cyclic {X : Subgroup G} (hX : IsCyclic X) {a b : G}
    (ha : a ∈ normalizer (X : Set G)) (hb : b ∈ normalizer (X : Set G)) :
    ⁅a, b⁆ ∈ centralizer (X : Set G) := by
  let _ := (IsCyclic.mulAutMulEquiv X).toMonoidHom.commGroupOfInjective
    (IsCyclic.mulAutMulEquiv X).injective
  let N : Subgroup G := normalizer (X : Set G)
  let a' : N := ⟨a, ha⟩
  let b' : N := ⟨b, hb⟩
  have hφ : X.normalizerMonoidHom ⁅a', b'⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have hcomm : (N.subtype ⁅a', b'⁆ : G) = ⁅a, b⁆ := map_commutatorElement N.subtype a' b'
  rw [mem_centralizer_iff]
  intro y hy
  have h1 := congrArg (fun m : MulAut X => (m ⟨y, hy⟩ : G)) hφ
  simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h1
  have h2 : ⁅a, b⁆ * y * ⁅a, b⁆⁻¹ = y := by
    rw [← hcomm]
    exact h1
  exact (mul_inv_eq_iff_eq_mul.mp h2).symm

theorem s62_commutator_le_centralizer_of_cyclic {X S : Subgroup G} (hX : IsCyclic X) {z : G}
    (hzX : z ∈ normalizer (X : Set G)) (hSX : S ≤ normalizer (X : Set G)) :
    ⁅zpowers z, S⁆ ≤ centralizer (X : Set G) := by
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  exact s62_commutator_mem_centralizer_of_cyclic hX ((zpowers_le.mpr hzX) ha) (hSX hb)

theorem s62_two_le_pRank {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) {X : Subgroup G}
    (hXp : IsPGroup f X) (hX : ¬ IsCyclic X) : 2 ≤ CFSG.Open.pRank f X := by
  haveI : Fact f.Prime := ⟨hf⟩
  haveI : Fact (IsPGroup f X) := ⟨hXp⟩
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a hf2 hX
  haveI := hSel
  have hSm : CFSG.IsElementaryAbelian f (S.map X.subtype) :=
    CFSG.IsElementaryAbelian.map_subtype
  have hcard : Nat.card (S.map X.subtype) = f ^ 2 := by
    rw [← hScard]
    exact (Nat.card_congr (S.equivMapOfInjective X.subtype X.subtype_injective).toEquiv).symm
  exact CFSG.SectionRank.le_pRank hf.one_lt (Subgroup.map_subtype_le S)
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian f _).mp hSm) hcard

theorem s62_two_le_pRank_of_commutator (c : S62Config p P M x z T) {f : ℕ} (hf : f.Prime)
    (hf2 : f ≠ 2) {X : Subgroup G} (hXp : IsPGroup f X) (hzX : z ∈ normalizer (X : Set G))
    (hSX : smallRankS x T ≤ normalizer (X : Set G))
    (hX : ∀ S₀ : Subgroup G, S₀ ≤ smallRankS x T → S₀ ≠ ⊥ →
      zpowers z ≤ normalizer (S₀ : Set G) → ¬ X ≤ centralizer (S₀ : Set G)) :
    2 ≤ CFSG.Open.pRank f X := by
  by_contra h2
  have hcyc : IsCyclic X := by
    by_contra hnc
    exact h2 (s62_two_le_pRank hf hf2 hXp hnc)
  have hRC : smallRankR x z T ≤ centralizer (X : Set G) :=
    s62_commutator_le_centralizer_of_cyclic hcyc hzX hSX
  exact hX _ c.R_le_S c.R_ne_bot c.z_le_normalizer_R (Subgroup.le_centralizer_iff.mp hRC)

theorem s62_localRank_le_three (hS : Situation G p P M) (h614 : Prop614At M x z) {f : ℕ}
    (hf : f.Prime) (hf2 : f ≠ 2) {X S : Subgroup G} (hXp : IsPGroup f X)
    (hX2 : 2 ≤ CFSG.Open.pRank f X) (hXM : ¬ X ≤ M) (hS2 : IsPGroup 2 S) (hSM : S ≤ M)
    (hS1 : S ≠ ⊥) (hBS : zpowers x ⊔ zpowers z ≤ normalizer (S : Set G))
    (hSBX : S ⊔ (zpowers x ⊔ zpowers z) ≤ normalizer (X : Set G)) :
    rankThreeLocalRank f G ≤ 3 := by
  by_contra h
  push Not at h
  have h4 : 4 ≤ GLBTwoLocalRank f G := h
  have hpos : 0 < rankThreeLocalRank f G := by omega
  obtain ⟨H', -, hH'r⟩ := rankThreeLocalRank_attained f hpos
  have hfdvd : f ∣ Nat.card G := prime_dvd_card_of_pRank_pos f H' (by rw [hH'r]; exact hpos)
  have hβ : f ∈ GLBBetaFour G := ⟨hf, hf2, hfdvd, h4⟩
  obtain ⟨F, hXF⟩ := hXp.exists_le_sylow
  obtain ⟨H, hHloc, hHcore⟩ :=
    CFSG.LocalAnalysis.RankFourTheoremC.deltaOne_of_fullCore hS.toGlobal.d1Global.pre
      hS.toGlobal.fullCore f hβ F
  have hXH : normalizer (X : Set G) ≤ H :=
    (le_sSup ⟨X, hXF, hX2, rfl⟩ : normalizer (X : Set G) ≤ GLBCore f 2 (F : Subgroup G)).trans
      hHcore
  have hSH : S ⊔ (zpowers x ⊔ zpowers z) ≤ H := hSBX.trans hXH
  have hBH : zpowers x ⊔ zpowers z ≤ H := le_sup_right.trans hSH
  have hHM : H ≤ M :=
    h614 H hHloc hBH ⟨S, le_inf (le_sup_left.trans hSH) hSM, hS1, hS2, hBS⟩
  exact hXM (le_normalizer.trans (hXH.trans hHM))

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
