module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KBlkAction
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KBlkBender
public import CFSG.LocalAnalysis.PreuniquenessRankFour.CoprimeAction

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KBlk

open Subgroup CFSG.Semidihedral.Principal CFSG.Semidihedral.Principal.CoprimeFixedPoint
open CFSG.GH74.Uniqueness.Bender
open scoped Pointwise

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ}

theorem closure_fixed_sup_sylow (hp : p.Prime) (hp2 : p ≠ 2)
    (σ : MulAut Y) (hσ : σ ^ p = 1) (N' : Subgroup Y) [N'.Normal] (hN : ∀ n ∈ N', σ n ∈ N')
    (hcop : ¬ p ∣ Nat.card Y) {n : ℕ} (hK : BenderType (Y ⧸ N') n 1 1) (T : Subgroup Y)
    (hNT : N' ≤ T) (hT2 : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index) (hTσ : ∀ t ∈ T, σ t ∈ T) :
    Subgroup.closure ({c : Y | σ c = c} ∪ (T : Set Y)) = ⊤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp0 : 0 < p := hp.pos
  let A : Subgroup (MulAut Y) := zpowers σ
  let α : ↥A →* MulAut Y := A.subtype
  have hApg : IsPGroup p A := isPGroup_zpowers hσ
  have hN' : ∀ a : ↥A, ∀ x ∈ N', α a x ∈ N' := fun a x hx =>
    mem_of_mem_zpowers hσ hp0 hN a.2 hx
  let β : ↥A →* MulAut (Y ⧸ N') := quotientAction α N' hN'
  letI : MulDistribMulAction ↥A (Y ⧸ N') := MulDistribMulAction.compHom (Y ⧸ N') β
  have hKp : ¬ p ∣ Nat.card (Y ⧸ N') := fun h =>
    hcop (h.trans (Subgroup.card_quotient_dvd_card N'))
  let π : Y →* Y ⧸ N' := QuotientGroup.mk' N'
  have hTbar2 : IsPGroup 2 (T.map π) := hT2.map π
  have hker : π.ker ≤ T := by
    show (QuotientGroup.mk' N').ker ≤ T
    rw [QuotientGroup.ker_mk']
    exact hNT
  have hTbarIdx : ¬ 2 ∣ (T.map π).index := by
    rw [Subgroup.index_map_eq T (QuotientGroup.mk'_surjective N') hker]
    exact hTi
  let PT : Sylow 2 (Y ⧸ N') := hTbar2.toSylow hTbarIdx
  have hPTcoe : (PT : Subgroup (Y ⧸ N')) = T.map π := rfl
  have hPTfix : ∀ a : ↥A, a • PT = PT := by
    intro a
    have hle : ((a • PT : Sylow 2 (Y ⧸ N')) : Subgroup (Y ⧸ N')) ≤
        (PT : Subgroup (Y ⧸ N')) := by
      intro x hx
      rw [Sylow.pointwise_smul_def, Subgroup.mem_smul_pointwise_iff_exists] at hx
      obtain ⟨s, hs, rfl⟩ := hx
      rw [hPTcoe] at hs ⊢
      obtain ⟨t, ht, rfl⟩ := hs
      exact ⟨α a t, mem_of_mem_zpowers hσ hp0 hTσ a.2 ht, rfl⟩
    exact Sylow.ext ((a • PT).is_maximal' PT.isPGroup' hle).symm
  have hmod : Nat.card (Sylow 2 (Y ⧸ N')) ≡
      Nat.card (MulAction.fixedPoints ↥A (Sylow 2 (Y ⧸ N'))) [MOD p] :=
    hApg.card_modEq_card_fixedPoints (Sylow 2 (Y ⧸ N'))
  rw [card_sylow_two hK] at hmod
  have hPTmem : PT ∈ MulAction.fixedPoints ↥A (Sylow 2 (Y ⧸ N')) := fun a => hPTfix a
  obtain ⟨P', hP'fix, hP'ne⟩ : ∃ P' ∈ MulAction.fixedPoints ↥A (Sylow 2 (Y ⧸ N')), P' ≠ PT := by
    by_contra hcon
    push Not at hcon
    have hone : Nat.card (MulAction.fixedPoints ↥A (Sylow 2 (Y ⧸ N'))) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun x y => Subtype.ext ((hcon x x.2).trans (hcon y y.2).symm)⟩, ⟨⟨PT, hPTmem⟩⟩⟩
    rw [hone] at hmod
    have h1 : p ∣ 2 ^ n := by
      have := (Nat.modEq_iff_dvd' (Nat.le_add_left 1 _)).mp hmod.symm
      simpa using this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1))
  have hP'fix' : ∀ a : ↥A, a • P' = P' := fun a => hP'fix a
  obtain ⟨c, hc, hcfix⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.invariant_sylows_conjugate_by_fixed_element
      p 2 hApg hKp PT P' hPTfix hP'fix'
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective N' c
  have hcσ : quotAut σ N' hN (y : Y ⧸ N') = (y : Y ⧸ N') := by
    have h1 := hcfix ⟨σ, Subgroup.mem_zpowers σ⟩
    have h2 : c = (y : Y ⧸ N') := hy.symm
    rw [h2] at h1
    exact h1
  obtain ⟨c', hc'σ, hc'y⟩ := exists_fixed_of_quotAut_fixed σ hσ N' hN
    (fun h => hcop (h.trans (Subgroup.card_subgroup_dvd_card N'))) y hcσ
  have hc'π : π c' = c := by
    rw [← hy]
    exact (QuotientGroup.eq.mpr hc'y).symm
  set H : Subgroup Y := Subgroup.closure ({c : Y | σ c = c} ∪ (T : Set Y)) with hH
  have hc'H : c' ∈ H := Subgroup.subset_closure (Or.inl hc'σ)
  have hTH : T ≤ H := fun t ht => Subgroup.subset_closure (Or.inr ht)
  have hPTJ : (PT : Subgroup (Y ⧸ N')) ≤ H.map π := by
    rw [hPTcoe]
    exact Subgroup.map_mono hTH
  have hnot : ¬ H.map π ≤ normalizer (PT : Set (Y ⧸ N')) := by
    intro hle
    have hcn : c ∈ normalizer (PT : Set (Y ⧸ N')) := hle ⟨c', hc'H, hc'π⟩
    have := Sylow.smul_eq_iff_mem_normalizer.mpr hcn
    exact hP'ne (hc ▸ this)
  have hJtop : H.map π = ⊤ := eq_top_of_sylow_le hK PT (H.map π) hPTJ hnot
  refine eq_top_iff.mpr fun y _ => ?_
  have hy' : π y ∈ H.map π := hJtop ▸ Subgroup.mem_top _
  obtain ⟨h, hhH, hh⟩ := hy'
  have hn : h⁻¹ * y ∈ N' := QuotientGroup.eq.mp hh
  have : y = h * (h⁻¹ * y) := by group
  rw [this]
  exact H.mul_mem hhH (hTH (hNT hn))

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KBlk
