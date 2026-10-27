module

public import CFSG.HardMathSupport.Solomon.Coordinator.ON25E27

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29

attribute [local irreducible] dotProduct

open Subgroup
open CFSG.RankThree.Native.ONTriple (GM zG xG omegaZ relG center_GM)
open CFSG.RankThree.PartTwo.Late (IsE27)
open scoped commutatorElement

section


theorem on_mem_center_GM_iff {g : GM} : g ∈ center GM ↔ g ∈ zpowers zG := by
  rw [center_GM]

theorem on_E27_through {L : Type} [Group L] (ψ : L ≃* GM) {b : L} (hb3 : b ^ 3 = 1)
    (hbz : b ∉ center L) : ∃ E : Subgroup L, IsE27 E ∧ b ∈ E := by
  obtain ⟨x, hx3, hxb, hxY⟩ :=
    CFSG.RankThree.PartTwo.Sec13.ON134.exists_centralizer ψ hb3 hbz
  have hg3 : ψ b ^ 3 = 1 := by rw [← map_pow, hb3, map_one]
  have hgZ : ψ b ∉ center GM := by
    intro h
    rw [on_mem_center_GM_iff] at h
    exact hbz ((CFSG.RankThree.PartTwo.Sec13.ON134.mem_center_iff_model ψ).2 h)
  have hx3' : ψ x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hxg : ψ x * ψ b = ψ b * ψ x := by rw [← map_mul, ← map_mul, hxb]
  have hZ : (center L).map ψ.toMonoidHom = center GM := by
    ext g
    rw [Subgroup.mem_map_equiv, CFSG.RankThree.PartTwo.Sec13.ON134.mem_center_iff_model ψ,
      MulEquiv.apply_symm_apply, on_mem_center_GM_iff]
  have hmap : (zpowers b ⊔ center L).map ψ.toMonoidHom = zpowers (ψ b) ⊔ center GM := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hZ]
    rfl
  have hxY' : ψ x ∉ zpowers (ψ b) ⊔ center GM := by
    intro h
    apply hxY
    rw [← hmap, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at h
    exact h
  have hE := CFSG.HardMathSupport.Solomon.Coordinator.on25_isE27_of_commute hg3 hgZ hx3' hxg hxY'
  refine ⟨(zpowers (ψ x) ⊔ (zpowers (ψ b) ⊔ center GM)).map ψ.symm.toMonoidHom,
    hE.map ψ.symm, ?_⟩
  refine Subgroup.mem_map.mpr ⟨ψ b, ?_, by simp⟩
  exact Subgroup.mem_sup_right (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))

theorem on_cube {L : Type} [Group L] (ψ : L ≃* GM) {l : L} (hl : l ^ 3 ∈ center L) :
    l ^ 3 = 1 := by
  have h1 : ψ (l ^ 3) ∈ zpowers zG :=
    (CFSG.RankThree.PartTwo.Sec13.ON134.mem_center_iff_model ψ).1 hl
  have h2 : (l ^ 3) ^ 3 = 1 := by
    apply ψ.injective
    rw [map_pow, map_one]
    exact relG.zpowers_pow_three h1
  have h3 : l ^ 3 ^ 2 = 1 := by
    rw [show (3 : ℕ) ^ 2 = 3 * 3 by norm_num, pow_mul]
    exact h2
  exact CFSG.RankThree.PartTwo.Sec13.ON134.pow_three_eq_one ψ h3

theorem on_three_le_pRank_top {L : Type} [Group L] [Finite L] {E : Subgroup L} (hE : IsE27 E) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) :=
  CFSG.SectionRank.le_pRank (by norm_num) (le_top : E ≤ ⊤) hE.1 (k := 3)
    (by rw [hE.2]; norm_num)

theorem on_three_le_pRank_centralizer {L : Type} [Group L] [Finite L] {E : Subgroup L}
    (hE : IsE27 E) {l : L} (hl : l ∈ E) :
    3 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer ({l} : Set L)) := by
  have hle : E ≤ Subgroup.centralizer ({l} : Set L) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact congrArg Subtype.val (hE.1.1.is_comm.comm ⟨l, hl⟩ ⟨e, he⟩)
  exact CFSG.SectionRank.le_pRank (by norm_num) hle hE.1 (k := 3) (by rw [hE.2]; norm_num)

theorem on_exists_noncentral_three {L : Type} [Group L] (ψ : L ≃* GM) :
    ∃ b : L, b ^ 3 = 1 ∧ b ∉ center L := by
  refine ⟨ψ.symm (xG 0), ?_, ?_⟩
  · rw [← map_pow, relG.vcube 0, map_one]
  · intro h
    have h' : xG 0 ∈ zpowers zG := by
      have h0 := (CFSG.RankThree.PartTwo.Sec13.ON134.mem_center_iff_model ψ).1 h
      rwa [MulEquiv.apply_symm_apply] at h0
    have hc : xG 0 ∈ center GM := on_mem_center_GM_iff.2 h'
    have hcomm : ⁅xG 0, xG 3⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp hc (xG 3)).symm
    have hw := relG.comm 0 3
    rw [hcomm] at hw
    have hval : (omegaZ 0 3).val = 1 := by decide
    rw [hval, pow_one] at hw
    exact relG.x1 hw.symm

theorem on_cover_data {L : Type} [Group L] [Finite L] (hq : CFSG.Open.IsQuasisimple L)
    (hZ : Nat.card (Subgroup.center L) = 3)
    (hL : Nonempty (L ⧸ Subgroup.center L ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group)) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) ∧
      ∀ l : L, l ∉ Subgroup.center L → l ^ 3 ∈ Subgroup.center L →
        l ^ 3 = 1 ∧ 3 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer ({l} : Set L)) := by
  have hperf : Group.IsPerfect L := Group.isPerfect_def.mpr hq.1
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have b' : CFSG.Blueprint.NativeSporadic.ON ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group := b
  obtain ⟨e⟩ := hL
  have hT : CFSG.RankThree.PartTwo.Sec4.IsTripleCover L CFSG.Blueprint.NativeSporadic.ON :=
    ⟨hZ, ⟨e.trans b'.symm⟩⟩
  obtain ⟨ψ⟩ := CFSG.RankThree.PartTwo.Sec13.ON134.nonempty_equiv_model hperf hT
  refine ⟨?_, ?_⟩
  · obtain ⟨b0, hb3, hb0⟩ := on_exists_noncentral_three ψ
    obtain ⟨E, hE, -⟩ := on_E27_through ψ hb3 hb0
    exact on_three_le_pRank_top hE
  · intro l hl hl3
    have hl1 : l ^ 3 = 1 := on_cube ψ hl3
    obtain ⟨E, hE, hlE⟩ := on_E27_through ψ hl1 hl
    exact ⟨hl1, on_three_le_pRank_centralizer hE hlE⟩

end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29

end
