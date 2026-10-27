module

import CFSG.LocalAnalysis.RankThreeTheoremC.FusionControl
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Setting
public import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionElements

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (not_isCyclic_of_two_le_pRank
  not_isCyclic_of_isAlperinSubgroup two_le_pRank_of_not_isCyclic)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G}

theorem mem_of_alperinDecomposition (hS : Situation G p P M) {A : Subgroup G} {c : G}
    (hdec : CFSG.RankTwoShapes.AlperinDecomposition p (P : Subgroup G) A c) : c ∈ M := by
  have hprime := hS.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  have hPM := hS.sylow_le
  have hPnc : ¬ IsCyclic (P : Subgroup G) :=
    not_isCyclic_of_two_le_pRank hprime (by have := hS.four_le_pRank; omega)
  induction hdec with
  | one => exact M.one_mem
  | step _ hQ _ hn ih =>
    have hQp : IsPGroup p _ := P.isPGroup'.to_le hQ.1
    exact M.mul_mem ih (hS.normalizer_le hQp (hQ.1.trans hPM)
      (two_le_pRank_of_not_isCyclic hprime hS.ne_two hQp
        (not_isCyclic_of_isAlperinSubgroup P.isPGroup' hPnc hQ)) hn)

theorem exists_mem_conj_eq_of_map_le (hS : Situation G p P M) {A : Subgroup G}
    (hA : A ≤ (P : Subgroup G)) {g : G}
    (hg : A.map (MulAut.conj g⁻¹).toMonoidHom ≤ (P : Subgroup G)) :
    ∃ c ∈ M, ∀ a ∈ A, c⁻¹ * a * c = g⁻¹ * a * g := by
  haveI : Fact p.Prime := ⟨hS.prime⟩
  obtain ⟨c, hdec, hc⟩ := CFSG.RankTwoShapes.alperin_centric_radical_fusion P hA hg
  exact ⟨c, mem_of_alperinDecomposition hS hdec, hc⟩

theorem le_of_plane_le (hS : Situation G p P M) {B : Subgroup G} (hBP : B ≤ (P : Subgroup G))
    (hBC : centralizer (B : Set G) ≤ M) {Q : Subgroup G} (hQ : IsPGroup p Q) (hBQ : B ≤ Q) :
    Q ≤ M := by
  haveI : Fact p.Prime := ⟨hS.prime⟩
  obtain ⟨m, hm⟩ := pGroup_conjugate_into_sylow_within_overgroup p hS.prime P ⊤ le_top Q hQ
    le_top
  set g : G := (m : G)⁻¹ with hgdef
  have hgP : ∀ q ∈ Q, g⁻¹ * q * g ∈ (P : Subgroup G) := by
    intro q hq
    have := hm ⟨q, hq, rfl⟩
    simpa [hgdef, MulAut.conj_apply] using this
  have hmap : B.map (MulAut.conj g⁻¹).toMonoidHom ≤ (P : Subgroup G) := by
    rintro _ ⟨b, hb, rfl⟩
    simpa [MulAut.conj_apply] using hgP b (hBQ hb)
  obtain ⟨c, hcM, hc⟩ := exists_mem_conj_eq_of_map_le hS hBP hmap
  have hd : g * c⁻¹ ∈ centralizer (B : Set G) := by
    rw [mem_centralizer_iff]
    intro b hb
    have h1 := hc b hb
    calc b * (g * c⁻¹) = g * (g⁻¹ * b * g) * c⁻¹ := by group
      _ = g * (c⁻¹ * b * c) * c⁻¹ := by rw [h1]
      _ = g * c⁻¹ * b := by group
  have hgM : g ∈ M := by
    have := M.mul_mem (hBC hd) hcM
    simpa using this
  intro q hq
  have hqP := hgP q hq
  have hqM : g * (g⁻¹ * q * g) * g⁻¹ ∈ M :=
    M.mul_mem (M.mul_mem hgM (hS.sylow_le hqP)) (M.inv_mem hgM)
  simpa [mul_assoc] using hqM

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
