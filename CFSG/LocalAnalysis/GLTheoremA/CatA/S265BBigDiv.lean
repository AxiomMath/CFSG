module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BBig
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BBigGood
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BRes
public import CFSG.HardMathSupport.Solomon.Coordinator.FixSubgroupInf

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup iInf_fixSubgroup_zpowers)
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie (IsGood)
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn

namespace BBig

theorem exists_good_zpowers_of_mulEquiv {S T : Type} [Group S] [Group T] [Finite S] [Finite T]
    (e : S ≃* T) {A : Subgroup (MulAut S)}
    (h : ∃ a ∈ A.map (MulAut.congr e).toMonoidHom, a ≠ 1 ∧ IsGood 3 (Subgroup.zpowers a)) :
    ∃ a ∈ A, a ≠ 1 ∧ IsGood 3 (Subgroup.zpowers a) := by
  obtain ⟨_, ⟨a, ha, rfl⟩, hne, hgood⟩ := h
  refine ⟨a, ha, fun h1 => hne (by rw [h1, map_one]), ?_⟩
  rw [isGood_iff_map_mulEquiv e (Subgroup.zpowers a), MonoidHom.map_zpowers]
  exact hgood

theorem xun_exists_good_zpowers {N : ℕ} (hN5 : 5 ≤ N) (hN9 : N ≤ 9)
    (A : Subgroup (MulAut (xunM N))) (hA : IsElemAbelian 3 A) (h4 : 3 ^ 4 ≤ Nat.card A)
    (hn : 3 ^ N ≤ 3 ^ 3 * Nat.card A) : ∃ a ∈ A, a ≠ 1 ∧ IsGood 3 (Subgroup.zpowers a) := by
  obtain ⟨c, hc⟩ := exists_diag_conj_of_isElemAbelian hN5 hN9 A hA h4 hn
  set γ : MulAut (xunM N) := xunConj N (by omega) c with hγ
  refine exists_good_zpowers_of_mulEquiv γ ?_
  have hA'' : IsElemAbelian 3 (A.map (MulAut.congr γ).toMonoidHom) :=
    isElemAbelian_map_of_injective (MulAut.congr γ).injective hA
  have h4'' : 3 ^ 4 ≤ Nat.card (A.map (MulAut.congr γ).toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective (MulAut.congr γ).injective]
  refine exists_isGood_zpowers_of_diag hN5 _ hA'' h4'' fun g hg => ?_
  rw [mem_map_mulAut_congr] at hg
  have hg' : xunConj N (by omega) (c⁻¹ * g * c) ∈ A := by
    have heq : xunConj N (by omega) (c⁻¹ * g * c) =
        MulAut.congr γ.symm (xunConj N (by omega) g) := by
      rw [mulAut_congr_eq_conj, map_mul, map_mul, map_inv, hγ]
      rfl
    rw [heq]
    exact hg
  have := hc (c⁻¹ * g * c) hg'
  have hcg : c * (c⁻¹ * g * c) * c⁻¹ = g := by group
  rw [hcg] at this
  exact this

end BBig

theorem un_exists_fix_layer {n : ℕ} (hn5 : 5 ≤ n) (hn9 : n ≤ 9) {G : Type} [Group G] [Finite G]
    (hG : catalogIs G (tyUnTwo n)) {A : Subgroup (MulAut G)} (hA : IsElemAbelian 3 A)
    (h4 : 3 ^ 4 ≤ Nat.card A) (hn : 3 ^ n ≤ 3 ^ 3 * Nat.card A) :
    ∃ a ∈ A, a ≠ 1 ∧ GLAPLayer 3 (fixSubgroup a) ≠ ⊥ := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hG
  cases i with
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | twistedA r q =>
      obtain ⟨hr, hq⟩ : r + 1 = n ∧ q.card = 2 := hi
      obtain ⟨e0⟩ := nonempty_mulEquiv_xunM r q hv hq
      subst hr
      have hmap : Nat.card (A.map (MulAut.congr (e.trans e0)).toMonoidHom) = Nat.card A :=
        Subgroup.card_map_of_injective (MulAut.congr (e.trans e0)).injective
      obtain ⟨a, ha, hne, hgood⟩ := BBig.exists_good_zpowers_of_mulEquiv (e.trans e0)
        (BBig.xun_exists_good_zpowers hn5 hn9 _
          (isElemAbelian_map_of_injective (MulAut.congr (e.trans e0)).injective hA)
          (by rw [hmap]; exact h4) (by rw [hmap]; exact hn))
      refine ⟨a, ha, hne, ?_⟩
      unfold IsGood at hgood
      rwa [iInf_fixSubgroup_zpowers] at hgood
    | _ => exact hi.elim
  | _ => exact hi.elim

end CFSG.LocalAnalysis.GLTheoremA.S265

end
