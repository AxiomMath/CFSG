module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCoreInner
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.FooteLit.HeCore

open CFSG Subgroup

theorem mem_of_odd_of_index_le_two {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (hH : H.index ≤ 2) {g : G} (hg : Odd (orderOf g)) : g ∈ H := by
  have h2 : g ^ 2 ∈ H := by
    have h0 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rcases (by omega : H.index = 1 ∨ H.index = 2) with h | h
    · rw [Subgroup.index_eq_one.mp h]
      exact mem_top _
    · exact Subgroup.sq_mem_of_index_two h g
  obtain ⟨k, hk⟩ := hg
  have h3 : g = (g ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = orderOf g + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [h3]
  exact H.pow_mem h2 _

theorem commute_of_odd_normal {G : Type*} [Group G] [Finite G] {C D N : Subgroup G}
    (hDC : D ≤ C) (hidx : D.relIndex C = 2) (hsimple : IsSimpleGroup (↥D ⧸ center ↥D))
    (heven : Even (Nat.card (↥D ⧸ center ↥D))) (hNC : N ≤ C)
    (hNn : ∀ c ∈ C, ∀ n ∈ N, c * n * c⁻¹ ∈ N) (hNodd : Odd (Nat.card N)) :
    ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := by
  have hND : N ≤ D := by
    intro n hn
    have hn' : (⟨n, hNC hn⟩ : C) ∈ D.subgroupOf C := by
      apply mem_of_odd_of_index_le_two (show (D.subgroupOf C).index ≤ 2 from hidx.le)
      rw [Subgroup.orderOf_mk]
      exact Odd.of_dvd_nat hNodd (N.orderOf_dvd_natCard hn)
    exact hn'
  have hN₁n : (N.subgroupOf D).Normal := ⟨fun n hn g => hNn g (hDC g.2) n hn⟩
  have hmap : ((N.subgroupOf D).map (QuotientGroup.mk' (center ↥D))).Normal :=
    hN₁n.map _ (QuotientGroup.mk'_surjective _)
  have := hsimple
  have := hmap
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((N.subgroupOf D).map (QuotientGroup.mk' (center ↥D))) with hbot | htop
  ·
    intro x hx y hy
    have hxZ : (⟨x, hND hx⟩ : D) ∈ center ↥D := by
      rw [← QuotientGroup.ker_mk' (center ↥D), MonoidHom.mem_ker]
      have h1 : QuotientGroup.mk' (center ↥D) ⟨x, hND hx⟩ ∈
          (N.subgroupOf D).map (QuotientGroup.mk' (center ↥D)) := ⟨⟨x, hND hx⟩, hx, rfl⟩
      rw [hbot, mem_bot] at h1
      exact h1
    have h2 := mem_center_iff.mp hxZ ⟨y, hND hy⟩
    exact (congrArg Subtype.val h2).symm
  ·
    exfalso
    have h1 : Nat.card (↥D ⧸ center ↥D) ∣ Nat.card N := by
      have h2 := card_map_dvd (N.subgroupOf D) (QuotientGroup.mk' (center ↥D))
      rwa [htop, card_top, Nat.card_congr (subgroupOfEquivOfLe hND).toEquiv] at h2
    exact (Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hNodd h1)) heven

theorem generalizedFitting_mulAut_he {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (θ : S ≃* Blueprint.NativeSporadic.He) :
    IsSimpleGroup (GeneralizedFitting.subgroup (MulAut S)) ∧
      (∃ x y : GeneralizedFitting.subgroup (MulAut S), x * y ≠ y * x) ∧
      Nonempty (GeneralizedFitting.subgroup (MulAut S) ≃* Blueprint.NativeSporadic.He) := by
  have hZ : center S = ⊥ := center_eq_bot_of_isSimpleGroup hna
  have hκ := mulAut_conj_injective hZ
  set Inn := (MulAut.conj : S →* MulAut S).range with hInn
  let e : S ≃* Inn := MonoidHom.ofInjective hκ
  have hF := generalizedFitting_mulAut_eq_range hna
  have : IsSimpleGroup Inn := e.symm.isSimpleGroup
  refine ⟨by rw [hF]; infer_instance, ?_, ⟨((MulEquiv.subgroupCongr hF).trans e.symm).trans θ⟩⟩
  rw [hF]
  obtain ⟨x, y, hxy⟩ := hna
  exact ⟨e x, e y, fun h => hxy (e.injective (by rw [map_mul, map_mul]; exact h))⟩

end CFSG.ComponentClassification.FooteLit.HeCore
