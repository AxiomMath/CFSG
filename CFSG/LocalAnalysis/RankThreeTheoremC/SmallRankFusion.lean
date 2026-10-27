module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankSetup
import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.MaximalPairGeometry

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem SmallRankPlane.exists_transvection {p : ℕ} (hp : p.Prime) {P : Subgroup G}
    (hP : IsPGroup p P) {x z : G} (hB : SmallRankPlane p P x z)
    (hzc : z ∈ centralizer (P : Set G)) (hz1 : z ≠ 1) (hzp : z ^ p = 1)
    (hA : ∃ A : Subgroup G, A ≤ P ∧ CFSG.IsElementaryAbelian p A ∧ Nat.card A = p ^ 3) :
    (∀ h ∈ P ⊓ normalizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G),
        h * x * h⁻¹ * x⁻¹ ∈ zpowers z) ∧
      ∃ h ∈ P ⊓ normalizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G),
        h * x * h⁻¹ * x⁻¹ ≠ 1 := by
  classical
  have hfact : Fact p.Prime := ⟨hp⟩
  have hBP : zpowers x ⊔ zpowers z ≤ P := hB.isIsolatedPlane.1
  have hBc : Nat.card ↥(zpowers x ⊔ zpowers z) = p ^ 2 := hB.card_eq
  have hBQ : zpowers x ⊔ zpowers z ≤
      P ⊓ normalizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G) :=
    le_inf hBP le_normalizer
  have hQp : IsPGroup p ↥(P ⊓ normalizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G)) :=
    hP.to_le inf_le_left
  have hezc : zpowers z ≤ centralizer (P : Set G) := zpowers_le.mpr hzc
  have hcz : Nat.card (zpowers z) = p := by rw [Nat.card_zpowers, orderOf_eq_prime hzp hz1]
  have hzne : zpowers z ≠ zpowers x ⊔ zpowers z := by
    intro h
    rw [← h, hcz] at hBc
    have h12 : (1 : ℕ) = 2 := Nat.pow_right_injective hp.two_le (by simpa using hBc)
    omega
  obtain ⟨u, huB, huz, hu⟩ := exists_mem_not_mem_commutator_mem hQp hBQ le_sup_right hzne
    inf_le_right (inf_le_left.trans (le_normalizer_zpowers_of_le_centralizer hzc))
  have hup : u ^ p = 1 := hB.isElemAbelian.2 u huB
  have hzu : ∀ e ∈ zpowers z, e * u = u * e := fun e he =>
    (mem_centralizer_iff.mp (hezc he) u (hBP huB)).symm
  have hBeq : zpowers z ⊔ zpowers u = zpowers x ⊔ zpowers z := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le le_sup_right (zpowers_le.mpr huB)) ?_
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp (zpowers z) hup huz hzu, hBc, hcz,
      pow_two]
  have hcommQ : ∀ h ∈ P ⊓ normalizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G),
      h * x * h⁻¹ * x⁻¹ ∈ zpowers z := by
    intro h hh
    have hxmem : x ∈ ((zpowers u ⊔ zpowers z : Subgroup G) : Set G) := by
      rw [sup_comm, hBeq]
      exact mem_sup_left (mem_zpowers x)
    rw [coe_mul_of_left_le_normalizer_right _ _
      (zpowers_le.mpr ((le_normalizer_zpowers_of_le_centralizer hzc) (hBP huB)))] at hxmem
    obtain ⟨a, ha, c, hc, hac⟩ := hxmem
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp ha
    have hcc : h * c * h⁻¹ = c := by
      rw [mem_centralizer_iff.mp (hezc hc) h hh.1, mul_inv_cancel_right]
    obtain ⟨d, hdeq⟩ : ∃ d, d = h * u * h⁻¹ * u⁻¹ := ⟨_, rfl⟩
    have hd : d ∈ zpowers z := hdeq ▸ hu h hh
    have hdu : Commute d u := (mem_centralizer_iff.mp (hezc hd) u (hBP huB)).symm
    have hhu : h * u * h⁻¹ = d * u := by rw [hdeq]; group
    have hhum : h * u ^ m * h⁻¹ = d ^ m * u ^ m := by
      rw [← conj_zpow, hhu, hdu.mul_zpow]
    rw [← hac]
    have key : h * (u ^ m * c) * h⁻¹ * (u ^ m * c)⁻¹ = d ^ m := by
      calc h * (u ^ m * c) * h⁻¹ * (u ^ m * c)⁻¹
          = (h * u ^ m * h⁻¹) * (h * c * h⁻¹) * c⁻¹ * (u ^ m)⁻¹ := by group
        _ = d ^ m * u ^ m * c * c⁻¹ * (u ^ m)⁻¹ := by rw [hhum, hcc]
        _ = d ^ m := by group
    rw [key]
    exact zpow_mem hd m
  refine ⟨hcommQ, ?_⟩
  by_contra hall
  push Not at hall
  have hQC : P ⊓ normalizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G) ≤
      centralizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G) := by
    intro h hh
    have hx' : h * x = x * h := by
      calc h * x = (h * x * h⁻¹ * x⁻¹) * x * h := by group
        _ = x * h := by rw [hall h hh, one_mul]
    have hBh : zpowers x ⊔ zpowers z ≤ centralizer ({h} : Set G) :=
      sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hx'.symm))
        (zpowers_le.mpr
          (mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hzc h hh.1).symm))
    exact mem_centralizer_iff.mpr fun b hb => mem_centralizer_singleton_iff.mp (hBh hb)
  obtain ⟨A, hAP, hAe, hAc⟩ := hA
  have hnot := (isolatedPlane_structure hp hP hB.isIsolatedPlane hAP hAe hAc).1
  have hQlt : P ⊓ normalizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G) < P :=
    lt_of_le_of_ne inf_le_left fun h => hnot (by rw [← h]; exact inf_le_right)
  obtain ⟨g, hg, hgQ⟩ := IsConcreteLE.exists_of_lt
    (pGroup_proper_subgroup_lt_internal_normalizer p hp P _ hP hQlt)
  have hBg : (zpowers x ⊔ zpowers z).map (MulAut.conj g).toMonoidHom ≤ zpowers x ⊔ zpowers z := by
    rintro _ ⟨b, hb, rfl⟩
    have hbp : b ^ p = 1 := hB.isElemAbelian.2 b hb
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine hB.mem_of_mem_centralizer _ (mem_centralizer_iff.mpr fun b₀ hb₀ => ?_) ?_
    · have hn : g⁻¹ * b₀ * g ∈ P ⊓ normalizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G) :=
        (mem_normalizer_iff.mp hg.2 (g⁻¹ * b₀ * g)).mpr
          (by rw [show g * (g⁻¹ * b₀ * g) * g⁻¹ = b₀ by group]; exact hBQ hb₀)
      have hcomm := mem_centralizer_iff.mp (hQC hn) b hb
      calc b₀ * (g * b * g⁻¹) = g * ((g⁻¹ * b₀ * g) * b) * g⁻¹ := by group
        _ = g * (b * (g⁻¹ * b₀ * g)) * g⁻¹ := by rw [hcomm]
        _ = g * b * g⁻¹ * b₀ := by group
    · rw [conj_pow, hbp, mul_one, mul_inv_cancel]
  exact hgQ ⟨hg.1, mem_normalizer_iff_map_conj_eq.mpr
    (Subgroup.eq_of_le_of_card_ge hBg (card_map_of_injective (MulAut.conj g).injective).ge)⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
