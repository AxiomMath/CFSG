module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog Subgroup

open scoped Pointwise

private theorem centerOf_eq_map_center {C : Type*} [Group C] (X : Subgroup C) :
    centerOf X = (Subgroup.center ↥X).map X.subtype := by
  ext g
  constructor
  · rintro ⟨hgX, hgC⟩
    refine ⟨⟨g, hgX⟩, Subgroup.mem_center_iff.mpr fun h => Subtype.ext ?_, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp hgC h h.2
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨h, hh⟩)

private theorem centerOf_map_of_injective {C D : Type*} [Group C] [Group D]
    (f : C →* D) (hf : Function.Injective f) (A : Subgroup C) :
    centerOf (A.map f) = (centerOf A).map f := by
  ext x
  constructor
  · rintro ⟨hx1, hx2⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx1
    refine Subgroup.mem_map.mpr ⟨a, ?_, rfl⟩
    refine ⟨ha, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
    apply hf
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp hx2 (f b) (Subgroup.mem_map_of_mem f hb)
  · rintro ⟨a, ha, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem f ha.1, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, ← map_mul]
    exact congrArg f (Subgroup.mem_centralizer_iff.mp ha.2 b hb)

private theorem conj_mem_centerOf_of_mem_normalizer {C : Type*} [Group C] {H : Subgroup C}
    {g x : C} (hg : g ∈ Subgroup.normalizer H) (hx : x ∈ centerOf H) :
    g * x * g⁻¹ ∈ centerOf H := by
  refine ⟨?_, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp hg x).mp hx.1
  · have hy' : g⁻¹ * y * g ∈ H := by
      have hconj : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
      exact (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * y * g)).mpr (hconj.symm ▸ hy)
    have hx2 : x ∈ Subgroup.centralizer H := hx.2
    have hcomm := Subgroup.mem_centralizer_iff.mp hx2 (g⁻¹ * y * g) hy'
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [hcomm]
      _ = (g * x * g⁻¹) * y := by group

private theorem eq_of_mem_zpowers_of_orderOf_eq_two {C : Type*} [Group C] [Finite C] {z x : C}
    (hz : orderOf z = 2) (hx : x ∈ Subgroup.zpowers z) (hx2 : orderOf x = 2) : x = z := by
  classical
  have hxne : x ≠ 1 := by rintro rfl; rw [orderOf_one] at hx2; norm_num at hx2
  obtain ⟨n, hn, hnx⟩ := Finset.mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1 hx)
  rw [Finset.mem_range, hz] at hn
  interval_cases n
  · exact absurd (by simpa using hnx.symm) hxne
  · simpa using hnx.symm

theorem IsExtraspecialPlusByA5WrTwoWith.centerOf_sylow {C : Type} [Group C] [Finite C]
    {Q : Subgroup C} [Q.Normal] (h : IsExtraspecialPlusByA5WrTwoWith C Q) {z : C}
    (hz : z ∈ Subgroup.center C) (hz2 : orderOf z = 2) (S : Sylow 2 C) :
    centerOf (S : Subgroup C) = Subgroup.zpowers z := by
  haveI : CFSG.IsExtraspecial 2 ↥Q := h.plus.1
  have hQp : IsPGroup 2 (Q : Subgroup C) := CFSG.IsExtraspecial.isPGroup 2 ↥Q
  have hQS : Q ≤ (S : Subgroup C) := IsPGroup.le_sylow_of_normal hQp S
  have hzcent : z ∈ Subgroup.centralizer (Q : Set C) :=
    Subgroup.mem_centralizer_iff.mpr fun q _ => Subgroup.mem_center_iff.mp hz q
  have hzQ : z ∈ Q := h.centralizer_le hzcent
  have hzcenterQ : z ∈ centerOf Q := ⟨hzQ, hzcent⟩
  have hcardQ : Nat.card (centerOf Q) = 2 := by
    rw [centerOf_eq_map_center, Subgroup.card_map_of_injective Q.subtype_injective,
      CFSG.IsExtraspecial.center_order_p 2 ↥Q]
  have hcenterQ : centerOf Q = Subgroup.zpowers z :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzcenterQ)
      (by rw [hcardQ, Nat.card_zpowers, hz2])).symm
  have hcentQ : Subgroup.centralizer (Q : Set C) ≤ Subgroup.zpowers z := by
    rw [← hcenterQ]
    exact le_of_eq (inf_eq_right.mpr h.centralizer_le).symm
  have hzS : z ∈ (S : Subgroup C) := hQS hzQ
  have hzcenterS : z ∈ centerOf (S : Subgroup C) :=
    ⟨hzS, Subgroup.mem_centralizer_iff.mpr fun q _ => Subgroup.mem_center_iff.mp hz q⟩
  refine le_antisymm ?_ (Subgroup.zpowers_le.mpr hzcenterS)
  exact le_trans inf_le_right
    (le_trans (Subgroup.centralizer_le (show (Q : Set C) ⊆ (S : Set C) from hQS)) hcentQ)

theorem exists_sylow_centerOf_eq_zpowers {G : Type} [Group G] [Finite G] {z : G}
    (hz : orderOf z = 2)
    (h : IsExtraspecialPlusByA5WrTwo (Subgroup.centralizer ({z} : Set G))) :
    ∃ S : Sylow 2 G, centerOf (S : Subgroup G) = Subgroup.zpowers z := by
  classical
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  obtain ⟨Q, hQn, hQ⟩ := h
  letI : Q.Normal := hQn
  have hzC : z ∈ C := by simp [hC, Subgroup.mem_centralizer_singleton_iff]
  let zC : C := ⟨z, hzC⟩
  have hzC_center : zC ∈ Subgroup.center C := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hC ▸ y.2)
  have hzC_order : orderOf zC = 2 := by simpa [zC] using hz
  let S₀ : Sylow 2 C := default
  have hcenter₀ : centerOf (S₀ : Subgroup C) = Subgroup.zpowers zC :=
    IsExtraspecialPlusByA5WrTwoWith.centerOf_sylow hQ hzC_center hzC_order S₀
  let S₁ : Subgroup G := (S₀ : Subgroup C).map C.subtype
  have hS₁p : IsPGroup 2 S₁ := S₀.isPGroup'.map C.subtype
  have hcenter₁ : centerOf S₁ = Subgroup.zpowers z := by
    change centerOf ((S₀ : Subgroup C).map C.subtype) = Subgroup.zpowers z
    rw [centerOf_map_of_injective C.subtype C.subtype_injective, hcenter₀,
      MonoidHom.map_zpowers]
    rfl
  obtain ⟨P, hS₁P⟩ := IsPGroup.exists_le_sylow hS₁p
  have hS₁P_eq : S₁ = (P : Subgroup G) := by
    refine le_antisymm hS₁P ?_
    by_contra hnot
    have hlt : S₁.subgroupOf P < ⊤ := by
      rw [lt_iff_le_and_ne]
      exact ⟨le_top, fun htop => hnot (Subgroup.subgroupOf_eq_top.mp htop)⟩
    haveI hnil : Group.IsNilpotent (P : Subgroup G) := P.isPGroup'.isNilpotent
    have hnc : NormalizerCondition (P : Subgroup G) := Group.normalizerCondition_of_isNilpotent
    have hnormalizer : ∃ g : ↥P, g ∈ Subgroup.normalizer (S₁.subgroupOf P) ∧
        g ∉ S₁.subgroupOf P := by
      by_contra h
      push Not at h
      have heq : Subgroup.normalizer (S₁.subgroupOf P) = S₁.subgroupOf P :=
        le_antisymm h Subgroup.le_normalizer
      exact (ne_of_lt (hnc (S₁.subgroupOf P) hlt)) heq.symm
    obtain ⟨g, hgN, hgS⟩ := hnormalizer
    have hgN' : (g : G) ∈ Subgroup.normalizer S₁ := by
      rw [← Subgroup.subgroupOf_normalizer_eq hS₁P] at hgN
      exact Subgroup.mem_subgroupOf.mp hgN
    have hg_notS₁ : (g : G) ∉ S₁ := hgS
    have hz_center₁ : z ∈ centerOf S₁ := by
      rw [hcenter₁]; exact Subgroup.mem_zpowers z
    have hconjz : (g : G) * z * (g : G)⁻¹ ∈ Subgroup.zpowers z := by
      rw [← hcenter₁]
      exact conj_mem_centerOf_of_mem_normalizer hgN' hz_center₁
    have hconjz_order : orderOf ((g : G) * z * (g : G)⁻¹) = 2 := by
      rw [← SemiconjBy.orderOf_eq (g : G) (SemiconjBy.conj_mk (g : G) z)]
      exact hz
    have hconjz_eq : (g : G) * z * (g : G)⁻¹ = z :=
      eq_of_mem_zpowers_of_orderOf_eq_two hz hconjz hconjz_order
    have hgC : (g : G) ∈ C := by
      rw [hC, Subgroup.mem_centralizer_singleton_iff]
      have h := congrArg (fun t => t * (g : G)) hconjz_eq
      simpa [mul_assoc] using h
    have hgP : (g : G) ∈ (P : Subgroup G) := g.2
    have hsup_le_P : S₁ ⊔ Subgroup.zpowers (g : G) ≤ (P : Subgroup G) :=
      sup_le hS₁P (Subgroup.zpowers_le.mpr hgP)
    have hsup_p : IsPGroup 2 ((S₁ ⊔ Subgroup.zpowers (g : G)) : Subgroup G) :=
      IsPGroup.to_le (H := (S₁ ⊔ Subgroup.zpowers (g : G) : Subgroup G)) P.isPGroup' hsup_le_P
    let N : Subgroup C := (S₁ ⊔ Subgroup.zpowers (g : G)).comap C.subtype
    have hNp : IsPGroup 2 N := hsup_p.comap_of_injective C.subtype C.subtype_injective
    have hS₀N : (S₀ : Subgroup C) ≤ N := by
      intro s hs
      exact Subgroup.mem_sup_left (Subgroup.mem_map_of_mem C.subtype hs)
    have hgC' : (⟨(g : G), hgC⟩ : C) ∈ N :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers (g : G))
    have hgC'_notS₀ : (⟨(g : G), hgC⟩ : C) ∉ (S₀ : Subgroup C) := by
      intro hmem
      exact hg_notS₁ (Subgroup.mem_map_of_mem C.subtype hmem)
    have hNeq : N ≠ (S₀ : Subgroup C) := fun hEq => hgC'_notS₀ (hEq ▸ hgC')
    exact hNeq (S₀.is_maximal' hNp hS₀N)
  exact ⟨P, by rw [← hcenter₁, hS₁P_eq]⟩

theorem odd_index_centralizer_of_isExtraspecialPlusByA5WrTwo {G : Type} [Group G] [Finite G] {z : G}
    (hz : orderOf z = 2)
    (h : IsExtraspecialPlusByA5WrTwo (Subgroup.centralizer ({z} : Set G))) :
    Odd (Subgroup.centralizer ({z} : Set G)).index := by
  obtain ⟨S, hS⟩ := exists_sylow_centerOf_eq_zpowers hz h
  have hzcenter : z ∈ centerOf (S : Subgroup G) := by
    rw [hS]; exact Subgroup.mem_zpowers z
  have hSC : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
    intro s hs
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hzcenter.2 s hs)
  have hSodd : Odd (S : Sylow 2 G).index := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact S.not_dvd_index
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h2
  exact hSodd.not_two_dvd_nat (h2.trans (Subgroup.index_dvd_of_le hSC))

theorem exists_isConj_centerOf_sylow {G : Type} [Group G] [Finite G] {z : G} (hz : orderOf z = 2)
    (h : IsExtraspecialPlusByA5WrTwo (Subgroup.centralizer ({z} : Set G))) (S : Sylow 2 G) :
    ∃ w : G, IsConj z w ∧ centerOf (S : Subgroup G) = Subgroup.zpowers w := by
  obtain ⟨S₀, hS₀⟩ := exists_sylow_centerOf_eq_zpowers hz h
  haveI : Finite (Sylow 2 G) := Sylow.finite_of_finiteIndex S₀
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (M := G) S₀ S
  refine ⟨g * z * g⁻¹, ?_, ?_⟩
  · exact isConj_iff.mpr ⟨g, rfl⟩
  · have hgsub : (S : Subgroup G) = S₀.map (MulAut.conj g).toMonoidHom := by
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      rfl
    rw [hgsub, centerOf_map_of_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,
      hS₀, MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

end CFSG.EvenSporadicStandard.HNRecog.Section3
