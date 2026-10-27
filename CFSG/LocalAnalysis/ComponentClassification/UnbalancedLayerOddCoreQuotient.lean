module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreFreeTwoLayer

public section

namespace CFSG.ComponentClassification.UnbalancedLayer

open CFSG CFSG.LocalCores Subgroup

variable {H : Type*} [Group H]

theorem map_conjugate {G' : Type*} [Group G'] (f : H →* G') (L : Subgroup H) (g : H) :
    (conjugate L g).map f = conjugate (L.map f) (f g) := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hy
    rw [mem_conjugate_iff] at hx ⊢
    rw [← map_inv, ← map_mul, ← map_mul]
    exact mem_map_of_mem f hx
  · intro hy
    rw [mem_conjugate_iff] at hy
    obtain ⟨x, hx, hxy⟩ := mem_map.mp hy
    refine ⟨g⁻¹ * x * g, conj_mem_conjugate hx g, ?_⟩
    rw [map_mul, map_mul, map_inv, hxy]
    group

theorem conjugate_eq_of_mem_normalizer {K : Subgroup H} {g : H}
    (hg : g ∈ normalizer (K : Set H)) : conjugate K g = K := by
  ext x
  rw [mem_conjugate_iff]
  exact ((mem_normalizer_iff.mp hg) x).symm

theorem centralizer_zpowers_eq (g : H) :
    centralizer ((zpowers g : Subgroup H) : Set H) = centralizer ({g} : Set H) := by
  refine le_antisymm (centralizer_le (Set.singleton_subset_iff.mpr (mem_zpowers g))) ?_
  intro x hx
  rw [mem_centralizer_iff]
  intro h hh
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
  have hc : Commute g x := (mem_centralizer_singleton_iff.mp hx).symm
  exact (hc.zpow_left k).eq

theorem isPComponent_conjugate {p : ℕ} {L : Subgroup H} (hL : IsPComponent p L) (g : H) :
    IsPComponent p (conjugate L g) := by
  unfold conjugate
  exact LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent p _ hL

variable [Finite H]

theorem exists_mem_centralizer_of_inv_mul_conj_mem {R : Subgroup H} [R.Normal]
    (hR : Odd (Nat.card R)) {t : H} (ht : t * t = 1) {x : H} (hx : x⁻¹ * (t⁻¹ * x * t) ∈ R) :
    ∃ c ∈ centralizer ({t} : Set H), x⁻¹ * c ∈ R := by
  classical
  have hmem : ∀ y : H, x⁻¹ * y ∈ R → x⁻¹ * (t⁻¹ * y * t) ∈ R := by
    intro y hy
    have h1 : t⁻¹ * (x⁻¹ * y) * t ∈ R := by
      have h := (inferInstance : R.Normal).conj_mem _ hy t⁻¹
      rwa [inv_inv] at h
    have h := mul_mem hx h1
    rwa [show x⁻¹ * (t⁻¹ * x * t) * (t⁻¹ * (x⁻¹ * y) * t) = x⁻¹ * (t⁻¹ * y * t) by group] at h
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hσσ : ∀ y : H, t⁻¹ * (t⁻¹ * y * t) * t = y := by
    intro y
    rw [htinv]
    calc t * (t * y * t) * t = (t * t) * y * (t * t) := by group
      _ = y := by rw [ht, one_mul, mul_one]
  let σ : Equiv.Perm {y : H // x⁻¹ * y ∈ R} :=
    { toFun := fun y => ⟨t⁻¹ * y.1 * t, hmem y.1 y.2⟩
      invFun := fun y => ⟨t⁻¹ * y.1 * t, hmem y.1 y.2⟩
      left_inv := fun y => Subtype.ext (hσσ y.1)
      right_inv := fun y => Subtype.ext (hσσ y.1) }
  have hσ : Function.Involutive σ := fun y => Subtype.ext (hσσ y.1)
  have hcard : Nat.card {y : H // x⁻¹ * y ∈ R} = Nat.card R :=
    Nat.card_congr
      { toFun := fun y => ⟨x⁻¹ * y.1, y.2⟩
        invFun := fun r => ⟨x * r.1, by simp⟩
        left_inv := fun y => Subtype.ext (by simp)
        right_inv := fun r => Subtype.ext (by simp) }
  have hmod := InvolutionFixedPoints.fixed_card_mod_two σ hσ
  rw [hcard, Nat.odd_iff.mp hR] at hmod
  have hne : Nat.card {y : {y : H // x⁻¹ * y ∈ R} // σ y = y} ≠ 0 := by omega
  obtain ⟨⟨⟨c, hc⟩, hfix⟩⟩ := (Nat.card_ne_zero.mp hne).1
  have hc' : t⁻¹ * c * t = c := congrArg Subtype.val hfix
  exact ⟨c, mem_centralizer_singleton_iff_conj.mpr hc', hc⟩

theorem map_centralizer_eq {R : Subgroup H} [R.Normal] (hR : Odd (Nat.card R)) {t : H}
    (ht : t * t = 1) :
    (centralizer ({t} : Set H)).map (QuotientGroup.mk' R) =
      centralizer ({QuotientGroup.mk' R t} : Set (H ⧸ R)) := by
  apply le_antisymm
  · intro q hq
    obtain ⟨c, hc, rfl⟩ := mem_map.mp hq
    rw [mem_centralizer_singleton_iff] at hc ⊢
    rw [← map_mul, ← map_mul, hc]
  · intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R q
    have hq' := mem_centralizer_singleton_iff.mp hq
    have hx : x⁻¹ * (t⁻¹ * x * t) ∈ R := by
      rw [← QuotientGroup.ker_mk' R, MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [mul_assoc (QuotientGroup.mk' R t)⁻¹, hq', inv_mul_cancel_left, inv_mul_cancel]
    obtain ⟨c, hc, hxc⟩ := exists_mem_centralizer_of_inv_mul_conj_mem hR ht hx
    refine ⟨c, hc, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq.mpr hxc).symm

theorem map_normal_centralizer {R : Subgroup H} [R.Normal] (hR : Odd (Nat.card R)) {t : H}
    (ht : t * t = 1) {D : Subgroup H} (hDC : D ≤ centralizer ({t} : Set H))
    (hDn : (D.subgroupOf (centralizer ({t} : Set H))).Normal) :
    D.map (QuotientGroup.mk' R) ≤ centralizer ({QuotientGroup.mk' R t} : Set (H ⧸ R)) ∧
      ((D.map (QuotientGroup.mk' R)).subgroupOf
        (centralizer ({QuotientGroup.mk' R t} : Set (H ⧸ R)))).Normal := by
  have hCmap := map_centralizer_eq hR ht
  have hle : D.map (QuotientGroup.mk' R) ≤
      centralizer ({QuotientGroup.mk' R t} : Set (H ⧸ R)) := by
    rw [← hCmap]
    exact map_mono hDC
  refine ⟨hle, ?_⟩
  rw [normal_subgroupOf_iff_le_normalizer hle, ← hCmap]
  intro q' hq'
  obtain ⟨c, hc, rfl⟩ := mem_map.mp hq'
  rw [mem_normalizer_iff]
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective R q
  constructor
  · intro hy
    obtain ⟨d, hd, hdy⟩ := mem_map.mp hy
    refine mem_map.mpr ⟨c * d * c⁻¹, conj_mem_of_normal_subgroupOf hDC hDn hc hd, ?_⟩
    rw [map_mul, map_mul, map_inv, hdy]
  · intro hy
    obtain ⟨d, hd, hdy⟩ := mem_map.mp hy
    refine mem_map.mpr
      ⟨c⁻¹ * d * c⁻¹⁻¹, conj_mem_of_normal_subgroupOf hDC hDn (inv_mem hc) hd, ?_⟩
    simp only [map_mul, map_inv, hdy]
    group

omit [Finite H] in
theorem orderOf_mk_eq_two {R : Subgroup H} [R.Normal] (hR : Odd (Nat.card R)) {t : H}
    (ht : orderOf t = 2) : orderOf (QuotientGroup.mk' R t) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htR : t ∉ R := fun h => by
    have hdvd := R.orderOf_dvd_natCard h
    rw [ht] at hdvd
    exact (Nat.not_even_iff_odd.mpr hR) (even_iff_two_dvd.mpr hdvd)
  apply orderOf_eq_prime
  · rw [← map_pow, ← ht, pow_orderOf_eq_one, map_one]
  · intro h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    exact htR h

theorem pComponent_eq_of_map_eq {p : ℕ} [Fact p.Prime] {L M : Subgroup H}
    (hL : IsPComponent p L) (hM : IsPComponent p M)
    (h : L.map (QuotientGroup.mk' (pPrimeCore p H)) = M.map (QuotientGroup.mk' (pPrimeCore p H))) :
    L = M :=
  (CatalogueBPrimeJoin.canonical_prime_component_lift p).2.injOn hL hM h

theorem mem_normalizer_of_map {p : ℕ} [Fact p.Prime] {L : Subgroup H} (hL : IsPComponent p L)
    {d : H} (hd : QuotientGroup.mk' (pPrimeCore p H) d ∈
      normalizer ((L.map (QuotientGroup.mk' (pPrimeCore p H)) : Subgroup _) : Set _)) :
    d ∈ normalizer (L : Set H) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  change L.map (MulAut.conj d).toMonoidHom = L
  rw [map_conj_eq_conjugate]
  apply pComponent_eq_of_map_eq (isPComponent_conjugate hL d⁻¹) hL
  rw [map_conjugate, map_inv]
  exact conjugate_eq_of_mem_normalizer (inv_mem hd)

theorem pPrimeCore_le_normalizer {p : ℕ} [Fact p.Prime] {L : Subgroup H}
    (hL : IsPComponent p L) : pPrimeCore p H ≤ normalizer (L : Set H) := by
  intro n hn
  apply mem_normalizer_of_map hL
  have h1 : QuotientGroup.mk' (pPrimeCore p H) n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
  rw [h1]
  exact one_mem _

end CFSG.ComponentClassification.UnbalancedLayer
