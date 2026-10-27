module

public import CFSG.CGT.M24S.Balance

public section

namespace CFSG.CGT.M24S

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.Holt.General

variable {G : Type} [Group G]

@[expose] def ConjAdj (T : Subgroup G) (g h : G) : Prop :=
  ∃ x ∈ T, x ≠ 1 ∧ ∃ y ∈ T, y ≠ 1 ∧
    g * x * g⁻¹ * (h * y * h⁻¹) = h * y * h⁻¹ * (g * x * g⁻¹)

@[expose] def componentStab (T : Subgroup G) : Subgroup G :=
  Subgroup.closure {g | ConjAdj T 1 g}

theorem ConjAdj.mul_left {T : Subgroup G} {g h : G} (hgh : ConjAdj T g h) (k : G) :
    ConjAdj T (k * g) (k * h) := by
  obtain ⟨x, hx, hx1, y, hy, hy1, hc⟩ := hgh
  refine ⟨x, hx, hx1, y, hy, hy1, ?_⟩
  calc k * g * x * (k * g)⁻¹ * (k * h * y * (k * h)⁻¹)
      = k * (g * x * g⁻¹ * (h * y * h⁻¹)) * k⁻¹ := by group
    _ = k * (h * y * h⁻¹ * (g * x * g⁻¹)) * k⁻¹ := by rw [hc]
    _ = k * h * y * (k * h)⁻¹ * (k * g * x * (k * g)⁻¹) := by group

theorem ConjAdj.symm {T : Subgroup G} {g h : G} (hgh : ConjAdj T g h) : ConjAdj T h g := by
  obtain ⟨x, hx, hx1, y, hy, hy1, hc⟩ := hgh
  exact ⟨y, hy, hy1, x, hx, hx1, hc.symm⟩

theorem mem_componentStab_of_conjAdj {T : Subgroup G} {g : G} (hg : ConjAdj T 1 g) :
    g ∈ componentStab T :=
  Subgroup.subset_closure hg

theorem normalizer_le_componentStab {T : Subgroup G} (hT : IsElemAbelian 2 T) {t : G}
    (ht : t ∈ T) (ht1 : t ≠ 1) : Subgroup.normalizer (T : Set G) ≤ componentStab T := by
  intro n hn
  apply mem_componentStab_of_conjAdj
  have hnt : n * t * n⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hn t).mp ht
  refine ⟨t, ht, ht1, t, ht, ht1, ?_⟩
  rw [one_mul, inv_one, mul_one]
  exact congrArg Subtype.val (hT.1.is_comm.comm (⟨t, ht⟩ : T) ⟨_, hnt⟩)

variable [Finite G] {T H : Subgroup G}

theorem componentStab_le_normalizer_oddCore (h : Hyp T H) (hL : LocalFacts T H) :
    componentStab T ≤
      Subgroup.normalizer (oddCoreOf (Subgroup.centralizer (T : Set G)) : Set G) := by
  rw [componentStab, Subgroup.closure_le]
  rintro g ⟨x, hx, hx1, y, hy, hy1, hc⟩
  rw [one_mul, inv_one, mul_one] at hc
  have heq := conjSubgroup_oddCore_eq_of_commute h hL hx hx1 hy hy1 hc
  refine Subgroup.mem_normalizer_iff.mpr fun k => ?_
  have hk : g * k * g⁻¹ ∈ conjSubgroup g (oddCoreOf (Subgroup.centralizer (T : Set G))) ↔
      k ∈ oddCoreOf (Subgroup.centralizer (T : Set G)) := by
    rw [mem_conjSubgroup, show g⁻¹ * (g * k * g⁻¹) * g = k by group]
  rw [heq] at hk
  exact hk.symm

theorem mem_componentStab_of_conj_mem (h : Hyp T H) (hL : LocalFacts T H) {z : G} (hz : z ∈ T)
    (hz1 : z ≠ 1) {g : G} (hg : g⁻¹ * z * g ∈ componentStab T) : g ∈ componentStab T := by
  have hT := h.wc.1
  set M := componentStab T with hM
  set N := Subgroup.normalizer (T : Set G) with hN
  have hNM : N ≤ M := normalizer_le_componentStab hT hz hz1
  have hrel : Odd (N.relIndex M) :=
    (h.odd.of_dvd_nat (Subgroup.index_dvd_of_le hL.le_normalizer)).of_dvd_nat
      (Dvd.intro _ (Subgroup.relIndex_mul_index hNM))
  have hzz : z * z = 1 := by rw [← sq]; exact hT.2 z hz
  set u : M := ⟨g⁻¹ * z * g, hg⟩ with hu
  have hu2 : u ^ 2 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one, sq]
    change (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1
    calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [hzz, mul_one, inv_mul_cancel])
  have hP : IsPGroup 2 (Subgroup.zpowers u) := by
    rintro ⟨x, hx⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine ⟨1, Subtype.ext ?_⟩
    change (u ^ k) ^ 2 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu2, one_zpow]
  obtain ⟨x, hx⟩ := IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card hP
    (↥M ⧸ N.subgroupOf M) (fun hd => by
      change 2 ∣ N.relIndex M at hd
      obtain ⟨j, hj⟩ := hrel
      omega)
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
  have hfix := hx ⟨u, Subgroup.mem_zpowers u⟩
  rw [Subgroup.mk_smul, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq,
    Subgroup.mem_subgroupOf] at hfix
  have hv : (m : G)⁻¹ * (g⁻¹ * z * g) * m ∈ N := by
    have h1 := N.inv_mem hfix
    have h2 : (((u * m)⁻¹ * m : M) : G)⁻¹ = (m : G)⁻¹ * (g⁻¹ * z * g) * m := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hu]
      group
    rwa [h2] at h1
  have hv2 : ((m : G)⁻¹ * (g⁻¹ * z * g) * m) ^ 2 = 1 := by
    rw [sq]
    calc (m : G)⁻¹ * (g⁻¹ * z * g) * m * ((m : G)⁻¹ * (g⁻¹ * z * g) * m)
        = (m : G)⁻¹ * g⁻¹ * (z * z) * g * m := by group
      _ = 1 := by rw [hzz, mul_one]; group
  have h4 := four_le_card_inf_centralizer_of_sq_eq_one hT hL.card_T hv hv2
  obtain ⟨⟨t, ht⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    ((Subgroup.one_lt_card_iff_ne_bot _).mp (lt_of_lt_of_le (by norm_num) h4))
  have htT := (Subgroup.mem_inf.mp ht).1
  have htv := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp ht).2
  have ht1' : t ≠ 1 := fun h1 => ht1 (Subtype.ext h1)
  have hadj : ConjAdj T g⁻¹ m := by
    refine ⟨z, hz, hz1, t, htT, ht1', ?_⟩
    rw [inv_inv]
    calc g⁻¹ * z * g * (m * t * (m : G)⁻¹)
        = m * (((m : G)⁻¹ * (g⁻¹ * z * g) * m) * t) * (m : G)⁻¹ := by group
      _ = m * (t * ((m : G)⁻¹ * (g⁻¹ * z * g) * m)) * (m : G)⁻¹ := by rw [htv]
      _ = m * t * (m : G)⁻¹ * (g⁻¹ * z * g) := by group
  have h1 := (hadj.mul_left (m : G)⁻¹).symm
  rw [inv_mul_cancel] at h1
  have hgM : g⁻¹ ∈ M := by
    have := M.mul_mem m.2 (mem_componentStab_of_conjAdj h1)
    rwa [mul_inv_cancel_left] at this
  exact (Subgroup.inv_mem_iff _).mp hgM

theorem isHoltTriple_componentStab (h : Hyp T H) (hL : LocalFacts T H) {S : Sylow 2 G} {z : G}
    (hzS : z ∈ (S : Subgroup G)) (hz : z ∈ T) (hz1 : z ≠ 1)
    (hSz : ∀ s ∈ (S : Subgroup G), s * z = z * s) :
    IsHoltTriple G (G ⧸ componentStab T) z ((1 : G) : G ⧸ componentStab T) := by
  have hT := h.wc.1
  have hzM : z ∈ componentStab T := normalizer_le_componentStab hT hz hz1 (T.le_normalizer hz)
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hT.2 z hz)
  refine ⟨inferInstance, orderOf_eq_prime (hT.2 z hz) hz1, fun ω => ?_,
    ⟨S, hzS, fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr (hSz s hs)⟩⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective ω
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq, QuotientGroup.eq, mul_one,
    show (z * g)⁻¹ * g = g⁻¹ * z * g by rw [mul_inv_rev, hzinv], Subgroup.inv_mem_iff]
  exact ⟨mem_componentStab_of_conj_mem h hL hz hz1, fun hg =>
    (componentStab T).mul_mem ((componentStab T).mul_mem ((Subgroup.inv_mem_iff _).mpr hg) hzM)
      hg⟩

end CFSG.CGT.M24S
