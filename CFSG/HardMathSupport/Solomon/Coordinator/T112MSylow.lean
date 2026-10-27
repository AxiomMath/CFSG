module

public import Mathlib.GroupTheory.Focal

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open scoped commutatorElement

section Cube

variable {G : Type*} [Group G]

theorem t112m_cube_mul {u v k : G} (hvu : v * u = u * v * k) (hku : k * u = u * k)
    (hkv : k * v = v * k) (hk3 : k ^ 3 = 1) : (u * v) ^ 3 = u ^ 3 * v ^ 3 := by
  have A : ∀ x : G, v * (u * x) = u * (v * (k * x)) := fun x => by
    rw [← mul_assoc, hvu, mul_assoc, mul_assoc]
  have B : ∀ x : G, k * (v * x) = v * (k * x) := fun x => by
    rw [← mul_assoc, hkv, mul_assoc]
  have C : ∀ x : G, k * (u * x) = u * (k * x) := fun x => by
    rw [← mul_assoc, hku, mul_assoc]
  have D : ∀ x : G, k * (k * (k * x)) = x := fun x => by
    calc k * (k * (k * x)) = k ^ 3 * x := by rw [pow_three]; simp only [mul_assoc]
      _ = x := by rw [hk3, one_mul]
  calc (u * v) ^ 3 = u * (v * (u * (v * (u * v)))) := by
        rw [pow_three]; simp only [mul_assoc]
    _ = u * (u * (v * (k * (v * (u * v))))) := by rw [A (v * (u * v))]
    _ = u * (u * (v * (v * (k * (u * v))))) := by rw [B (u * v)]
    _ = u * (u * (v * (v * (u * (k * v))))) := by rw [C v]
    _ = u * (u * (v * (u * (v * (k * (k * v)))))) := by rw [A (k * v)]
    _ = u * (u * (u * (v * (k * (v * (k * (k * v))))))) := by rw [A (v * (k * (k * v)))]
    _ = u * (u * (u * (v * (v * (k * (k * (k * v))))))) := by rw [B (k * (k * v))]
    _ = u * (u * (u * (v * (v * v)))) := by rw [D v]
    _ = u ^ 3 * v ^ 3 := by rw [pow_three, pow_three]; simp only [mul_assoc]

theorem t112m_normal_of_le_center {Z : Subgroup G} (hZ : Z ≤ Subgroup.center G) : Z.Normal :=
  ⟨fun n hn g => by
    have hc := Subgroup.mem_center_iff.1 (hZ hn) g
    rw [hc, mul_inv_cancel_right]
    exact hn⟩

end Cube

section Sylow

variable {K : Type*} [Group K] [Finite K]

open scoped IsMulCommutative in
theorem t112m_sylow_nonabelian (hperf : commutator K = ⊤) {z : K}
    (hz : z ∈ Subgroup.center K) (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1) (R : Sylow 3 K) :
    ∃ r ∈ (R : Subgroup K), ∃ s ∈ (R : Subgroup K), r * s ≠ s * r := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hab
  push Not at hab
  have : IsMulCommutative ↥(R : Subgroup K) :=
    ⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩
  have hoz : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hzle : Subgroup.zpowers z ≤ Subgroup.center K := Subgroup.zpowers_le.2 hz
  have hzN : (Subgroup.zpowers z).Normal := t112m_normal_of_le_center hzle
  have hzp : IsPGroup 3 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hoz, pow_one])
  have hzR : z ∈ (R : Subgroup K) := hzp.le_sylow_of_normal R (Subgroup.mem_zpowers z)
  have key : ∀ (k : ℕ) (g₀ : K), g₀⁻¹ * z ^ k * g₀ ∈ (R : Subgroup K) →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hc := Subgroup.mem_center_iff.1 (Subgroup.pow_mem _ hz k) g₀
    rw [mul_assoc, ← hc, inv_mul_cancel_left]
  have hV : MonoidHom.transfer (MonoidHom.id ↥(R : Subgroup K)) z = 1 := by
    have h : z ∈ (MonoidHom.transfer (MonoidHom.id ↥(R : Subgroup K))).ker :=
      Abelianization.commutator_subset_ker _ (hperf ▸ Subgroup.mem_top z)
    exact h
  rw [MonoidHom.transfer_eq_pow _ z key] at hV
  have h1 : z ^ (R : Subgroup K).index = 1 := congrArg Subtype.val hV
  have h2 : orderOf z ∣ (R : Subgroup K).index := orderOf_dvd_of_pow_eq_one h1
  rw [hoz] at h2
  exact R.not_dvd_index h2

theorem t112m_sylow_exponent (hperf : commutator K = ⊤) {Z₀ : Subgroup K}
    (hZ₀ : Z₀ ≤ Subgroup.center K) (hZ3 : Nat.card Z₀ = 3) (R : Sylow 3 K)
    (hR : Nat.card ↥(R : Subgroup K) = 27)
    (hna : ∃ r ∈ (R : Subgroup K), ∃ s ∈ (R : Subgroup K), r * s ≠ s * r) :
    ∀ r ∈ (R : Subgroup K), r ^ 3 = 1 := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set P : Subgroup K := (R : Subgroup K) with hP
  have hZN : Z₀.Normal := t112m_normal_of_le_center hZ₀
  have hZp : IsPGroup 3 Z₀ := IsPGroup.of_card (n := 1) (by rw [hZ3, pow_one])
  have hZR : Z₀ ≤ P := hZp.le_sylow_of_normal R
  set N : Subgroup ↥P := Z₀.subgroupOf P with hNdef
  have hNc : N ≤ Subgroup.center ↥P := by
    intro n hn
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hZ₀ ((Subgroup.mem_subgroupOf).1 hn)) g)
  have hNcard : Nat.card N = 3 := by
    rw [hNdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZR).toEquiv, hZ3]
  have hQ : Nat.card (↥P ⧸ N) = 3 ^ 2 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hR, hNcard] at this
    norm_num
    omega
  have hnc : ¬ IsCyclic (↥P ⧸ N) := by
    intro hcyc
    have hcomm := (QuotientGroup.mk' N).isMulCommutative_of_isCyclic_of_ker_le_center
      (by rw [QuotientGroup.ker_mk']; exact hNc)
    obtain ⟨r, hr, s, hs, hrs⟩ := hna
    exact hrs (congrArg Subtype.val (hcomm.is_comm.comm ⟨r, hr⟩ ⟨s, hs⟩))
  have hQ3 : ∀ q : ↥P ⧸ N, q ^ 3 = 1 := by
    intro q
    have hdvd : orderOf q ∣ 3 ^ 2 := hQ ▸ orderOf_dvd_natCard q
    obtain ⟨k, hk, hkq⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    interval_cases k
    · rw [pow_zero, orderOf_eq_one_iff] at hkq
      rw [hkq, one_pow]
    · rw [pow_one] at hkq
      rw [← hkq, pow_orderOf_eq_one]
    · exact absurd (isCyclic_of_orderOf_eq_card q (by rw [hkq, hQ])) hnc
  have hQc := (IsPGroup.isMulCommutative_of_card_eq_prime_sq hQ).is_comm.comm
  have hcube : ∀ r : ↥P, (r : K) ^ 3 ∈ Z₀ := by
    intro r
    have h1 := hQ3 (QuotientGroup.mk r)
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
    have h2 := (Subgroup.mem_subgroupOf).1 h1
    simpa using h2
  have hcomm : ∀ r s : ↥P, ((r : K) * s)⁻¹ * ((s : K) * r) ∈ Z₀ := by
    intro r s
    have h1 := hQc (QuotientGroup.mk r) (QuotientGroup.mk s)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h1
    have h2 := (Subgroup.mem_subgroupOf).1 h1
    simpa using h2
  have hZexp : ∀ k ∈ Z₀, k ^ 3 = 1 := by
    intro k hk
    have : orderOf (⟨k, hk⟩ : Z₀) ∣ 3 := hZ3 ▸ orderOf_dvd_natCard _
    exact congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.1 this)
  let c : ↥P →* ↥(Subgroup.center K) :=
    { toFun := fun r => ⟨(r : K) ^ 3, hZ₀ (hcube r)⟩
      map_one' := by ext; simp
      map_mul' := fun r s => by
        ext
        have hk := hcomm r s
        have hkc := Subgroup.mem_center_iff.1 (hZ₀ hk)
        have hvu : (s : K) * r = r * s * (((r : K) * s)⁻¹ * ((s : K) * r)) := by group
        simpa using t112m_cube_mul hvu (hkc r).symm (hkc s).symm (hZexp _ hk) }
  have hc : ∀ r : ↥P, ((c r : ↥(Subgroup.center K)) : K) = (r : K) ^ 3 := fun r => rfl
  have hgen : P.focalSubgroup ≤ c.ker.map P.subtype := by
    rw [Subgroup.focalSubgroup_def, Subgroup.closure_le]
    rintro g ⟨hgP, x, hxP, u, rfl⟩
    have hy : u * x⁻¹ * u⁻¹ ∈ P := by
      have h1 : u * x⁻¹ * u⁻¹ = x⁻¹ * ⁅x, u⁆ := by rw [commutatorElement_def]; group
      rw [h1]
      exact P.mul_mem (P.inv_mem hxP) hgP
    refine ⟨⟨_, hgP⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    apply Subtype.ext
    rw [hc]
    have hxy : (⁅x, u⁆ : K) = x * (u * x⁻¹ * u⁻¹) := by rw [commutatorElement_def]; group
    have hm := congrArg Subtype.val (c.map_mul ⟨x, hxP⟩ ⟨u * x⁻¹ * u⁻¹, hy⟩)
    simp only [Subgroup.coe_mul, hc] at hm
    have hy3 : (u * x⁻¹ * u⁻¹) ^ 3 = (x ^ 3)⁻¹ := by
      rw [conj_pow, inv_pow]
      have hxc : u * (x ^ 3)⁻¹ = (x ^ 3)⁻¹ * u :=
        Subgroup.mem_center_iff.1 ((Subgroup.center K).inv_mem (hZ₀ (hcube ⟨x, hxP⟩))) u
      rw [hxc, mul_inv_cancel_right]
    show (⁅x, u⁆ : K) ^ 3 = 1
    rw [hxy, hm, hy3, mul_inv_cancel]
  have hfoc : P = P.focalSubgroup := by
    have h := Subgroup.commutator_inf_eq_focalSubgroup R
    rw [hperf, top_inf_eq] at h
    exact h
  intro r hr
  rw [hfoc] at hr
  obtain ⟨w, hw, hwr⟩ := hgen hr
  rw [SetLike.mem_coe, MonoidHom.mem_ker] at hw
  have h1 := congrArg Subtype.val hw
  rw [hc] at h1
  rw [← hwr]
  exact h1

theorem t112m_sylow_of_perfect (hperf : commutator K = ⊤) {Z₀ : Subgroup K}
    (hZ₀ : Z₀ ≤ Subgroup.center K) (hZ3 : Nat.card Z₀ = 3)
    (h3 : (Nat.card K).factorization 3 = 3) (R : Sylow 3 K) :
    Nat.card ↥(R : Subgroup K) = 27 ∧
      (∃ r ∈ (R : Subgroup K), ∃ s ∈ (R : Subgroup K), r * s ≠ s * r) ∧
      ∀ r ∈ (R : Subgroup K), r ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR : Nat.card ↥(R : Subgroup K) = 27 := by
    have h := R.card_eq_multiplicity
    rw [h3] at h
    exact h.trans (by norm_num)
  obtain ⟨z, hz1⟩ : ∃ z : Z₀, z ≠ 1 := by
    by_contra h
    push Not at h
    have : Subsingleton Z₀ := ⟨fun a b => (h a).trans (h b).symm⟩
    have := Nat.card_unique (α := Z₀)
    omega
  have hz3 : (z : K) ^ 3 = 1 := by
    have : orderOf z ∣ 3 := hZ3 ▸ orderOf_dvd_natCard z
    exact congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.1 this)
  have hz1' : (z : K) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hna := t112m_sylow_nonabelian hperf (hZ₀ z.2) hz1' hz3 R
  exact ⟨hR, hna, t112m_sylow_exponent hperf hZ₀ hZ3 R hR hna⟩

end Sylow

end CFSG.HardMathSupport.Solomon.Coordinator
