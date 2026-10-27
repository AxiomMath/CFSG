module

public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.Semidihedral.Principal

@[expose, reducible] def indexTwoQuotientCommGroup {G : Type*} [Group G] (N : Subgroup G)
    [N.Normal] (hN : N.index = 2) : CommGroup (G ⧸ N) :=
  have : IsCyclic (G ⧸ N) :=
    isCyclic_of_prime_card (p := 2) (by rw [← Subgroup.index_eq_card]; exact hN)
  IsCyclic.commGroup

theorem transfer_eq_pow_of_conj_mem {G A : Type*} [Group G] [CommGroup A] {H : Subgroup G}
    [H.FiniteIndex] (ϕ : H →* A) (g : H)
    (key : ∀ (k : ℕ) (g₀ : G) (hk : g₀⁻¹ * (g : G) ^ k * g₀ ∈ H),
      ϕ ⟨g₀⁻¹ * (g : G) ^ k * g₀, hk⟩ = ϕ g ^ k) :
    ϕ.transfer (g : G) = ϕ g ^ H.index := by
  classical
  have : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers (g : G)) (G ⧸ H))) :=
    Fintype.ofFinite _
  rw [Subgroup.index_eq_sum_minimalPeriod H (g : G), ← Finset.prod_pow_eq_pow_sum,
    MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  exact Finset.prod_congr rfl fun q _ => key _ _ _

theorem eq_of_orderOf_eq_two_of_isCyclic {G : Type*} [Group G] [IsCyclic G] [Finite G]
    {a b : G} (ha : orderOf a = 2) (hb : orderOf b = 2) : a = b := by
  have hle : Subgroup.zpowers a ≤ Subgroup.zpowers b := by
    rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers, Nat.card_zpowers, ha, hb]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hle (Subgroup.mem_zpowers a))
  have h : a = b ^ (k % 2) := by
    rw [← hk, ← zpow_mod_orderOf b k, hb]
    rfl
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · rw [h0, zpow_zero] at h
    rw [h, orderOf_one] at ha
    exact absurd ha (by norm_num)
  · rwa [h1, zpow_one] at h

theorem mk'_eq_mk'_iff_of_index_two {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (hN : N.index = 2) (u v : G) :
    QuotientGroup.mk' N u = QuotientGroup.mk' N v ↔ (u ∈ N ↔ v ∈ N) := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mul_mem_iff_of_index_two hN, inv_mem_iff]

theorem dihedral_central_involution_transfer_kernel {H : Type*} [Group H] [Finite H]
    (S : Sylow 2 H) (A : Subgroup (S : Subgroup H)) [A.Normal] (hAcyc : IsCyclic A)
    (hAindex : A.index = 2) (_hAcard : 2 ≤ Nat.card A)
    (hout : ∀ x : (S : Subgroup H), x ∉ A → orderOf x = 2)
    (z : (S : Subgroup H)) (hzA : z ∈ A) (hz : orderOf z = 2)
    (hzcenter : (z : H) ∈ Subgroup.center H) :
    letI : CommGroup ((S : Subgroup H) ⧸ A) := indexTwoQuotientCommGroup A hAindex
    let T : H →* (S : Subgroup H) ⧸ A := (QuotientGroup.mk' A).transfer
    (∀ a : (S : Subgroup H), a ∈ A → T (a : H) = 1) ∧
    (∀ x : (S : Subgroup H), x ∉ A → T (x : H) = QuotientGroup.mk' A x) ∧
    T.ker.Normal ∧ T.ker.index = 2 ∧
    (S : Subgroup H) ⊓ T.ker = A.map (S : Subgroup H).subtype ∧
    IsCyclic (A.map (S : Subgroup H).subtype) ∧
    ∃ P : Sylow 2 T.ker,
      (P : Subgroup T.ker).map T.ker.subtype = A.map (S : Subgroup H).subtype := by
  let _ : CommGroup ((S : Subgroup H) ⧸ A) := indexTwoQuotientCommGroup A hAindex
  intro T
  have hzuniq : ∀ a : (S : Subgroup H), a ∈ A → orderOf a = 2 → a = z := by
    intro a ha ha2
    have h := eq_of_orderOf_eq_two_of_isCyclic (G := A) (a := ⟨a, ha⟩) (b := ⟨z, hzA⟩)
      (by rw [Subgroup.orderOf_mk, ha2]) (by rw [Subgroup.orderOf_mk, hz])
    exact congrArg Subtype.val h
  have hconj : ∀ (u v : (S : Subgroup H)) (g₀ : H), (v : H) = g₀⁻¹ * (u : H) * g₀ →
      u ∈ A → v ∈ A := by
    intro u v g₀ huv hu
    by_contra hv
    have hv2 := hout v hv
    have hu2 : orderOf u = 2 := by
      have h : orderOf (v : H) = orderOf (u : H) := by
        rw [huv]
        have := (MulAut.conj g₀⁻¹).orderOf_eq (u : H)
        rwa [MulAut.conj_apply, inv_inv] at this
      rw [← Subgroup.orderOf_coe u, ← h, Subgroup.orderOf_coe, hv2]
    have huz := hzuniq u hu hu2
    have hvz : v = z := by
      apply Subtype.ext
      rw [huv, huz, Subgroup.mem_center_iff.mp hzcenter g₀⁻¹, mul_assoc, inv_mul_cancel,
        mul_one]
    exact hv (hvz ▸ hzA)
  have hTS : ∀ g : (S : Subgroup H), T (g : H) = QuotientGroup.mk' A g := by
    intro g
    have hkey := transfer_eq_pow_of_conj_mem (QuotientGroup.mk' A) g (fun k g₀ hk => by
      rw [← map_pow, mk'_eq_mk'_iff_of_index_two A hAindex]
      constructor
      · intro h
        exact hconj ⟨_, hk⟩ (g ^ k) g₀⁻¹ (by
          simp only [Subgroup.coe_pow, inv_inv]
          group) h
      · intro h
        exact hconj (g ^ k) ⟨_, hk⟩ g₀ (by simp only [Subgroup.coe_pow]) h)
    have hodd : ¬ 2 ∣ (S : Subgroup H).index := S.not_dvd_index
    have hsq : ∀ q : (S : Subgroup H) ⧸ A, q ^ 2 = 1 := by
      intro q
      have h := pow_card_eq_one' (x := q)
      rwa [← Subgroup.index_eq_card, hAindex] at h
    obtain ⟨j, hj⟩ := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
    change (QuotientGroup.mk' A).transfer (g : H) = QuotientGroup.mk' A g
    rw [hkey, hj, pow_succ, pow_mul, hsq, one_pow, one_mul]
  have hTA : ∀ a : (S : Subgroup H), a ∈ A → T (a : H) = 1 := fun a ha => by
    rw [hTS, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ha
  have hTout : ∀ x : (S : Subgroup H), x ∉ A → T (x : H) = QuotientGroup.mk' A x :=
    fun x _ => hTS x
  have hsurj : Function.Surjective T := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective A q
    exact ⟨g, hTS g⟩
  have hkerindex : T.ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top,
      ← Subgroup.index_eq_card, hAindex]
  have hinf : (S : Subgroup H) ⊓ T.ker = A.map (S : Subgroup H).subtype := by
    ext y
    simp only [Subgroup.mem_inf, MonoidHom.mem_ker, Subgroup.mem_map, Subgroup.coe_subtype]
    constructor
    · rintro ⟨hyS, hy⟩
      refine ⟨⟨y, hyS⟩, ?_, rfl⟩
      have h := hTS ⟨y, hyS⟩
      rw [hy, eq_comm, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
      exact h
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.2, hTA a ha⟩
  have hA'S : A.map (S : Subgroup H).subtype ≤ (S : Subgroup H) := Subgroup.map_subtype_le A
  have hA'K : A.map (S : Subgroup H).subtype ≤ T.ker := hinf ▸ inf_le_right
  have hA'cyc : IsCyclic (A.map (S : Subgroup H).subtype) :=
    (MulEquiv.isCyclic (A.equivMapOfInjective _ (S : Subgroup H).subtype_injective)).mp hAcyc
  have hrelS : (A.map (S : Subgroup H).subtype).relIndex (S : Subgroup H) = 2 := by
    have hsub : (A.map (S : Subgroup H).subtype).subgroupOf (S : Subgroup H) = A := by
      ext x
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_map_iff_mem (f := (S : Subgroup H).subtype)
        (Subgroup.subtype_injective (S : Subgroup H))
    rw [Subgroup.relIndex, hsub, hAindex]
  have hrelK : (A.map (S : Subgroup H).subtype).relIndex T.ker = (S : Subgroup H).index := by
    have h1 := Subgroup.relIndex_mul_index hA'K
    have h2 := Subgroup.relIndex_mul_index hA'S
    rw [hkerindex] at h1
    rw [hrelS] at h2
    omega
  have hP1 : IsPGroup 2 ((A.map (S : Subgroup H).subtype).subgroupOf T.ker) :=
    (S.isPGroup'.to_le hA'S).of_equiv (Subgroup.subgroupOfEquivOfLe hA'K).symm
  have hP2 : ¬ 2 ∣ ((A.map (S : Subgroup H).subtype).subgroupOf T.ker).index := by
    rw [← Subgroup.relIndex, hrelK]
    exact S.not_dvd_index
  refine ⟨hTA, hTout, inferInstance, hkerindex, hinf, hA'cyc, hP1.toSylow hP2, ?_⟩
  rw [IsPGroup.toSylow_coe, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hA'K]

end CFSG.Semidihedral.Principal
