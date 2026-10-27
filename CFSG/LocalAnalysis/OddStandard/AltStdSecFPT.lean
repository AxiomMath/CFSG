module

public import CFSG.GroupTheory.ThompsonIndexTwo

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup

variable {G : Type*} [Group G]

theorem mem_of_conj_mem {z : G} {M : Subgroup G}
    (hC : centralizer ({z} : Set G) ≤ M)
    (hfus : ∀ g : G, g⁻¹ * z * g ∈ M → ∃ m ∈ M, g⁻¹ * z * g = m⁻¹ * z * m)
    {g : G} (hg : g⁻¹ * z * g ∈ M) : g ∈ M := by
  obtain ⟨m, hm, hmg⟩ := hfus g hg
  have h1 : z * g = g * (m⁻¹ * z * m) := by
    calc z * g = g * (g⁻¹ * z * g) := by group
      _ = g * (m⁻¹ * z * m) := by rw [hmg]
  have hc : g * m⁻¹ ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc g * m⁻¹ * z = g * (m⁻¹ * z * m) * m⁻¹ := by group
      _ = z * g * m⁻¹ := by rw [← h1]
      _ = z * (g * m⁻¹) := by group
  have h3 : g = (g * m⁻¹) * m := by group
  rw [h3]
  exact mul_mem (hC hc) hm

theorem card_fixedPoints_eq_one [Finite G] {z : G} {M : Subgroup G}
    (hC : centralizer ({z} : Set G) ≤ M)
    (hfus : ∀ g : G, g⁻¹ * z * g ∈ M → ∃ m ∈ M, g⁻¹ * z * g = m⁻¹ * z * m)
    (hz2 : z * z = 1) :
    Nat.card (MulAction.fixedPoints (zpowers z) (G ⧸ M)) = 1 := by
  have hzM : z ∈ M := hC (mem_centralizer_singleton_iff.2 rfl)
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨((1 : G) : G ⧸ M), ?_⟩, ?_⟩
  · intro h
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h.2
    have hk' : (h : G) = z ^ k := hk.symm
    show (((h : G) * 1 : G) : G ⧸ M) = ((1 : G) : G ⧸ M)
    rw [QuotientGroup.eq, hk']
    simpa using inv_mem (zpow_mem hzM k)
  · rintro ⟨x, hx⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have h1 : (⟨z, mem_zpowers z⟩ : zpowers z) • ((g : G) : G ⧸ M) = ((g : G) : G ⧸ M) :=
      hx ⟨z, mem_zpowers z⟩
    have h2 : g⁻¹ * z * g ∈ M := by
      have := (QuotientGroup.eq.1 h1)
      change (z * g)⁻¹ * g ∈ M at this
      have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
      simp only [mul_inv_rev] at this
      rw [hzi] at this
      simpa [mul_assoc] using this
    have hgM := mem_of_conj_mem hC hfus h2
    apply Subtype.ext
    show ((g : G) : G ⧸ M) = ((1 : G) : G ⧸ M)
    rw [QuotientGroup.eq]
    simpa using inv_mem hgM

theorem not_two_dvd_index [Finite G] {z : G} {M : Subgroup G} (hz : orderOf z = 2)
    (hC : centralizer ({z} : Set G) ≤ M)
    (hfus : ∀ g : G, g⁻¹ * z * g ∈ M → ∃ m ∈ M, g⁻¹ * z * g = m⁻¹ * z * m) :
    ¬ 2 ∣ M.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : z * z = 1 := by rw [← sq, ← hz]; exact pow_orderOf_eq_one z
  have hp : IsPGroup 2 (zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  have h := hp.card_modEq_card_fixedPoints (G ⧸ M)
  rw [card_fixedPoints_eq_one hC hfus hz2] at h
  intro hd
  have h1 : M.index % 2 = 1 % 2 := h
  have h2 : M.index % 2 = 0 := Nat.mod_eq_zero_of_dvd hd
  omega

theorem false_of_simple_of_index_two [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {N : Subgroup G} [N.Normal] (hN : N.index = 2) : False := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h1 | h1
  · rw [h1, Subgroup.index_bot] at hN
    have := isCyclic_of_prime_card (α := G) (p := 2) (by simpa using hN)
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (IsCyclic.commGroup.mul_comm a b)
  · rw [h1, Subgroup.index_top] at hN
    exact absurd hN (by norm_num)

theorem false_of_fixedPoint_thompson [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {z : G} (hz : orderOf z = 2) {M : Subgroup G}
    (hC : centralizer ({z} : Set G) ≤ M)
    (hfus : ∀ g : G, g⁻¹ * z * g ∈ M → ∃ m ∈ M, g⁻¹ * z * g = m⁻¹ * z * m)
    {A : Type*} [CommGroup A] (hA : Nat.card A = 2) (χ : M →* A)
    (hχ : χ ⟨z, hC (mem_centralizer_singleton_iff.2 rfl)⟩ ≠ 1) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzM : z ∈ M := hC (mem_centralizer_singleton_iff.2 rfl)
  have hodd := not_two_dvd_index hz hC hfus
  set z' : M := ⟨z, hzM⟩ with hz'
  have hz'2 : orderOf z' = 2 := by rw [hz', Subgroup.orderOf_mk]; exact hz
  have hp' : IsPGroup 2 (zpowers z') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz'2, pow_one])
  obtain ⟨Q, hQ⟩ := hp'.exists_le_sylow
  set T : Subgroup G := (Q : Subgroup M).map M.subtype with hT
  have hTM : T ≤ M := Subgroup.map_subtype_le _
  have hTp : IsPGroup 2 T := Q.isPGroup'.map M.subtype
  have hzQ : z' ∈ (Q : Subgroup M) := hQ (mem_zpowers z')
  have hzT : z ∈ T := ⟨z', hzQ, rfl⟩
  have hTidx : ¬ 2 ∣ T.index := by
    have h1 : T.relIndex M * M.index = T.index := Subgroup.relIndex_mul_index hTM
    have h2 : T.relIndex M = (Q : Subgroup M).index := by
      unfold Subgroup.relIndex
      rw [hT, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _)]
    rw [← h1]
    intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hd with h | h
    · exact Q.not_dvd_index (h2 ▸ h)
    · exact hodd h
  let ψ : T →* A := χ.comp (Subgroup.inclusion hTM)
  set U : Subgroup G := ψ.ker.map T.subtype with hU
  have hUT : U ≤ T := Subgroup.map_subtype_le _
  have hψz : ψ ⟨z, hzT⟩ = χ z' := rfl
  have hrange : ψ.range = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hall : ∀ a b : A, a ≠ 1 → b ≠ 1 → a = b := by
      obtain ⟨x, w, hxw, hset⟩ := Nat.card_eq_two_iff.1 hA
      have hmem : ∀ a : A, a = x ∨ a = w := fun a => by
        have : a ∈ ({x, w} : Set A) := by rw [hset]; trivial
        simpa using this
      intro a b ha hb
      rcases hmem a with rfl | rfl <;> rcases hmem b with rfl | rfl <;> rcases hmem 1 with h1 | h1
      all_goals first | rfl | exact absurd h1.symm ‹_›
    by_cases hy : y = 1
    · rw [hy]; exact one_mem _
    · have : y = ψ ⟨z, hzT⟩ := hall _ _ hy (by rw [hψz]; exact hχ)
      rw [this]; exact ⟨_, rfl⟩
  have hrel : U.relIndex T = 2 := by
    unfold Subgroup.relIndex
    rw [hU, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _)]
    rw [Subgroup.index_ker, hrange, Subgroup.card_top, hA]
  have hzU : z ∉ U := by
    rintro ⟨t, ht, htz⟩
    have : t = ⟨z, hzT⟩ := Subtype.ext htz
    rw [this] at ht
    exact hχ (by rw [← hψz]; exact ht)
  have hmin : ∀ y ∈ T, y ∉ U → orderOf z ≤ orderOf y := by
    intro y _ hyU
    have hy1 : y ≠ 1 := fun h1 => hyU (h1 ▸ U.one_mem)
    rw [hz]
    have h1 := orderOf_pos y
    have h2 : orderOf y ≠ 1 := fun h3 => hy1 (orderOf_eq_one_iff.1 h3)
    omega
  have hconj : ∀ g : G, g⁻¹ * z * g ∉ U := by
    intro g hg
    obtain ⟨t, ht, htg⟩ := hg
    have htM : (t : G) ∈ M := hTM t.2
    obtain ⟨m, hm, hmg⟩ := hfus g (by rw [← htg]; exact htM)
    have hψt : χ ⟨t, htM⟩ = 1 := ht
    have htg' : (t : G) = g⁻¹ * z * g := htg
    have h1 : (⟨t, htM⟩ : M) = ⟨m, hm⟩⁻¹ * z' * ⟨m, hm⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [htg', hmg]
    rw [h1, map_mul, map_mul, map_inv] at hψt
    have h2 : (χ ⟨m, hm⟩)⁻¹ * χ z' * χ ⟨m, hm⟩ = χ z' := by
      rw [mul_comm ((χ ⟨m, hm⟩)⁻¹) (χ z'), mul_assoc, inv_mul_cancel, mul_one]
    exact hχ (h2 ▸ hψt)
  obtain ⟨N, hN, hidx⟩ := CFSG.ThompsonIndexTwo.exists_normal_index_two_of_thompson
    (T := T) (U := U) hTp hTidx hUT hrel hzT hzU hmin hconj
  exact false_of_simple_of_index_two hnonab hidx

theorem false_of_symmetric_overgroup [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {N : ℕ} {M : Subgroup G}
    (e : Equiv.Perm (Fin N) ≃* M) {z : G} (hz : orderOf z = 2)
    (hC : centralizer ({z} : Set G) ≤ M)
    (hswap : ∀ g : G, ∀ hg : g⁻¹ * z * g ∈ M, (e.symm ⟨g⁻¹ * z * g, hg⟩).IsSwap) : False := by
  have hzM : z ∈ M := hC (mem_centralizer_singleton_iff.2 rfl)
  have hz1 : (e.symm ⟨z, hzM⟩).IsSwap := by
    have := hswap 1 (by simpa using hzM)
    simpa using this
  let χ : M →* ℤˣ := (Equiv.Perm.sign : Equiv.Perm (Fin N) →* ℤˣ).comp e.symm.toMonoidHom
  have hcard : Nat.card ℤˣ = 2 := Nat.card_eq_fintype_card.trans Fintype.card_units_int
  refine false_of_fixedPoint_thompson hnonab hz hC ?_ hcard χ ?_
  · intro g hg
    obtain ⟨x, y, hxy, hxe⟩ := hz1
    obtain ⟨x', y', hxy', hxe'⟩ := hswap g hg
    obtain ⟨c, hc⟩ := isConj_iff.1 (Equiv.Perm.isConj_swap hxy hxy')
    refine ⟨(((e c : M)) : G)⁻¹, (e c)⁻¹.2, ?_⟩
    have h1 : (⟨g⁻¹ * z * g, hg⟩ : M) = (e c) * ⟨z, hzM⟩ * (e c)⁻¹ := by
      apply e.symm.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply, hxe', hxe, ← hc]
    have h2 := congrArg (fun w : M => (w : G)) h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
    rw [h2]
    simp [mul_assoc]
  · have : χ ⟨z, hzM⟩ = -1 := by
      obtain ⟨x, y, hxy, hxe⟩ := hz1
      show Equiv.Perm.sign (e.symm ⟨z, hzM⟩) = -1
      rw [hxe, Equiv.Perm.sign_swap hxy]
    rw [this]
    decide

end CFSG.OddStandard.AltStdSec
