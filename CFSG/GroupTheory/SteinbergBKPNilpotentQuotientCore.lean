module

public import CFSG.GroupTheory.FrobeniusNormalComplement

public section

namespace CFSG.GroupTheory.SteinbergBK

open CFSG.GroupTheory.FrobeniusNormalComplement Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]

omit hp in
theorem eq_one_of_mem_of_mem {P N : Subgroup G} (hP : IsPGroup p P)
    (hN : Nat.Coprime (Nat.card N) p) {x : G} (hxP : x ∈ P) (hxN : x ∈ N) : x = 1 := by
  obtain ⟨j, hj⟩ := hP ⟨x, hxP⟩
  have hj' : x ^ p ^ j = 1 := by
    have := congrArg Subtype.val hj
    rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
  exact orderOf_eq_one_of_dvd (Nat.Coprime.pow_right j hN) (orderOf_dvd_of_mem hxN)
    (orderOf_dvd_of_pow_eq_one hj')

omit [Finite G] hp in
theorem isPGroup_of_isNormalPComplement_bot {K : Subgroup G} {R : Subgroup K}
    (hR : IsNormalPComplement p R) (hRb : R = ⊥) : IsPGroup p K := by
  obtain ⟨-, -, j, hj⟩ := hR
  rw [hRb, Subgroup.index_bot] at hj
  exact IsPGroup.of_card hj

omit hp in
theorem normal_map_of_isNormalPComplement {K : Subgroup G} [K.Normal] {R : Subgroup K}
    (hR : IsNormalPComplement p R) : (R.map K.subtype).Normal := by
  refine ⟨fun l hl g => ?_⟩
  obtain ⟨l₀, hl₀, rfl⟩ := hl
  have hfix := (IsNormalPComplement.characteristic hR).fixed (MulAut.conjNormal g)
  have hmem : l₀ ∈ R.comap (MulAut.conjNormal g).toMonoidHom := by
    rw [hfix]
    exact hl₀
  exact ⟨_, hmem, by rw [Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, MulAut.conjNormal_apply]⟩

theorem p_nilpotent_quotient_core_centralizer (hO : CFSG.pPrimeCore p G = ⊥)
    (hquot : ∃ N : Subgroup (G ⧸ CFSG.pCore p G), IsNormalPComplement p N) :
    centralizer (CFSG.pCore p G : Set G) ≤ CFSG.pCore p G ∧
      ∀ H : Subgroup G, CFSG.pCore p G ≤ H → (∃ N : Subgroup H, IsNormalPComplement p N) →
        IsPGroup p H := by
  set Q := CFSG.pCore p G with hQdef
  have hQp : IsPGroup p Q := CFSG.pCore_isPGroup
  obtain ⟨N, hNn, hNc, k, hk⟩ := hquot
  set π := QuotientGroup.mk' Q
  set L := N.comap π with hLdef
  have hLn : L.Normal := hNn.comap π
  have hLidx : L.index = p ^ k := by
    rw [hLdef, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective Q), hk]
  have hpL : ∀ x ∈ L, ∀ j : ℕ, x ^ p ^ j = 1 → x ∈ Q := by
    intro x hxL j hj
    have h1 : π x = 1 := orderOf_eq_one_of_dvd (Nat.Coprime.pow_right j hNc)
      (orderOf_dvd_of_mem hxL) (orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hj, map_one]))
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  set C := centralizer (Q : Set G) with hCdef
  set D := C ⊓ L with hDdef
  have hDn : D.Normal := inferInstance
  have hautD : ∀ P : Subgroup D, IsPGroup p P → IsPGroup p (normalizer (P : Set D) ⧸
      (centralizer (P : Set D)).subgroupOf (normalizer (P : Set D))) := by
    intro P hP x
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
    refine ⟨0, ?_⟩
    rw [pow_zero, pow_one, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨j, hj⟩ := hP ⟨y, hy⟩
    have hyj : (y : G) ^ p ^ j = 1 := by
      have := congrArg (fun z : P => ((z : D) : G)) hj
      simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one] using this
    have hyQ : (y : G) ∈ Q := hpL _ (y : D).2.2 j hyj
    have hnC : ((n : D) : G) ∈ C := (n : D).2.1
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hnC) _ hyQ
  obtain ⟨R, hR⟩ := ((frobenius_normal_p_complement (G := D) p).1).mpr hautD
  have hRn := normal_map_of_isNormalPComplement hR
  have hRc : Nat.Coprime p (Nat.card (R.map D.subtype)) := by
    rw [Subgroup.card_map_of_injective D.subtype_injective]
    exact hR.2.1.symm
  have hRle : R.map D.subtype ≤ CFSG.pPrimeCore p G := le_sSup ⟨hRn, hRc⟩
  rw [hO, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ D.subtype_injective] at hRle
  have hDp : IsPGroup p D := isPGroup_of_isNormalPComplement_bot hR hRle
  have hGL : IsPGroup p (G ⧸ L) := IsPGroup.of_card (n := k) hLidx
  have hCp : IsPGroup p C := by
    intro c
    obtain ⟨a, ha⟩ := hGL (QuotientGroup.mk (c : G))
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at ha
    have hcD : (c : G) ^ p ^ a ∈ D := ⟨pow_mem c.2 _, ha⟩
    obtain ⟨b, hb⟩ := hDp ⟨_, hcD⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have := congrArg Subtype.val hb
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, pow_add, pow_mul]
    exact this
  have hCQ : C ≤ Q := le_sSup ⟨inferInstance, hCp⟩
  refine ⟨hCQ, fun H hQH ⟨RH, hRH⟩ => ?_⟩
  obtain ⟨hRHn, hRHc, j, hj⟩ := hRH
  have hQRH : ∀ x : H, x ∈ RH → (x : G) ∈ Q → x = 1 := fun x hxR hxQ => by
    have h1 := eq_one_of_mem_of_mem (P := Q) (N := RH.map H.subtype) hQp
      (by rw [Subgroup.card_map_of_injective H.subtype_injective]; exact hRHc) hxQ ⟨x, hxR, rfl⟩
    exact Subtype.ext h1
  have hRHb : RH = ⊥ := by
    rw [eq_bot_iff]
    intro r hr
    have hrC : (r : G) ∈ C := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hqH : q ∈ H := hQH hq
      have h1 : q * (r : G) * q⁻¹ * (r : G)⁻¹ ∈ Q := by
        have h := Subgroup.Normal.conj_mem inferInstance q⁻¹ (inv_mem hq) (r : G)
        rw [show q * (r : G) * q⁻¹ * (r : G)⁻¹ = q * ((r : G) * q⁻¹ * (r : G)⁻¹) by group]
        exact mul_mem hq h
      have h2 : (⟨q, hqH⟩ : H) * r * (⟨q, hqH⟩ : H)⁻¹ * r⁻¹ ∈ RH :=
        mul_mem (hRHn.conj_mem r hr _) (inv_mem hr)
      have h3 := hQRH _ h2 h1
      have h4 : q * (r : G) * q⁻¹ * (r : G)⁻¹ = 1 := congrArg Subtype.val h3
      calc q * (r : G) = q * (r : G) * q⁻¹ * (r : G)⁻¹ * ((r : G) * q) := by group
        _ = (r : G) * q := by rw [h4, one_mul]
    rw [Subgroup.mem_bot]
    exact hQRH r hr (hCQ hrC)
  exact isPGroup_of_isNormalPComplement_bot ⟨hRHn, hRHc, j, hj⟩ hRHb

end CFSG.GroupTheory.SteinbergBK
