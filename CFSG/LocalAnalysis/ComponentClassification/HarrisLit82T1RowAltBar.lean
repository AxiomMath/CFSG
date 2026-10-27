module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Rows

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.RowAlt

open CFSG Subgroup

theorem centralizer_le_of_odd_index {X : Type} [Group X] [Finite X] (hO : pPrimeCore 2 X = ⊥)
    {E : Subgroup X} [E.Normal] (hodd : Odd E.index)
    (h2 : ∀ x ∈ centralizer (E : Set X), x ∈ E → ∃ k : ℕ, x ^ 2 ^ k = 1) :
    centralizer (E : Set X) ≤ E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (E : Set X) with hCdef
  have hCn : C.Normal := Subgroup.normal_centralizer
  set N := E.subgroupOf C with hN
  have hNn : N.Normal := Subgroup.Normal.subgroupOf inferInstance C
  have hNc : ∀ n ∈ N, ∀ c : C, n * c = c * n := fun n hn c =>
    Subtype.ext (mem_centralizer_iff.mp c.2 n hn)
  have hN2 : IsPGroup 2 ↥N := fun n => by
    obtain ⟨k, hk⟩ := h2 ((n : C) : X) (n : C).2 n.2
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using hk))⟩
  have hNodd : Odd N.index := hodd.of_dvd_nat (Subgroup.relIndex_dvd_index_of_normal E C)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hN2
  have hcop : Nat.Coprime (Nat.card N) N.index := by
    rw [hk]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hNodd)
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hHodd : Odd (Nat.card H) := by
    have h1 := hH.card_mul_card
    have h2 := N.card_mul_index
    have hpos : 0 < Nat.card N := Nat.card_pos
    have : Nat.card H = N.index := Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
    rwa [this]
  have hmemH : ∀ c : C, Odd (orderOf c) → c ∈ H := by
    intro c hc
    have hc' : c ∈ ((N ⊔ H : Subgroup C) : Set C) := by rw [hH.sup_eq_top]; exact mem_top c
    rw [Subgroup.normal_mul] at hc'
    obtain ⟨n, hn, h, hh, rfl⟩ := Set.mem_mul.mp hc'
    have hnh : Commute n h := hNc n hn h
    have hpow := pow_orderOf_eq_one (n * h)
    rw [hnh.mul_pow] at hpow
    set m := orderOf (n * h)
    have hnm : n ^ m ∈ N ⊓ H := by
      refine ⟨N.pow_mem hn m, ?_⟩
      rw [eq_inv_of_mul_eq_one_left hpow]
      exact H.inv_mem (H.pow_mem hh m)
    rw [hH.disjoint.eq_bot, mem_bot] at hnm
    have hn2 : n ^ 2 ^ k = 1 := by
      have := pow_card_eq_one' (x := (⟨n, hn⟩ : N))
      rw [hk] at this
      exact congrArg Subtype.val this
    have hn1 : n = 1 := by
      have hd1 : orderOf n ∣ m := orderOf_dvd_of_pow_eq_one hnm
      have hd2 : orderOf n ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hn2
      have hcop' : Nat.Coprime m (2 ^ k) := Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hc)
      exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (hcop'.coprime_dvd_left hd1) hd2)
    rw [hn1, one_mul]
    exact hh
  have hH'n : (H.map C.subtype).Normal := by
    refine ⟨fun y hy x => ?_⟩
    obtain ⟨h, hh, rfl⟩ := hy
    have hxC : x * (h : X) * x⁻¹ ∈ C := hCn.conj_mem _ h.2 x
    refine ⟨⟨_, hxC⟩, hmemH _ ?_, rfl⟩
    have he : orderOf (⟨_, hxC⟩ : C) = orderOf h := by
      have h1 : orderOf (⟨_, hxC⟩ : C) = orderOf (x * (h : X) * x⁻¹) :=
        (Subgroup.orderOf_coe _).symm
      have h2 : orderOf h = orderOf (h : X) := (Subgroup.orderOf_coe _).symm
      rw [h1, h2, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    rw [he, ← Subgroup.orderOf_mk h hh]
    exact hHodd.of_dvd_nat (orderOf_dvd_natCard _)
  have hH'O : H.map C.subtype ≤ pPrimeCore 2 X :=
    le_sSup ⟨hH'n, Nat.coprime_two_left.mpr
      (by rwa [Subgroup.card_map_of_injective C.subtype_injective])⟩
  rw [hO, le_bot_iff, map_eq_bot_iff_of_injective _ C.subtype_injective] at hH'O
  rw [hH'O, isComplement'_bot_right] at hH
  intro c hc
  have : (⟨c, hc⟩ : C) ∈ N := hH ▸ mem_top _
  exact this

variable {G : Type} [Group G] [Finite G]

theorem nonempty_bar_equiv
    (htop : (GH74.GLS.oPrimeResidual 2 G).map (QuotientGroup.mk' (pPrimeCore 2 G)) = ⊤) :
    Nonempty (G ⧸ pPrimeCore 2 G ≃*
      ↥(GH74.GLS.oPrimeResidual 2 G) ⧸ pPrimeCore 2 ↥(GH74.GLS.oPrimeResidual 2 G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := GH74.GLS.oPrimeResidual 2 G with hYdef
  have hYn : Y.Normal := oPrimeResidual_two_normal
  set φ : ↥Y →* G ⧸ pPrimeCore 2 G := (QuotientGroup.mk' (pPrimeCore 2 G)).comp Y.subtype
    with hφ
  have hφk : φ.ker = pPrimeCore 2 ↥Y := by
    rw [CatalogueBHeldSmallCore.primeCore_subnormal_intersection 2 Y
      (Subgroup.Normal.isSubnormal hYn), hφ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rfl
  have htop' : φ.range = ⊤ := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
    exact htop
  exact ⟨((Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop'.symm)).trans
    ((QuotientGroup.quotientMulEquivOfEq hφk.symm).trans
      (QuotientGroup.quotientKerEquivRange φ)).symm)⟩

end CFSG.ComponentClassification.HarrisLit.T1.RowAlt
