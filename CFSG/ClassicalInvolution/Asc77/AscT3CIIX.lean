module

public import CFSG.ClassicalInvolution.Asc77.AscT3CIIStmt
public import CFSG.ClassicalInvolution.Asc77.AscT3Final

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

variable {G : Type} [Group G]

omit [Group G] in
theorem conj_eq_of_mem_centralizer' [Group G] {c z : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) : c * z * c⁻¹ = z := by
  have h := Subgroup.mem_centralizer_singleton_iff.mp hc
  calc c * z * c⁻¹ = z * c * c⁻¹ := by rw [h]
    _ = z := by group

theorem conjSub_mem_twinSet {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {K L : Subgroup G}
    {z : G} (hz : IsUniqueInvolution K z) (hL : L ∈ twinSet Ω K) {c : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) : conjSub c L ∈ twinSet Ω K := by
  obtain ⟨hLΩ, z', hz'K, hz'L⟩ := hL
  have e : z' = z := hz'K.eq hz
  subst e
  refine ⟨hΩ c L hLΩ, z', hz'K, ?_⟩
  have := hz'L.conj c
  rwa [conj_eq_of_mem_centralizer' hc] at this

theorem conjSub_mem_pair {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {K K' L : Subgroup G}
    {z : G} (hz : IsUniqueInvolution K z) (htw : twinSet Ω K = {K, K'}) (hL : L = K ∨ L = K')
    {c : G} (hc : c ∈ Subgroup.centralizer ({z} : Set G)) :
    conjSub c L = K ∨ conjSub c L = K' := by
  have hmem : L ∈ twinSet Ω K := by rw [htw]; exact hL
  have := conjSub_mem_twinSet hΩ hz hmem hc
  rwa [htw] at this

theorem conjSub_sup_pair {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {K K' : Subgroup G}
    {z : G} (hz : IsUniqueInvolution K z) (htw : twinSet Ω K = {K, K'}) (hne : K' ≠ K) {c : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) : conjSub c (K ⊔ K') = K ⊔ K' := by
  have h1 := conjSub_mem_pair hΩ hz htw (Or.inl rfl) hc
  have h2 := conjSub_mem_pair hΩ hz htw (Or.inr rfl) hc
  have hinj : conjSub c K ≠ conjSub c K' := fun h => hne ((conjSub_inj c).mp h).symm
  rw [conjSub_sup']
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hinj
  · rw [h1, h2]
  · rw [h1, h2, sup_comm]
  · exact absurd (h1.trans h2.symm) hinj

section Normalizer

variable [Finite G]

theorem mem_normalizer_of_conjSub_le {A : Subgroup G} {g : G} (h : conjSub g A ≤ A) :
    g ∈ Subgroup.normalizer (A : Set G) := by
  have hcard : Nat.card (conjSub g A) = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  exact mem_normalizer_iff_conjSub_eq.mpr (Subgroup.eq_of_le_of_card_ge h (by rw [hcard]))

omit [Finite G] in
theorem conjSub_iSup_le' {η : Set (Subgroup G)} {g : G} (h : ∀ U ∈ η, conjSub g U ∈ η) :
    conjSub g (⨆ U ∈ η, U) ≤ ⨆ U ∈ η, U := by
  change (⨆ U ∈ η, U).map (MulAut.conj g).toMonoidHom ≤ _
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun U hU => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_iSup₂ (f := fun V (_ : V ∈ η) => V) (conjSub g U) (h U hU)

omit [Finite G] in
theorem conjSub_sec20X_le {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {K K' : Subgroup G}
    {z : G} (hz : IsUniqueInvolution K z) (htw : twinSet Ω K = {K, K'}) {c : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) :
    conjSub c (sec20X Ω z K K') ≤ sec20X Ω z K K' := by
  unfold sec20X
  rw [conjSub_sup', conjSub_sup']
  have h1 := conjSub_mem_pair hΩ hz htw (Or.inl rfl) hc
  have h2 := conjSub_mem_pair hΩ hz htw (Or.inr rfl) hc
  refine sup_le (sup_le ?_ ?_) ?_
  · refine le_trans (conjSub_iSup_le' ?_) (le_trans le_sup_left le_sup_left)
    intro U hU
    refine ⟨USet.conj hΩ hU.1 c, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.centralizer _).mul_mem ((Subgroup.centralizer _).mul_mem hc (hU.2 hy))
      ((Subgroup.centralizer _).inv_mem hc)
  · rcases h1 with h | h <;> rw [h]
    · exact le_trans le_sup_right le_sup_left
    · exact le_sup_right
  · rcases h2 with h | h <;> rw [h]
    · exact le_trans le_sup_right le_sup_left
    · exact le_sup_right

theorem le_normalizer_sec20X {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {K K' : Subgroup G}
    {z : G} (hz : IsUniqueInvolution K z) (htw : twinSet Ω K = {K, K'}) :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (sec20X Ω z K K' : Set G) :=
  fun _ hc => mem_normalizer_of_conjSub_le (conjSub_sec20X_le hΩ hz htw hc)

omit [Finite G] in
theorem le_normalizer_sup_pair {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {K K' : Subgroup G}
    {z : G} (hz : IsUniqueInvolution K z) (htw : twinSet Ω K = {K, K'}) (hne : K' ≠ K) :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer ((K ⊔ K' : Subgroup G) : Set G) :=
  fun _ hc => mem_normalizer_iff_conjSub_eq.mpr (conjSub_sup_pair hΩ hz htw hne hc)

end Normalizer

theorem mem_of_odd_orderOf_of_mem_sup [Finite G] {N P : Subgroup G} (hP : IsPGroup 2 P)
    (hPN : P ≤ Subgroup.normalizer (N : Set G)) {x : G} (hx : x ∈ N ⊔ P)
    (hodd : Odd (orderOf x)) : x ∈ N := by
  have hNH : N ≤ Subgroup.normalizer (N : Set G) := fun n hn => Subgroup.mem_normalizer_iff.mpr
    fun y => ⟨fun hy => N.mul_mem (N.mul_mem hn hy) (N.inv_mem hn), fun hy => by
      have := N.mul_mem (N.mul_mem (N.inv_mem hn) hy) hn
      simpa [mul_assoc] using this⟩
  have hNorm : (N.subgroupOf (N ⊔ P)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    exact sup_le hNH hPN
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left N P hPN] at hx
  obtain ⟨n, hn, v, hv, rfl⟩ := hx
  set H : Subgroup G := N ⊔ P with hH
  set π := QuotientGroup.mk' (N.subgroupOf H) with hπ
  have hnH : n ∈ H := Subgroup.mem_sup_left hn
  have hvH : v ∈ H := Subgroup.mem_sup_right hv
  have hxH : n * v ∈ H := H.mul_mem hnH hvH
  have h1 : π ⟨n * v, hxH⟩ = π ⟨v, hvH⟩ := by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    rw [Subgroup.mem_subgroupOf]
    have hvi : v⁻¹ ∈ Subgroup.normalizer (N : Set G) :=
      (Subgroup.normalizer (N : Set G)).inv_mem (hPN hv)
    have := (Subgroup.mem_normalizer_iff.mp hvi n⁻¹).mp (N.inv_mem hn)
    simpa [mul_assoc] using this
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  set a : H := ⟨n * v, hxH⟩ with ha
  have hd1 : orderOf (π a) ∣ orderOf (n * v) := by
    have h3 : orderOf a = orderOf (n * v) := Subgroup.orderOf_mk _ _
    rw [← h3]
    exact orderOf_map_dvd π a
  have hd2 : orderOf (π a) ∣ 2 ^ k := by
    rw [ha, h1]
    have h3 : orderOf (⟨v, hvH⟩ : H) = orderOf v := Subgroup.orderOf_mk _ _
    have h4 := orderOf_map_dvd π (⟨v, hvH⟩ : H)
    rw [h3] at h4
    exact h4.trans (hk ▸ Subgroup.orderOf_dvd_natCard P hv)
  have hodd' : Odd (orderOf (π a)) := hodd.of_dvd_nat hd1
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd2
  have hi0 : i = 0 := by
    by_contra h
    rw [hi] at hodd'
    exact (Nat.not_even_iff_odd.mpr hodd') (Nat.even_pow.mpr ⟨even_two, h⟩)
  rw [hi0, pow_zero, orderOf_eq_one_iff] at hi
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff a).mp hi)

section TwinData

variable {Ω : Set (Subgroup G)}

structure Twin20 (Ω : Set (Subgroup G)) (K K' : Subgroup G) (z : G) (S V : Subgroup G) :
    Prop where
  hΩ : ConjInvariant Ω
  hz : IsUniqueInvolution K z
  htw : twinSet Ω K = {K, K'}
  hne : K' ≠ K
  hSz : S ≤ Subgroup.centralizer ({z} : Set G)
  hV : V ∈ USet Ω
  hVS : V ≤ S
  hV2 : IsPGroup 2 V

end TwinData

end CFSG.ClassicalInvolution.Asc77.T3CII
