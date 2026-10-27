module

public import CFSG.LocalAnalysis.GH72.MaxInvariant
public import CFSG.LocalAnalysis.GH72.OuterCyclic
public import CFSG.GroupTheory.ABGDGroups.LinearFieldCentralizers

public section

namespace CFSG.GH72

open Subgroup
open scoped MatrixGroups
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.GorensteinWalter (PSL2 PGL2 PGammaL2 IsOddPrimePower pGammaL2PSLRange)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

local notation "A₇" => alternatingGroup (Fin 7)

theorem exists_isLinearDecomposition_of_normal_psl2 {H : Type} [Group H] [Finite H] {F : Type}
    [Field F] [Finite F] (hF : IsOddPrimePower (Nat.card F)) (hq : 3 < Nat.card F)
    {N : Subgroup H} [N.Normal] (e : N ≃* PSL2 F) (hC : centralizer (N : Set H) = ⊥)
    (hodd : Odd N.index) (S : Sylow 2 H) :
    ∃ (ι : H →* PGammaL2 F) (E : Subgroup H), CFSG.ABGDGroups.IsLinearDecomposition ι N E S ∧
      CFSG.ABGDGroups.linearCore ι = N := by
  obtain ⟨ι, hι, hPSL, hcore⟩ := CFSG.ABGDGroups.exists_embedding_of_normal_psl2 hF hq e hC
  have hodd' : Odd ((pGammaL2PSLRange F).relIndex ι.range) := by
    rw [← Subgroup.index_comap]
    change Odd (CFSG.ABGDGroups.linearCore ι).index
    rw [hcore]
    exact hodd
  obtain ⟨ι', E, hd, hmap⟩ := CFSG.ABGDGroups.exists_isLinearDecomposition_of_embedding hF hι
    (Or.inl rfl) hPSL hodd' S
  have hL : (pGammaL2PSLRange F).comap ι = N := hcore
  rw [hL] at hd hmap
  refine ⟨ι', E, hd, ?_⟩
  change (pGammaL2PSLRange F).comap ι' = N
  rw [← hmap, comap_map_eq_self_of_injective hd.injective]

theorem mem_of_odd_orderOf_of_mem_sup {G : Type*} [Group G] [Finite G] {T E : Subgroup G}
    (hT : IsPGroup 2 T) (hE : Odd (Nat.card E)) (hTE : T ≤ centralizer (E : Set G)) {x : G}
    (hx : x ∈ T ⊔ E) (hxo : Odd (orderOf x)) : x ∈ E := by
  have hTN : T ≤ normalizer (E : Set G) := hTE.trans (centralizer_le_normalizer _)
  have hx' : x ∈ ((T ⊔ E : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right T E hTN] at hx'
  obtain ⟨t, ht, f, hf, rfl⟩ := hx'
  have hcomm : Commute t f := (mem_centralizer_iff.mp (hTE ht) f hf).symm
  obtain ⟨m, hm⟩ := hxo
  have hpow : (t * f) ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one _
  rw [hcomm.mul_pow] at hpow
  have htf : t ^ (2 * m + 1) = (f ^ (2 * m + 1))⁻¹ := eq_inv_of_mul_eq_one_left hpow
  have hTE' : t ^ (2 * m + 1) ∈ T ⊓ E :=
    ⟨T.pow_mem ht _, by rw [htf]; exact E.inv_mem (E.pow_mem hf _)⟩
  have hdisj : T ⊓ E = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have h1 : orderOf y ∣ Nat.card E := Subgroup.orderOf_dvd_natCard E hy.2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hT ⟨y, hy.1⟩
    have h2 : orderOf y ∣ 2 ^ k := by
      rw [← Subgroup.orderOf_mk y hy.1]
      exact orderOf_dvd_of_pow_eq_one hk
    have h3 : orderOf y = 1 :=
      Nat.eq_one_of_dvd_coprimes ((Nat.coprime_two_right.mpr hE).pow_right k).symm h2 h1
    exact (mem_bot).2 (orderOf_eq_one_iff.mp h3)
  rw [hdisj, mem_bot] at hTE'
  have ht1 : t = 1 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
    have h2 : orderOf t ∣ 2 ^ k := by
      rw [← Subgroup.orderOf_mk t ht]
      exact orderOf_dvd_of_pow_eq_one hk
    have h1 : orderOf t ∣ 2 * m + 1 := orderOf_dvd_of_pow_eq_one hTE'
    have hcop : Nat.Coprime (2 ^ k) (2 * m + 1) :=
      (Nat.coprime_two_left.mpr (odd_two_mul_add_one m)).pow_left k
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 h1)
  subst ht1
  simpa using hf

section ASeven

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem exists_mem_conj_eq_of_odd_of_aSeven {J : Subgroup X} (e : J ≃* A₇) {x : X}
    (hx : x ∈ normalizer (J : Set X)) (hxo : Odd (orderOf x)) :
    ∃ j ∈ J, ∀ z ∈ J, x * z * x⁻¹ = j * z * j⁻¹ := by
  set Y := normalizer (J : Set X) with hYdef
  have hJ' : (J.subgroupOf Y).Normal := Subgroup.normal_in_normalizer
  set eJ : J.subgroupOf Y ≃* A₇ := (subgroupOfEquivOfLe le_normalizer).trans e
  set α : MulAut (J.subgroupOf Y) := MulAut.conjNormal (⟨x, hx⟩ : Y)
  set E := CFSG.ComponentClassification.OuterAutomorphisms.equivalence eJ
  have h2 : (QuotientGroup.mk' (inner (J.subgroupOf Y)) α) ^ 2 = 1 := by
    apply E.injective
    rw [map_pow, map_one, sq, outer_alternatingGroup_seven_mul_self]
  have hn : (QuotientGroup.mk' (inner (J.subgroupOf Y)) α) ^ orderOf x = 1 := by
    rw [← map_pow]
    have : α ^ orderOf x = 1 := by
      rw [← map_pow]
      have hpow : (⟨x, hx⟩ : Y) ^ orderOf x = 1 := by
        apply Subtype.ext
        simp [pow_orderOf_eq_one]
      rw [hpow, map_one]
    rw [this, map_one]
  have h1 : QuotientGroup.mk' (inner (J.subgroupOf Y)) α = 1 := by
    have hd2 := orderOf_dvd_of_pow_eq_one h2
    have hdn := orderOf_dvd_of_pow_eq_one hn
    have := Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr hxo) hd2 hdn
    exact orderOf_eq_one_iff.mp this
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  obtain ⟨j', hj'⟩ := h1
  refine ⟨((j' : Y) : X), j'.2, fun z hz => ?_⟩
  have := congrArg (fun β : MulAut (J.subgroupOf Y) =>
    (((β ⟨⟨z, le_normalizer hz⟩, by simpa [mem_subgroupOf] using hz⟩ : J.subgroupOf Y) : Y) : X))
    hj'
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, α,
    MulAut.conjNormal_apply] at this
  exact this.symm

omit [Finite X] in
theorem le_and_card_dvd_three_of_aSeven {J V : Subgroup X} (e : J ≃* A₇) (hV : IsKleinFour V)
    (hVJ : V ≤ J) {U : Subgroup X} (hUJ : U ≤ normalizer (J : Set X)) (hU : Odd (Nat.card U))
    (hUV : U ≤ centralizer (V : Set X)) (hfaith : (J ⊔ U) ⊓ centralizer (J : Set X) = ⊥) :
    U ≤ J ∧ Nat.card U ∣ 3 := by
  have hUJ' : U ≤ J := fun u hu => by
    obtain ⟨j, hj, hju⟩ := exists_mem_conj_eq_of_odd_of_aSeven e (hUJ hu)
      (hU.of_dvd_nat (Subgroup.orderOf_dvd_natCard U hu))
    have hc : j⁻¹ * u ∈ (J ⊔ U) ⊓ centralizer (J : Set X) := by
      refine ⟨mul_mem_sup (J.inv_mem hj) hu, mem_centralizer_iff.mpr fun z hz => ?_⟩
      have h := hju z hz
      calc z * (j⁻¹ * u) = j⁻¹ * (j * z * j⁻¹) * u := by group
        _ = j⁻¹ * (u * z * u⁻¹) * u := by rw [h]
        _ = j⁻¹ * u * z := by group
    rw [hfaith, mem_bot] at hc
    have : u = j := by
      calc u = j * (j⁻¹ * u) := by group
        _ = j := by rw [hc, mul_one]
    rw [this]
    exact hj
  refine ⟨hUJ', ?_⟩
  obtain ⟨v, hv, hv1, -⟩ := exists_mem_kleinFour_ne hV (one_mem V)
  have hv2 : orderOf v = 2 := orderOf_eq_prime (sq_eq_one_of_mem_kleinFour hV hv) hv1
  obtain ⟨Uv, -, hUvc, hodd⟩ := exists_card_eq_three_forall_odd_mem_of_aSeven e (hVJ hv) hv2
  have hle : U ≤ Uv := fun u hu => hodd u
    ⟨hUJ' hu, mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hUV hu)) v hv).symm⟩
    (hU.of_dvd_nat (Subgroup.orderOf_dvd_natCard U hu))
  have hfin : Finite Uv := Nat.finite_of_card_ne_zero (by rw [hUvc]; norm_num)
  exact hUvc ▸ Subgroup.card_dvd_of_le hle

theorem exists_le_centralizer_of_odd_of_le_normalizer_of_aSeven
    {J V P : Subgroup X} (e : J ≃* A₇) (hV : IsKleinFour V) (hVJ : V ≤ J)
    (hPJ : P ≤ normalizer (J : Set X)) (hP : Odd (Nat.card P))
    (hVP : V ≤ normalizer (P : Set X)) : ∃ a ∈ V, a ≠ 1 ∧ P ≤ centralizer ({a} : Set X) := by
  have hZ : J ⊓ centralizer (J : Set X) = ⊥ := inf_centralizer_eq_bot_of_isL2OrA7 J (qmin := 5)
    (Or.inl ⟨e⟩)
  let W : Subgroup X :=
    { carrier := {j | j ∈ J ∧ ∃ x ∈ P, ∀ z ∈ J, x * z * x⁻¹ = j * z * j⁻¹}
      one_mem' := ⟨J.one_mem, 1, P.one_mem, fun z _ => by group⟩
      mul_mem' := by
        rintro j₁ j₂ ⟨hj₁, x₁, hx₁, h₁⟩ ⟨hj₂, x₂, hx₂, h₂⟩
        refine ⟨J.mul_mem hj₁ hj₂, x₁ * x₂, P.mul_mem hx₁ hx₂, fun z hz => ?_⟩
        have hz' : j₂ * z * j₂⁻¹ ∈ J := J.mul_mem (J.mul_mem hj₂ hz) (J.inv_mem hj₂)
        calc x₁ * x₂ * z * (x₁ * x₂)⁻¹ = x₁ * (x₂ * z * x₂⁻¹) * x₁⁻¹ := by group
          _ = x₁ * (j₂ * z * j₂⁻¹) * x₁⁻¹ := by rw [h₂ z hz]
          _ = j₁ * (j₂ * z * j₂⁻¹) * j₁⁻¹ := h₁ _ hz'
          _ = j₁ * j₂ * z * (j₁ * j₂)⁻¹ := by group
      inv_mem' := by
        rintro j ⟨hj, x, hx, h⟩
        refine ⟨J.inv_mem hj, x⁻¹, P.inv_mem hx, fun z hz => ?_⟩
        have hz' : x⁻¹ * z * x ∈ J := by
          have := (mem_normalizer_iff.mp (hPJ (P.inv_mem hx)) z).mp hz
          simpa using this
        have h' := h _ hz'
        have h'' : z = j * (x⁻¹ * z * x) * j⁻¹ := by
          rw [← h']
          group
        calc x⁻¹ * z * x⁻¹⁻¹ = j⁻¹ * (j * (x⁻¹ * z * x) * j⁻¹) * j := by group
          _ = j⁻¹ * z * j⁻¹⁻¹ := by rw [← h'']; group }
  have hWJ : W ≤ J := fun j hj => hj.1
  have hWodd : Odd (Nat.card W) := by
    by_contra heven
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at heven
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨⟨j, hjJ, x, hx, h⟩, hj2'⟩ := exists_prime_orderOf_dvd_card' 2 heven
    have hj2 : orderOf j = 2 := (orderOf_injective W.subtype W.subtype_injective _).trans hj2' 
    have hpow : ∀ k : ℕ, ∀ z ∈ J, x ^ k * z * (x ^ k)⁻¹ = j ^ k * z * (j ^ k)⁻¹ := by
      intro k
      induction k with
      | zero => intro z _; group
      | succ k ih =>
        intro z hz
        have hz' : j ^ k * z * (j ^ k)⁻¹ ∈ J :=
          J.mul_mem (J.mul_mem (J.pow_mem hjJ k) hz) (J.inv_mem (J.pow_mem hjJ k))
        calc x ^ (k + 1) * z * (x ^ (k + 1))⁻¹ = x * (x ^ k * z * (x ^ k)⁻¹) * x⁻¹ := by group
          _ = x * (j ^ k * z * (j ^ k)⁻¹) * x⁻¹ := by rw [ih z hz]
          _ = j * (j ^ k * z * (j ^ k)⁻¹) * j⁻¹ := h _ hz'
          _ = j ^ (k + 1) * z * (j ^ (k + 1))⁻¹ := by group
    have hxo : Odd (orderOf x) := hP.of_dvd_nat (Subgroup.orderOf_dvd_natCard P hx)
    have hjn : j ^ orderOf x ∈ J ⊓ centralizer (J : Set X) := by
      refine ⟨J.pow_mem hjJ _, mem_centralizer_iff.mpr fun z hz => ?_⟩
      have h1 := hpow (orderOf x) z hz
      rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h1
      calc z * j ^ orderOf x = j ^ orderOf x * z * (j ^ orderOf x)⁻¹ * j ^ orderOf x := by
            rw [← h1]
        _ = j ^ orderOf x * z := by group
    rw [hZ, mem_bot] at hjn
    have hdvd : orderOf j ∣ orderOf x := orderOf_dvd_of_pow_eq_one hjn
    rw [hj2] at hdvd
    exact (Nat.not_even_iff_odd.mpr hxo) (even_iff_two_dvd.mpr hdvd)
  have hVW : V ≤ normalizer (W : Set X) := fun v hv => by
    apply mem_normalizer_fintype
    rintro j ⟨hjJ, x, hx, h⟩
    refine ⟨J.mul_mem (J.mul_mem (hVJ hv) hjJ) (J.inv_mem (hVJ hv)), v * x * v⁻¹,
      (mem_normalizer_iff.mp (hVP hv) x).mp hx, fun z hz => ?_⟩
    have hz' : v⁻¹ * z * v ∈ J := J.mul_mem (J.mul_mem (J.inv_mem (hVJ hv)) hz) (hVJ hv)
    calc v * x * v⁻¹ * z * (v * x * v⁻¹)⁻¹ = v * (x * (v⁻¹ * z * v) * x⁻¹) * v⁻¹ := by group
      _ = v * (j * (v⁻¹ * z * v) * j⁻¹) * v⁻¹ := by rw [h _ hz']
      _ = v * j * v⁻¹ * z * (v * j * v⁻¹)⁻¹ := by group
  obtain ⟨-, a, ha, ha1, hWa⟩ :=
    isCyclic_and_exists_le_centralizer_of_aSeven e hV hVJ hWJ hWodd hVW
  refine ⟨a, ha, ha1, fun x hx => ?_⟩
  obtain ⟨j, hj, hjx⟩ := exists_mem_conj_eq_of_odd_of_aSeven e (hPJ hx)
    (hP.of_dvd_nat (Subgroup.orderOf_dvd_natCard P hx))
  have hjW : j ∈ W := ⟨hj, x, hx, hjx⟩
  have hja := mem_centralizer_singleton_iff.mp (hWa hjW)
  rw [mem_centralizer_singleton_iff]
  have h := hjx a (hVJ ha)
  calc x * a = x * a * x⁻¹ * x := by group
    _ = j * a * j⁻¹ * x := by rw [h]
    _ = a * x := by rw [hja]; group

end ASeven

theorem inf_eq_bot_of_odd_of_le_centralizer_kleinFour
    {X : Type*} [Group X] [Finite X]
    {J V : Subgroup X} {r k : ℕ} [Fact r.Prime] (hr : r ≠ 2) (hq : 5 ≤ r ^ k)
    (e : J ≃* PSL(2, GaloisField r k)) (hV : IsKleinFour V) (hVJ : V ≤ J) {U : Subgroup X}
    (hU : Odd (Nat.card U)) (hUV : U ≤ centralizer (V : Set X)) : U ⊓ J = ⊥ := by
  have hF := isOddPrimePower_card_galoisField hr (by omega : 3 ≤ r ^ k)
  set f : PSL2 (GaloisField r k) →* X := J.subtype.comp e.symm.toMonoidHom with hfdef
  have hf : Function.Injective f := J.subtype_injective.comp e.symm.injective
  have hfr : f.range = J := range_subtype_comp_symm e
  have hVr : V ≤ f.range := hfr ▸ hVJ
  have hC := CFSG.GorensteinWalter.psl2_kleinFour_centralizer_eq_self _ hF (V.comap f)
    (isKleinFour_comap f hf hV hVr)
  have hle : U ⊓ J ≤ V := by
    rintro x ⟨hxU, hxJ⟩
    obtain ⟨x', rfl⟩ := hfr ▸ hxJ
    have hx' : x' ∈ centralizer ((V.comap f : Subgroup _) : Set (PSL2 (GaloisField r k))) :=
      mem_centralizer_iff.mpr fun v hv => hf (by
        rw [map_mul, map_mul]
        exact mem_centralizer_iff.mp (hUV hxU) (f v) hv)
    rw [hC] at hx'
    exact hx'
  exact eq_bot_of_le_of_isKleinFour hV hle (hU.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))

section Faithful

variable {X : Type} [Group X] [Finite X]

theorem exists_isLinearDecomposition_sup
    {J V U : Subgroup X} {r k : ℕ} [Fact r.Prime] (hr : r ≠ 2) (hq : 5 ≤ r ^ k)
    (e : J ≃* PSL(2, GaloisField r k)) (hV : IsKleinFour V) (hVJ : V ≤ J)
    (hUJ : U ≤ normalizer (J : Set X)) (hU : Odd (Nat.card U))
    (hUV : U ≤ centralizer (V : Set X)) (hfaith : (J ⊔ U) ⊓ centralizer (J : Set X) = ⊥) :
    ∃ (ι : ↥(J ⊔ U) →* PGammaL2 (GaloisField r k)) (E : Subgroup ↥(J ⊔ U))
      (S : Sylow 2 ↥(J ⊔ U)),
      CFSG.ABGDGroups.IsLinearDecomposition ι (J.subgroupOf (J ⊔ U)) E S ∧
      CFSG.ABGDGroups.linearCore ι = J.subgroupOf (J ⊔ U) ∧
      V.subgroupOf (J ⊔ U) ≤ S ∧ U.subgroupOf (J ⊔ U) = E := by
  have hk : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hq
    omega
  have hF := isOddPrimePower_card_galoisField hr (by omega : 3 ≤ r ^ k)
  have hq3 : 3 < Nat.card (GaloisField r k) := by rw [GaloisField.card r k hk]; omega
  have hHN : J ⊔ U ≤ normalizer (J : Set X) := sup_le le_normalizer hUJ
  have hN : (J.subgroupOf (J ⊔ U)).Normal := normal_subgroupOf_of_le_normalizer hHN
  have e' : J.subgroupOf (J ⊔ U) ≃* PSL2 (GaloisField r k) :=
    (subgroupOfEquivOfLe le_sup_left).trans e
  have hC : centralizer ((J.subgroupOf (J ⊔ U) : Subgroup ↥(J ⊔ U)) : Set ↥(J ⊔ U)) = ⊥ := by
    rw [eq_bot_iff]
    intro h hh
    have hmem : (h : X) ∈ (J ⊔ U) ⊓ centralizer (J : Set X) := by
      refine ⟨h.2, mem_centralizer_iff.mpr fun z hz => ?_⟩
      have := mem_centralizer_iff.mp hh ⟨z, (le_sup_left : J ≤ J ⊔ U) hz⟩
        (by simpa [mem_subgroupOf] using hz)
      exact congrArg Subtype.val this
    rw [hfaith, mem_bot] at hmem
    exact (mem_bot).2 (Subtype.ext hmem)
  have hUJbot : U ⊓ J = ⊥ := inf_eq_bot_of_odd_of_le_centralizer_kleinFour hr hq e hV hVJ hU hUV
  have hindex : (J.subgroupOf (J ⊔ U)).index = Nat.card (U.subgroupOf (J ⊔ U)) := by
    have htop : J.subgroupOf (J ⊔ U) ⊔ U.subgroupOf (J ⊔ U) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    rw [← Subgroup.relIndex_top_right, ← htop, Subgroup.relIndex_sup_left]
    have hbot : (J.subgroupOf (J ⊔ U)).subgroupOf (U.subgroupOf (J ⊔ U)) = ⊥ := by
      rw [eq_bot_iff]
      rintro ⟨⟨x, hxH⟩, hxU⟩ hxJ
      have hxJ' : x ∈ J := hxJ
      have hxU' : x ∈ U := hxU
      have : x ∈ U ⊓ J := ⟨hxU', hxJ'⟩
      rw [hUJbot, mem_bot] at this
      subst this
      rfl
    rw [Subgroup.relIndex, hbot, Subgroup.index_bot]
  have hodd : Odd (J.subgroupOf (J ⊔ U)).index := by
    rw [hindex, Nat.card_congr (subgroupOfEquivOfLe le_sup_right).toEquiv]
    exact hU
  have hVH : V ≤ J ⊔ U := hVJ.trans le_sup_left
  have hT : IsKleinFour (V.subgroupOf (J ⊔ U)) :=
    ⟨by rw [Nat.card_congr (subgroupOfEquivOfLe hVH).toEquiv]; exact hV.card_four,
      by rw [Monoid.exponent_eq_of_mulEquiv (subgroupOfEquivOfLe hVH)]; exact hV.exponent_two⟩
  obtain ⟨S, hTS⟩ := (CFSG.ABGDGroups.isPGroup_two_of_isKleinFour hT).exists_le_sylow
  obtain ⟨ι, E, hd, hcore⟩ := exists_isLinearDecomposition_of_normal_psl2 hF hq3 e' hC hodd S
  refine ⟨ι, E, S, hd, hcore, hTS, ?_⟩
  have hCT := (hd.centralizer_kleinFour hT hTS).1
  have hUC : U.subgroupOf (J ⊔ U) ≤ centralizer ((V.subgroupOf (J ⊔ U) : Subgroup _) : Set _) :=
    fun u hu => mem_centralizer_iff.mpr fun v hv => Subtype.ext
      (mem_centralizer_iff.mp (hUV hu) (v : X) hv)
  have hTE : V.subgroupOf (J ⊔ U) ≤ centralizer (E : Set ↥(J ⊔ U)) := fun t ht =>
    mem_centralizer_iff.mpr fun f hf =>
      (mem_centralizer_iff.mp (hd.le_centralizer hf) t (hTS ht)).symm
  have hUodd : Odd (Nat.card (U.subgroupOf (J ⊔ U))) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe le_sup_right).toEquiv]
  have hUE : U.subgroupOf (J ⊔ U) ≤ E := fun u hu => by
    have hu' := hCT ▸ hUC hu
    exact mem_of_odd_orderOf_of_mem_sup (CFSG.ABGDGroups.isPGroup_two_of_isKleinFour hT)
      hd.odd_card hTE hu' (hUodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hu))
  have hcardE : Nat.card E = Nat.card (U.subgroupOf (J ⊔ U)) := by
    rw [← hd.index_eq_card, hindex]
  exact Subgroup.eq_of_le_of_card_ge hUE (by rw [hcardE])

theorem isCyclic_of_odd_of_le_centralizer_kleinFour
    {J V : Subgroup X} (hJ : IsL2OrA7 J 5) (hV : IsKleinFour V) (hVJ : V ≤ J) {U : Subgroup X}
    (hUJ : U ≤ normalizer (J : Set X)) (hU : Odd (Nat.card U)) (hUV : U ≤ centralizer (V : Set X))
    (hfaith : (J ⊔ U) ⊓ centralizer (J : Set X) = ⊥) : IsCyclic U := by
  rcases hJ with ⟨⟨e⟩⟩ | ⟨r, k, hr, hr2, hq, ⟨e⟩⟩
  · obtain ⟨-, h3⟩ := le_and_card_dvd_three_of_aSeven e hV hVJ hUJ hU hUV hfaith
    rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
    · have : Subsingleton U := (Nat.card_eq_one_iff_unique.mp h).1
      exact isCyclic_of_subsingleton
    · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact isCyclic_of_prime_card h
  · obtain ⟨ι, E, S, hd, -, -, hUE⟩ := exists_isLinearDecomposition_sup hr2 hq e hV hVJ hUJ hU hUV
      hfaith
    have hEc : IsCyclic E := hd.isCyclic
    rw [← hUE] at hEc
    exact (subgroupOfEquivOfLe (le_sup_right : U ≤ J ⊔ U)).isCyclic.mp hEc

theorem finite_mulAut (G : Type*) [Group G] [Finite G] : Finite (MulAut G) :=
  Finite.of_injective (fun α : MulAut G => (α : G ≃ G)) MulEquiv.toEquiv_injective

theorem exists_le_centralizer_of_odd_of_le_normalizer_of_psl2
    {J V P : Subgroup X} {r k : ℕ}
    [Fact r.Prime] (hr : r ≠ 2) (hq : 5 ≤ r ^ k) (e : J ≃* PSL(2, GaloisField r k))
    (hV : IsKleinFour V) (hVJ : V ≤ J) (hPJ : P ≤ normalizer (J : Set X))
    (hP : Odd (Nat.card P)) (hVP : V ≤ normalizer (P : Set X)) :
    ∃ a ∈ V, a ≠ 1 ∧ P ≤ centralizer ({a} : Set X) := by
  have hk : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hq
    omega
  have hF := isOddPrimePower_card_galoisField hr (by omega : 3 ≤ r ^ k)
  have hq3 : 3 < Nat.card (GaloisField r k) := by rw [GaloisField.card r k hk]; omega
  have hJ5 : IsL2OrA7 J 5 := Or.inr ⟨r, k, inferInstance, hr, hq, ⟨e⟩⟩
  have hZ : J ⊓ centralizer (J : Set X) = ⊥ := inf_centralizer_eq_bot_of_isL2OrA7 J hJ5
  set Y := normalizer (J : Set X) with hYdef
  have hJ'n : (J.subgroupOf Y).Normal := Subgroup.normal_in_normalizer
  set J' := J.subgroupOf Y with hJ'def
  have : Finite (MulAut J') := finite_mulAut J'
  set φ : Y →* MulAut J' := MulAut.conjNormal with hφdef
  have hZ' : center J' = ⊥ :=
    center_eq_bot_of_isL2OrA7 (isL2OrA7_of_mulEquiv (subgroupOfEquivOfLe le_normalizer) hJ5)
  have hinj : Function.Injective (MulAut.conj : J' →* MulAut J') := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro j hj
    rw [MonoidHom.mem_ker] at hj
    have hjc : j ∈ center J' := mem_center_iff.mpr fun z => by
      have := congrArg (fun β : MulAut J' => β z) hj
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc z * j = j * z * j⁻¹ * j := by rw [this]
        _ = j * z := by group
    rw [hZ'] at hjc
    exact hjc
  have hcent : ∀ c : Y, MulAut.conjNormal c = (1 : MulAut J') →
      (c : X) ∈ centralizer (J : Set X) := by
    intro c hc
    rw [mem_centralizer_iff]
    intro z hz
    have h := congrArg (fun β : MulAut J' =>
      (((β ⟨⟨z, le_normalizer hz⟩, hz⟩ : J') : Y) : X)) hc
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
    change (c : X) * z * (c : X)⁻¹ = z at h
    calc z * (c : X) = (c : X) * z * (c : X)⁻¹ * c := by rw [h]
      _ = c * z := by group
  have hkey : ∀ x v : Y, (v : X) ∈ J → φ x * φ v = φ v * φ x → (x : X) * v = v * x := by
    intro x v hv h
    have h1 : φ (x * v * x⁻¹ * v⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
      group
    have hcJ : ((x * v * x⁻¹ * v⁻¹ : Y) : X) ∈ J := by
      have h2 : (x : X) * v * (x : X)⁻¹ ∈ J := (mem_normalizer_iff.mp x.2 v).mp hv
      simpa using J.mul_mem h2 (J.inv_mem hv)
    have hc : ((x * v * x⁻¹ * v⁻¹ : Y) : X) ∈ J ⊓ centralizer (J : Set X) := ⟨hcJ, hcent _ h1⟩
    rw [hZ, mem_bot] at hc
    have : (x : X) * v * (x : X)⁻¹ * (v : X)⁻¹ = 1 := by simpa using hc
    calc (x : X) * v = (x : X) * v * (x : X)⁻¹ * (v : X)⁻¹ * v * x := by group
      _ = v * x := by rw [this, one_mul]
  set Inn : Subgroup (MulAut J') := inner J' with hInndef
  set P₀ : Subgroup (MulAut J') := (P.subgroupOf Y).map φ with hP₀def
  set Hs : Subgroup (MulAut J') := Inn ⊔ P₀ with hHsdef
  have hInn : Inn.Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal J'
  have hN : (Inn.subgroupOf Hs).Normal := inferInstance
  have e' : Inn.subgroupOf Hs ≃* PSL2 (GaloisField r k) :=
    (subgroupOfEquivOfLe (le_sup_left : Inn ≤ Hs)).trans
      ((MonoidHom.ofInjective hinj).symm.trans ((subgroupOfEquivOfLe le_normalizer).trans e))
  have hC : centralizer ((Inn.subgroupOf Hs : Subgroup ↥Hs) : Set ↥Hs) = ⊥ := by
    rw [eq_bot_iff]
    intro α hα
    have h1 : ∀ j : J', (α : MulAut J') j = j := by
      intro j
      have hmem : (⟨MulAut.conj j, mem_sup_left ⟨j, rfl⟩⟩ : Hs) ∈ Inn.subgroupOf Hs := ⟨j, rfl⟩
      have h2 := congrArg Subtype.val (mem_centralizer_iff.mp hα _ hmem)
      change MulAut.conj j * (α : MulAut J') = (α : MulAut J') * MulAut.conj j at h2
      have h3 : MulAut.conj ((α : MulAut J') j) = MulAut.conj j := by
        apply MulEquiv.ext
        intro z
        have h4 := congrArg (fun β : MulAut J' => β ((α : MulAut J').symm z)) h2
        simp only [MulAut.mul_apply, MulAut.conj_apply, MulEquiv.apply_symm_apply] at h4
        rw [MulAut.conj_apply, MulAut.conj_apply]
        have h5 : (α : MulAut J') (j * (α : MulAut J').symm z * j⁻¹) =
            (α : MulAut J') j * z * ((α : MulAut J') j)⁻¹ := by
          rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
        rw [← h5, h4]
      exact hinj h3
    exact (mem_bot).2 (Subtype.ext (MulEquiv.ext h1))
  have hodd : Odd (Inn.subgroupOf Hs).index := by
    change Odd (Inn.relIndex (Inn ⊔ P₀))
    rw [Subgroup.relIndex_sup_left]
    refine (hP.of_dvd_nat ?_)
    refine (Subgroup.relIndex_dvd_card Inn P₀).trans ((Subgroup.card_map_dvd _ _).trans ?_)
    rw [Nat.card_congr (subgroupOfEquivOfLe hPJ).toEquiv]
  have hVY : V ≤ Y := hVJ.trans le_normalizer
  have hVY' : IsKleinFour (V.subgroupOf Y) :=
    ⟨by rw [Nat.card_congr (subgroupOfEquivOfLe hVY).toEquiv]; exact hV.card_four,
      by rw [Monoid.exponent_eq_of_mulEquiv (subgroupOfEquivOfLe hVY)]; exact hV.exponent_two⟩
  have hker : V.subgroupOf Y ⊓ φ.ker = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hvV, hvk⟩
    have hc : (v : X) ∈ J ⊓ centralizer (J : Set X) := ⟨hVJ hvV, hcent v hvk⟩
    rw [hZ, mem_bot] at hc
    exact (mem_bot).2 (Subtype.ext hc)
  have hT₀ : IsKleinFour ((V.subgroupOf Y).map φ) :=
    CFSG.ABGDGroups.isKleinFour_map_of_inf_ker_eq_bot φ hVY' hker
  have hT₀Inn : (V.subgroupOf Y).map φ ≤ Inn := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨⟨v, hVJ hv⟩, (MulAut.conjNormal_val (h := (⟨v, hVJ hv⟩ : J'))).symm⟩
  have hT₀H : (V.subgroupOf Y).map φ ≤ Hs := hT₀Inn.trans le_sup_left
  have hT : IsKleinFour (((V.subgroupOf Y).map φ).subgroupOf Hs) :=
    ⟨by rw [Nat.card_congr (subgroupOfEquivOfLe hT₀H).toEquiv]; exact hT₀.card_four,
      by rw [Monoid.exponent_eq_of_mulEquiv (subgroupOfEquivOfLe hT₀H)]; exact hT₀.exponent_two⟩
  have hP₀H : P₀ ≤ Hs := le_sup_right
  have hY₀odd : Odd (Nat.card (P₀.subgroupOf Hs)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hP₀H).toEquiv]
    refine hP.of_dvd_nat ((Subgroup.card_map_dvd _ _).trans ?_)
    rw [Nat.card_congr (subgroupOfEquivOfLe hPJ).toEquiv]
  have hTY : ((V.subgroupOf Y).map φ).subgroupOf Hs ≤
      normalizer ((P₀.subgroupOf Hs : Subgroup ↥Hs) : Set ↥Hs) := by
    rintro ⟨t, ht⟩ htT
    obtain ⟨v, hv, rfl⟩ := htT
    apply mem_normalizer_fintype
    rintro ⟨y, hy⟩ hyP
    obtain ⟨x, hx, rfl⟩ := hyP
    have hvx : v * x * v⁻¹ ∈ P.subgroupOf Y := by
      change (v : X) * x * (v : X)⁻¹ ∈ P
      exact (mem_normalizer_iff.mp (hVP hv) x).mp hx
    refine ⟨v * x * v⁻¹, hvx, ?_⟩
    rw [map_mul, map_mul, map_inv]
    rfl
  have hYT : P₀.subgroupOf Hs ⊓ ((V.subgroupOf Y).map φ).subgroupOf Hs = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyP, hyT⟩
    have h1 : orderOf y ∣ Nat.card (P₀.subgroupOf Hs) := Subgroup.orderOf_dvd_natCard _ hyP
    have h2 : orderOf y ∣ 2 ^ 2 := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hT.card_four]
      exact Subgroup.orderOf_dvd_natCard _ hyT
    have h3 :=
      Nat.eq_one_of_dvd_coprimes ((Nat.coprime_two_right.mpr hY₀odd).pow_right 2).symm h2 h1
    exact (mem_bot).2 (orderOf_eq_one_iff.mp h3)
  obtain ⟨S, hTS⟩ := (CFSG.ABGDGroups.isPGroup_two_of_isKleinFour hT).exists_le_sylow
  obtain ⟨ι, E, hd, -⟩ := exists_isLinearDecomposition_of_normal_psl2 hF hq3 e' hC hodd S
  obtain ⟨t, htT, ht1, hYt⟩ := hd.exists_le_centralizer_of_kleinFour hT hTY hYT
  obtain ⟨v, hv, hvt⟩ := htT
  have hvt' : (t : MulAut J') = φ v := hvt.symm
  refine ⟨(v : X), hv, fun h => ht1 (Subtype.ext ?_), fun x hx => ?_⟩
  · have hv1 : v = 1 := Subtype.ext h
    rw [hvt', hv1, map_one]
    rfl
  · have hxY : x ∈ Y := hPJ hx
    have hyP : (⟨φ ⟨x, hxY⟩, hP₀H ⟨⟨x, hxY⟩, hx, rfl⟩⟩ : Hs) ∈ P₀.subgroupOf Hs :=
      ⟨⟨x, hxY⟩, hx, rfl⟩
    have h1 := congrArg Subtype.val (mem_centralizer_singleton_iff.mp (hYt hyP))
    change φ ⟨x, hxY⟩ * (t : MulAut J') = (t : MulAut J') * φ ⟨x, hxY⟩ at h1
    rw [hvt'] at h1
    have h2 := hkey ⟨x, hxY⟩ v (hVJ hv) h1
    rw [mem_centralizer_singleton_iff]
    exact h2

theorem exists_le_centralizer_of_odd_of_le_normalizer
    {J V : Subgroup X} (hJ : IsL2OrA7 J 5) (hV : IsKleinFour V) (hVJ : V ≤ J) {P : Subgroup X}
    (hPJ : P ≤ normalizer (J : Set X)) (hP : Odd (Nat.card P))
    (hVP : V ≤ normalizer (P : Set X)) : ∃ a ∈ V, a ≠ 1 ∧ P ≤ centralizer ({a} : Set X) := by
  rcases hJ with ⟨⟨e⟩⟩ | ⟨r, k, hr, hr2, hq, ⟨e⟩⟩
  · exact exists_le_centralizer_of_odd_of_le_normalizer_of_aSeven e hV hVJ hPJ hP hVP
  · exact exists_le_centralizer_of_odd_of_le_normalizer_of_psl2 hr2 hq e hV hVJ hPJ hP hVP

end Faithful

end CFSG.GH72
