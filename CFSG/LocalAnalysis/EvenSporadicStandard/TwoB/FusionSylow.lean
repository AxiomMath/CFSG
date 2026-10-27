module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Branch55
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.SylowIntersectionNormalizerGrowth

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.EvenSporadicStandard.TwoFi22
open scoped Pointwise

variable {G : Type} [Group G]

section Sylow

variable [Finite G] {t z : G}

theorem eq_of_le_of_card_two_pow {H S X : Subgroup G} (hSX : S ≤ X) (hXH : X ≤ H)
    (hX : IsPGroup 2 X) (hS : Nat.card S = 2 ^ (Nat.card H).factorization 2) : X = S := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hX
  have hdvd : 2 ^ n ∣ Nat.card H := hn ▸ Subgroup.card_dvd_of_le hXH
  have hle : n ≤ (Nat.card H).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hdvd
  have hcard : Nat.card X ≤ Nat.card S := by
    rw [hn, hS]
    exact Nat.pow_le_pow_right (by norm_num) hle
  exact (Subgroup.eq_of_le_of_card_ge hSX hcard).symm

theorem exists_isPGroup_card_le (H : Subgroup G) :
    ∃ S : Subgroup G, S ≤ H ∧ O2In H ≤ S ∧ IsPGroup 2 S ∧
      Nat.card S = 2 ^ (Nat.card H).factorization 2 := by
  obtain ⟨S0⟩ := (inferInstance : Nonempty (Sylow 2 ↥H))
  refine ⟨(S0 : Subgroup ↥H).map H.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · exact Subgroup.map_mono (CFSG.pCore_isPGroup.le_sylow_of_normal S0)
  · exact S0.isPGroup'.map _
  · rw [Subgroup.card_map_of_injective H.subtype_injective, S0.card_eq_multiplicity]

theorem Level55.mem_pair_iff_of_le (d : Level55 G t z) (h54 : IsTwoConstrained (centZ z))
    (hle : centZ z ≤ centralizer ({t} : Set G)) {S : Subgroup G} (hSK : S ≤ centZ z)
    (hQS : O2In (centZ z) ≤ S) :
    ∀ x : G, x ∈ pair z t ↔ x ∈ S ∧ ∀ s ∈ S, s * x = x * s := by
  have hK : centPair z t = centZ z := by
    rw [centPair_eq_inf]; exact inf_of_le_left hle
  intro x
  constructor
  · intro hx
    have hxQ : x ∈ O2In (centZ z) := hK ▸ d.pair_le_O2K hx
    refine ⟨hQS hxQ, fun s hs => ?_⟩
    have hs' : s ∈ centPair z t := hK ▸ hSK hs
    exact mem_centralizer_iff.1 hs' x hx |>.symm
  · rintro ⟨hxS, hxc⟩
    have hxQ : x ∈ O2In (centZ z) :=
      h54 ⟨hSK hxS, mem_centralizer_iff.2 fun r hr => hxc r (hQS hr)⟩
    refine d.mem_pair_of_central (hK ▸ hxQ) fun r hr => ?_
    exact (hxc r (hQS (hK ▸ hr))).symm

theorem not_conj_of_lt (hle : centZ z ≤ centralizer ({t} : Set G))
    (hne : ¬ centralizer ({t} : Set G) ≤ centZ z) (y : G) :
    y * t * y⁻¹ ≠ z ∧ y * z * y⁻¹ ≠ t := by
  have hlt : Nat.card (centralizer ({z} : Set G)) < Nat.card (centralizer ({t} : Set G)) :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hle fun h => hne h.ge)
  constructor
  · intro h
    have e : Nat.card (centralizer ({t} : Set G)) =
        Nat.card (centralizer ({(MulAut.conj y) t} : Set G)) :=
      Nat.card_congr (centralizerEquiv (MulAut.conj y) t).toEquiv
    rw [MulAut.conj_apply, h] at e
    omega
  · intro h
    have e : Nat.card (centralizer ({z} : Set G)) =
        Nat.card (centralizer ({(MulAut.conj y) z} : Set G)) :=
      Nat.card_congr (centralizerEquiv (MulAut.conj y) z).toEquiv
    rw [MulAut.conj_apply, h] at e
    omega

theorem conj_mem_pair_of_mem_normalizer {S : Subgroup G}
    (hZ : ∀ x : G, x ∈ pair z t ↔ x ∈ S ∧ ∀ s ∈ S, s * x = x * s)
    {y : G} (hy : y ∈ normalizer (S : Set G)) {x : G} (hx : x ∈ pair z t) :
    y * x * y⁻¹ ∈ pair z t := by
  obtain ⟨hxS, hxc⟩ := (hZ x).1 hx
  refine (hZ _).2 ⟨(mem_normalizer_iff.1 hy x).1 hxS, fun s hs => ?_⟩
  have hs' : y⁻¹ * s * y ∈ S := by
    refine (mem_normalizer_iff.1 hy (y⁻¹ * s * y)).2 ?_
    have e : y * (y⁻¹ * s * y) * y⁻¹ = s := by group
    rw [e]
    exact hs
  have h := hxc _ hs'
  calc s * (y * x * y⁻¹) = y * ((y⁻¹ * s * y) * x) * y⁻¹ := by group
    _ = y * (x * (y⁻¹ * s * y)) * y⁻¹ := by rw [h]
    _ = y * x * y⁻¹ * s := by group

theorem Level55.conj_eq_of_mem_normalizer (d : Level55 G t z)
    (hle : centZ z ≤ centralizer ({t} : Set G))
    (hne : ¬ centralizer ({t} : Set G) ≤ centZ z) {S : Subgroup G}
    (hZ : ∀ x : G, x ∈ pair z t ↔ x ∈ S ∧ ∀ s ∈ S, s * x = x * s)
    {y : G} (hy : y ∈ normalizer (S : Set G)) : y * t * y⁻¹ = t := by
  have hz1 : z ≠ 1 := by
    intro h
    have := d.z_ord
    rw [h, orderOf_one] at this
    omega
  have ht1 : t ≠ 1 := by
    intro h
    have := d.t_ord
    rw [h, orderOf_one] at this
    omega
  obtain ⟨hn1, hn2⟩ := not_conj_of_lt hle hne y
  have hty : y * t * y⁻¹ ∈ pair z t :=
    conj_mem_pair_of_mem_normalizer hZ hy (t_mem_pair z t)
  rcases mem_pair_cases d.z_ord d.t_ord d.zt_comm hty with h | h | h | h
  · exact absurd (by simpa using h) ht1
  · exact absurd h hn1
  · exact h
  · exfalso
    have hzy : y * z * y⁻¹ ∈ pair z t :=
      conj_mem_pair_of_mem_normalizer hZ hy (z_mem_pair z t)
    rcases mem_pair_cases d.z_ord d.t_ord d.zt_comm hzy with h' | h' | h' | h'
    · exact hz1 (by simpa using h')
    · have hyz : y ∈ centZ z := mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 h')
      have hyt : y * t * y⁻¹ = t :=
        mul_inv_eq_iff_eq_mul.2 (mem_centralizer_singleton_iff.1 (hle hyz))
      exact hz1 (mul_eq_right.1 (h.symm.trans hyt))
    · exact hn2 h'
    · exact d.z_ne_t (by simpa using h'.trans h.symm)

theorem exists_sylow_centZ (d : Level55 G t z) (h54 : IsTwoConstrained (centZ z))
    (hle : centZ z ≤ centralizer ({t} : Set G))
    (hL2 : (Nat.card (centralizer ({t} : Set G))).factorization 2 =
      (Nat.card (centZ z)).factorization 2)
    (hne : ¬ centralizer ({t} : Set G) ≤ centZ z) :
    ∃ T : Sylow 2 G, (T : Subgroup G) ≤ centZ z ∧
      (∀ x : G, x ∈ pair z t ↔ x ∈ (T : Subgroup G) ∧ ∀ s ∈ (T : Subgroup G), s * x = x * s) ∧
      (∀ g : G, g⁻¹ * t * g ∈ pair z t → g⁻¹ * t * g = t) := by
  obtain ⟨S, hSK, hQS, hS2, hScard⟩ := exists_isPGroup_card_le (centZ z)
  have hZS := d.mem_pair_iff_of_le h54 hle hSK hQS
  obtain ⟨T, hST⟩ := hS2.exists_le_sylow
  have hTS : (T : Subgroup G) ≤ S := by
    by_contra hTS
    refine GorensteinWalter.sylow_intersection_not_le_of_inner_normalizer_le T S S hTS ?_
      inf_le_right
    rintro y ⟨hyT, hyN⟩
    rw [inf_eq_right.2 hST] at hyN
    have hyt : y * t * y⁻¹ = t := d.conj_eq_of_mem_normalizer hle hne hZS hyN
    have hyL : y ∈ centralizer ({t} : Set G) :=
      mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 hyt)
    have hX : IsPGroup 2 ↥(S ⊔ zpowers y) :=
      T.isPGroup'.to_le (sup_le hST (zpowers_le.2 hyT))
    have hXL : S ⊔ zpowers y ≤ centralizer ({t} : Set G) :=
      sup_le (hSK.trans hle) (zpowers_le.2 hyL)
    have hSL : Nat.card S = 2 ^ (Nat.card (centralizer ({t} : Set G))).factorization 2 := by
      rw [hL2]; exact hScard
    have hXS := eq_of_le_of_card_two_pow le_sup_left hXL hX hSL
    have hy : y ∈ S ⊔ zpowers y := mem_sup_right (mem_zpowers y)
    rwa [hXS] at hy
  have hTeq : (T : Subgroup G) = S := le_antisymm hTS hST
  have hZT : ∀ x : G, x ∈ pair z t ↔
      x ∈ (T : Subgroup G) ∧ ∀ s ∈ (T : Subgroup G), s * x = x * s := by
    rw [hTeq]; exact hZS
  refine ⟨T, hTeq ▸ hSK, hZT, fun g hg => ?_⟩
  have h1 : t ∈ centralizer ((T : Subgroup G) : Set G) :=
    mem_centralizer_iff.2 ((hZT t).1 (t_mem_pair z t)).2
  have h2 : g⁻¹ * t * g ∈ centralizer ((T : Subgroup G) : Set G) :=
    mem_centralizer_iff.2 ((hZT _).1 hg).2
  obtain ⟨n, hn, hgn⟩ := T.conj_eq_normalizer_conj_of_mem_centralizer t g h1 h2
  have h3 := d.conj_eq_of_mem_normalizer hle hne hZT (inv_mem hn : n⁻¹ ∈ normalizer
    ((T : Subgroup G) : Set G))
  rw [inv_inv] at h3
  exact hgn.trans h3

end Sylow

end CFSG.EvenSporadicStandard.TwoB
