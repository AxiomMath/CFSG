module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuaternionReduction
public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCover
public import CFSG.Goldschmidt.Steps.GSz8MultBasic
public import CFSG.GH74.KGroups.KI5

public section

namespace CFSG.GH74.Uniqueness.SU.K.R6

open Subgroup CFSG

section Z4Core

variable {L : Type} [Group L]

theorem z4_eq_one_or_eq {a x : L} (ha : a * a = 1) (hx : x ∈ zpowers a) : x = 1 ∨ x = a := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · left
    rw [hm, zpow_mul]
    have : a ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ha
    rw [this, one_zpow]
  · right
    rw [hm, zpow_add, zpow_mul, zpow_one]
    have : a ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ha
    rw [this, one_zpow, one_mul]

theorem z4_exists_sq_eq_one {c b : L} (hc : c ∈ center L) (hb : b * b ∈ zpowers (c ^ 2)) :
    ∃ i : ℤ, (b * c ^ (-i)) * (b * c ^ (-i)) = 1 := by
  obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hb
  refine ⟨i, ?_⟩
  have hcomm : Commute b (c ^ (-i)) := (Commute.zpow_right (Subgroup.mem_center_iff.mp hc b) (-i))
  have h1 : (b * c ^ (-i)) * (b * c ^ (-i)) = (b * b) * (c ^ (-i) * c ^ (-i)) := by
    calc (b * c ^ (-i)) * (b * c ^ (-i)) = b * (c ^ (-i) * b) * c ^ (-i) := by group
      _ = b * (b * c ^ (-i)) * c ^ (-i) := by rw [← hcomm.eq]
      _ = (b * b) * (c ^ (-i) * c ^ (-i)) := by group
  rw [h1, ← hi]
  group

theorem z4_unique_involution {c x : L} (hcn : 2 ∣ orderOf c) (hx : x ∈ zpowers c)
    (hxx : x * x = 1) : x = 1 ∨ x = c ^ (orderOf c / 2) := by
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hx
  obtain ⟨n', hn'⟩ := hcn
  have h2m : c ^ (m + m) = 1 := by rw [zpow_add]; exact hxx
  have hdvd : ((orderOf c : ℕ) : ℤ) ∣ m + m := orderOf_dvd_iff_zpow_eq_one.mpr h2m
  rw [hn'] at hdvd
  obtain ⟨j, hj⟩ := hdvd
  have hm : m = (n' : ℤ) * j := by push_cast at hj; linarith
  have hcn' : c ^ n' * c ^ n' = 1 := by
    rw [← pow_add, ← two_mul, ← hn']
    exact pow_orderOf_eq_one c
  have hmem : c ^ m ∈ zpowers (c ^ n') := by
    rw [hm, zpow_mul, zpow_natCast]
    exact zpow_mem_zpowers _ _
  have := z4_eq_one_or_eq hcn' hmem
  rw [hn', Nat.mul_div_cancel_left _ (by norm_num)]
  exact this

theorem z4_normalizer_sup_center {D : Subgroup L} {x : L} (hx : x ∈ normalizer (D : Set L)) :
    x ∈ normalizer ((D ⊔ center L : Subgroup L) : Set L) := by
  rw [mem_normalizer_iff] at hx ⊢
  intro y
  rw [mem_sup_of_normal_right, mem_sup_of_normal_right]
  constructor
  · rintro ⟨d, hd, z, hz, rfl⟩
    refine ⟨x * d * x⁻¹, (hx d).mp hd, z, hz, ?_⟩
    have hxz : x * z * x⁻¹ = z := by
      rw [mem_center_iff.mp hz x, mul_inv_cancel_right]
    calc x * d * x⁻¹ * z = x * d * x⁻¹ * (x * z * x⁻¹) := by rw [hxz]
      _ = x * (d * z) * x⁻¹ := by group
  · rintro ⟨d', hd', z, hz, h⟩
    refine ⟨x⁻¹ * d' * x, ?_, z, hz, ?_⟩
    · refine (hx (x⁻¹ * d' * x)).mpr ?_
      have : x * (x⁻¹ * d' * x) * x⁻¹ = d' := by group
      rw [this]
      exact hd'
    · have hxz : x⁻¹ * z * x = z := by
        rw [mem_center_iff.mp hz x⁻¹, inv_mul_cancel_right]
      calc x⁻¹ * d' * x * z = x⁻¹ * d' * x * (x⁻¹ * z * x) := by rw [hxz]
        _ = x⁻¹ * (d' * z) * x := by group
        _ = x⁻¹ * (x * y * x⁻¹) * x := by rw [h]
        _ = y := by group

variable [Finite L]

theorem z4_core
    (hQ : CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleProperCoreClassification)
    [hperf : Group.IsPerfect L] (hsimp : IsSimpleGroup (L ⧸ center L))
    {c : L} (hcZ : c ∈ center L) (hgen : ∀ z ∈ center L, z ∈ zpowers c)
    (hZ2 : IsPGroup 2 (center L)) (hZ4 : 4 ≤ Nat.card (center L))
    (hrank : 2 ≤ Open.twoRank L) (Q : Sylow 2 L) (B : Subgroup L)
    (hQB : (Q : Subgroup L) ≤ B) (hB : B ≠ ⊤)
    (hΓ : Open.properTwoGenCoreGamma (Q : Subgroup L) 2 ≤ B) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZeq : center L = zpowers c := le_antisymm (fun z hz => hgen z hz) (zpowers_le.mpr hcZ)
  have hord : orderOf c = Nat.card (center L) := by rw [hZeq, Nat.card_zpowers]
  obtain ⟨k, hk⟩ := hZ2.exists_card_eq
  have hk2 : 2 ≤ k := by
    by_contra h
    push Not at h
    have : Nat.card (center L) ≤ 2 ^ 1 := by
      rw [hk]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hn4 : 4 ∣ orderOf c := by
    rw [hord, hk]
    have h4 := Nat.pow_dvd_pow 2 hk2
    norm_num at h4
    exact h4
  have hnpos : 0 < orderOf c := orderOf_pos c
  have h2n : 2 ∣ orderOf c := dvd_trans (by norm_num) hn4
  set t : L := c ^ (orderOf c / 2) with ht
  have htt : t * t = 1 := by
    rw [ht, ← pow_add, ← two_mul, Nat.mul_div_cancel' h2n]
    exact pow_orderOf_eq_one c
  have htZ : t ∈ center L := pow_mem hcZ _
  have ht1 : t ≠ 1 := by
    intro h
    have h1 : orderOf c ∣ orderOf c / 2 := orderOf_dvd_of_pow_eq_one h
    have h2 := Nat.le_of_dvd (by omega) h1
    omega
  have htZ0 : t ∈ zpowers (c ^ 2) := by
    obtain ⟨m, hm⟩ := hn4
    refine mem_zpowers_iff.mpr ⟨(m : ℤ), ?_⟩
    have : orderOf c / 2 = 2 * m := by omega
    rw [ht, this, zpow_natCast, ← pow_mul]
  set Z₀ : Subgroup L := zpowers (c ^ 2) with hZ₀
  have hZ₀Z : Z₀ ≤ center L := zpowers_le.mpr (pow_mem hcZ 2)
  have : Z₀.Normal := normal_of_le_center hZ₀Z
  set π : L →* L ⧸ Z₀ := QuotientGroup.mk' Z₀ with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Z₀
  have hker : π.ker = Z₀ := QuotientGroup.ker_mk' Z₀
  have hπmem : ∀ x : L, π x = 1 ↔ x ∈ Z₀ := fun x => QuotientGroup.eq_one_iff x
  have hcnot : c ∉ Z₀ := by
    intro h
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp h
    have h1 : c ^ ((2 : ℤ) * j - 1) = 1 := by
      have : c ^ ((2 : ℤ) * j - 1) = (c ^ 2) ^ j * c⁻¹ := by group
      rw [this, hj, mul_inv_cancel]
    have h2 : ((orderOf c : ℕ) : ℤ) ∣ 2 * j - 1 := orderOf_dvd_iff_zpow_eq_one.mpr h1
    have h3 : (2 : ℤ) ∣ ((orderOf c : ℕ) : ℤ) := by exact_mod_cast h2n
    have h4 : (2 : ℤ) ∣ 2 * j - 1 := dvd_trans h3 h2
    omega
  have hπc1 : π c ≠ 1 := fun h => hcnot ((hπmem c).mp h)
  have hcc : c * c ∈ Z₀ := by rw [← sq]; exact mem_zpowers _
  have hπcc : π c * π c = 1 := by rw [← map_mul]; exact (hπmem _).mpr hcc
  have hcenterJ : center (L ⧸ Z₀) = (center L).map π := by
    apply le_antisymm
    · intro y hy
      obtain ⟨x, rfl⟩ := hπs y
      refine ⟨x, ?_, rfl⟩
      have hx : QuotientGroup.mk' (center L) x ∈ center (L ⧸ center L) := by
        rw [mem_center_iff]
        intro g'
        obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (center L) g'
        have h1 : π g * π x = π x * π g := mem_center_iff.mp hy (π g)
        have h2 : π (g * x) = π (x * g) := by rw [map_mul, map_mul]; exact h1
        have h3 : (g * x)⁻¹ * (x * g) ∈ Z₀ := QuotientGroup.eq.mp h2
        rw [← map_mul, ← map_mul]
        exact QuotientGroup.eq.mpr (hZ₀Z h3)
      rw [Group.IsPerfect.center_quotient_center_eq_bot L] at hx
      exact (QuotientGroup.eq_one_iff x).mp (mem_bot.mp hx)
    · rintro _ ⟨z, hz, rfl⟩
      rw [mem_center_iff]
      intro g'
      obtain ⟨g, rfl⟩ := hπs g'
      rw [← map_mul, ← map_mul, mem_center_iff.mp hz g]
  have hcardJ : Nat.card (center (L ⧸ Z₀)) = 2 := by
    rw [hcenterJ]
    let f : ↥(center L) →* L ⧸ Z₀ := π.comp (center L).subtype
    have h1 := Subgroup.card_ker_mul_card_range f
    have hrange : f.range = (center L).map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hker' : f.ker = Z₀.subgroupOf (center L) := by
      ext z
      simp only [f, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
        Subgroup.mem_subgroupOf]
      exact hπmem _
    have hcardker : Nat.card f.ker = Nat.card Z₀ := by
      rw [hker']
      have : (Z₀.subgroupOf (center L)).map (center L).subtype = Z₀ := by
        rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hZ₀Z]
      conv_rhs => rw [← this]
      exact (Subgroup.card_map_of_injective (center L).subtype_injective).symm
    have hZ₀card : Nat.card Z₀ = orderOf c / 2 := by
      rw [hZ₀, Nat.card_zpowers, orderOf_pow_of_dvd (by norm_num) h2n]
    rw [hrange, hcardker, hZ₀card, ← hord] at h1
    have hpos' : 0 < orderOf c / 2 := by omega
    have h5 : orderOf c / 2 * 2 = orderOf c := Nat.div_mul_cancel h2n
    exact Nat.eq_of_mul_eq_mul_left hpos' (by rw [h1]; exact h5.symm)
  let eJ : (L ⧸ Z₀) ⧸ center (L ⧸ Z₀) ≃* L ⧸ center L :=
    (QuotientGroup.quotientMulEquivOfEq hcenterJ).trans
      (QuotientGroup.quotientQuotientEquivQuotient Z₀ (center L) hZ₀Z)
  have hsimpJ : IsSimpleGroup ((L ⧸ Z₀) ⧸ center (L ⧸ Z₀)) :=
    (MulEquiv.isSimpleGroup_congr eJ).mpr hsimp
  have hrankJ : 2 ≤ Open.twoRank (L ⧸ Z₀) := by
    obtain ⟨E, -, hE, hEcard⟩ :=
      SU1.exists_isElemAbelian_of_le_pRank (H := (⊤ : Subgroup L)) Nat.prime_two hrank
    have hex : ∃ e ∈ E, e ∉ zpowers c := by
      by_contra hno
      push Not at hno
      have hEle : E ≤ zpowers t := by
        intro x hx
        have hxx : x * x = 1 := by
          have := (SU1.isElemAbelian_iff.mp hE).2 x hx
          rwa [pow_two] at this
        rcases z4_unique_involution h2n (hno x hx) hxx with h | h
        · rw [h]; exact one_mem _
        · rw [h]; exact mem_zpowers _
      have h1 := Subgroup.card_le_of_le hEle
      rw [hEcard, Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact htt) ht1] at h1
      omega
    obtain ⟨e, heE, hec⟩ := hex
    have hee : e * e = 1 := by
      have := (SU1.isElemAbelian_iff.mp hE).2 e heE
      rwa [pow_two] at this
    have hπe1 : π e ≠ 1 := by
      intro h
      apply hec
      rw [hZeq.symm]
      exact hZ₀Z ((hπmem e).mp h)
    have hπec : π e ≠ π c := by
      intro h
      apply hec
      have h1 : e⁻¹ * c ∈ Z₀ := QuotientGroup.eq.mp h
      have h2 : e⁻¹ * c ∈ zpowers c := hZeq ▸ hZ₀Z h1
      have h3 : e = c * (e⁻¹ * c)⁻¹ := by group
      rw [h3]
      exact mul_mem (mem_zpowers c) (inv_mem h2)
    have hπee : π e * π e = 1 := by rw [← map_mul, hee, map_one]
    obtain ⟨hel, hcard⟩ := SU1.isElemAbelian_card_sup_zpowers Nat.prime_two (a := π e) (y := π c)
      (by rw [pow_two]; exact hπee) (by rw [pow_two]; exact hπcc) hπe1
      (by
        intro h
        rcases z4_eq_one_or_eq hπee h with h1 | h1
        · exact hπc1 h1
        · exact hπec h1.symm)
      (by rw [← map_mul, ← map_mul, mem_center_iff.mp hcZ e])
    exact SU1.le_pRank (by norm_num) le_top hel hcard
  have hZQ : center L ≤ (Q : Subgroup L) := hZ2.le_sylow_of_normal Q
  have hZ₀Q : Z₀ ≤ (Q : Subgroup L) := hZ₀Z.trans hZQ
  let Q' : Sylow 2 (L ⧸ Z₀) := Q.mapSurjective hπs
  have hQ'coe : (Q' : Subgroup (L ⧸ Z₀)) = (Q : Subgroup L).map π := Sylow.coe_mapSurjective hπs Q
  let B' : Subgroup (L ⧸ Z₀) := B.map π
  have hQ'B' : (Q' : Subgroup (L ⧸ Z₀)) ≤ B' := by
    rw [hQ'coe]
    exact map_mono hQB
  have hB'top : B' ≠ ⊤ := by
    intro h
    apply hB
    have h1 : B'.comap π = ⊤ := by rw [h]; exact comap_top π
    rw [show B'.comap π = B ⊔ π.ker from comap_map_eq π B, hker,
      sup_eq_left.mpr (hZ₀Q.trans hQB)] at h1
    exact h1
  have hΓ' : Open.properTwoGenCoreGamma (Q' : Subgroup (L ⧸ Z₀)) 2 ≤ B' := by
    rw [CFSG.ProperTwoGeneratedCore.gamma_le_iff]
    intro Db hDbQ hDbrank
    set D : Subgroup L := Db.comap π with hD
    have hDQ : D ≤ (Q : Subgroup L) := by
      intro x hx
      have h1 : π x ∈ (Q : Subgroup L).map π := by rw [← hQ'coe]; exact hDbQ hx
      have h2 : x ∈ ((Q : Subgroup L).map π).comap π := h1
      rw [comap_map_eq π (Q : Subgroup L), hker, sup_eq_left.mpr hZ₀Q] at h2
      exact h2
    obtain ⟨Ē, hĒle, hĒ, hĒcard⟩ := SU1.exists_isElemAbelian_of_le_pRank Nat.prime_two hDbrank
    have hex : ∃ ē ∈ Ē, ē ∉ zpowers (π c) := by
      by_contra hno
      push Not at hno
      have h1 := Subgroup.card_le_of_le (show Ē ≤ zpowers (π c) from fun x hx => hno x hx)
      rw [hĒcard, Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hπcc) hπc1] at h1
      omega
    obtain ⟨ē, hēĒ, hēc⟩ := hex
    obtain ⟨b, hb⟩ := hπs ē
    have hbD : b ∈ D := by
      rw [hD, mem_comap, hb]
      exact hĒle hēĒ
    have hēē : ē * ē = 1 := by
      have := (SU1.isElemAbelian_iff.mp hĒ).2 ē hēĒ
      rwa [pow_two] at this
    have hbb : b * b ∈ Z₀ := by
      rw [← hπmem, map_mul, hb]
      exact hēē
    obtain ⟨i, hi⟩ := z4_exists_sq_eq_one hcZ hbb
    set b' : L := b * c ^ (-i) with hb'
    have hb'Z₀ : b' ∉ Z₀ := by
      intro h
      apply hēc
      have h1 : π b' = 1 := (hπmem b').mpr h
      have h2 : b = b' * c ^ i := by rw [hb']; group
      have h3 : ē = (π c) ^ i := by rw [← hb, h2, map_mul, h1, one_mul, map_zpow]
      rw [h3]
      exact zpow_mem_zpowers _ _
    have hb'1 : b' ≠ 1 := fun h => hb'Z₀ (h ▸ one_mem _)
    have hnot : t ∉ zpowers b' := by
      intro h
      rcases z4_eq_one_or_eq hi h with h1 | h1
      · exact ht1 h1
      · exact hb'Z₀ (h1 ▸ htZ0)
    obtain ⟨hel, hcard⟩ := SU1.isElemAbelian_card_sup_zpowers Nat.prime_two (a := b') (y := t)
      (by rw [pow_two]; exact hi) (by rw [pow_two]; exact htt) hb'1 hnot
      (mem_center_iff.mp htZ b')
    have hb'DZ : b' ∈ D ⊔ center L :=
      mul_mem (mem_sup_left hbD) (mem_sup_right (zpow_mem hcZ _))
    have htDZ : t ∈ D ⊔ center L := mem_sup_right htZ
    have hrk2 : 2 ≤ Open.pRank 2 (D ⊔ center L) :=
      SU1.le_pRank (by norm_num) (sup_le (zpowers_le.mpr hb'DZ) (zpowers_le.mpr htDZ)) hel hcard
    have hDZQ : D ⊔ center L ≤ (Q : Subgroup L) := sup_le hDQ hZQ
    have hN : normalizer ((D ⊔ center L : Subgroup L) : Set L) ≤ B :=
      (CFSG.ProperTwoGeneratedCore.gamma_le_iff _ _ 2).mp hΓ _ hDZQ hrk2
    intro xb hxb
    obtain ⟨x, rfl⟩ := hπs xb
    have hxD : x ∈ normalizer (D : Set L) := by
      rw [mem_normalizer_iff]
      intro h
      have := mem_normalizer_iff.mp hxb (π h)
      simpa [hD, mem_comap, map_mul, map_inv] using this
    exact mem_map_of_mem π (hN (z4_normalizer_sup_center hxD))
  have hJ := hQ (L ⧸ Z₀) inferInstance hsimpJ hcardJ hrankJ Q' B' hQ'B' hB'top hΓ'
  rcases hJ with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  ·
    let e' : L ⧸ center L ≃* alternatingGroup (Fin 9) := eJ.symm.trans e
    let η : L →* alternatingGroup (Fin 9) := e'.toMonoidHom.comp (QuotientGroup.mk' (center L))
    have hη : Function.Surjective η := e'.surjective.comp (QuotientGroup.mk'_surjective _)
    have hηker : η.ker = center L := by
      ext x
      rw [MonoidHom.mem_ker]
      constructor
      · intro hx
        have h1 : e' ((QuotientGroup.mk' (center L)) x) = 1 := hx
        exact (QuotientGroup.eq_one_iff x).mp ((map_eq_one_iff e' e'.injective).mp h1)
      · intro hx
        have h1 : (QuotientGroup.mk' (center L)) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
        show e' ((QuotientGroup.mk' (center L)) x) = 1
        rw [h1, map_one]
    have := CFSG.LocalAnalysis.ComponentInitial.alternating_perfect_central_two_kernel_order_at_most_two
      (n := 9) (by norm_num) η hη hηker.le (by rw [hηker]; exact hZ2)
    rw [hηker] at this
    omega
  ·
    obtain ⟨eO⟩ := CFSG.GH74.KGroups.KI5.equiv_open_of_szModel ⟨eJ.symm.trans e⟩
    have hquasi : CFSG.Open.IsQuasisimple L := ⟨hperf.commutator_eq_top, hsimp⟩
    have hel := CFSG.Goldschmidt.GSz8Mult.isElemAbelian_center hquasi eO
    have hle : center L ≤ zpowers t := by
      intro x hx
      have hxx : x * x = 1 := by
        have := (SU1.isElemAbelian_iff.mp hel).2 x hx
        rwa [pow_two] at this
      rcases z4_unique_involution h2n (hZeq ▸ hx) hxx with h | h
      · rw [h]; exact one_mem _
      · rw [h]; exact mem_zpowers _
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact htt) ht1] at h1
    omega

end Z4Core

end CFSG.GH74.Uniqueness.SU.K.R6
