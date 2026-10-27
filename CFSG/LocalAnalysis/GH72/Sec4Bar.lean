module

public import CFSG.LocalAnalysis.GH72.Sec4Basic

public section

namespace CFSG.GH72

open Subgroup CFSG.ABGLocalTools
open CFSG.CGT.Foote81L6.TStruct (isElemAbelian_two_iff)

section Odd

variable {G : Type*} [Group G]

theorem eq_one_of_mem_of_isPGroup_of_odd {P N : Subgroup G} (hP : IsPGroup 2 P)
    (hN : Odd (Nat.card N)) {x : G} (hxP : x ∈ P) (hxN : x ∈ N) : x = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP ⟨x, hxP⟩
  have h1 : orderOf x ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h2 : orderOf x ∣ Nat.card N := by
    have h := orderOf_dvd_natCard (⟨x, hxN⟩ : N)
    rwa [Subgroup.orderOf_mk] at h
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  rcases j with _ | j
  · rw [pow_zero] at hj
    exact orderOf_eq_one_iff.1 hj
  · exfalso
    rw [hj] at h2
    exact (Nat.not_even_iff_odd.2 hN)
      (even_iff_two_dvd.2 ((dvd_pow_self 2 j.succ_ne_zero).trans h2))

theorem exists_conj_of_inv_mul_mem {O : Subgroup G} (hO : Odd (Nat.card O)) {u v : G}
    (hu : u * u = 1) (hv : v * v = 1) (huv : u⁻¹ * v ∈ O) : ∃ w ∈ O, w⁻¹ * u * w = v := by
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have hn : Odd (orderOf (u⁻¹ * v)) := by
    have h := orderOf_dvd_natCard (⟨u⁻¹ * v, huv⟩ : O)
    rw [Subgroup.orderOf_mk] at h
    exact Odd.of_dvd_nat hO h
  obtain ⟨m, hm⟩ := hn
  set o := u⁻¹ * v with ho
  set w := o ^ (m + 1) with hw
  refine ⟨w, pow_mem huv _, ?_⟩
  have hw2 : w * w = o := by
    rw [hw, ← pow_add, show m + 1 + (m + 1) = orderOf o + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have hinv : u * o * u⁻¹ = o⁻¹ := by
    rw [ho, show u * (u⁻¹ * v) * u⁻¹ = v * u⁻¹ by group, mul_inv_rev, inv_inv, huinv, hvinv]
  have huw : u * w * u⁻¹ = w⁻¹ := by
    rw [hw, ← MulAut.conj_apply, map_pow, MulAut.conj_apply, hinv, inv_pow]
  calc w⁻¹ * u * w = w⁻¹ * (u * w * u⁻¹) * u := by group
    _ = w⁻¹ * w⁻¹ * u := by rw [huw]
    _ = (w * w)⁻¹ * u := by group
    _ = o⁻¹ * u := by rw [hw2]
    _ = v := by rw [ho, mul_inv_rev, inv_inv, hvinv, mul_assoc, hu, mul_one]

end Odd

section Bar

variable {G : Type*} [Group G] [Finite G] {H : Subgroup G}

theorem eq_one_of_mem_O_of_isPGroup {P : Subgroup G} (hP : IsPGroup 2 P) {x : G} (hxP : x ∈ P)
    (hxO : x ∈ O H) : x = 1 :=
  eq_one_of_mem_of_isPGroup_of_odd hP (card_O_odd H) hxP hxO

theorem mk_inj_of_isPGroup {P : Subgroup G} (hP : IsPGroup 2 P) {x y : H} (hx : (x : G) ∈ P)
    (hy : (y : G) ∈ P) (h : (QuotientGroup.mk x : Bar H) = QuotientGroup.mk y) : x = y := by
  rw [QuotientGroup.eq] at h
  have h1 : ((x⁻¹ * y : H) : G) = 1 :=
    eq_one_of_mem_O_of_isPGroup hP (mul_mem (inv_mem hx) hy) ⟨_, h, rfl⟩
  exact inv_mul_eq_one.1 (Subtype.ext h1)

theorem mem_of_mk_mem_bar {P Q : Subgroup G} (hPQ : P ≤ Q) (hQ : IsPGroup 2 Q) {x : G}
    (hxH : x ∈ H) (hxQ : x ∈ Q) (h : (QuotientGroup.mk ⟨x, hxH⟩ : Bar H) ∈ bar H P) : x ∈ P := by
  obtain ⟨⟨p, hpH⟩, hp, hpx⟩ := h
  have hpP : p ∈ P := hp
  have e := mk_inj_of_isPGroup (H := H) hQ (x := ⟨p, hpH⟩) (y := ⟨x, hxH⟩) (hPQ hpP) hxQ hpx
  have e' : p = x := congrArg Subtype.val e
  rwa [← e']

theorem mk_mem_bar {P : Subgroup G} {x : G} (hxH : x ∈ H) (hxP : x ∈ P) :
    (QuotientGroup.mk ⟨x, hxH⟩ : Bar H) ∈ bar H P :=
  ⟨⟨x, hxH⟩, hxP, rfl⟩

theorem nonempty_mulEquiv_bar {P : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup 2 P) :
    Nonempty (P ≃* bar H P) := by
  let φ : P →* Bar H := (QuotientGroup.mk' (CFSG.oddCore H)).comp (inclusion hPH)
  have hφ : Function.Injective φ := fun a b hab =>
    inclusion_injective hPH (mk_inj_of_isPGroup hP a.2 b.2 hab)
  have hrange : φ.range = bar H P := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  exact ⟨(MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr hrange)⟩

theorem card_bar {P : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup 2 P) :
    Nat.card (bar H P) = Nat.card P := by
  obtain ⟨e⟩ := nonempty_mulEquiv_bar hPH hP
  exact (Nat.card_congr e.toEquiv).symm

theorem isPGroup_bar {P : Subgroup G} (hP : IsPGroup 2 P) : IsPGroup 2 (bar H P) := by
  have h : IsPGroup 2 (P.subgroupOf H) := hP.comap_subtype
  exact h.map _

theorem bar_sup {P Q : Subgroup G} (hPH : P ≤ H) (hQH : Q ≤ H) :
    bar H (P ⊔ Q) = bar H P ⊔ bar H Q := by
  rw [bar, bar, bar, subgroupOf_sup hPH hQH, Subgroup.map_sup]

theorem bar_mono {P Q : Subgroup G} (h : P ≤ Q) : bar H P ≤ bar H Q :=
  map_mono fun _ hx => h hx

theorem bar_bot : bar H (⊥ : Subgroup G) = ⊥ := by
  rw [bar, bot_subgroupOf, Subgroup.map_bot]

theorem bar_inf_of_isPGroup {P Q R : Subgroup G} (hPR : P ≤ R) (hQR : Q ≤ R) (hR : IsPGroup 2 R)
    (hRH : R ≤ H) : bar H (P ⊓ Q) = bar H P ⊓ bar H Q := by
  refine le_antisymm (le_inf (bar_mono inf_le_left) (bar_mono inf_le_right)) ?_
  rintro _ ⟨⟨⟨p, hpH⟩, hp, rfl⟩, hq⟩
  have hpP : p ∈ P := hp
  exact mk_mem_bar hpH ⟨hpP, mem_of_mk_mem_bar hQR hR hpH (hPR hpP) hq⟩

theorem bar_le_centralizer {P Q : Subgroup G} (h : Q ≤ centralizer (P : Set G)) :
    bar H Q ≤ centralizer (bar H P : Set (Bar H)) := by
  rintro _ ⟨⟨q, hqH⟩, hq, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨⟨p, hpH⟩, hp, rfl⟩
  have hpq : p * q = q * p := mem_centralizer_iff.1 (h hq) p hp
  show (QuotientGroup.mk' (CFSG.oddCore H) ⟨p, hpH⟩) * QuotientGroup.mk' _ ⟨q, hqH⟩ =
    QuotientGroup.mk' _ ⟨q, hqH⟩ * QuotientGroup.mk' (CFSG.oddCore H) ⟨p, hpH⟩
  rw [← map_mul, ← map_mul]
  exact congrArg _ (Subtype.ext hpq)

theorem IsDih.bar {P : Subgroup G} (hP : IsDih P) (hPH : P ≤ H) : IsDih (bar H P) := by
  obtain ⟨a, ha, ⟨e⟩⟩ := hP
  obtain ⟨f⟩ := nonempty_mulEquiv_bar hPH (IsDih.isPGroup ⟨a, ha, ⟨e⟩⟩)
  exact ⟨a, ha, ⟨f.symm.trans e⟩⟩

theorem IsDihNonab.bar {P : Subgroup G} (hP : IsDihNonab P) (hPH : P ≤ H) :
    IsDihNonab (bar H P) := by
  obtain ⟨a, ha, ⟨e⟩⟩ := hP
  obtain ⟨f⟩ := nonempty_mulEquiv_bar hPH (IsDih.isPGroup (isDih_of_isDihNonab ⟨a, ha, ⟨e⟩⟩))
  exact ⟨a, ha, ⟨f.symm.trans e⟩⟩

theorem IsE16.bar {E : Subgroup G} (hE : IsE16 E) (hEH : E ≤ H) : IsE16 (bar H E) := by
  have hE2 := isElemAbelian_two_iff.1 hE.1
  have hEp : IsPGroup 2 E := IsPGroup.of_card (n := 4) (by rw [hE.2]; norm_num)
  refine ⟨isElemAbelian_two_iff.2 ?_, by rw [card_bar hEH hEp, hE.2]⟩
  rintro _ ⟨⟨e, heH⟩, he, rfl⟩
  have he' : e ∈ E := he
  rw [← map_mul]
  exact (QuotientGroup.eq_one_iff _).2 (by
    have : (⟨e, heH⟩ : H) * ⟨e, heH⟩ = 1 := Subtype.ext (hE2 e he')
    rw [this]
    exact one_mem _)

theorem isSylowOf_bar {T K : Subgroup G} (hKH : K ≤ H) (hT : IsSylowOf 2 T K) :
    IsSylowOf 2 (bar H T) (bar H K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' : IsSylowOf 2 (T.subgroupOf H) (K.subgroupOf H) := by
    rw [← isSylowOf_map_subtype_iff H, map_subgroupOf_eq_of_le (hT.le.trans hKH),
      map_subgroupOf_eq_of_le hKH]
    exact hT
  exact isSylowOf_map_hom hT' _

theorem bar_self : bar H H = ⊤ := by
  rw [bar, subgroupOf_self, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

theorem exists_conj_of_mk_isConj {P : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup 2 P) {x y : G}
    (hx : x ∈ P) (hy : y ∈ P) (hx2 : x * x = 1)
    (hc : IsConj (QuotientGroup.mk ⟨x, hPH hx⟩ : Bar H) (QuotientGroup.mk ⟨y, hPH hy⟩)) :
    ∃ g ∈ H, g * x * g⁻¹ = y := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hc
  obtain ⟨⟨c, hcH⟩, rfl⟩ := QuotientGroup.mk_surjective c
  have hmk : (QuotientGroup.mk (⟨c, hcH⟩ * ⟨x, hPH hx⟩ * (⟨c, hcH⟩ : H)⁻¹) : Bar H) =
      QuotientGroup.mk ⟨y, hPH hy⟩ := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hc
  rw [QuotientGroup.eq] at hmk
  have hO : (c * x * c⁻¹)⁻¹ * y ∈ O H := ⟨_, hmk, rfl⟩
  have hy2 : y * y = 1 := by
    have h1 : (QuotientGroup.mk (⟨y, hPH hy⟩ * ⟨y, hPH hy⟩ : H) : Bar H) = 1 := by
      have hxx : (⟨x, hPH hx⟩ : H) * ⟨x, hPH hx⟩ = 1 := Subtype.ext hx2
      rw [QuotientGroup.mk_mul, ← hc]
      calc _ = (QuotientGroup.mk ⟨c, hcH⟩ : Bar H) *
            (QuotientGroup.mk ((⟨x, hPH hx⟩ : H) * ⟨x, hPH hx⟩)) *
            (QuotientGroup.mk ⟨c, hcH⟩ : Bar H)⁻¹ := by
            rw [QuotientGroup.mk_mul]
            group
        _ = 1 := by rw [hxx, QuotientGroup.mk_one, mul_one, mul_inv_cancel]
    exact eq_one_of_mem_O_of_isPGroup hP (mul_mem hy hy)
      ⟨_, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩
  have hu2 : c * x * c⁻¹ * (c * x * c⁻¹) = 1 := by
    calc c * x * c⁻¹ * (c * x * c⁻¹) = c * (x * x) * c⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  obtain ⟨w, hwO, hw⟩ := exists_conj_of_inv_mul_mem (card_O_odd H) hu2 hy2 hO
  refine ⟨w⁻¹ * c, mul_mem (inv_mem (map_subtype_le _ hwO)) hcH, ?_⟩
  rw [← hw]
  group

end Bar

namespace Sec4Setting

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G)

theorem separate_of_mk_isConj {H P : Subgroup G} (hPH : P ≤ H) (hPS : P ≤ 𝔖.S) {x y : G}
    (hx : x ∈ P) (hy : y ∈ P) (hx2 : orderOf x = 2)
    (hc : IsConj (QuotientGroup.mk ⟨x, hPH hx⟩ : Bar H) (QuotientGroup.mk ⟨y, hPH hy⟩)) :
    (x ∈ 𝔖.S₁ ↔ y ∈ 𝔖.S₁) ∧ (x ∈ 𝔖.S₂ ↔ y ∈ 𝔖.S₂) := by
  have hP : IsPGroup 2 P := 𝔖.S.isPGroup'.to_le hPS
  have hxx : x * x = 1 := by
    have h := pow_orderOf_eq_one x
    rwa [hx2, pow_two] at h
  obtain ⟨g, -, hg⟩ := exists_conj_of_mk_isConj hPH hP hx hy hxx hc
  have hxS : x ∈ 𝔖.S₁ ⊔ 𝔖.S₂ := by
    rw [𝔖.decomp.sup_eq]
    exact hPS hx
  have hyS : y ∈ 𝔖.S₁ ⊔ 𝔖.S₂ := by
    rw [𝔖.decomp.sup_eq]
    exact hPS hy
  exact 𝔖.fusion.separate x hxS y hyS hx2 (isConj_iff.2 ⟨g, hg⟩)

end Sec4Setting

end CFSG.GH72
