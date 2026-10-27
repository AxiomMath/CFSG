module

public import CFSG.LocalAnalysis.GH72.Sec4Util
import CFSG.Quasithin.Vol2.Ch10SecQ34LA
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.LocalAnalysis.GH72.Sec4Conj

public section

namespace CFSG.GH72

open Subgroup
open scoped commutatorElement

namespace G4b

section OddCoreFree

variable {X : Type*} [Group X] [Finite X]

theorem eq_bot_of_odd_of_le_normal (hO : CFSG.oddCore X = ⊥) {H R : Subgroup X} (hHn : H.Normal)
    (hRH : R ≤ H) (hHR : H ≤ normalizer (R : Set X)) (hR : Odd (Nat.card R)) : R = ⊥ := by
  have h1 : R ≤ O H := le_O_of_odd hRH hHR hR
  have hOn : (O H).Normal := by
    constructor
    intro n hn g
    have hmap : (O H).map (MulAut.conj g).toMonoidHom = O H := by
      rw [map_O]
      congr 1
      exact mem_normalizer_iff_map_conj_eq'.1 (by rw [normalizer_eq_top_iff.2 hHn]; exact mem_top g)
    rw [← hmap]
    exact ⟨n, hn, rfl⟩
  have h2 : O H ≤ CFSG.oddCore X := le_sSup ⟨hOn, card_O_odd H⟩
  rw [hO] at h2
  exact eq_bot_iff.2 (h1.trans h2)

end OddCoreFree

section Basic

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_mem_of_mem {A B : Subgroup G} (hA : IsPGroup 2 A) (hB : Odd (Nat.card B))
    {x : G} (hxA : x ∈ A) (hxB : x ∈ B) : x = 1 := by
  obtain ⟨k, hk⟩ := hA ⟨x, hxA⟩
  have h1 : orderOf x ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h2 : orderOf x ∣ Nat.card B := Subgroup.orderOf_dvd_natCard B hxB
  have hcop : Nat.Coprime (2 ^ k) (Nat.card B) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hB)
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

omit [Finite G] in
theorem eq_one_of_pow_odd {A : Subgroup G} (hA : IsPGroup 2 A) {x : G} (hx : x ∈ A) {m : ℕ}
    (hm : Odd m) (hxm : x ^ m = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hA ⟨x, hx⟩
  have h1 : orderOf x ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h2 : orderOf x ∣ m := orderOf_dvd_of_pow_eq_one hxm
  have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hm)
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

omit [Finite G] in
theorem odd_card_of_le {A B : Subgroup G} (hAB : A ≤ B) (hB : Odd (Nat.card B)) :
    Odd (Nat.card A) :=
  Odd.of_dvd_nat hB (card_dvd_of_le hAB)

theorem O2_eq_self_of_isSylowOf {H T : Subgroup G} (hT : ABGLocalTools.IsSylowOf 2 T H)
    (hTH : T ≤ ⁅H, H⁆) : O2 H = H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := O2 H with hN
  have hNH : N ≤ H := twoResidualOf_le_self H
  have hNn : (N.subgroupOf H).Normal := twoResidualOf_subgroupOf_normal H
  have h2 : IsPGroup 2 (H ⧸ N.subgroupOf H) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := exists_pow_mem_twoResidualOf x.2
    exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]; exact hk⟩
  have hTN : H ≤ T ⊔ N := by
    have h1 : (T ⊔ N).relIndex H ∣ T.relIndex H := relIndex_dvd_of_le_left H le_sup_left
    have h1' : (T ⊔ N).relIndex H ∣ N.relIndex H := relIndex_dvd_of_le_left H le_sup_right
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h2
    have hNk : N.relIndex H = 2 ^ k := hk
    have hTodd : ¬ 2 ∣ T.relIndex H := (ABGLocalTools.isSylowOf_iff.1 hT).2.2
    have hcop : Nat.Coprime (T.relIndex H) (2 ^ k) :=
      Nat.Coprime.pow_right _ (Nat.coprime_comm.1 (Nat.coprime_two_left.2
        (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hTodd))))
    exact relIndex_eq_one.1 (Nat.eq_one_of_dvd_coprimes hcop h1 (hNk ▸ h1'))
  have hTn : T ≤ normalizer (N : Set G) := hT.le.trans (le_normalizer_twoResidualOf H)
  set f := QuotientGroup.mk' (N.subgroupOf H) with hf
  have hperf : commutator (H ⧸ N.subgroupOf H) = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf H) q
    obtain ⟨t, ht, n, hn, rfl⟩ := mem_sup_of_le_normalizer hTn (hTN hx)
    have htc : (⟨t, hT.le ht⟩ : H) ∈ commutator H := by
      have h3 : t ∈ (commutator H).map H.subtype := by
        rw [map_subtype_commutator]
        exact hTH ht
      obtain ⟨y, hy, hyt⟩ := h3
      rwa [show y = ⟨t, hT.le ht⟩ from Subtype.ext hyt] at hy
    have e : f ⟨t * n, hx⟩ = f ⟨t, hT.le ht⟩ := by
      rw [hf, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, eq_comm, QuotientGroup.eq,
        mem_subgroupOf]
      simpa using hn
    rw [e]
    have h4 : f ⟨t, hT.le ht⟩ ∈ (commutator H).map f := ⟨_, htc, rfl⟩
    rw [commutator_def, map_commutator] at h4
    exact commutator_mono le_top le_top h4
  have hsub : Subsingleton (H ⧸ N.subgroupOf H) := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    have : Group.IsPerfect (H ⧸ N.subgroupOf H) := ⟨hperf⟩
    exact Group.IsPerfect.not_isNilpotent _ h2.isNilpotent
  refine le_antisymm hNH fun x hx => ?_
  have h5 : f ⟨x, hx⟩ = 1 := Subsingleton.elim _ _
  rw [hf, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h5
  exact h5

theorem isSylowOf_of_forall_card_le {Q K : Subgroup G} (hQK : Q ≤ K) (hQ : IsPGroup 2 Q)
    (h : ∀ R ≤ K, IsPGroup 2 R → Nat.card R ≤ Nat.card Q) : ABGLocalTools.IsSylowOf 2 Q K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  have hTQ : (T : Subgroup K).map K.subtype = Q := by
    have hle : Q ≤ (T : Subgroup K).map K.subtype := fun q hq => ⟨⟨q, hQK hq⟩, hT hq, rfl⟩
    refine (eq_of_le_of_card_ge hle ?_).symm
    exact h _ (map_subtype_le _) (T.isPGroup'.map _)
  exact ⟨T, hTQ⟩

theorem le_sup_inf_normalizer {Q K W : Subgroup G} (hQ : ABGLocalTools.IsSylowOf 2 Q K)
    (hKW : K ≤ W) (hWK : W ≤ normalizer (K : Set G)) :
    W ≤ K ⊔ (W ⊓ normalizer (Q : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro w hw
  have hKw : K.map (MulAut.conj w).toMonoidHom = K := mem_normalizer_iff_map_conj_eq'.1 (hWK hw)
  have h1 := isSylowOf_map_hom hQ (MulAut.conj w).toMonoidHom
  rw [hKw] at h1
  obtain ⟨k, hk, hkx⟩ := hQ.exists_mem_conj h1
  have hn : k⁻¹ * w ∈ normalizer (Q : Set G) := by
    rw [mem_normalizer_iff]
    intro q
    have e : k⁻¹ * w * q * (k⁻¹ * w)⁻¹ = k⁻¹ * (w * q * w⁻¹) * k := by group
    rw [e, ← hkx, mem_map_conj]
    have e' : w⁻¹ * (w * q * w⁻¹) * w = q := by group
    rw [e']
  have e : w = k * (k⁻¹ * w) := by group
  rw [e]
  exact mul_mem_sup hk (mem_inf.2 ⟨mul_mem (inv_mem (hKW hk)) hw, hn⟩)

theorem exists_zpow_mul_zpow (x : G) : ∃ a b : ℤ, x ^ a * x ^ b = x ∧
    (∃ k : ℕ, (x ^ a) ^ 2 ^ k = 1) ∧ Odd (orderOf (x ^ b)) := by
  obtain ⟨k, m, hm, hxm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hm)
  have hb := Nat.gcd_eq_gcd_ab (2 ^ k) m
  rw [hcop.gcd_eq_one, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat] at hb
  refine ⟨m * Nat.gcdB (2 ^ k) m, 2 ^ k * Nat.gcdA (2 ^ k) m, ?_, ⟨k, ?_⟩, ?_⟩
  · rw [← zpow_add, add_comm, ← hb, zpow_one]
  · rw [← zpow_natCast, ← zpow_mul]
    refine orderOf_dvd_iff_zpow_eq_one.1 ?_
    rw [hxm]
    exact ⟨Nat.gcdB (2 ^ k) m, by push_cast; ring⟩
  · refine Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one ?_)
    rw [← zpow_natCast, ← zpow_mul]
    refine orderOf_dvd_iff_zpow_eq_one.1 ?_
    rw [hxm]
    exact ⟨Nat.gcdA (2 ^ k) m, by push_cast; ring⟩

end Basic

section BarMaps

variable {G : Type*} [Group G]

theorem bar_mono {H K L : Subgroup G} (hKL : K ≤ L) : bar H K ≤ bar H L :=
  map_mono (comap_mono hKL)

theorem mk_mem_bar {H K : Subgroup G} {x : G} (hxH : x ∈ H) (hxK : x ∈ K) :
    QuotientGroup.mk' (CFSG.oddCore H) ⟨x, hxH⟩ ∈ bar H K :=
  ⟨⟨x, hxH⟩, hxK, rfl⟩

theorem bar_sup {H K L : Subgroup G} (hK : K ≤ H) (hL : L ≤ H) :
    bar H (K ⊔ L) = bar H K ⊔ bar H L := by
  rw [bar, bar, bar, subgroupOf_sup hK hL, Subgroup.map_sup]

theorem bar_commutator {H K L : Subgroup G} (hK : K ≤ H) (hL : L ≤ H) :
    bar H ⁅K, L⁆ = ⁅bar H K, bar H L⁆ := by
  have hKL : ⁅K, L⁆ ≤ H := (commutator_mono hK hL).trans (commutator_le_self H)
  have h : ⁅K, L⁆.subgroupOf H = ⁅K.subgroupOf H, L.subgroupOf H⁆ := by
    apply map_injective H.subtype_injective
    rw [map_commutator, subgroupOf_map_subtype, subgroupOf_map_subtype, subgroupOf_map_subtype,
      inf_eq_left.2 hK, inf_eq_left.2 hL, inf_eq_left.2 hKL]
  rw [bar, bar, bar, h, map_commutator]

theorem bar_O (H : Subgroup G) : bar H (O H) = ⊥ := by
  rw [bar, O, subgroupOf, comap_map_eq_self_of_injective H.subtype_injective,
    QuotientGroup.map_mk'_self]

theorem le_O_of_bar_eq_bot {H K : Subgroup G} (hKH : K ≤ H) (h : bar H K = ⊥) : K ≤ O H := by
  intro x hx
  have h1 := mk_mem_bar (hKH hx) hx
  rw [h, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact ⟨_, h1, rfl⟩

theorem inv_mul_mem_O_of_mk_eq {H : Subgroup G} {a b : H}
    (h : QuotientGroup.mk' (CFSG.oddCore H) a = QuotientGroup.mk' (CFSG.oddCore H) b) :
    (a : G)⁻¹ * b ∈ O H := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h
  exact ⟨_, h, rfl⟩

theorem bar_le_normalizer_bar {H K D : Subgroup G} (hKD : K ≤ normalizer (D : Set G)) :
    bar H K ≤ normalizer (bar H D : Set (Bar H)) := by
  rintro _ ⟨k, hk, rfl⟩
  have hk' : (k : G) ∈ K := hk
  apply mem_normalizer_of_conj_mem
  · rintro _ ⟨d, hd, rfl⟩
    have hd' : (d : G) ∈ D := hd
    refine ⟨k * d * k⁻¹, ?_, by simp⟩
    exact (mem_normalizer_iff.1 (hKD hk') d).1 hd'
  · rintro _ ⟨d, hd, rfl⟩
    have hd' : (d : G) ∈ D := hd
    refine ⟨k⁻¹ * d * k, ?_, by simp⟩
    have := (mem_normalizer_iff.1 (inv_mem (hKD hk')) d).1 hd'
    rw [inv_inv] at this
    exact this

theorem bar_le_centralizer_bar {H K D : Subgroup G} (hKD : K ≤ centralizer (D : Set G)) :
    bar H K ≤ centralizer (bar H D : Set (Bar H)) := by
  rintro _ ⟨k, hk, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨d, hd, rfl⟩
  have h := mem_centralizer_iff.1 (hKD (show (k : G) ∈ K from hk)) d hd
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext h

variable [Finite G]

theorem nonempty_mulEquiv_bar {H K : Subgroup G} (hKH : K ≤ H) (hK : IsPGroup 2 K) :
    Nonempty (K ≃* bar H K) := by
  set g := (QuotientGroup.mk' (CFSG.oddCore H)).comp (K.subgroupOf H).subtype with hg
  have hinj : Function.Injective g := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker, hg, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at ha
    have h1 : ((a : H) : G) ∈ O H := ⟨a, ha, rfl⟩
    have h2 : ((a : H) : G) ∈ K := a.2
    have h3 := eq_one_of_mem_of_mem hK (card_O_odd H) h2 h1
    exact (mem_bot).2 (Subtype.ext (Subtype.ext h3))
  have hrange : g.range = bar H K := by
    rw [hg, MonoidHom.range_comp, range_subtype, bar]
  exact ⟨((subgroupOfEquivOfLe hKH).symm.trans (MonoidHom.ofInjective hinj)).trans
    (MulEquiv.subgroupCongr hrange)⟩

theorem card_bar_of_isPGroup {H K : Subgroup G} (hKH : K ≤ H) (hK : IsPGroup 2 K) :
    Nat.card (bar H K) = Nat.card K := by
  obtain ⟨e⟩ := nonempty_mulEquiv_bar hKH hK
  exact (Nat.card_congr e.toEquiv).symm

omit [Finite G] in
theorem isPGroup_bar {H K : Subgroup G} (hK : IsPGroup 2 K) : IsPGroup 2 (bar H K) :=
  (hK.comap_subtype (K := H)).map _

omit [Finite G] in
theorem odd_card_bar {H K : Subgroup G} (hK : Odd (Nat.card K)) : Odd (Nat.card (bar H K)) := by
  refine Odd.of_dvd_nat ?_ (Subgroup.card_map_dvd _ _)
  have h : Nat.card (K.subgroupOf H) ∣ Nat.card K := by
    rw [← card_map_of_injective H.subtype_injective, subgroupOf_map_subtype]
    exact card_dvd_of_le inf_le_left
  exact Odd.of_dvd_nat hK h

end BarMaps

section Side

variable {G : Type} [Group G] [Finite G] {z : G} {P : Subgroup G} {H₁ : Subgroup (Bar (C z))}

omit [Finite G] in
theorem mem_normalizer_inf {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hA hB ⊢
  intro h
  simp only [mem_inf] at hA hB ⊢
  exact and_congr (hA h) (hB h)

omit [Finite G] in
theorem normal_H₁ (h₂ : bar (C z) P ⊔ H₁ = ⊤)
    (h₃ : H₁ ≤ centralizer (bar (C z) P : Set (Bar (C z)))) : H₁.Normal := by
  rw [← normalizer_eq_top_iff, eq_top_iff, ← h₂]
  exact sup_le ((le_centralizer_iff.1 h₃).trans (centralizer_le_normalizer _)) le_normalizer

omit [Finite G] in
theorem mem_H₁_of_odd (hP : IsPGroup 2 P) (h₁ : bar (C z) P ⊓ H₁ = ⊥)
    (h₂ : bar (C z) P ⊔ H₁ = ⊤) (h₃ : H₁ ≤ centralizer (bar (C z) P : Set (Bar (C z))))
    {y : Bar (C z)} (hy : Odd (orderOf y)) : y ∈ H₁ := by
  have hPH : bar (C z) P ≤ normalizer (H₁ : Set (Bar (C z))) :=
    (le_centralizer_iff.1 h₃).trans (centralizer_le_normalizer _)
  obtain ⟨p, hp, h, hh, rfl⟩ := mem_sup_of_le_normalizer hPH (h₂ ▸ mem_top y)
  have hc : Commute p h := mem_centralizer_iff.1 (h₃ hh) p hp
  have hm : (p * h) ^ orderOf (p * h) = 1 := pow_orderOf_eq_one _
  rw [hc.mul_pow] at hm
  have hpm : p ^ orderOf (p * h) ∈ bar (C z) P ⊓ H₁ := by
    refine mem_inf.2 ⟨pow_mem hp _, ?_⟩
    rw [eq_inv_of_mul_eq_one_left hm]
    exact inv_mem (pow_mem hh _)
  rw [h₁, mem_bot] at hpm
  rw [eq_one_of_pow_odd (isPGroup_bar hP) hp hy hpm, one_mul]
  exact hh

theorem bar_O2_le (hP : IsPGroup 2 P) (h₁ : bar (C z) P ⊓ H₁ = ⊥)
    (h₂ : bar (C z) P ⊔ H₁ = ⊤) (h₃ : H₁ ≤ centralizer (bar (C z) P : Set (Bar (C z)))) :
    bar (C z) (O2 (C z)) ≤ H₁ := by
  rw [bar_twoResidualOf, twoResidualOf_top_eq_closure, closure_le]
  exact fun y hy => mem_H₁_of_odd hP h₁ h₂ h₃ hy

theorem le_bar_centralizer (hP : IsPGroup 2 P) (hPz : P ≤ C z)
    (h₃ : H₁ ≤ centralizer (bar (C z) P : Set (Bar (C z)))) :
    H₁ ≤ bar (C z) (centralizer (P : Set G)) := by
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore (C z)) y
  have hPN : P ≤ normalizer (O (C z) : Set G) := hPz.trans (le_normalizer_O (C z))
  have hx : ∀ t ∈ P, (x : G)⁻¹ * (t * x * t⁻¹) ∈ O (C z) := by
    intro t ht
    have htz : t ∈ C z := hPz ht
    have hcomm := mem_centralizer_iff.1 (h₃ hy) _ (mk_mem_bar htz ht)
    have e : QuotientGroup.mk' (CFSG.oddCore (C z)) x =
        QuotientGroup.mk' (CFSG.oddCore (C z)) (⟨t, htz⟩ * x * (⟨t, htz⟩ : C z)⁻¹) := by
      rw [map_mul, map_mul, hcomm, map_inv, mul_inv_cancel_right]
    simpa using inv_mul_mem_O_of_mk_eq e
  obtain ⟨n, hn, hfix⟩ := exists_mul_mem_centralizer hP (card_O_odd (C z)) hPN hx
  have hnz : n ∈ C z := O_le_self _ hn
  refine ⟨⟨x * n, mul_mem x.2 hnz⟩, ?_, ?_⟩
  · show (x : G) * n ∈ centralizer (P : Set G)
    rw [mem_centralizer_iff]
    intro t ht
    calc t * (x * n) = t * (x * n) * t⁻¹ * t := by group
      _ = x * n * t := by rw [hfix t ht]
  · rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have hn' : (⟨n, hnz⟩ : C z) ∈ CFSG.oddCore (C z) := (mem_oddCore_iff _).2 hn
    have e : (⟨(x : G) * n, mul_mem x.2 hnz⟩ : C z)⁻¹ * x = (⟨n, hnz⟩ : C z)⁻¹ :=
      Subtype.ext (by simp)
    rw [e]
    exact inv_mem hn'

theorem mem_bar_O2_of_odd {D : Subgroup G} (hH : H₁ ≤ bar (C z) D)
    {y : Bar (C z)} (hy : y ∈ H₁) (hodd : Odd (orderOf y)) : y ∈ bar (C z) (O2 D) := by
  obtain ⟨⟨d, hdz⟩, hd, rfl⟩ := hH hy
  have hd' : d ∈ D := hd
  obtain ⟨k, hk, hke⟩ :=
    exists_pow_odd_map_eq (QuotientGroup.mk' (CFSG.oddCore (C z))) ⟨d, hdz⟩ hodd
  refine ⟨⟨d, hdz⟩ ^ k, ?_, hke⟩
  have e : ((⟨d, hdz⟩ ^ k : C z) : G) = d ^ k := by simp
  have hk' : Odd (orderOf (d ^ k)) := by
    rw [← e, Subgroup.orderOf_coe]
    exact hk
  show ((⟨d, hdz⟩ ^ k : C z) : G) ∈ O2 D
  rw [e]
  exact mem_twoResidualOf_of_odd (pow_mem hd' k) hk'

theorem bar_O2_eq (hP : IsPGroup 2 P) (h₁ : bar (C z) P ⊓ H₁ = ⊥)
    (h₂ : bar (C z) P ⊔ H₁ = ⊤) (h₃ : H₁ ≤ centralizer (bar (C z) P : Set (Bar (C z))))
    (hgen : O2 H₁ = H₁) {D : Subgroup G} (hDz : D ≤ C z) (hH : H₁ ≤ bar (C z) D) :
    bar (C z) (O2 D) = H₁ := by
  refine le_antisymm ((bar_mono (twoResidualOf_mono hDz)).trans (bar_O2_le hP h₁ h₂ h₃)) ?_
  rw [← hgen]
  exact twoResidualOf_le_of_forall fun y hy hodd => mem_bar_O2_of_odd hH hy hodd

theorem le_O_C_of_odd (hP : IsPGroup 2 P) (h₁ : bar (C z) P ⊓ H₁ = ⊥)
    (h₂ : bar (C z) P ⊔ H₁ = ⊤) (h₃ : H₁ ≤ centralizer (bar (C z) P : Set (Bar (C z))))
    {D R : Subgroup G} (hH : H₁ ≤ bar (C z) D) (hRz : R ≤ C z) (hR : Odd (Nat.card R))
    (hDR : D ≤ normalizer (R : Set G)) : R ≤ O (C z) := by
  apply le_O_of_bar_eq_bot hRz
  have hRH : bar (C z) R ≤ H₁ := fun y hy => mem_H₁_of_odd hP h₁ h₂ h₃
    (Odd.of_dvd_nat (odd_card_bar hR) (Subgroup.orderOf_dvd_natCard _ hy))
  exact eq_bot_of_odd_of_le_normal (oddCore_quotient_oddCore_eq_bot (C z)) (normal_H₁ h₂ h₃)
    hRH (hH.trans (bar_le_normalizer_bar hDR)) (odd_card_bar hR)

theorem O_eq_inf (hP : IsPGroup 2 P) (h₁ : bar (C z) P ⊓ H₁ = ⊥)
    (h₂ : bar (C z) P ⊔ H₁ = ⊤) (h₃ : H₁ ≤ centralizer (bar (C z) P : Set (Bar (C z))))
    {W : Subgroup G} (hWz : W ≤ C z) (hH : H₁ ≤ bar (C z) W) : O W = W ⊓ O (C z) := by
  apply le_antisymm
  · exact le_inf (O_le_self W) (le_O_C_of_odd hP h₁ h₂ h₃ hH ((O_le_self W).trans hWz)
      (card_O_odd W) (le_normalizer_O W))
  · refine le_O_of_odd inf_le_left (fun w hw => mem_normalizer_inf (le_normalizer hw)
      (le_normalizer_O (C z) (hWz hw))) (odd_card_of_le inf_le_right (card_O_odd (C z)))

theorem O2_eq_sup (hP : IsPGroup 2 P) (h₁ : bar (C z) P ⊓ H₁ = ⊥)
    (h₂ : bar (C z) P ⊔ H₁ = ⊤) (h₃ : H₁ ≤ centralizer (bar (C z) P : Set (Bar (C z))))
    (hgen : O2 H₁ = H₁) {D W : Subgroup G} (hDW : D ≤ W) (hWz : W ≤ C z)
    (hH : H₁ ≤ bar (C z) D) : O2 W = O2 D ⊔ O W := by
  have hHW : H₁ ≤ bar (C z) W := hH.trans (bar_mono hDW)
  apply le_antisymm
  · intro x hx
    have hxW : x ∈ W := twoResidualOf_le_self W hx
    have hxz : x ∈ C z := hWz hxW
    have hmem : QuotientGroup.mk' (CFSG.oddCore (C z)) ⟨x, hxz⟩ ∈ bar (C z) (O2 D) := by
      rw [bar_O2_eq hP h₁ h₂ h₃ hgen (hDW.trans hWz) hH,
        ← bar_O2_eq hP h₁ h₂ h₃ hgen hWz hHW]
      exact mk_mem_bar hxz hx
    obtain ⟨⟨d, hdz⟩, hd, hde⟩ := hmem
    have hd' : d ∈ O2 D := hd
    have ho := inv_mul_mem_O_of_mk_eq hde
    have hoW : d⁻¹ * x ∈ O W := by
      rw [O_eq_inf hP h₁ h₂ h₃ hWz hHW]
      exact mem_inf.2 ⟨mul_mem (inv_mem (hDW (twoResidualOf_le_self D hd'))) hxW, ho⟩
    have e : x = d * (d⁻¹ * x) := by group
    rw [e]
    exact mul_mem_sup hd' hoW
  · exact sup_le (twoResidualOf_mono hDW) (O_le_O2 W)

theorem core_eq (hP : IsPGroup 2 P) (h₁ : bar (C z) P ⊓ H₁ = ⊥)
    (h₂ : bar (C z) P ⊔ H₁ = ⊤) (h₃ : H₁ ≤ centralizer (bar (C z) P : Set (Bar (C z))))
    (hgen : O2 H₁ = H₁) {D W : Subgroup G} (hDW : D ≤ W) (hWz : W ≤ C z)
    (hH : H₁ ≤ bar (C z) D) :
    ⁅O2 W, O2 W⁆ ⊔ O W = ⁅O2 D, O2 D⁆ ⊔ O W := by
  rw [O2_eq_sup hP h₁ h₂ h₃ hgen hDW hWz hH]
  exact commutator_sup_sup_eq ((twoResidualOf_le_self D).trans (hDW.trans (le_normalizer_O W)))

omit [Finite G] in
theorem core_le (W : Subgroup G) : ⁅O2 W, O2 W⁆ ⊔ O W ≤ W :=
  sup_le ((commutator_mono (twoResidualOf_le_self W) (twoResidualOf_le_self W)).trans
    (commutator_le_self W)) (O_le_self W)

omit [Finite G] in
theorem le_normalizer_core (W : Subgroup G) :
    W ≤ normalizer ((⁅O2 W, O2 W⁆ ⊔ O W : Subgroup G) : Set G) := by
  intro w hw
  rw [mem_normalizer_iff_map_conj_eq', Subgroup.map_sup, map_commutator, map_O2, map_O,
    mem_normalizer_iff_map_conj_eq'.1 (le_normalizer hw)]

theorem bar_core (hP : IsPGroup 2 P) (h₁ : bar (C z) P ⊓ H₁ = ⊥)
    (h₂ : bar (C z) P ⊔ H₁ = ⊤) (h₃ : H₁ ≤ centralizer (bar (C z) P : Set (Bar (C z))))
    (hgen : O2 H₁ = H₁) {W : Subgroup G} (hWz : W ≤ C z) (hH : H₁ ≤ bar (C z) W) :
    bar (C z) (⁅O2 W, O2 W⁆ ⊔ O W) = ⁅H₁, H₁⁆ := by
  have hO2W : O2 W ≤ C z := (twoResidualOf_le_self W).trans hWz
  have hOW : O W ≤ C z := (O_le_self W).trans hWz
  have hO : bar (C z) (O W) = ⊥ := by
    rw [O_eq_inf hP h₁ h₂ h₃ hWz hH]
    exact eq_bot_iff.2 ((bar_mono inf_le_right).trans (bar_O (C z)).le)
  rw [bar_sup ((commutator_mono hO2W hO2W).trans (commutator_le_self _)) hOW,
    bar_commutator hO2W hO2W, bar_O2_eq hP h₁ h₂ h₃ hgen hWz hH, hO, sup_bot_eq]

variable {Q : Subgroup G}

theorem card_le_of_le_H₁ (hS : ABGLocalTools.IsSylowOf 2 (P ⊔ Q) (C z))
    (hQP : Q ≤ centralizer (P : Set G)) (hPQ : P ⊓ Q = ⊥) (h₁ : bar (C z) P ⊓ H₁ = ⊥)
    (h₃ : H₁ ≤ centralizer (bar (C z) P : Set (Bar (C z)))) {L : Subgroup (Bar (C z))}
    (hLH : L ≤ H₁) (hL : IsPGroup 2 L) : Nat.card L ≤ Nat.card Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSz : P ⊔ Q ≤ C z := hS.le
  have hS2 : IsPGroup 2 ↥(P ⊔ Q) := hS.isPGroup
  have hP2 : IsPGroup 2 P := hS2.to_le le_sup_left
  have hcardS : Nat.card ↥(P ⊔ Q) = Nat.card P * Nat.card Q :=
    CFSG.CGT.Foote81L6.card_sup_of_le_normalizer (hQP.trans (centralizer_le_normalizer _)) hPQ
  obtain ⟨T, hT⟩ := hS.exists_sylow_eq_subgroupOf
  let Tb : Sylow 2 (Bar (C z)) :=
    T.mapSurjective (QuotientGroup.mk'_surjective (CFSG.oddCore (C z)))
  have hTb : (Tb : Subgroup (Bar (C z))) = bar (C z) (P ⊔ Q) := by
    rw [Sylow.coe_mapSurjective, hT]
    rfl
  have hLP : L ≤ normalizer (bar (C z) P : Set (Bar (C z))) :=
    (hLH.trans h₃).trans (centralizer_le_normalizer _)
  have hPL2 : IsPGroup 2 ↥(bar (C z) P ⊔ L) := (isPGroup_bar hP2).to_sup_of_normal_left' hL hLP
  obtain ⟨T', hT'⟩ := hPL2.exists_le_sylow
  have h1 : Nat.card ↥(bar (C z) P ⊔ L) ≤ Nat.card ↥(P ⊔ Q) := by
    calc Nat.card ↥(bar (C z) P ⊔ L) ≤ Nat.card (T' : Subgroup (Bar (C z))) := card_le_of_le hT'
      _ = Nat.card (Tb : Subgroup (Bar (C z))) := by
          rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
      _ = Nat.card ↥(bar (C z) (P ⊔ Q)) := by rw [hTb]
      _ = Nat.card ↥(P ⊔ Q) := card_bar_of_isPGroup hSz hS2
  have h2 : Nat.card ↥(bar (C z) P ⊔ L) = Nat.card P * Nat.card L := by
    rw [CFSG.CGT.Foote81L6.card_sup_of_le_normalizer hLP
      (eq_bot_iff.2 ((inf_le_inf_left _ hLH).trans h₁.le)),
      card_bar_of_isPGroup (le_sup_left.trans hSz) hP2]
  rw [h2, hcardS] at h1
  exact Nat.le_of_mul_le_mul_left h1 Nat.card_pos

theorem card_le_of_bar_le (hS : ABGLocalTools.IsSylowOf 2 (P ⊔ Q) (C z))
    (hQP : Q ≤ centralizer (P : Set G)) (hPQ : P ⊓ Q = ⊥) (h₁ : bar (C z) P ⊓ H₁ = ⊥)
    (h₃ : H₁ ≤ centralizer (bar (C z) P : Set (Bar (C z)))) {R : Subgroup G} (hRz : R ≤ C z)
    (hR : IsPGroup 2 R) (hRH : bar (C z) R ≤ H₁) : Nat.card R ≤ Nat.card Q := by
  rw [← card_bar_of_isPGroup hRz hR]
  exact card_le_of_le_H₁ hS hQP hPQ h₁ h₃ hRH (isPGroup_bar hR)

theorem isSylowOf_bar (hS : ABGLocalTools.IsSylowOf 2 (P ⊔ Q) (C z))
    (hQP : Q ≤ centralizer (P : Set G)) (hPQ : P ⊓ Q = ⊥) (h₁ : bar (C z) P ⊓ H₁ = ⊥)
    (h₃ : H₁ ≤ centralizer (bar (C z) P : Set (Bar (C z)))) (h₄ : bar (C z) Q ≤ ⁅H₁, H₁⁆) :
    ABGLocalTools.IsSylowOf 2 (bar (C z) Q) H₁ := by
  have hSz : P ⊔ Q ≤ C z := hS.le
  have hQ2 : IsPGroup 2 Q := hS.isPGroup.to_le le_sup_right
  refine isSylowOf_of_forall_card_le (h₄.trans (commutator_le_self H₁)) (isPGroup_bar hQ2)
    fun L hL hL2 => ?_
  rw [card_bar_of_isPGroup (le_sup_right.trans hSz) hQ2]
  exact card_le_of_le_H₁ hS hQP hPQ h₁ h₃ hL hL2

theorem O2_H₁ (hS : ABGLocalTools.IsSylowOf 2 (P ⊔ Q) (C z))
    (hQP : Q ≤ centralizer (P : Set G)) (hPQ : P ⊓ Q = ⊥) (h₁ : bar (C z) P ⊓ H₁ = ⊥)
    (h₃ : H₁ ≤ centralizer (bar (C z) P : Set (Bar (C z)))) (h₄ : bar (C z) Q ≤ ⁅H₁, H₁⁆) :
    O2 H₁ = H₁ :=
  O2_eq_self_of_isSylowOf (isSylowOf_bar hS hQP hPQ h₁ h₃ h₄) h₄

theorem le_core (hS : ABGLocalTools.IsSylowOf 2 (P ⊔ Q) (C z))
    (hQP : Q ≤ centralizer (P : Set G)) (hPQ : P ⊓ Q = ⊥) (h₁ : bar (C z) P ⊓ H₁ = ⊥)
    (h₂ : bar (C z) P ⊔ H₁ = ⊤) (h₃ : H₁ ≤ centralizer (bar (C z) P : Set (Bar (C z))))
    (h₄ : bar (C z) Q ≤ ⁅H₁, H₁⁆) {W : Subgroup G} (hWz : W ≤ C z) (hH : H₁ ≤ bar (C z) W)
    (hQW : Q ≤ W) : Q ≤ ⁅O2 W, O2 W⁆ ⊔ O W := by
  have hP : IsPGroup 2 P := hS.isPGroup.to_le le_sup_left
  have hgen := O2_H₁ hS hQP hPQ h₁ h₃ h₄
  intro q hq
  have hqz : q ∈ C z := hWz (hQW hq)
  have hmem : QuotientGroup.mk' (CFSG.oddCore (C z)) ⟨q, hqz⟩ ∈
      bar (C z) (⁅O2 W, O2 W⁆ ⊔ O W) := by
    rw [bar_core hP h₁ h₂ h₃ hgen hWz hH]
    exact h₄ (mk_mem_bar hqz hq)
  obtain ⟨⟨c, hcz⟩, hc, hce⟩ := hmem
  have hc' : c ∈ ⁅O2 W, O2 W⁆ ⊔ O W := hc
  have ho := inv_mul_mem_O_of_mk_eq hce
  have hoW : c⁻¹ * q ∈ O W := by
    rw [O_eq_inf hP h₁ h₂ h₃ hWz hH]
    exact mem_inf.2 ⟨mul_mem (inv_mem (core_le W hc')) (hQW hq), ho⟩
  have e : q = c * (c⁻¹ * q) := by group
  rw [e]
  exact mul_mem hc' (mem_sup_right hoW)

theorem isSylowOf_core (hS : ABGLocalTools.IsSylowOf 2 (P ⊔ Q) (C z))
    (hQP : Q ≤ centralizer (P : Set G)) (hPQ : P ⊓ Q = ⊥) (h₁ : bar (C z) P ⊓ H₁ = ⊥)
    (h₂ : bar (C z) P ⊔ H₁ = ⊤) (h₃ : H₁ ≤ centralizer (bar (C z) P : Set (Bar (C z))))
    (h₄ : bar (C z) Q ≤ ⁅H₁, H₁⁆) {W : Subgroup G} (hWz : W ≤ C z) (hH : H₁ ≤ bar (C z) W)
    (hQW : Q ≤ W) : ABGLocalTools.IsSylowOf 2 Q (⁅O2 W, O2 W⁆ ⊔ O W) := by
  have hP : IsPGroup 2 P := hS.isPGroup.to_le le_sup_left
  have hgen := O2_H₁ hS hQP hPQ h₁ h₃ h₄
  have hQ2 : IsPGroup 2 Q := hS.isPGroup.to_le le_sup_right
  refine isSylowOf_of_forall_card_le (le_core hS hQP hPQ h₁ h₂ h₃ h₄ hWz hH hQW) hQ2
    fun R hR hR2 => ?_
  exact card_le_of_bar_le hS hQP hPQ h₁ h₃ (hR.trans ((core_le W).trans hWz)) hR2
    ((bar_mono hR).trans ((bar_core hP h₁ h₂ h₃ hgen hWz hH).le.trans (commutator_le_self H₁)))

theorem quotIs_core (hP : IsPGroup 2 P) (h₁ : bar (C z) P ⊓ H₁ = ⊥)
    (h₂ : bar (C z) P ⊔ H₁ = ⊤) (h₃ : H₁ ≤ centralizer (bar (C z) P : Set (Bar (C z))))
    (hgen : O2 H₁ = H₁) {W : Subgroup G} (hWz : W ≤ C z) (hH : H₁ ≤ bar (C z) W)
    {Pr : ∀ L : Type, Group L → Prop} (hPr : Pr ↥⁅H₁, H₁⁆ inferInstance) :
    QuotIs (⁅O2 W, O2 W⁆ ⊔ O W) (O W) Pr := by
  have hKz : ⁅O2 W, O2 W⁆ ⊔ O W ≤ C z := (core_le W).trans hWz
  have hbar := bar_core hP h₁ h₂ h₃ hgen hWz hH
  let g : ↥(⁅O2 W, O2 W⁆ ⊔ O W) →* Bar (C z) :=
    (QuotientGroup.mk' (CFSG.oddCore (C z))).comp (inclusion hKz)
  have hg : ∀ k, g k ∈ ⁅H₁, H₁⁆ := fun k => hbar ▸ mk_mem_bar (hKz k.2) k.2
  refine ⟨↥⁅H₁, H₁⁆, inferInstance, g.codRestrict _ hg, ?_, ?_, hPr⟩
  · rintro ⟨y, hy⟩
    have hy' := hy
    rw [← hbar] at hy'
    obtain ⟨⟨k, hkz⟩, hk, rfl⟩ := hy'
    exact ⟨⟨k, hk⟩, rfl⟩
  · ext k
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    have hk1 : (g.codRestrict _ hg) k = 1 ↔ (k : G) ∈ O (C z) := by
      rw [Subtype.ext_iff]
      change QuotientGroup.mk' (CFSG.oddCore (C z)) (inclusion hKz k) = 1 ↔ _
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_oddCore_iff]
      rfl
    have hOW : ∀ x : G, x ∈ O W ↔ x ∈ W ⊓ O (C z) := fun x => by
      rw [O_eq_inf hP h₁ h₂ h₃ hWz hH]
    rw [hk1, hOW, mem_inf]
    exact ⟨fun h => ⟨core_le W k.2, h⟩, fun h => h.2⟩

theorem normalizer_le_sup_centralizer (hS : ABGLocalTools.IsSylowOf 2 (P ⊔ Q) (C z))
    (hQP : Q ≤ centralizer (P : Set G)) (hPQ : P ⊓ Q = ⊥) (h₁ : bar (C z) P ⊓ H₁ = ⊥)
    (h₂ : bar (C z) P ⊔ H₁ = ⊤) (h₃ : H₁ ≤ centralizer (bar (C z) P : Set (Bar (C z))))
    (h₄ : bar (C z) Q ≤ ⁅H₁, H₁⁆)
    (hQodd : ∀ g ∈ normalizer (Q : Set G), Odd (orderOf g) → g ∈ centralizer (Q : Set G))
    {W : Subgroup G} (hWz : W ≤ C z) (hQW : Q ≤ W) :
    W ⊓ normalizer (Q : Set G) ≤ Q ⊔ (W ⊓ centralizer (Q : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 P := hS.isPGroup.to_le le_sup_left
  have hQ2 : IsPGroup 2 Q := hS.isPGroup.to_le le_sup_right
  have hSyl := isSylowOf_bar hS hQP hPQ h₁ h₃ h₄
  have hPQc : P ≤ centralizer (Q : Set G) := le_centralizer_iff.1 hQP
  have hPH : bar (C z) P ≤ normalizer (H₁ : Set (Bar (C z))) :=
    (le_centralizer_iff.1 h₃).trans (centralizer_le_normalizer _)
  have two : ∀ n ∈ W ⊓ normalizer (Q : Set G), (∃ k : ℕ, n ^ 2 ^ k = 1) →
      n ∈ Q ⊔ (W ⊓ centralizer (Q : Set G)) := by
    intro n hn ⟨k, hk⟩
    obtain ⟨hnW, hnN⟩ := mem_inf.1 hn
    have hnz : n ∈ C z := hWz hnW
    obtain ⟨pb, hpb, hb, hhb, hpe⟩ := mem_sup_of_le_normalizer hPH
      (h₂ ▸ mem_top (QuotientGroup.mk' (CFSG.oddCore (C z)) ⟨n, hnz⟩))
    have hnQ : QuotientGroup.mk' (CFSG.oddCore (C z)) ⟨n, hnz⟩ ∈
        normalizer (bar (C z) Q : Set (Bar (C z))) :=
      bar_le_normalizer_bar le_rfl (mk_mem_bar hnz hnN)
    have hpQ : pb ∈ normalizer (bar (C z) Q : Set (Bar (C z))) :=
      centralizer_le_normalizer _ (bar_le_centralizer_bar hPQc hpb)
    have hhQ : hb ∈ normalizer (bar (C z) Q : Set (Bar (C z))) := by
      have e : hb = pb⁻¹ * QuotientGroup.mk' (CFSG.oddCore (C z)) ⟨n, hnz⟩ := by
        rw [← hpe]
        group
      rw [e]
      exact mul_mem (inv_mem hpQ) hnQ
    obtain ⟨j, hj⟩ := isPGroup_bar hP ⟨pb, hpb⟩
    have hpj : pb ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hc : Commute pb hb := mem_centralizer_iff.1 (h₃ hhb) pb hpb
    have hn1 : (⟨n, hnz⟩ : C z) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    have hπ1 : QuotientGroup.mk' (CFSG.oddCore (C z)) ⟨n, hnz⟩ ^ 2 ^ (j + k) = 1 := by
      rw [pow_add, pow_mul', ← map_pow, hn1, map_one, one_pow]
    have hp1 : pb ^ 2 ^ (j + k) = 1 := by
      rw [pow_add, pow_mul, hpj, one_pow]
    have hh2 : hb ^ 2 ^ (j + k) = 1 := by
      rw [← hpe, hc.mul_pow, hp1, one_mul] at hπ1
      exact hπ1
    have hzp : IsPGroup 2 (zpowers hb) := by
      rintro ⟨y, hy⟩
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hy
      refine ⟨j + k, Subtype.ext ?_⟩
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hh2, one_zpow]
    have hR2 : IsPGroup 2 ↥(bar (C z) Q ⊔ zpowers hb) :=
      (isPGroup_bar hQ2).to_sup_of_normal_left' hzp (zpowers_le.2 hhQ)
    have hRH : bar (C z) Q ⊔ zpowers hb ≤ H₁ :=
      sup_le (h₄.trans (commutator_le_self H₁)) (zpowers_le.2 hhb)
    have heq := hSyl.eq_of_le le_sup_left hRH hR2
    have hhQ' : hb ∈ bar (C z) Q := heq ▸ mem_sup_right (mem_zpowers hb)
    obtain ⟨⟨q, hqz⟩, hq, rfl⟩ := hhQ'
    obtain ⟨⟨p, hpz'⟩, hp, rfl⟩ := hpb
    have hq' : q ∈ Q := hq
    have hp' : p ∈ P := hp
    have e : QuotientGroup.mk' (CFSG.oddCore (C z)) (⟨p, hpz'⟩ * ⟨q, hqz⟩) =
        QuotientGroup.mk' (CFSG.oddCore (C z)) ⟨n, hnz⟩ := by
      rw [map_mul]
      exact hpe
    have ho : (p * q)⁻¹ * n ∈ O (C z) := by simpa using inv_mul_mem_O_of_mk_eq e
    have hoN : (p * q)⁻¹ * n ∈ normalizer (Q : Set G) :=
      mul_mem (inv_mem (mul_mem (centralizer_le_normalizer _ (hPQc hp')) (le_normalizer hq'))) hnN
    have hoodd : Odd (orderOf ((p * q)⁻¹ * n)) :=
      Odd.of_dvd_nat (card_O_odd (C z)) (Subgroup.orderOf_dvd_natCard _ ho)
    have hoC := hQodd _ hoN hoodd
    have hpq : q * p = p * q := mem_centralizer_iff.1 (hPQc hp') q hq'
    have e2 : q⁻¹ * n = p * ((p * q)⁻¹ * n) := by
      calc q⁻¹ * n = q⁻¹ * (q * p) * ((p * q)⁻¹ * n) := by rw [hpq]; group
        _ = p * ((p * q)⁻¹ * n) := by group
    have hmem : q⁻¹ * n ∈ W ⊓ centralizer (Q : Set G) :=
      mem_inf.2 ⟨mul_mem (inv_mem (hQW hq')) hnW, e2 ▸ mul_mem (hPQc hp') hoC⟩
    have e3 : n = q * (q⁻¹ * n) := by group
    rw [e3]
    exact mul_mem_sup hq' hmem
  intro n hn
  obtain ⟨hnW, hnN⟩ := mem_inf.1 hn
  obtain ⟨a, b, hab, ⟨k, hk⟩, hodd⟩ := exists_zpow_mul_zpow n
  have h2 := two (n ^ a) (mem_inf.2 ⟨zpow_mem hnW a, zpow_mem hnN a⟩) ⟨k, hk⟩
  have h1 : n ^ b ∈ W ⊓ centralizer (Q : Set G) :=
    mem_inf.2 ⟨zpow_mem hnW b, hQodd _ (zpow_mem hnN b) hodd⟩
  rw [← hab]
  exact mul_mem h2 (mem_sup_right h1)

omit [Finite G] in
theorem mem_normalizer_sup {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq'] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem isKleinFour_of_commutator_eq (hS : ABGLocalTools.IsSylowOf 2 (P ⊔ Q) (C z))
    (hQP : Q ≤ centralizer (P : Set G)) (hPQ : P ⊓ Q = ⊥) (h₁ : bar (C z) P ⊓ H₁ = ⊥)
    (h₃ : H₁ ≤ centralizer (bar (C z) P : Set (Bar (C z)))) (h₄ : bar (C z) Q ≤ ⁅H₁, H₁⁆)
    (hQ : IsDih Q) (heq : ⁅H₁, H₁⁆ = bar (C z) Q) : IsKleinFour Q := by
  rcases hQ.isKleinFour_or_isDihNonab with h | h
  · exact h
  exfalso
  obtain ⟨a, ha, ⟨e⟩⟩ := h
  have hQ2 : IsPGroup 2 Q := hS.isPGroup.to_le le_sup_right
  obtain ⟨eb⟩ := nonempty_mulEquiv_bar (le_sup_right.trans hS.le) hQ2
  have e' : ↥(bar (C z) Q) ≃* DihedralGroup (2 ^ a) := eb.symm.trans e
  have h4 : 4 ≤ 2 ^ a := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have hgen := O2_H₁ hS hQP hPQ h₁ h₃ h₄
  have hHn : H₁ ≤ normalizer (bar (C z) Q : Set (Bar (C z))) := by
    rw [← heq]
    exact le_normalizer_iff_commutator_le_right.2 (commutator_mono le_rfl (commutator_le_self H₁))
  have hHc : H₁ ≤ centralizer (bar (C z) Q : Set (Bar (C z))) := by
    calc H₁ = O2 H₁ := hgen.symm
      _ ≤ _ := twoResidualOf_le_of_forall fun y hy hodd =>
        CFSG.Quasithin.Vol2.Ch10.SecB.C10P34.mem_centralizer_of_dihedral h4 e' (isPGroup_bar hQ2)
          (hHn hy) hodd
  have hcomm : ∀ x ∈ bar (C z) Q, ∀ y ∈ bar (C z) Q, x * y = y * x := fun x hx y hy =>
    mem_centralizer_iff.1 (hHc ((h₄.trans (commutator_le_self _)) hy)) x hx
  refine DihedralGroup.not_commutative (n := 2 ^ a) (by omega) (by omega)
    (IsMulCommutative.of_comm fun u v => ?_)
  apply e'.symm.injective
  rw [map_mul, map_mul]
  exact Subtype.ext (hcomm _ (e'.symm u).2 _ (e'.symm v).2)

theorem side_lemma (hS : ABGLocalTools.IsSylowOf 2 (P ⊔ Q) (C z))
    (hQP : Q ≤ centralizer (P : Set G)) (hPQ : P ⊓ Q = ⊥) (h₁ : bar (C z) P ⊓ H₁ = ⊥)
    (h₂ : bar (C z) P ⊔ H₁ = ⊤) (h₃ : H₁ ≤ centralizer (bar (C z) P : Set (Bar (C z))))
    (h₄ : bar (C z) Q ≤ ⁅H₁, H₁⁆) {V V' A M : Subgroup G} (hVP : V ≤ P) (hzV : z ∈ V)
    (hA : V ⊔ V' = A) (hV'Q : V' ≤ Q)
    (hQodd : (∀ g ∈ normalizer (Q : Set G), Odd (orderOf g) → g ∈ centralizer (Q : Set G)) ∨
      V' = Q)
    (hconj : ∀ x ∈ V, x ≠ 1 → ∃ n : G, n * z * n⁻¹ = x ∧ n ∈ normalizer (V : Set G))
    (hM : M = centralizer (V : Set G)) :
    (∀ {Pr : ∀ L : Type, Group L → Prop}, Pr ↥⁅H₁, H₁⁆ inferInstance →
      QuotIs (⁅O2 M, O2 M⁆ ⊔ O M) (O M) Pr) ∧
    ABGLocalTools.IsSylowOf 2 Q (⁅O2 M, O2 M⁆ ⊔ O M) ∧
    M = (⁅O2 M, O2 M⁆ ⊔ O M) ⊔ (M ⊓ normalizer (A : Set G)) ∧
    M = (⁅O2 M, O2 M⁆ ⊔ O M) ⊔ (M ⊓ normalizer (Q : Set G)) ∧
    (∀ x ∈ V, x ≠ 1 → O2 (C x) = (O2 M ⊓ O2 (C x)) ⊔ O (C x)) ∧
    (∀ x ∈ V, x ≠ 1 → ⁅O2 (C x), O2 (C x)⁆ ⊔ O (C x) =
      ((⁅O2 M, O2 M⁆ ⊔ O M) ⊓ ⁅O2 (C x), O2 (C x)⁆) ⊔ O (C x)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 P := hS.isPGroup.to_le le_sup_left
  have hgen : O2 H₁ = H₁ := O2_H₁ hS hQP hPQ h₁ h₃ h₄
  have hPz : P ≤ C z := le_sup_left.trans hS.le
  have hCp : H₁ ≤ bar (C z) (centralizer (P : Set G)) := le_bar_centralizer hP hPz h₃
  have hCpM : centralizer (P : Set G) ≤ M := hM ▸ centralizer_le (SetLike.coe_subset_coe.2 hVP)
  have hMz : M ≤ C z := hM ▸ centralizer_le (Set.singleton_subset_iff.2 hzV)
  have hHM : H₁ ≤ bar (C z) M := hCp.trans (bar_mono hCpM)
  have hQM : Q ≤ M := hQP.trans hCpM
  have hii := isSylowOf_core hS hQP hPQ h₁ h₂ h₃ h₄ hMz hHM hQM
  have hM₀M : ⁅O2 M, O2 M⁆ ⊔ O M ≤ M := core_le M
  have hiii₂ : M = (⁅O2 M, O2 M⁆ ⊔ O M) ⊔ (M ⊓ normalizer (Q : Set G)) :=
    le_antisymm (le_sup_inf_normalizer hii hM₀M (le_normalizer_core M)) (sup_le hM₀M inf_le_left)
  have hNA : M ⊓ normalizer (Q : Set G) ≤ (⁅O2 M, O2 M⁆ ⊔ O M) ⊔ (M ⊓ normalizer (A : Set G)) := by
    rcases hQodd with hQodd | hV'
    · have hN := normalizer_le_sup_centralizer hS hQP hPQ h₁ h₂ h₃ h₄ hQodd hMz hQM
      have hCA : M ⊓ centralizer (Q : Set G) ≤ M ⊓ normalizer (A : Set G) := by
        refine le_inf inf_le_left fun g hg => centralizer_le_normalizer _ ?_
        obtain ⟨hgM, hgQ⟩ := mem_inf.1 hg
        rw [hM] at hgM
        have hAg : A ≤ C g := by
          rw [← hA]
          refine sup_le (fun x hx => ?_) (fun y hy => ?_)
          · exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hgM x hx)
          · exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hgQ y (hV'Q hy))
        rw [mem_centralizer_iff]
        exact fun a ha => mem_centralizer_singleton_iff.1 (hAg ha)
      exact hN.trans (sup_le (hii.le.trans le_sup_left) (hCA.trans le_sup_right))
    · refine le_sup_of_le_right (le_inf inf_le_left fun g hg => ?_)
      obtain ⟨hgM, hgQ⟩ := mem_inf.1 hg
      rw [hM] at hgM
      rw [← hA]
      exact mem_normalizer_sup (centralizer_le_normalizer _ hgM) (hV' ▸ hgQ)
  have hiii₁ : M = (⁅O2 M, O2 M⁆ ⊔ O M) ⊔ (M ⊓ normalizer (A : Set G)) := by
    refine le_antisymm ?_ (sup_le hM₀M inf_le_left)
    calc M ≤ (⁅O2 M, O2 M⁆ ⊔ O M) ⊔ (M ⊓ normalizer (Q : Set G)) := hiii₂.le
      _ ≤ (⁅O2 M, O2 M⁆ ⊔ O M) ⊔ (M ⊓ normalizer (A : Set G)) := sup_le le_sup_left hNA
  have hO2z : O2 (C z) = O2 M ⊔ O (C z) := by
    have h := O2_eq_sup hP h₁ h₂ h₃ hgen (hCpM.trans hMz) le_rfl hCp
    refine le_antisymm ?_ (sup_le (twoResidualOf_mono hMz) (O_le_O2 _))
    rw [h]
    exact sup_le_sup_right (twoResidualOf_mono hCpM) _
  have hiv₀ : O2 (C z) = (O2 M ⊓ O2 (C z)) ⊔ O (C z) := by
    rw [inf_eq_left.2 (twoResidualOf_mono hMz)]
    exact hO2z
  have hv₀ : ⁅O2 (C z), O2 (C z)⁆ ⊔ O (C z) =
      ((⁅O2 M, O2 M⁆ ⊔ O M) ⊓ ⁅O2 (C z), O2 (C z)⁆) ⊔ O (C z) := by
    have hc : ⁅O2 (C z), O2 (C z)⁆ ⊔ O (C z) = ⁅O2 M, O2 M⁆ ⊔ O (C z) := by
      rw [hO2z]
      exact commutator_sup_sup_eq (((twoResidualOf_le_self _).trans hMz).trans (le_normalizer_O _))
    refine le_antisymm ?_ (sup_le_sup_right inf_le_right _)
    rw [hc]
    exact sup_le_sup_right (le_inf le_sup_left
      (commutator_mono (twoResidualOf_mono hMz) (twoResidualOf_mono hMz))) _
  refine ⟨fun hPr => quotIs_core hP h₁ h₂ h₃ hgen hMz hHM hPr, hii, hiii₁, hiii₂,
    fun x hx hx1 => ?_, fun x hx hx1 => ?_⟩
  · obtain ⟨n, hnx, hnV⟩ := hconj x hx hx1
    have hCx : (C z).map (MulAut.conj n).toMonoidHom = C x := by
      rw [map_C, MulAut.conj_apply, hnx]
    have hMn : M.map (MulAut.conj n).toMonoidHom = M :=
      mem_normalizer_iff_map_conj_eq'.1 (hM ▸ mem_normalizer_centralizer hnV)
    have h := congrArg (Subgroup.map (MulAut.conj n).toMonoidHom) hiv₀
    simp only [Subgroup.map_sup, Subgroup.map_inf _ _ (MulAut.conj n).toMonoidHom
      (MulAut.conj n).injective, map_O2, map_O, hMn, hCx] at h
    exact h
  · obtain ⟨n, hnx, hnV⟩ := hconj x hx hx1
    have hCx : (C z).map (MulAut.conj n).toMonoidHom = C x := by
      rw [map_C, MulAut.conj_apply, hnx]
    have hM₀n : (⁅O2 M, O2 M⁆ ⊔ O M).map (MulAut.conj n).toMonoidHom = ⁅O2 M, O2 M⁆ ⊔ O M :=
      mem_normalizer_iff_map_conj_eq'.1 (hM ▸ mem_normalizer_centralizer_core hnV)
    have h := congrArg (Subgroup.map (MulAut.conj n).toMonoidHom) hv₀
    rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_inf _ _ (MulAut.conj n).toMonoidHom
      (MulAut.conj n).injective, hM₀n, map_commutator, map_O2, map_O, hCx] at h
    exact h

end Side

end G4b

namespace Sec4Setting

open G4b

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G}
  (hAS : A ≤ 𝔖.S) (hA : IsE16 A)
include hAS hA

theorem lemma_4_7_of
    (h315 : ∀ z₁ z₂ : G, (z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁) →
      (z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) →
      (∃ H₁ : Subgroup (Bar (C z₁)), bar (C z₁) 𝔖.S₁ ⊓ H₁ = ⊥ ∧ bar (C z₁) 𝔖.S₁ ⊔ H₁ = ⊤ ∧
        H₁ ≤ centralizer (bar (C z₁) 𝔖.S₁ : Set (Bar (C z₁))) ∧
        bar (C z₁) 𝔖.S₂ ≤ ⁅H₁, H₁⁆ ∧ IsL2OrA7 (⁅H₁, H₁⁆ : Subgroup (Bar (C z₁))) 7) ∧
      (∃ K₁ : Subgroup (Bar (C z₂)), bar (C z₂) 𝔖.S₂ ⊓ K₁ = ⊥ ∧ bar (C z₂) 𝔖.S₂ ⊔ K₁ = ⊤ ∧
        K₁ ≤ centralizer (bar (C z₂) 𝔖.S₂ : Set (Bar (C z₂))) ∧
        bar (C z₂) 𝔖.S₁ ≤ ⁅K₁, K₁⁆ ∧
        (IsL2OrA7 (⁅K₁, K₁⁆ : Subgroup (Bar (C z₂))) 5 ∨ ⁅K₁, K₁⁆ = bar (C z₂) 𝔖.S₁))) :
    QuotIs (𝔖.M₀ A) (O (𝔖.M A)) (fun L _ => IsL2OrA7 L 7) ∧
    CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₂ (𝔖.M₀ A) ∧
    𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (A : Set G)) ∧
    𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (𝔖.S₂ : Set G)) ∧
    (∀ x ∈ 𝔖.X A, x ≠ 1 → O2 (C x) = (O2 (𝔖.M A) ⊓ O2 (C x)) ⊔ O (C x)) ∧
    (∀ x ∈ 𝔖.X A, x ≠ 1 → ⁅O2 (C x), O2 (C x)⁆ ⊔ O (C x) =
      (𝔖.M₀ A ⊓ ⁅O2 (C x), O2 (C x)⁆) ⊔ O (C x)) := by
  obtain ⟨⟨H₁, h₁, h₂, h₃, h₄, h₅⟩, -⟩ := h315 𝔖.z₁ 𝔖.z₂ 𝔖.hz₁ 𝔖.hz₂
  have hS : ABGLocalTools.IsSylowOf 2 (𝔖.S₁ ⊔ 𝔖.S₂) (C 𝔖.z₁) := by
    rw [𝔖.decomp.sup_eq]
    exact isSylowOf_of_sylow_le 𝔖.S 𝔖.S_le_C_z₁
  have hQodd : ∀ g ∈ normalizer (𝔖.S₂ : Set G), Odd (orderOf g) →
      g ∈ centralizer (𝔖.S₂ : Set G) := by
    obtain ⟨a, ha, ⟨e⟩⟩ := 𝔖.decomp.dih₂
    intro g hg hodd
    have h4 : 4 ≤ 2 ^ a := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    exact CFSG.Quasithin.Vol2.Ch10.SecB.C10P34.mem_centralizer_of_dihedral h4 e
      (hS.isPGroup.to_le le_sup_right) hg hodd
  obtain ⟨c₁, c₂, c₃, c₄, c₅, c₆⟩ := side_lemma hS (S₂_le_centralizer_S₁ 𝔖) 𝔖.decomp.inf_eq
    h₁ h₂ h₃ h₄ (X_le_S₁ 𝔖) (z₁_mem_X 𝔖 hAS hA) (X_sup_Y 𝔖 hAS hA) (Y_le_S₂ 𝔖) (Or.inl hQodd)
    (fun x hx hx1 => by
      obtain ⟨n, hnA, hnx⟩ := exists_mem_normalizer_conj_eq_of_mem_X 𝔖 hAS hA hx hx1
      exact ⟨n, hnx, normalizer_le_normalizer_X 𝔖 hAS hA hnA⟩) (M := 𝔖.M A) rfl
  exact ⟨c₁ h₅, c₂, c₃, c₄, c₅, c₆⟩

theorem lemma_4_8_of
    (h315 : ∀ z₁ z₂ : G, (z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁) →
      (z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) →
      (∃ H₁ : Subgroup (Bar (C z₁)), bar (C z₁) 𝔖.S₁ ⊓ H₁ = ⊥ ∧ bar (C z₁) 𝔖.S₁ ⊔ H₁ = ⊤ ∧
        H₁ ≤ centralizer (bar (C z₁) 𝔖.S₁ : Set (Bar (C z₁))) ∧
        bar (C z₁) 𝔖.S₂ ≤ ⁅H₁, H₁⁆ ∧ IsL2OrA7 (⁅H₁, H₁⁆ : Subgroup (Bar (C z₁))) 7) ∧
      (∃ K₁ : Subgroup (Bar (C z₂)), bar (C z₂) 𝔖.S₂ ⊓ K₁ = ⊥ ∧ bar (C z₂) 𝔖.S₂ ⊔ K₁ = ⊤ ∧
        K₁ ≤ centralizer (bar (C z₂) 𝔖.S₂ : Set (Bar (C z₂))) ∧
        bar (C z₂) 𝔖.S₁ ≤ ⁅K₁, K₁⁆ ∧
        (IsL2OrA7 (⁅K₁, K₁⁆ : Subgroup (Bar (C z₂))) 5 ∨ ⁅K₁, K₁⁆ = bar (C z₂) 𝔖.S₁))) :
    QuotIs (𝔖.N₀ A) (O (𝔖.N A)) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) ∧
    CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₁ (𝔖.N₀ A) ∧
    𝔖.N A = 𝔖.N₀ A ⊔ (𝔖.N A ⊓ normalizer (A : Set G)) ∧
    𝔖.N A = 𝔖.N₀ A ⊔ (𝔖.N A ⊓ normalizer (𝔖.S₁ : Set G)) ∧
    (∀ y ∈ 𝔖.Y A, y ≠ 1 → O2 (C y) = (O2 (𝔖.N A) ⊓ O2 (C y)) ⊔ O (C y)) ∧
    (∀ y ∈ 𝔖.Y A, y ≠ 1 → ⁅O2 (C y), O2 (C y)⁆ ⊔ O (C y) =
      (𝔖.N₀ A ⊓ ⁅O2 (C y), O2 (C y)⁆) ⊔ O (C y)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨K₁, k₁, k₂, k₃, k₄, k₅⟩⟩ := h315 𝔖.z₁ 𝔖.z₂ 𝔖.hz₁ 𝔖.hz₂
  have hS : ABGLocalTools.IsSylowOf 2 (𝔖.S₂ ⊔ 𝔖.S₁) (C 𝔖.z₂) := by
    rw [sup_comm, 𝔖.decomp.sup_eq]
    exact isSylowOf_of_sylow_le 𝔖.S (S_le_C_z₂ 𝔖)
  have hQP : 𝔖.S₁ ≤ centralizer (𝔖.S₂ : Set G) := S₁_le_centralizer_S₂ 𝔖
  have hPQ : 𝔖.S₂ ⊓ 𝔖.S₁ = ⊥ := by rw [inf_comm]; exact 𝔖.decomp.inf_eq
  have hQ2 : IsPGroup 2 𝔖.S₁ := hS.isPGroup.to_le le_sup_right
  have hQodd : (∀ g ∈ normalizer (𝔖.S₁ : Set G), Odd (orderOf g) →
      g ∈ centralizer (𝔖.S₁ : Set G)) ∨ 𝔖.X A = 𝔖.S₁ := by
    rcases 𝔖.decomp.dih₁.isKleinFour_or_isDihNonab with h | ⟨a, ha, ⟨e⟩⟩
    · refine Or.inr (eq_of_le_of_card_ge (X_le_S₁ 𝔖) ?_)
      rw [h.card_four, (isKleinFour_X 𝔖 hAS hA).card_four]
    · refine Or.inl fun g hg hodd => ?_
      have h4 : 4 ≤ 2 ^ a := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
      exact CFSG.Quasithin.Vol2.Ch10.SecB.C10P34.mem_centralizer_of_dihedral h4 e hQ2 hg hodd
  have hA' : 𝔖.Y A ⊔ 𝔖.X A = A := by rw [sup_comm]; exact X_sup_Y 𝔖 hAS hA
  obtain ⟨c₁, c₂, c₃, c₄, c₅, c₆⟩ := side_lemma hS hQP hPQ k₁ k₂ k₃ k₄ (Y_le_S₂ 𝔖)
    (z₂_mem_Y 𝔖 hAS hA) hA' (X_le_S₁ 𝔖) hQodd
    (fun y hy hy1 => by
      obtain ⟨n, hnA, hny⟩ := exists_mem_normalizer_conj_eq_of_mem_Y 𝔖 hAS hA hy hy1
      exact ⟨n, hny, normalizer_le_normalizer_Y 𝔖 hAS hA hnA⟩) (M := 𝔖.N A) rfl
  refine ⟨c₁ ?_, c₂, c₃, c₄, c₅, c₆⟩
  rcases k₅ with h | h
  · exact Or.inl h
  ·
    have hfour := isKleinFour_of_commutator_eq hS hQP hPQ k₁ k₃ k₄ 𝔖.decomp.dih₁ h
    obtain ⟨eb⟩ := nonempty_mulEquiv_bar (le_sup_right.trans hS.le) hQ2
    refine Or.inr ⟨?_, ?_⟩
    · rw [h, ← Nat.card_congr eb.toEquiv, hfour.card_four]
    · rw [h, ← Monoid.exponent_eq_of_mulEquiv eb, hfour.exponent_two]

end Sec4Setting

end CFSG.GH72
