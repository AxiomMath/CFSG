module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LocalAnalysis.SectionRank.SQT
public import Mathlib.GroupTheory.NoncommCoprod

public section

namespace CFSG.ComponentClassification.UnbalancedGS

namespace RankOneCenter

open Subgroup

variable {p : ℕ} [hp : Fact p.Prime]

theorem le_pRank_of_subgroup {K : Type*} [Group K] [Finite K] {A : Subgroup K}
    (hA : IsElementaryAbelian p A) {r : ℕ} (hr : Nat.card A = p ^ r) : r ≤ pRank p K := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.SectionRank.le_pRank hp.out.one_lt le_top
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p A).mp hA) hr

theorem exists_subgroup_card_pRank (K : Type*) [Group K] [Finite K] :
    ∃ A : Subgroup K, IsElementaryAbelian p A ∧ Nat.card A = p ^ pRank p K := by
  obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (G := K) hp.out.one_lt ⊤
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact ⟨E, (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E).mpr hE, hcard⟩

theorem card_sup_mul_card_inf_of_commute {H : Type*} [Group H] [Finite H] (L R : Subgroup H)
    (hc : ∀ x ∈ L, ∀ y ∈ R, x * y = y * x) :
    Nat.card (L ⊔ R : Subgroup H) * Nat.card (L ⊓ R : Subgroup H) = Nat.card L * Nat.card R := by
  let μ : L × R →* H := MonoidHom.noncommCoprod L.subtype R.subtype fun x y => hc x x.2 y y.2
  have hμ : ∀ x : L × R, μ x = (x.1 : H) * x.2 := fun _ => rfl
  have hrange : μ.range = L ⊔ R := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hμ]
      exact mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)
    · refine sup_le (fun l hl => ⟨(⟨l, hl⟩, 1), by rw [hμ]; simp⟩)
        (fun r hr => ⟨(1, ⟨r, hr⟩), by rw [hμ]; simp⟩)
  have hker : Nat.card μ.ker = Nat.card (L ⊓ R : Subgroup H) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.1 : H), x.1.1.2, ?_⟩
        invFun := fun z => ⟨(⟨z, z.2.1⟩, ⟨(z : H)⁻¹, inv_mem z.2.2⟩), ?_⟩
        left_inv := fun x => ?_
        right_inv := fun z => rfl }
    · have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_eq_inv] at h
      rw [h]
      exact R.inv_mem x.1.2.2
    · rw [MonoidHom.mem_ker, hμ]
      exact mul_inv_cancel _
    · apply Subtype.ext
      have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_inv_eq] at h
      exact Prod.ext rfl (Subtype.ext h)
  have := Subgroup.card_ker_mul_card_range μ
  rw [hrange, hker, Nat.card_prod] at this
  rw [mul_comm]
  exact this

theorem pair_isElementaryAbelian_card {H : Type*} [Group H] [Finite H] {t x : H}
    (ht : orderOf t = p) (hx : orderOf x = p) (hcomm : t * x = x * t) (hxt : x ∉ zpowers t) :
    IsElementaryAbelian p (zpowers t ⊔ zpowers x : Subgroup H) ∧
      Nat.card (zpowers t ⊔ zpowers x : Subgroup H) = p ^ 2 := by
  have : IsElementaryAbelian p (zpowers t) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (ht ▸ pow_orderOf_eq_one t)
  have : IsElementaryAbelian p (zpowers x) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (hx ▸ pow_orderOf_eq_one x)
  have hc : ∀ a ∈ zpowers t, ∀ b ∈ zpowers x, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow hcomm i j).eq
  refine ⟨IsElementaryAbelian.sup_of_le_centralizer ?_, ?_⟩
  · rw [zpowers_le, mem_centralizer_iff]
    intro a ha
    exact hc a ha x (mem_zpowers x)
  · have hinf : (zpowers t ⊓ zpowers x : Subgroup H) = ⊥ := by
      have hdvd : Nat.card (zpowers t ⊓ zpowers x : Subgroup H) ∣ p := by
        rw [← hx, ← Nat.card_zpowers]
        exact card_dvd_of_le inf_le_right
      rcases (Nat.dvd_prime hp.out).mp hdvd with h | h
      · exact eq_bot_of_card_eq _ h
      · exfalso
        have heq : (zpowers t ⊓ zpowers x : Subgroup H) = zpowers x :=
          eq_of_le_of_card_ge inf_le_right (by rw [h, Nat.card_zpowers, hx])
        have hmem : x ∈ (zpowers t ⊓ zpowers x : Subgroup H) := by
          rw [heq]
          exact mem_zpowers x
        exact hxt (mem_inf.mp hmem).1
    have h := card_sup_mul_card_inf_of_commute _ _ hc
    rw [hinf, card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, ht, hx] at h
    rw [h, pow_two]

variable {G : Type*} [Group G]

theorem mem_map_center_iff {T : Subgroup G} {x : G} :
    x ∈ (center T).map T.subtype ↔ x ∈ T ∧ ∀ y ∈ T, y * x = x * y := by
  constructor
  · rintro ⟨x', hx', rfl⟩
    refine ⟨x'.2, fun y hy => ?_⟩
    exact congrArg Subtype.val (mem_center_iff.mp hx' ⟨y, hy⟩)
  · rintro ⟨hxT, hx⟩
    exact ⟨⟨x, hxT⟩, mem_center_iff.mpr fun y => Subtype.ext (hx y y.2), rfl⟩

variable [Finite G]

theorem mem_zpowers_of_pRank_center_le_one {T : Subgroup G} (hrank : pRank p (center T) ≤ 1)
    {t x : G} (ht : t ∈ (center T).map T.subtype) (hx : x ∈ (center T).map T.subtype)
    (hto : orderOf t = p) (hxo : orderOf x = p) : x ∈ zpowers t := by
  obtain ⟨t', ht'Z, rfl⟩ := mem_map.mp ht
  obtain ⟨x', hx'Z, rfl⟩ := mem_map.mp hx
  by_contra hxt
  let t'' : center T := ⟨t', ht'Z⟩
  let x'' : center T := ⟨x', hx'Z⟩
  have hto'' : orderOf t'' = p := by
    rw [← hto, Subgroup.coe_subtype, Subgroup.orderOf_coe, ← Subgroup.orderOf_coe t'']
  have hxo'' : orderOf x'' = p := by
    rw [← hxo, Subgroup.coe_subtype, Subgroup.orderOf_coe, ← Subgroup.orderOf_coe x'']
  have hcomm : t'' * x'' = x'' * t'' := Subtype.ext (mem_center_iff.mp hx'Z t')
  have hxt'' : x'' ∉ zpowers t'' := by
    rintro ⟨k, hk⟩
    apply hxt
    refine ⟨k, ?_⟩
    have := congrArg (fun z : center T => ((z : T) : G)) hk
    simpa [t'', x''] using this
  have h := pair_isElementaryAbelian_card hto'' hxo'' hcomm hxt''
  have := le_pRank_of_subgroup h.1 h.2
  omega

theorem commute_of_normalizes {T : Subgroup G} (hrank : pRank p (center T) ≤ 1) {t u : G}
    (ht : t ∈ (center T).map T.subtype) (hto : orderOf t = p)
    (hu : ∀ y ∈ T, u * y * u⁻¹ ∈ T) (hu' : ∀ y ∈ T, u⁻¹ * y * u ∈ T) {m : ℕ}
    (hum : u ^ (p ^ m) = 1) : u * t = t * u := by
  have htT := (mem_map_center_iff.mp ht)
  have hs : u * t * u⁻¹ ∈ (center T).map T.subtype := by
    refine mem_map_center_iff.mpr ⟨hu t htT.1, fun y hy => ?_⟩
    have hc := htT.2 _ (hu' y hy)
    calc y * (u * t * u⁻¹) = u * ((u⁻¹ * y * u) * t) * u⁻¹ := by group
      _ = u * (t * (u⁻¹ * y * u)) * u⁻¹ := by rw [hc]
      _ = u * t * u⁻¹ * y := by group
  have hso : orderOf (u * t * u⁻¹) = p := by
    rw [← hto]
    exact orderOf_injective (MulAut.conj u).toMonoidHom (MulAut.conj u).injective t
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp
    (mem_zpowers_of_pRank_center_le_one hrank ht hs hto hso)
  have hiter : ∀ n : ℕ, u ^ n * t * (u ^ n)⁻¹ = t ^ (k ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hc : ∀ j : ℤ, u * t ^ j * u⁻¹ = (u * t * u⁻¹) ^ j := fun j => by
        simpa only [MulAut.conj_apply] using map_zpow (MulAut.conj u) t j
      calc u ^ (n + 1) * t * (u ^ (n + 1))⁻¹ = u * (u ^ n * t * (u ^ n)⁻¹) * u⁻¹ := by group
        _ = t ^ (k ^ (n + 1)) := by rw [ih, hc, ← hk, ← zpow_mul, pow_succ, mul_comm]
  have hfix := hiter (p ^ m)
  rw [hum, one_mul, inv_one, mul_one] at hfix
  have hmod : (k : ZMod p) = 1 := by
    have h1 : t ^ (k ^ p ^ m) = t ^ (1 : ℤ) := by rw [← hfix, zpow_one]
    rw [zpow_eq_zpow_iff_modEq, hto] at h1
    have h2 := (ZMod.intCast_eq_intCast_iff _ _ p).mpr h1
    push_cast at h2
    rwa [ZMod.pow_card_pow] at h2
  have hk1 : t ^ k = t := by
    conv_rhs => rw [← zpow_one t]
    rw [zpow_eq_zpow_iff_modEq, hto]
    exact (ZMod.intCast_eq_intCast_iff _ _ p).mp (by rw [hmod, Int.cast_one])
  rw [hk1] at hk
  calc u * t = u * t * u⁻¹ * u := by group
    _ = t * u := by rw [← hk]

end RankOneCenter

open RankOneCenter Subgroup

theorem centralizer_sylow_rank_one_center {G : Type*} [Group G] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] {t : G} (ht : orderOf t = p) :
    (∀ T : Subgroup G, (∃ Q : Sylow p (centralizer ({t} : Set G)),
        (Q : Subgroup (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype = T) →
      pRank p (center T) = 1 →
        (∃ P : Sylow p G, (P : Subgroup G) = T) ∧ t ∈ (center T).map T.subtype) ∧
    ((∀ P : Sylow p G, t ∉ (center (P : Subgroup G)).map (P : Subgroup G).subtype) →
      ∀ T : Subgroup G, (∃ Q : Sylow p (centralizer ({t} : Set G)),
        (Q : Subgroup (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype = T) →
      2 ≤ pRank p (center T) ∧
        ∃ E : Subgroup G, E ≤ (center T).map T.subtype ∧ IsElementaryAbelian p E ∧
          Nat.card E = p ^ 2 ∧ t ∈ E) := by
  set C := centralizer ({t} : Set G) with hCdef
  have hcenter : ∀ T : Subgroup G, (∃ Q : Sylow p C, (Q : Subgroup C).map C.subtype = T) →
      T ≤ C ∧ t ∈ (center T).map T.subtype := by
    rintro T ⟨Q, rfl⟩
    refine ⟨map_subtype_le _, ?_⟩
    let tC : C := ⟨t, mem_centralizer_singleton_iff.mpr rfl⟩
    have htZ : tC ∈ center C := mem_center_iff.mpr fun c =>
      Subtype.ext (mem_centralizer_singleton_iff.mp c.2)
    have : (zpowers tC).Normal := normal_of_le_center (zpowers_le.mpr htZ)
    have hpC : IsPGroup p (zpowers tC) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, pow_one, ← ht, ← Subgroup.orderOf_coe tC]
    have htQ : tC ∈ (Q : Subgroup C) := hpC.le_sylow_of_normal Q (mem_zpowers tC)
    refine mem_map_center_iff.mpr ⟨⟨tC, htQ, rfl⟩, fun y hy => ?_⟩
    obtain ⟨c, -, rfl⟩ := mem_map.mp hy
    exact mem_centralizer_singleton_iff.mp c.2
  have hfirst : ∀ T : Subgroup G, (∃ Q : Sylow p C, (Q : Subgroup C).map C.subtype = T) →
      pRank p (center T) = 1 → (∃ P : Sylow p G, (P : Subgroup G) = T) := by
    rintro T ⟨Q, hQT⟩ hrank
    have hTC : T ≤ C := (hcenter T ⟨Q, hQT⟩).1
    have htZ := (hcenter T ⟨Q, hQT⟩).2
    have hTp : IsPGroup p T := by
      rw [← hQT]
      exact Q.isPGroup'.map C.subtype
    obtain ⟨P, hTP⟩ := hTp.exists_le_sylow
    refine ⟨P, ?_⟩
    by_contra hne
    have hlt : T.subgroupOf P < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun htop => hne ?_
      apply le_antisymm _ hTP
      intro g hg
      have : (⟨g, hg⟩ : P) ∈ T.subgroupOf P := htop ▸ mem_top _
      exact this
    have hnc := CFSG.LocalAnalysis.ComponentInitial.p_group_normalizer_condition
      (P := (P : Subgroup G)) P.isPGroup' hlt
    obtain ⟨u, hu_norm, hu_not⟩ := IsConcreteLE.exists_of_lt hnc
    have hconj : ∀ v ∈ normalizer ((T.subgroupOf P : Subgroup P) : Set P), ∀ y ∈ T,
        (v : G) * y * (v : G)⁻¹ ∈ T := by
      intro v hv y hy
      have := (mem_normalizer_iff.mp hv ⟨y, hTP hy⟩).mp (mem_subgroupOf.mpr hy)
      exact mem_subgroupOf.mp this
    obtain ⟨m, hm⟩ := P.isPGroup' u
    have hum : (u : G) ^ (p ^ m) = 1 := by
      rw [← Subgroup.coe_pow, hm, Subgroup.coe_one]
    have hcomm := commute_of_normalizes hrank.le htZ ht (hconj u hu_norm)
      (fun y hy => by simpa using hconj u⁻¹ (inv_mem hu_norm) y hy) hum
    have huC : (u : G) ∈ C := mem_centralizer_singleton_iff.mpr hcomm
    set N := T ⊔ zpowers (u : G) with hN
    have hNC : N ≤ C := sup_le hTC (zpowers_le.mpr huC)
    have hNP : N ≤ P := sup_le hTP (zpowers_le.mpr u.2)
    have hNp : IsPGroup p (N.subgroupOf C) :=
      (P.isPGroup'.to_le hNP).of_equiv (subgroupOfEquivOfLe hNC).symm
    have hQN : (Q : Subgroup C) ≤ N.subgroupOf C := by
      intro c hc
      exact mem_subgroupOf.mpr (le_sup_left (a := T) (hQT ▸ mem_map_of_mem _ hc))
    have heq := Q.is_maximal' hNp hQN
    have huN : (⟨u, huC⟩ : C) ∈ N.subgroupOf C :=
      mem_subgroupOf.mpr (le_sup_right (a := T) (mem_zpowers _))
    rw [heq] at huN
    apply hu_not
    rw [mem_subgroupOf, ← hQT]
    exact ⟨_, huN, rfl⟩
  refine ⟨fun T hT hrank => ⟨hfirst T hT hrank, (hcenter T hT).2⟩, ?_⟩
  intro hnot T hT
  have htZ := (hcenter T hT).2
  obtain ⟨t', ht'Z, ht't⟩ := mem_map.mp htZ
  let t'' : center T := ⟨t', ht'Z⟩
  have hto'' : orderOf t'' = p := by
    rw [← ht, ← ht't, Subgroup.coe_subtype, Subgroup.orderOf_coe, ← Subgroup.orderOf_coe t'']
  have hge1 : 1 ≤ pRank p (center T) := by
    have : IsElementaryAbelian p (zpowers t'') :=
      IsElementaryAbelian.zpowers_of_pow_eq_one (hto'' ▸ pow_orderOf_eq_one t'')
    exact le_pRank_of_subgroup this (by rw [Nat.card_zpowers, hto'', pow_one])
  have hne1 : pRank p (center T) ≠ 1 := by
    intro h1
    obtain ⟨P, hPT⟩ := hfirst T hT h1
    apply hnot P
    rw [hPT]
    exact htZ
  have hge2 : 2 ≤ pRank p (center T) := by omega
  refine ⟨hge2, ?_⟩
  obtain ⟨B, hB, hBcard⟩ := exists_subgroup_card_pRank (p := p) (center T)
  have hnotle : ¬ B ≤ zpowers t'' := by
    intro hle
    have h1 := card_le_of_le hle
    rw [hBcard, Nat.card_zpowers, hto''] at h1
    have h2 : p ^ 2 ≤ p ^ pRank p (center T) := Nat.pow_le_pow_right hp.out.pos hge2
    have h3 : p < p ^ 2 := by
      rw [pow_two]
      exact lt_mul_left hp.out.pos hp.out.one_lt
    omega
  obtain ⟨x, hxB, hxt⟩ := Set.not_subset.mp hnotle
  have hxo : orderOf x = p := by
    apply orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian x hxB)
    rintro rfl
    exact hxt (one_mem _)
  have hcomm : t'' * x = x * t'' := Subtype.ext (mem_center_iff.mp x.2 t')
  obtain ⟨hE, hEcard⟩ := pair_isElementaryAbelian_card hto'' hxo hcomm hxt
  let f : center T →* G := T.subtype.comp (center T).subtype
  have hf : Function.Injective f := T.subtype_injective.comp (center T).subtype_injective
  refine ⟨(zpowers t'' ⊔ zpowers x).map f, ?_, IsElementaryAbelian.map f, ?_, ?_⟩
  · rw [show f = T.subtype.comp (center T).subtype from rfl, ← map_map]
    exact map_mono (map_subtype_le _)
  · rw [card_map_of_injective hf, hEcard]
  · exact ⟨t'', mem_sup_left (mem_zpowers t''), ht't⟩

end CFSG.ComponentClassification.UnbalancedGS
