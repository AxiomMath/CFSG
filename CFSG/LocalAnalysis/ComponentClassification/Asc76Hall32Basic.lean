module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76XLemma311

public section

namespace CFSG.ComponentClassification.Asc76X.Hall32

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76
open CFSG.ComponentClassification.Asc76X

variable {G : Type} [Group G]

theorem le_normalizer_of_weaklyClosed {S T : Subgroup G} (hTS : T ≤ S)
    (hwc : ∀ g : G, rightConjugate T g ≤ S → rightConjugate T g = T) :
    S ≤ normalizer (T : Set G) := fun s hs => by
  rw [← rightConjugate_eq_self_iff]
  refine hwc s fun x hx => ?_
  rw [mem_rightConjugate_iff] at hx
  have e : x = s⁻¹ * (s * x * s⁻¹) * s := by group
  rw [e]
  exact mul_mem (mul_mem (inv_mem hs) (hTS hx)) hs

theorem normalizer_le_of_weaklyClosed {S T P : Subgroup G} (hTP : T ≤ P) (hPS : P ≤ S)
    (hwc : ∀ g : G, rightConjugate T g ≤ S → rightConjugate T g = T) :
    normalizer (P : Set G) ≤ normalizer (T : Set G) := fun n hn => by
  rw [← rightConjugate_eq_self_iff]
  refine hwc n fun x hx => hPS ?_
  rw [← (rightConjugate_eq_self_iff P n).mpr hn, mem_rightConjugate_iff]
  rw [mem_rightConjugate_iff] at hx
  exact hTP hx

theorem isPGroup_rightConjugate {T : Subgroup G} (hT : IsPGroup 2 T) (g : G) :
    IsPGroup 2 (rightConjugate T g) :=
  hT.map _

theorem rightConjugate_le_of_normal {M T : Subgroup G} (hMn : M.Normal) (hTM : T ≤ M) (g : G) :
    rightConjugate T g ≤ M := fun x hx => by
  rw [mem_rightConjugate_iff] at hx
  have e : x = g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ := by group
  rw [e]
  exact hMn.conj_mem _ (hTM hx) g⁻¹

variable [Finite G]

theorem exists_normalizer_mul_of_weaklyClosed {S T M : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    (hTS : T ≤ S) (hwc : ∀ g : G, rightConjugate T g ≤ S → rightConjugate T g = T)
    (hMn : M.Normal) (hTM : T ≤ M) (g : G) :
    ∃ n ∈ normalizer (T : Set G), ∃ m ∈ M, g = n * m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsSylowOf 2 (S ⊓ M) M :=
    isSylowOf_inf le_top (by rw [normalizer_eq_top_iff.mpr hMn]) hS
  have hPg : IsSylowOf 2 (rightConjugate (S ⊓ M) g) M := by
    have h := isSylowOf_rightConjugate hP g
    rwa [(rightConjugate_eq_self_iff M g).mpr
      (by rw [normalizer_eq_top_iff.mpr hMn]; exact mem_top g)] at h
  obtain ⟨m, hm, hPm⟩ := exists_conj_of_isSylowOf hP hPg
  refine ⟨g * m⁻¹, normalizer_le_of_weaklyClosed (le_inf hTS hTM) inf_le_left hwc ?_, m, hm,
    by group⟩
  rw [← rightConjugate_eq_self_iff, ← rightConjugate_mul, hPm, rightConjugate_mul, mul_inv_cancel,
    rightConjugate_one]

theorem normalClosure_subgroupOf_eq_top {S T : Subgroup G} (hS : IsSylowOf 2 S ⊤) (hTS : T ≤ S)
    (hwc : ∀ g : G, rightConjugate T g ≤ S → rightConjugate T g = T) :
    normalClosure (T.subgroupOf (normalClosure (T : Set G)) : Set ↥(normalClosure (T : Set G))) =
      ⊤ := by
  set M := normalClosure (T : Set G) with hMdef
  have hMn : M.Normal := normalClosure_normal
  have hTM : T ≤ M := subset_normalClosure
  set N := normalClosure ((T.subgroupOf M : Subgroup M) : Set M) with hNdef
  have hNn : N.Normal := normalClosure_normal
  have hMN : ∀ g : G, g ∈ normalizer (M : Set G) := fun g => by
    rw [normalizer_eq_top_iff.mpr hMn]
    exact mem_top g
  have hinv : ∀ n ∈ normalizer (T : Set G), ∀ y ∈ N, conjAutOf M (hMN n) y ∈ N := by
    intro n hn y hy
    have h1 : N.map (conjAutOf M (hMN n)).toMonoidHom ≤ N := by
      refine (map_normalClosure_le _ _).trans (normalClosure_mono ?_)
      rintro _ ⟨x, hx, rfl⟩
      show ((conjAutOf M (hMN n) x : M) : G) ∈ T
      rw [conjAutOf_apply]
      exact (mem_normalizer_iff.mp hn x).mp hx
    exact h1 ⟨y, hy, rfl⟩
  have hK : (N.map M.subtype).Normal := by
    refine ⟨fun k hk g => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hk
    obtain ⟨n, hn, m, hm, rfl⟩ := exists_normalizer_mul_of_weaklyClosed hS hTS hwc hMn hTM g
    have hy' : (⟨m, hm⟩ : M) * y * (⟨m, hm⟩ : M)⁻¹ ∈ N := hNn.conj_mem y hy _
    refine ⟨_, hinv n hn _ hy', ?_⟩
    change ((conjAutOf M (hMN n) _ : M) : G) = _
    rw [conjAutOf_apply]
    simp only [coe_mul, coe_inv, M.coe_subtype]
    group
  have hle : M ≤ N.map M.subtype := normalClosure_le_normal fun t ht =>
    ⟨⟨t, hTM ht⟩, subset_normalClosure (show (⟨t, hTM ht⟩ : M) ∈ T.subgroupOf M from ht), rfl⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hyx⟩ := hle x.2
  rwa [show x = y from Subtype.ext hyx.symm]

theorem exists_conj_of_not_stronglyClosed {S T M : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    (hTS : T ≤ S) (hwc : ∀ g : G, rightConjugate T g ≤ S → rightConjugate T g = T)
    (hMn : M.Normal) (hTM : T ≤ M) (h : ∃ t ∈ T, ∃ g : G, g⁻¹ * t * g ∈ S ∧ g⁻¹ * t * g ∉ T) :
    ∃ t ∈ T, ∃ m ∈ M, m⁻¹ * t * m ∈ S ∧ m⁻¹ * t * m ∉ T := by
  obtain ⟨t, ht, g, hgS, hgT⟩ := h
  obtain ⟨n, hn, m, hm, rfl⟩ := exists_normalizer_mul_of_weaklyClosed hS hTS hwc hMn hTM g
  have ht' : n⁻¹ * t * n ∈ T := by
    have h1 := (mem_normalizer_iff.mp (inv_mem hn) t).mp ht
    simpa using h1
  have e : m⁻¹ * (n⁻¹ * t * n) * m = (n * m)⁻¹ * t * (n * m) := by group
  exact ⟨n⁻¹ * t * n, ht', m, hm, by rw [e]; exact hgS, by rw [e]; exact hgT⟩

theorem conj_mem_of_mem_centralizer {S T : Subgroup G} (hS : IsSylowOf 2 S ⊤) (hTS : T ≤ S)
    (hTab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (hwc : ∀ g : G, rightConjugate T g ≤ S → rightConjugate T g = T) {t h : G} (ht : t ∈ T)
    (hth : h⁻¹ * t * h ∈ centralizer (T : Set G)) : h⁻¹ * t * h ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := IsPGroup.of_card (isSylowOf_iff_card.mp hS).2
  have hT2 : IsPGroup 2 T := hS2.to_le hTS
  set y := h⁻¹ * t * h with hydef
  set C := centralizer ({y} : Set G) with hCdef
  have hmemC : ∀ x, x * y = y * x → x ∈ C := fun x hx => mem_centralizer_iff.mpr fun w hw => by
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact hx.symm
  have hTC : T ≤ C := fun w hw => hmemC w (mem_centralizer_iff.mp hth w hw)
  have hThC : rightConjugate T h ≤ C := by
    intro x hx
    rw [mem_rightConjugate_iff] at hx
    apply hmemC
    have h1 := hTab _ hx _ ht
    calc x * y = h⁻¹ * ((h * x * h⁻¹) * t) * h := by rw [hydef]; group
      _ = h⁻¹ * (t * (h * x * h⁻¹)) * h := by rw [h1]
      _ = y * x := by rw [hydef]; group
  obtain ⟨Q, hQ, hTQ⟩ := exists_isSylowOf_le hTC hT2
  obtain ⟨Q', hQ', hTQ'⟩ := exists_isSylowOf_le hThC (isPGroup_rightConjugate hT2 h)
  obtain ⟨c, hc, hQc⟩ := exists_conj_of_isSylowOf hQ hQ'
  have hQ2 : IsPGroup 2 Q := IsPGroup.of_card (isSylowOf_iff_card.mp hQ).2
  obtain ⟨S', hS'', hQS'⟩ := exists_isSylowOf_le (le_top : Q ≤ ⊤) hQ2
  obtain ⟨d, -, hS'd⟩ := exists_conj_of_isSylowOf hS hS''
  have hcy : c * y * c⁻¹ = y := by
    have h1 := mem_centralizer_iff.mp hc y (Set.mem_singleton y)
    rw [← h1, mul_inv_cancel_right]
  have hd1 : rightConjugate T d⁻¹ = T := hwc _ fun x hx => by
    rw [mem_rightConjugate_iff, inv_inv] at hx
    have h1 := hQS' (hTQ hx)
    rw [hS'd, mem_rightConjugate_iff] at h1
    have e : d * (d⁻¹ * x * d) * d⁻¹ = x := by group
    rwa [e] at h1
  have hd2 : rightConjugate T (h * c⁻¹ * d⁻¹) = T := hwc _ fun x hx => by
    rw [mem_rightConjugate_iff] at hx
    set w := h * c⁻¹ * d⁻¹ * x * (h * c⁻¹ * d⁻¹)⁻¹ with hwdef
    have h1 : h⁻¹ * w * h ∈ rightConjugate T h := by
      rw [mem_rightConjugate_iff]
      have e : h * (h⁻¹ * w * h) * h⁻¹ = w := by group
      rw [e]
      exact hx
    have h2 := hTQ' h1
    rw [hQc, mem_rightConjugate_iff] at h2
    have h3 := hQS' h2
    rw [hS'd, mem_rightConjugate_iff] at h3
    have e : d * (c * (h⁻¹ * w * h) * c⁻¹) * d⁻¹ = x := by rw [hwdef]; group
    rwa [e] at h3
  have hn : h * c⁻¹ ∈ normalizer (T : Set G) := by
    rw [← rightConjugate_eq_self_iff]
    have e1 : rightConjugate T d = T := by
      have h1 := congrArg (rightConjugate · d) hd1
      simp only [rightConjugate_mul, inv_mul_cancel, rightConjugate_one] at h1
      exact h1.symm
    have h1 := congrArg (rightConjugate · d) hd2
    simp only [rightConjugate_mul, inv_mul_cancel_right] at h1
    rw [h1, e1]
  have e : y = (h * c⁻¹)⁻¹ * t * (h * c⁻¹) := by
    calc y = c * y * c⁻¹ := hcy.symm
      _ = (h * c⁻¹)⁻¹ * t * (h * c⁻¹) := by rw [hydef]; group
  rw [e]
  have h1 := (mem_normalizer_iff.mp (inv_mem hn) t).mp ht
  simpa using h1

theorem exists_conj_le_of_le_sup {X : Type} [Group X] [Finite X] {O P Q : Subgroup X}
    [O.Normal] (hO : Odd (Nat.card O)) (hP : IsPGroup 2 P) (hQ : IsPGroup 2 Q)
    (hQP : Q ≤ P ⊔ O) : ∃ y ∈ O, rightConjugate Q y ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPs : IsSylowOf 2 P (P ⊔ O) := by
    rw [isSylowOf_iff]
    refine ⟨le_sup_left, hP, fun h2 => ?_⟩
    rw [sup_comm, relIndex_sup_eq_relIndex_of_normal] at h2
    exact hO.not_two_dvd_nat (h2.trans (P.subgroupOf O).index_dvd_card)
  obtain ⟨P', hP', hQP'⟩ := exists_isSylowOf_le hQP hQ
  obtain ⟨x, hx, hP'x⟩ := exists_conj_of_isSylowOf hPs hP'
  obtain ⟨p, hp, o, ho, rfl⟩ := mem_sup_of_normal_right.mp hx
  have h1 : rightConjugate P (p * o) = rightConjugate P o := by
    rw [← rightConjugate_mul, (rightConjugate_eq_self_iff P p).mpr (le_normalizer hp)]
  refine ⟨o⁻¹, inv_mem ho, fun z hz => ?_⟩
  rw [mem_rightConjugate_iff, inv_inv] at hz
  have h2 := hQP' hz
  rw [hP'x, h1, mem_rightConjugate_iff] at h2
  have e : o * (o⁻¹ * z * o) * o⁻¹ = z := by group
  rwa [e] at h2

theorem exists_conj_le_of_bar_le {M S Q : Subgroup G} (hS : IsPGroup 2 S) (hQM : Q ≤ M)
    (hQ : IsPGroup 2 Q) (hle : bar M Q ≤ bar M S) :
    ∃ y : M, barMk M y = 1 ∧ rightConjugate Q (y : G) ≤ S := by
  have hS' : IsPGroup 2 (S.subgroupOf M) := hS.comap_of_injective M.subtype M.subtype_injective
  have hQ' : IsPGroup 2 (Q.subgroupOf M) := hQ.comap_of_injective M.subtype M.subtype_injective
  have hQP : Q.subgroupOf M ≤ S.subgroupOf M ⊔ CFSG.oddCore M := by
    intro q hq
    obtain ⟨s, hs, hsq⟩ := hle ⟨q, hq, rfl⟩
    rw [mem_sup_of_normal_right]
    refine ⟨s, hs, s⁻¹ * q, ?_, by group⟩
    rw [← ker_barMk, MonoidHom.mem_ker, map_mul, map_inv, hsq, inv_mul_cancel]
  obtain ⟨y, hy, hyQ⟩ :=
    exists_conj_le_of_le_sup (CFSG.ComponentClassification.OddCore.odd_card M) hS' hQ' hQP
  refine ⟨y, ?_, fun x hx => ?_⟩
  · rw [← MonoidHom.mem_ker, ker_barMk]
    exact hy
  · rw [mem_rightConjugate_iff] at hx
    have hxM : x ∈ M := by
      have h1 : (y : G) * x * (y : G)⁻¹ ∈ M := hQM hx
      have e : x = (y : G)⁻¹ * ((y : G) * x * (y : G)⁻¹) * y := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem y.2) h1) y.2
    have h2 : (⟨x, hxM⟩ : M) ∈ rightConjugate (Q.subgroupOf M) y := by
      rw [mem_rightConjugate_iff, mem_subgroupOf]
      simpa using hx
    exact hyQ h2

theorem mem_of_barMk_mem {M P T : Subgroup G} (hP : IsPGroup 2 P) (hTP : T ≤ P) {x : M}
    (hxP : (x : G) ∈ P) (hx : barMk M x ∈ bar M T) : (x : G) ∈ T := by
  obtain ⟨t, ht, htx⟩ := hx
  have h1 : barMk M (t⁻¹ * x) = 1 := by rw [map_mul, map_inv, htx, inv_mul_cancel]
  obtain ⟨k, hk⟩ := hP ⟨(t : G)⁻¹ * x, mul_mem (inv_mem (hTP ht)) hxP⟩
  have hk' : (t⁻¹ * x) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
  have h2 := eq_one_of_two_element_of_ker (barMk M) (odd_card_ker_barMk M) hk' h1
  rw [show x = t from (inv_mul_eq_one.mp h2).symm]
  exact ht

theorem bar_weaklyClosed {M S T : Subgroup G} (hS : IsPGroup 2 S) (hMn : M.Normal) (hTM : T ≤ M)
    (hT : IsPGroup 2 T) (hwc : ∀ g : G, rightConjugate T g ≤ S → rightConjugate T g = T) :
    ∀ g : BarGroup M, rightConjugate (bar M T) g ≤ bar M S →
      rightConjugate (bar M T) g = bar M T := by
  intro g hg
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore M) g
  have e1 : rightConjugate (bar M T) (QuotientGroup.mk' (CFSG.oddCore M) m) =
      bar M (rightConjugate T m) := (bar_rightConjugate M T m).symm
  rw [e1] at hg ⊢
  obtain ⟨y, hy1, hy⟩ := exists_conj_le_of_bar_le hS (rightConjugate_le_of_normal hMn hTM m)
    (isPGroup_rightConjugate hT m) hg
  rw [rightConjugate_mul] at hy
  have h1 := hwc _ hy
  have h2 : bar M (rightConjugate T ((m * y : M) : G)) = bar M (rightConjugate T m) := by
    rw [bar_rightConjugate, bar_rightConjugate, map_mul, hy1, mul_one]
  rw [← h2, coe_mul, h1]

theorem bar_stronglyClosed {M S T : Subgroup G} (hS : IsPGroup 2 S) (hTS : T ≤ S)
    (hsc : ∀ t ∈ T, ∀ g : G, g⁻¹ * t * g ∈ S → g⁻¹ * t * g ∈ T) :
    ∀ x ∈ bar M T, ∀ g : BarGroup M, g⁻¹ * x * g ∈ bar M S → g⁻¹ * x * g ∈ bar M T := by
  intro x hx g hg
  obtain ⟨t, ht, rfl⟩ := hx
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore M) g
  have hw : (QuotientGroup.mk' (CFSG.oddCore M) m)⁻¹ * barMk M t *
      QuotientGroup.mk' (CFSG.oddCore M) m = barMk M (m⁻¹ * t * m) := by
    rw [map_mul, map_mul, map_inv]
  rw [hw] at hg ⊢
  set w : M := m⁻¹ * t * m with hwdef
  obtain ⟨k, hk⟩ := hS ⟨t, hTS ht⟩
  have htk : (t : G) ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hwk : (w : G) ^ (2 ^ k) = 1 := by
    have e := conj_pow (a := (m : G)⁻¹) (b := (t : G)) (i := 2 ^ k)
    rw [inv_inv] at e
    simp only [hwdef, coe_mul, coe_inv]
    rw [e, htk, mul_one, inv_mul_cancel]
  have hQS : bar M (zpowers (w : G)) ≤ bar M S := by
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (mem_subgroupOf.mp hq)
    have e : q = w ^ j := Subtype.ext (by rw [coe_zpow]; exact hj.symm)
    rw [e, map_zpow]
    exact zpow_mem hg j
  obtain ⟨y, hy1, hyS⟩ := exists_conj_le_of_bar_le hS (zpowers_le.mpr w.2)
    (isPGroup_zpowers_of_two_element hwk) hQS
  have h1 : ((m * y : M) : G)⁻¹ * t * ((m * y : M) : G) ∈ S := by
    have h2 : (y : G)⁻¹ * w * y ∈ rightConjugate (zpowers (w : G)) y := by
      rw [mem_rightConjugate_iff]
      have e : (y : G) * ((y : G)⁻¹ * w * y) * (y : G)⁻¹ = w := by group
      rw [e]
      exact mem_zpowers _
    have e : ((m * y : M) : G)⁻¹ * t * ((m * y : M) : G) = (y : G)⁻¹ * w * y := by
      simp only [hwdef, coe_mul, coe_inv]
      group
    rw [e]
    exact hyS h2
  refine ⟨(m * y)⁻¹ * t * (m * y), hsc t ht _ h1, ?_⟩
  rw [map_mul, map_mul, map_inv, map_mul, hy1, mul_one, map_mul, map_mul, map_inv]

theorem bar_not_stronglyClosed {M S T : Subgroup G} (hS : IsPGroup 2 S) (hTS : T ≤ S)
    (hTM : T ≤ M) {t m : G} (ht : t ∈ T) (hm : m ∈ M) (hmS : m⁻¹ * t * m ∈ S)
    (hmT : m⁻¹ * t * m ∉ T) :
    ∃ x ∈ bar M T, ∃ g : BarGroup M, g⁻¹ * x * g ∈ bar M S ∧ g⁻¹ * x * g ∉ bar M T := by
  refine ⟨barMk M ⟨t, hTM ht⟩, barMk_mem_bar ht, barMk M ⟨m, hm⟩, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  exact ⟨barMk_mem_bar hmS, fun h => hmT (mem_of_barMk_mem hS hTS hmS h)⟩

theorem isSylowOf_bar {M S : Subgroup G} (hMn : M.Normal) (hS : IsSylowOf 2 S ⊤) :
    IsSylowOf 2 (bar M S) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSM : IsSylowOf 2 (S ⊓ M) M :=
    isSylowOf_inf le_top (by rw [normalizer_eq_top_iff.mpr hMn]) hS
  have hS2 : IsPGroup 2 ↥(S ⊓ M) := hSM.isPGroup
  have e : bar M S = bar M (S ⊓ M) := by
    unfold bar
    congr 1
    ext x
    simp [mem_subgroupOf]
  rw [isSylowOf_iff_card]
  refine ⟨le_top, ?_⟩
  rw [e, card_bar_of_pGroup inf_le_right hS2, (isSylowOf_iff_card.mp hSM).2, ← bar_self M,
    factorization_card_bar le_rfl]

omit [Finite G] in
theorem normalClosure_bar_eq_top {M T : Subgroup G}
    (h : normalClosure ((T.subgroupOf M : Subgroup M) : Set M) = ⊤) :
    normalClosure ((bar M T : Subgroup (BarGroup M)) : Set (BarGroup M)) = ⊤ := by
  rw [bar, coe_map, ← map_normalClosure _ _ (QuotientGroup.mk'_surjective _), h,
    ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]

theorem eq_bot_of_normal_of_odd_bar (M : Subgroup G) (N : Subgroup (BarGroup M)) (hN : N.Normal)
    (hodd : Odd (Nat.card N)) : N = ⊥ := by
  rw [eq_bot_iff, ← oddCore_quotient_oddCore M]
  exact le_sSup ⟨hN, hodd⟩

theorem inf_centralizer_le_of_bar {M S T : Subgroup G} (hS : IsPGroup 2 S) (hTS : T ≤ S)
    (h : bar M S ⊓ centralizer (bar M T : Set (BarGroup M)) = bar M T) :
    S ⊓ M ⊓ centralizer (T : Set G) ≤ T := by
  intro x hx
  rw [mem_inf, mem_inf] at hx
  obtain ⟨⟨hxS, hxM⟩, hxC⟩ := hx
  have h1 : barMk M ⟨x, hxM⟩ ∈ bar M S ⊓ centralizer (bar M T : Set (BarGroup M)) := by
    refine mem_inf.mpr ⟨barMk_mem_bar hxS, ?_⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_iff.mp hxC t ht)
  rw [h] at h1
  exact mem_of_barMk_mem hS hTS hxS h1

end CFSG.ComponentClassification.Asc76X.Hall32
