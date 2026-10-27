module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma21Basic
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma34Basic
public import CFSG.Open.FusionDefs
public import CFSG.Assembly.Subnormal
import CFSG.LocalAnalysis.ComponentClassification.TightEmbeddingConjugate

public section

namespace CFSG.ComponentClassification.AS76b

namespace Lemma22

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open Lemma34

variable {G : Type*} [Group G]

section Sylow

variable [Finite G]

theorem odd_card_of_forall_orderOf_ne_two {X : Subgroup G} (h : ∀ x ∈ X, orderOf x ≠ 2) :
    Odd (Nat.card X) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card X := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 2 h2
  exact h x x.2 (by rwa [Subgroup.orderOf_coe])

theorem exists_orderOf_eq_two {X : Subgroup G} (h : ¬ Odd (Nat.card X)) :
    ∃ x ∈ X, orderOf x = 2 := by
  by_contra hne
  push Not at hne
  exact h (odd_card_of_forall_orderOf_ne_two hne)

omit [Finite G] in
theorem orderOf_conj_eq (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  simpa using (MulAut.conj g).orderOf_eq x

omit [Finite G] in
theorem isPGroup_zpowers_of_orderOf_eq_two {x : G} (hx : orderOf x = 2) :
    IsPGroup 2 (zpowers x) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])

theorem exists_conj_mem_of_isSylowOf {S H : Subgroup G} (hS : IsSylowOf 2 S H) {x : G}
    (hx : x ∈ H) (h2 : IsPGroup 2 (zpowers x)) : ∃ h ∈ H, h⁻¹ * x * h ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, rfl⟩ := hS
  obtain ⟨Q', hQ'⟩ := (h2.comap_subtype (K := H)).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Q' Q
  refine ⟨(g : G)⁻¹, H.inv_mem g.2, ?_⟩
  have hx' : (⟨x, hx⟩ : H) ∈ (Q' : Subgroup H) := hQ' (by
    change (x : G) ∈ zpowers x
    exact mem_zpowers x)
  have hmem : g * ⟨x, hx⟩ * g⁻¹ ∈ (Q : Subgroup H) := by
    rw [← hg]
    change g * ⟨x, hx⟩ * g⁻¹ ∈ ((g • Q' : Sylow 2 H) : Set H)
    rw [Sylow.coe_smul, Set.mem_smul_set_iff_inv_smul_mem, MulAut.smul_def,
      MulAut.conj_inv_apply]
    simpa [mul_assoc] using (show (⟨x, hx⟩ : H) ∈ Q' from hx')
  exact ⟨_, hmem, by simp⟩

theorem exists_conj_eq_of_isSylowOf {P Q H : Subgroup G} (hP : IsSylowOf 2 P H)
    (hQ : IsSylowOf 2 Q H) : ∃ h ∈ H, Q = conj P h := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P', rfl⟩ := hP
  obtain ⟨Q', rfl⟩ := hQ
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P' Q'
  refine ⟨(g : G), g.2, ?_⟩
  rw [← hg]
  ext x
  rw [mem_conj_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    change y ∈ ((g • P' : Sylow 2 H) : Set H) at hy
    rw [Sylow.coe_smul, Set.mem_smul_set_iff_inv_smul_mem, MulAut.smul_def,
      MulAut.conj_inv_apply] at hy
    exact ⟨g⁻¹ * y * g, hy, by simp⟩
  · rintro ⟨y, hy, hyx⟩
    refine ⟨g * y * g⁻¹, ?_, ?_⟩
    · change g * y * g⁻¹ ∈ ((g • P' : Sylow 2 H) : Set H)
      rw [Sylow.coe_smul, Set.mem_smul_set_iff_inv_smul_mem, MulAut.smul_def,
        MulAut.conj_inv_apply]
      simpa [mul_assoc] using hy
    · have hyx' : (y : G) = (g : G)⁻¹ * x * g := hyx
      simp only [coe_subtype, coe_mul, coe_inv]
      rw [hyx']
      group

end Sylow

section Tight

variable [Finite G]

theorem tightlyEmbedded_of_isSylowOf {K H R : Subgroup G} (hK : TightlyEmbedded K)
    (hRK : IsSylowOf 2 R K) (hRH : IsSylowOf 2 R H) (hR : R ≠ ⊥)
    (hN : normalizer (K : Set G) ≤ normalizer (H : Set G)) : TightlyEmbedded H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRp : IsPGroup 2 R := hRH.isPGroup
  refine ⟨?_, fun g hg => ?_⟩
  ·
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hRp
    rcases n with _ | n
    · exact absurd (card_eq_one.mp (by simpa using hn)) hR
    · refine even_iff_two_dvd.mpr ((dvd_pow_self 2 (Nat.succ_ne_zero n)).trans ?_)
      rw [← hn]
      exact card_dvd_of_le hRH.le
  · by_contra hodd
    obtain ⟨s, hs, hs2⟩ := exists_orderOf_eq_two hodd
    have hsH : s ∈ H := (mem_inf.mp hs).1
    have hsg : g * s * g⁻¹ ∈ H := (mem_rightConjugate_iff H g s).mp (mem_inf.mp hs).2
    have hps := isPGroup_zpowers_of_orderOf_eq_two hs2
    have hps' : IsPGroup 2 (zpowers (g * s * g⁻¹)) := by
      apply isPGroup_zpowers_of_orderOf_eq_two
      rw [orderOf_conj_eq, hs2]
    obtain ⟨m₁, hm₁, hr₁⟩ := exists_conj_mem_of_isSylowOf hRH hsH hps
    obtain ⟨m₂, hm₂, hr₂⟩ := exists_conj_mem_of_isSylowOf hRH hsg hps'
    set y := m₂⁻¹ * g * m₁ with hy
    have hconj : y * (m₁⁻¹ * s * m₁) * y⁻¹ = m₂⁻¹ * (g * s * g⁻¹) * m₂ := by
      rw [hy]
      group
    have hr₁K : m₁⁻¹ * s * m₁ ∈ K := hRK.le hr₁
    have hr₁y : m₁⁻¹ * s * m₁ ∈ rightConjugate K y := by
      rw [mem_rightConjugate_iff, hconj]
      exact hRK.le hr₂
    have hyN : y ∈ normalizer (K : Set G) := by
      by_contra hyN
      have hoddK := hK.2 y hyN
      have hord : orderOf (m₁⁻¹ * s * m₁) = 2 := by
        rw [show m₁⁻¹ * s * m₁ = m₁⁻¹ * s * m₁⁻¹⁻¹ by rw [inv_inv], orderOf_conj_eq, hs2]
      have hdvd : 2 ∣ Nat.card (K ⊓ rightConjugate K y : Subgroup G) := by
        rw [← hord, ← Subgroup.orderOf_mk (m₁⁻¹ * s * m₁) (mem_inf.mpr ⟨hr₁K, hr₁y⟩)]
        exact orderOf_dvd_natCard _
      exact (Nat.not_even_iff_odd.mpr hoddK) (even_iff_two_dvd.mpr hdvd)
    have hyH := hN hyN
    apply hg
    have hge : g = m₂ * y * m₁⁻¹ := by rw [hy]; group
    rw [hge]
    exact mul_mem (mul_mem (le_normalizer hm₂) hyH) (inv_mem (le_normalizer hm₁))

theorem ne_bot_of_isSylowOf_of_tightlyEmbedded {K R : Subgroup G} (hK : TightlyEmbedded K)
    (hR : IsSylowOf 2 R K) : R ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hbot
  have hcard := hR.card_eq
  rw [hbot, Subgroup.card_bot] at hcard
  have h2 : 2 ∣ Nat.card K := even_iff_two_dvd.mp hK.1
  have hpos : 0 < (Nat.card K).factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2
  have : 2 ^ (Nat.card K).factorization 2 ≠ 1 :=
    (Nat.one_lt_pow hpos.ne' (by norm_num)).ne'
  exact this hcard.symm

end Tight

section Conj

theorem normalizer_le_normalizer_centralizer (L : Subgroup G) :
    normalizer (L : Set G) ≤ normalizer (centralizer (L : Set G) : Set G) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro c
  simp only [SetLike.mem_coe, mem_centralizer_iff]
  constructor
  · intro hc l hl
    have hl' : g⁻¹ * l * g ∈ L := by
      have := (mem_normalizer_iff.mp (inv_mem hg) l).mp hl
      simpa using this
    have h := hc _ hl'
    calc l * (g * c * g⁻¹) = g * ((g⁻¹ * l * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * l * g)) * g⁻¹ := by rw [h]
      _ = g * c * g⁻¹ * l := by group
  · intro hc l hl
    have hl' : g * l * g⁻¹ ∈ L := (mem_normalizer_iff.mp hg l).mp hl
    have h := hc _ hl'
    have h2 : g * (l * c) * g⁻¹ = g * (c * l) * g⁻¹ := by
      calc g * (l * c) * g⁻¹ = (g * l * g⁻¹) * (g * c * g⁻¹) := by group
        _ = (g * c * g⁻¹) * (g * l * g⁻¹) := h
        _ = g * (c * l) * g⁻¹ := by group
    simpa using h2

theorem centralizer_conj (L : Subgroup G) (g : G) :
    centralizer (conj L g : Set G) = conj (centralizer (L : Set G)) g := by
  ext c
  rw [mem_conj_iff, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro hc l hl
    have h := hc (g * l * g⁻¹) (conj_mem_conj hl)
    calc l * (g⁻¹ * c * g) = g⁻¹ * ((g * l * g⁻¹) * c) * g := by group
      _ = g⁻¹ * (c * (g * l * g⁻¹)) * g := by rw [h]
      _ = g⁻¹ * c * g * l := by group
  · intro hc x hx
    have hx' := mem_conj_iff.mp hx
    have h := hc _ hx'
    calc x * c = g * ((g⁻¹ * x * g) * (g⁻¹ * c * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * c * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
      _ = c * x := by group

theorem normalizer_conj (L : Subgroup G) (g : G) :
    normalizer (conj L g : Set G) = conj (normalizer (L : Set G)) g := by
  ext n
  rw [mem_conj_iff, ← conj_eq_self_iff, ← conj_eq_self_iff, conj_conj]
  constructor
  · intro h
    have e : conj L (g⁻¹ * n * g) = conj (conj L (n * g)) g⁻¹ := by
      rw [conj_conj]
      congr 1
      group
    rw [e, h, conj_conj, inv_mul_cancel, conj_one]
  · intro h
    have e : conj L (n * g) = conj (conj L (g⁻¹ * n * g)) g := by
      rw [conj_conj]
      congr 1
      group
    rw [e, h]

theorem tightlyEmbedded_conj {K : Subgroup G} (hK : TightlyEmbedded K) (g : G) :
    TightlyEmbedded (conj K g) := by
  have h := StandardSubgroupAPI.tightlyEmbedded_rightConjugate hK g⁻¹
  rwa [rightConjugate, inv_inv] at h

theorem isQuasisimple_of_mulEquiv {H K : Type*} [Group H] [Group K] (e : H ≃* K)
    (h : CFSG.Open.IsQuasisimple H) : CFSG.Open.IsQuasisimple K :=
  h.of_mulEquiv e.symm

theorem isQuasisimple_conj {L : Subgroup G} (hL : CFSG.Open.IsQuasisimple ↥L) (g : G) :
    CFSG.Open.IsQuasisimple ↥(conj L g) :=
  isQuasisimple_of_mulEquiv
    (L.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective) hL

end Conj

section Frattini

variable [Finite G]

theorem normalizer_centralizer_le {K R L : Subgroup G} (hK : TightlyEmbedded K)
    (hRK : IsSylowOf 2 R K) (hRL : IsSylowOf 2 R (centralizer (L : Set G))) (hR : R ≠ ⊥)
    (hNL : normalizer (K : Set G) ≤ normalizer (L : Set G)) :
    normalizer (centralizer (L : Set G) : Set G) ≤ normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer (L : Set G)
  intro x hx
  have hRx : IsSylowOf 2 (conj R x) H := by
    refine isSylowOf_of_card ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact (mem_normalizer_iff.mp hx y).mp (hRL.le hy)
    · rw [card_conj]
      exact hRL.card_eq
  obtain ⟨h, hh, hRh⟩ := exists_conj_eq_of_isSylowOf hRx hRL
  have hN : h * x ∈ normalizer (R : Set G) := by
    rw [← conj_eq_self_iff, ← conj_conj]
    exact hRh.symm
  have hNK := normalizer_two_subgroup_le K R hK hRL.isPGroup hRK.le hR hN
  have hhL : h⁻¹ ∈ normalizer (L : Set G) :=
    centralizer_le_normalizer (L : Set G) (inv_mem hh)
  have hxe : x = h⁻¹ * (h * x) := by group
  rw [hxe]
  exact mul_mem hhL (hNL hNK)

end Frattini

section Strong

variable [Finite G]

theorem four_dvd_card_of_isQuasisimple {A : Subgroup G} (hA : CFSG.Open.IsQuasisimple ↥A) :
    4 ∣ Nat.card A := by
  have : Group.IsPerfect ↥A := ⟨hA.1⟩
  have : Nontrivial ↥A := by
    obtain ⟨a, ha, b, hb, hab⟩ := exists_not_commute hA
    refine ⟨⟨⟨a, ha⟩, 1, fun h => hab ?_⟩⟩
    have : a = 1 := congrArg Subtype.val h
    rw [this, one_mul, mul_one]
  exact four_dvd_card_of_isPerfect

theorem even_card_of_isQuasisimple {A : Subgroup G} (hA : CFSG.Open.IsQuasisimple ↥A) :
    Even (Nat.card A) :=
  even_iff_two_dvd.mpr ((show (2 : ℕ) ∣ 4 by norm_num).trans (four_dvd_card_of_isQuasisimple hA))

theorem not_le_centralizer_of_isSylowOf {A S : Subgroup G} (hA : CFSG.Open.IsQuasisimple ↥A)
    (hS : IsSylowOf 2 S A) : ¬ S ≤ centralizer (A : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hSC
  set Z : Subgroup G := (center ↥A).map A.subtype
  have hSZ : S ≤ Z := by
    intro x hx
    refine ⟨⟨x, hS.le hx⟩, Subgroup.mem_center_iff.mpr fun y => ?_, rfl⟩
    apply Subtype.ext
    exact mem_centralizer_iff.mp (hSC hx) y y.2
  have hZA : Z ≤ A := map_subtype_le _
  have : Group.IsPerfect ↥A := ⟨hA.1⟩
  have : Group.IsPerfect (↥A ⧸ center ↥A) :=
    Group.IsPerfect.ofSurjective (G := ↥A) (G' := ↥A ⧸ center ↥A)
      (f := QuotientGroup.mk' (center ↥A)) (QuotientGroup.mk'_surjective _)
  have : Nontrivial (↥A ⧸ center ↥A) := hA.2.toNontrivial
  have h4 : 4 ∣ Nat.card (↥A ⧸ center ↥A) := four_dvd_card_of_isPerfect
  have hrel : Z.relIndex A = Nat.card (↥A ⧸ center ↥A) := by
    rw [Subgroup.relIndex, ← Subgroup.index_eq_card]
    congr 1
    exact Subgroup.comap_map_eq_self_of_injective A.subtype_injective _
  have hdvd : 2 ∣ S.relIndex A := by
    rw [← Subgroup.relIndex_mul_relIndex S Z A hSZ hZA, hrel]
    exact ((show (2 : ℕ) ∣ 4 by norm_num).trans h4).mul_left _
  exact ((isSylowOf_iff.mp hS).2.2) hdvd

theorem fusionStronglyEmbedded_of_tightlyEmbedded {K A S : Subgroup G} (hK : TightlyEmbedded K)
    (hS : IsSylowOf 2 S A) (hSK : S ≤ K) (hS1 : S ≠ ⊥)
    (hAK : ¬ A ≤ normalizer (K : Set G)) :
    fusionStronglyEmbedded ((A ⊓ normalizer (K : Set G)).subgroupOf A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup G := A ⊓ normalizer (K : Set G) with hM
  have hSM : S ≤ M := le_inf hS.le (hSK.trans le_normalizer)
  have hSyl : IsSylowOf 2 S M := hS.of_le hSM inf_le_left
  refine ⟨?_, ?_, fun a ha => ?_⟩
  ·
    intro htop
    apply hAK
    intro x hx
    have : (⟨x, hx⟩ : A) ∈ M.subgroupOf A := htop ▸ mem_top _
    exact (mem_inf.mp this).2
  ·
    have hcard : Nat.card (M.subgroupOf A) = Nat.card M :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : M ≤ A)).toEquiv
    rw [hcard]
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS.isPGroup
    rcases n with _ | n
    · exact absurd (card_eq_one.mp (by simpa using hn)) hS1
    · refine even_iff_two_dvd.mpr ((dvd_pow_self 2 (Nat.succ_ne_zero n)).trans ?_)
      rw [← hn]
      exact card_dvd_of_le hSM
  ·
    by_contra hodd
    obtain ⟨s, hs, hs2⟩ := exists_orderOf_eq_two hodd
    have hsM : (s : G) ∈ M := (mem_inf.mp hs).1
    have hsa : (a : G) * s * (a : G)⁻¹ ∈ M := by
      obtain ⟨t, ht, hts⟩ := (mem_inf.mp hs).2
      have ht' : (t : G) ∈ M := ht
      have : (a : G) * s * (a : G)⁻¹ = t := by
        rw [← hts]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, coe_mul, coe_inv]
        group
      rw [this]
      exact ht'
    have hs2' : orderOf (s : G) = 2 := by rwa [Subgroup.orderOf_coe]
    obtain ⟨m₁, hm₁, hr₁⟩ := exists_conj_mem_of_isSylowOf hSyl hsM
      (isPGroup_zpowers_of_orderOf_eq_two hs2')
    obtain ⟨m₂, hm₂, hr₂⟩ := exists_conj_mem_of_isSylowOf hSyl hsa
      (isPGroup_zpowers_of_orderOf_eq_two (by rw [orderOf_conj_eq, hs2']))
    set y := m₂⁻¹ * (a : G) * m₁ with hy
    have hconj : y * (m₁⁻¹ * s * m₁) * y⁻¹ = m₂⁻¹ * ((a : G) * s * (a : G)⁻¹) * m₂ := by
      rw [hy]
      group
    have hr₁K : m₁⁻¹ * s * m₁ ∈ K := hSK hr₁
    have hr₁y : m₁⁻¹ * s * m₁ ∈ rightConjugate K y := by
      rw [mem_rightConjugate_iff, hconj]
      exact hSK hr₂
    have hyN : y ∈ normalizer (K : Set G) := by
      by_contra hyN
      have hoddK := hK.2 y hyN
      have hord : orderOf (m₁⁻¹ * s * m₁) = 2 := by
        rw [show m₁⁻¹ * (s : G) * m₁ = m₁⁻¹ * s * m₁⁻¹⁻¹ by rw [inv_inv], orderOf_conj_eq, hs2']
      have hdvd : 2 ∣ Nat.card (K ⊓ rightConjugate K y : Subgroup G) := by
        rw [← hord, ← Subgroup.orderOf_mk (m₁⁻¹ * s * m₁) (mem_inf.mpr ⟨hr₁K, hr₁y⟩)]
        exact orderOf_dvd_natCard _
      exact (Nat.not_even_iff_odd.mpr hoddK) (even_iff_two_dvd.mpr hdvd)
    have hyA : y ∈ A := by
      rw [hy]
      exact mul_mem (mul_mem (inv_mem (mem_inf.mp hm₂).1) a.2) (mem_inf.mp hm₁).1
    apply ha
    show (a : G) ∈ M
    have hae : (a : G) = m₂ * y * m₁⁻¹ := by rw [hy]; group
    rw [hae]
    exact mul_mem (mul_mem hm₂ (mem_inf.mpr ⟨hyA, hyN⟩)) (inv_mem hm₁)

end Strong

end Lemma22

end CFSG.ComponentClassification.AS76b
