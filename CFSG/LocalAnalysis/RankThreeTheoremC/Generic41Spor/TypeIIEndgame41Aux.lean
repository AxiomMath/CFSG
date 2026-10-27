module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Open.GLBDefs
import CFSG.LocalAnalysis.AGLEmbedding.Signalizer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup

theorem eg41_zpowers_eq_of_mem {p : ℕ} (hp : p.Prime) {Y : Type*} [Group Y] {a x : Y}
    (hx : orderOf x = p) (hax : a ∈ zpowers x) (ha1 : a ≠ 1) : zpowers a = zpowers x := by
  have hdvd : orderOf a ∣ p := by
    have := Subgroup.orderOf_dvd_natCard (zpowers x) hax
    rwa [Nat.card_zpowers, hx] at this
  have hord : orderOf a = p := by
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ha1
    · exact h
  have : Finite (zpowers x) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hx]; exact hp.ne_zero)
  refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hax) ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, hx, hord]

section Fin

variable {Y : Type*} [Group Y] [Finite Y]

omit [Finite Y] in
theorem eg41_eq_bot_of_normalized_coprime {p : ℕ} (hcore : primeComplementCore (G := Y) p = ⊥)
    {O : Subgroup Y} (hcop : Nat.Coprime p (Nat.card O)) (hn : ∀ g : Y, ∀ o ∈ O, g * o * g⁻¹ ∈ O) :
    O = ⊥ := by
  have hnormal : O.Normal := ⟨fun o ho g => hn g o ho⟩
  have := normal_coprime_le_primeComplementCore p O hnormal hcop
  rwa [hcore, le_bot_iff] at this

private theorem eg41_eq_bot_of_normal_in_normal {p : ℕ}
    (hcore : primeComplementCore (G := Y) p = ⊥)
    {C D : Subgroup Y} [C.Normal] (hDC : D ≤ C) (hcop : Nat.Coprime p (Nat.card D))
    (hn : ∀ c ∈ C, ∀ d ∈ D, c * d * c⁻¹ ∈ D) : D = ⊥ := by
  set A : Subgroup C := primeComplementCore (G := C) p with hA
  have : A.Characteristic := primeComplementCore_characteristic p
  have hD' : (D.subgroupOf C).Normal :=
    ⟨fun d hd c => Subgroup.mem_subgroupOf.mpr (hn c c.2 d (Subgroup.mem_subgroupOf.mp hd))⟩
  have hDA : D.subgroupOf C ≤ A := by
    refine normal_coprime_le_primeComplementCore p _ hD' ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv]
    exact hcop
  have hAn : (A.map C.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
  have hAcop : Nat.Coprime p (Nat.card (A.map C.subtype)) := by
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact primeComplementCore_coprime p
  have hAbot : A.map C.subtype = ⊥ := by
    have := normal_coprime_le_primeComplementCore p _ hAn hAcop
    rwa [hcore, le_bot_iff] at this
  rw [eq_bot_iff]
  intro d hd
  have h1 : (⟨d, hDC hd⟩ : C) ∈ A := hDA (Subgroup.mem_subgroupOf.mpr hd)
  have h2 : d ∈ A.map C.subtype := ⟨⟨d, hDC hd⟩, h1, rfl⟩
  rw [hAbot] at h2
  exact h2

theorem eg41_centralizes_of_normal_centralizer {p : ℕ} [Fact p.Prime]
    (hcore : primeComplementCore (G := Y) p = ⊥)
    {Γ O K S R : Subgroup Y} {x : Y} (hxo : orderOf x = p) (hcop : Nat.Coprime p (Nat.card O))
    (hOΓ : ∀ g ∈ Γ, ∀ o ∈ O, g * o * g⁻¹ ∈ O) (hxΓ : x ∈ Γ) (hKn : K.Normal)
    (hKC : K ≤ centralizer ({x} : Set Y)) (hKΓ : ¬ K ≤ Γ) (hSyl : IsSylowOf p S ⊤)
    (hΩ : ∀ s ∈ S, s ^ p = 1 → s ∈ R)
    (hothers : ∀ a ∈ R, a ≠ 1 → zpowers a ≠ zpowers x → centralizer ({a} : Set Y) ≤ Γ) :
    ∀ o ∈ O, o * x = x * o := by
  have hx3 : x ^ p = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  intro o ho
  have hdO : o * x * o⁻¹ * x⁻¹ ∈ O := by
    have := O.mul_mem ho (hOΓ x hxΓ o⁻¹ (O.inv_mem ho))
    simpa [mul_assoc] using this
  have hfin : o * x * o⁻¹ * x⁻¹ = 1 → o * x = x * o := fun h => by
    have h1 : o * x * o⁻¹ = x := mul_inv_eq_one.mp h
    calc o * x = (o * x * o⁻¹) * o := by group
      _ = x * o := by rw [h1]
  by_cases hxK : x ∈ K
  ·
    have hc : o * x * o⁻¹ ∈ K := hKn.conj_mem x hxK o
    have hcx : (o * x * o⁻¹) * x = x * (o * x * o⁻¹) := mem_centralizer_singleton_iff.mp (hKC hc)
    apply hfin
    have hcomm : Commute (o * x * o⁻¹) x⁻¹ := by
      have : Commute (o * x * o⁻¹) x := hcx
      exact this.inv_right
    have hc3 : (o * x * o⁻¹) ^ p = 1 := by rw [conj_pow, hx3, mul_one, mul_inv_cancel]
    have hg3 : (o * x * o⁻¹ * x⁻¹) ^ p = 1 := by
      rw [hcomm.mul_pow, hc3, inv_pow, hx3, inv_one, one_mul]
    have hord : orderOf (o * x * o⁻¹ * x⁻¹) ∣ p := orderOf_dvd_of_pow_eq_one hg3
    have hord2 : orderOf (o * x * o⁻¹ * x⁻¹) ∣ Nat.card O := by
      have := orderOf_dvd_natCard (⟨_, hdO⟩ : O)
      rwa [Subgroup.orderOf_mk] at this
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hord hord2)
  ·
    have hpK : p ∣ Nat.card K := by
      by_contra h3
      have hKcop : Nat.Coprime p (Nat.card K) :=
        (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr h3
      have := normal_coprime_le_primeComplementCore p K hKn hKcop
      rw [hcore] at this
      exact hKΓ (this.trans bot_le)
    obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := K) p hpK
    have hko : orderOf (k : Y) = p := (Subgroup.orderOf_coe k).trans hk
    obtain ⟨Q, hQ⟩ : ∃ Q : Sylow p Y, (Q : Subgroup Y) = S := by
      obtain ⟨-, hp, hdvd⟩ := isSylowOf_iff.1 hSyl
      rw [Subgroup.relIndex_top_right] at hdvd
      exact ⟨hp.toSylow hdvd, IsPGroup.toSylow_coe _ _⟩
    have hkp : IsPGroup p (zpowers (k : Y)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hko, pow_one])
    obtain ⟨Q', hQ'⟩ := hkp.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y Q Q'
    have hkQ' : (k : Y) ∈ ((g • Q : Sylow p Y) : Subgroup Y) := by
      rw [hg]
      exact hQ' (mem_zpowers _)
    rw [Sylow.coe_subgroup_smul, hQ, Subgroup.mem_smul_pointwise_iff_exists] at hkQ'
    obtain ⟨a, haS, hak⟩ := hkQ'
    have hak2 : g * a * g⁻¹ = (k : Y) := by
      simpa [MulAut.smul_def, MulAut.conj_apply] using hak
    have hak' : a = g⁻¹ * (k : Y) * g := by
      rw [← hak2]
      group
    have haK : a ∈ K := by
      rw [hak']
      simpa using hKn.conj_mem (k : Y) k.2 g⁻¹
    have ha3 : a ^ p = 1 := by
      have h1 : (g⁻¹ * (k : Y) * g) ^ p = g⁻¹ * (k : Y) ^ p * g := by
        simpa using conj_pow (a := g⁻¹) (b := (k : Y)) (i := p)
      have hk3 : (k : Y) ^ p = 1 := by rw [← hko]; exact pow_orderOf_eq_one _
      rw [hak', h1, hk3]
      group
    have haR : a ∈ R := hΩ a haS ha3
    have ha1 : a ≠ 1 := by
      intro h1
      rw [h1] at hak2
      have : (k : Y) = 1 := by simpa using hak2.symm
      rw [this, orderOf_one] at hko
      exact (Fact.out : p.Prime).one_lt.ne' hko.symm
    have hax : zpowers a ≠ zpowers x := by
      intro h
      apply hxK
      have : x ∈ zpowers a := h ▸ mem_zpowers x
      exact zpowers_le.mpr haK this
    have hCa := hothers a haR ha1 hax
    have hCK : centralizer (K : Set Y) ≤ Γ :=
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haK)).trans hCa
    have hCn : (centralizer (K : Set Y)).Normal := ⟨fun c hc y => by
      rw [mem_centralizer_iff]
      intro k hk
      have h1 : (y⁻¹ * k * y) * c = c * (y⁻¹ * k * y) := by
        have := mem_centralizer_iff.mp hc (y⁻¹ * k * y) (by simpa using hKn.conj_mem k hk y⁻¹)
        exact this
      calc k * (y * c * y⁻¹) = y * ((y⁻¹ * k * y) * c) * y⁻¹ := by group
        _ = y * (c * (y⁻¹ * k * y)) * y⁻¹ := by rw [h1]
        _ = y * c * y⁻¹ * k := by group⟩
    have hxC : x ∈ centralizer (K : Set Y) := by
      rw [mem_centralizer_iff]
      intro k hk
      exact mem_centralizer_singleton_iff.mp (hKC hk)
    have hdC : o * x * o⁻¹ * x⁻¹ ∈ centralizer (K : Set Y) :=
      Subgroup.mul_mem _ (hCn.conj_mem x hxC o) (Subgroup.inv_mem _ hxC)
    have hDbot : O ⊓ centralizer (K : Set Y) = ⊥ := by
      refine eg41_eq_bot_of_normal_in_normal hcore (C := centralizer (K : Set Y)) inf_le_right
        (hcop.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)) ?_
      intro c hc δ hδ
      exact ⟨hOΓ c (hCK hc) δ hδ.1, hCn.conj_mem δ hδ.2 c⟩
    exact hfin (by simpa using (Subgroup.mem_bot.mp (hDbot ▸ (⟨hdO, hdC⟩ :
      o * x * o⁻¹ * x⁻¹ ∈ O ⊓ centralizer (K : Set Y)))))

end Fin

theorem eg41_mem_glbPrimeCore_of_mk_eq_one {p : ℕ} {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {r : G} (hr : r ∈ H)
    (h : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨r, hr⟩ = 1) :
    r ∈ GLBPrimeCore p H := by
  have h1 : (⟨r, hr⟩ : H) ∈ primeComplementCore (G := H) p := (QuotientGroup.eq_one_iff _).mp h
  rw [← glbPrimeCore_subgroupOf] at h1
  exact Subgroup.mem_subgroupOf.mp h1

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
