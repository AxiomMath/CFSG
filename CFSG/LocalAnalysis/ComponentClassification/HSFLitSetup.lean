module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerSemidihedralTwoComponents

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise

structure Config {X : Type} [Group X] (t : X) (L : Subgroup X) : Prop where
  orderOf_eq : orderOf t = 2
  le_centralizer : L ≤ centralizer ({t} : Set X)
  isPComponent : IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set X)))
  isSimpleGroup : IsSimpleGroup (L ⧸ pPrimeCore 2 L)
  pRank_eq : pRank 2 (L ⧸ pPrimeCore 2 L) = 2
  exists_sylow : ∃ P : Sylow 2 (L ⧸ pPrimeCore 2 L),
    Nat.card (P : Subgroup (L ⧸ pPrimeCore 2 L)) = 8
  isCyclic : ∀ P : Sylow 2 ↥(coreActionKernel L), IsCyclic (P : Subgroup ↥(coreActionKernel L))

variable {X : Type} [Group X] {t : X} {L : Subgroup X}

namespace Config

theorem card_sylow [Finite X] (h : Config t L) (P : Sylow 2 (L ⧸ pPrimeCore 2 L)) :
    Nat.card (P : Subgroup (L ⧸ pPrimeCore 2 L)) = 8 := by
  obtain ⟨Q, hQ⟩ := h.exists_sylow
  rw [← hQ]
  exact Nat.card_congr (Sylow.equiv P Q).toEquiv

theorem eight_dvd_card (h : Config t L) : 8 ∣ Nat.card (L ⧸ pPrimeCore 2 L) := by
  obtain ⟨Q, hQ⟩ := h.exists_sylow
  rw [← hQ]
  exact Subgroup.card_subgroup_dvd_card _

theorem quot_nonabelian [Finite X] (h : Config t L) :
    ∃ a b : L ⧸ pPrimeCore 2 L, a * b ≠ b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs := h.isSimpleGroup
  by_contra hcomm
  push Not at hcomm
  have hnormal : ∀ K : Subgroup (L ⧸ pPrimeCore 2 L), K.Normal := fun K =>
    ⟨fun n hn g => by rw [hcomm g n, mul_inv_cancel_right]; exact hn⟩
  obtain ⟨Q, hQ⟩ := h.exists_sylow
  rcases (hnormal (Q : Subgroup _)).eq_bot_or_eq_top with hb | ht
  · rw [hb, card_bot] at hQ
    exact absurd hQ (by norm_num)
  · have h8 : Nat.card (L ⧸ pPrimeCore 2 L) = 8 := by
      rw [← hQ, ht, card_top]
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := L ⧸ pPrimeCore 2 L) 2
      (by rw [h8]; norm_num)
    rcases (hnormal (zpowers g)).eq_bot_or_eq_top with hb | ht'
    · have : g = 1 := by
        have hg1 : g ∈ zpowers g := mem_zpowers g
        rw [hb] at hg1
        exact hg1
      rw [this, orderOf_one] at hg
      exact absurd hg (by norm_num)
    · have := Nat.card_zpowers g
      rw [ht', card_top, h8, hg] at this
      exact absurd this (by norm_num)

theorem center_quot_eq_bot [Finite X] (h : Config t L) : center (L ⧸ pPrimeCore 2 L) = ⊥ := by
  have hs := h.isSimpleGroup
  rcases (inferInstance : (center (L ⧸ pPrimeCore 2 L)).Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · exfalso
    obtain ⟨a, b, hab⟩ := h.quot_nonabelian
    have ha : a ∈ center (L ⧸ pPrimeCore 2 L) := by rw [ht]; exact mem_top a
    exact hab ((mem_center_iff.mp ha b).symm)

theorem odd_card_pPrimeCore [Finite X] : Odd (Nat.card (pPrimeCore 2 L)) := by
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 L)) := pPrimeCore_coprime_card
  exact Nat.odd_iff.mpr (by
    rcases Nat.even_or_odd (Nat.card (pPrimeCore 2 L)) with he | ho
    · exfalso
      have h2 : 2 ∣ Nat.card (pPrimeCore 2 L) := even_iff_two_dvd.mp he
      have := Nat.Coprime.eq_one_of_dvd hcop h2
      norm_num at this
    · exact Nat.odd_iff.mp ho)

theorem not_mem [Finite X] (h : Config t L) : t ∉ L := by
  intro htL
  set t' : L := ⟨t, htL⟩ with ht'
  have hcent : t' ∈ center L := by
    rw [mem_center_iff]
    intro g
    apply Subtype.ext
    exact (mem_centralizer_singleton_iff.mp (h.le_centralizer g.2))
  have hcentq : (QuotientGroup.mk t' : L ⧸ pPrimeCore 2 L) ∈ center (L ⧸ pPrimeCore 2 L) := by
    rw [mem_center_iff]
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.mp hcent g]
  rw [h.center_quot_eq_bot, mem_bot, QuotientGroup.eq_one_iff] at hcentq
  have hdvd : orderOf t' ∣ Nat.card (pPrimeCore 2 L) := by
    have := Subgroup.orderOf_dvd_natCard (pPrimeCore 2 L) hcentq
    exact this
  have h2 : orderOf t' = 2 := by
    rw [ht', Subgroup.orderOf_mk]
    exact h.orderOf_eq
  rw [h2] at hdvd
  exact (Nat.not_even_iff_odd.mpr odd_card_pPrimeCore) (even_iff_two_dvd.mpr hdvd)

theorem isSubnormal (h : Config t L) :
    (L.subgroupOf (centralizer ({t} : Set X))).IsSubnormal := by
  obtain ⟨-, -, hsub, -⟩ := h.isPComponent
  exact hsub

theorem card_quot_dvd [Finite X] : Nat.card (L ⧸ pPrimeCore 2 L) ∣ Nat.card L := by
  rw [← Subgroup.index_eq_card]
  exact Subgroup.index_dvd_card _

theorem card_dvd_centralizer [Finite X] (h : Config t L) :
    Nat.card L ∣ Nat.card (centralizer ({t} : Set X)) :=
  Subgroup.card_dvd_of_le h.le_centralizer

theorem card_quot_dvd_centralizer [Finite X] (h : Config t L) :
    Nat.card (L ⧸ pPrimeCore 2 L) ∣ Nat.card (centralizer ({t} : Set X)) :=
  card_quot_dvd.trans h.card_dvd_centralizer

theorem ne_bot [Finite X] (h : Config t L) : L ≠ ⊥ := by
  intro hL
  have h8 := h.eight_dvd_card
  have h1 : Nat.card L = 1 := by rw [hL, card_bot]
  have := Nat.eq_one_of_dvd_one (h1 ▸ (card_quot_dvd (L := L)))
  rw [this] at h8
  norm_num at h8

private theorem card_sup_eq_mul {G : Type*} [Group G] {N H : Subgroup G}
    (hle : H ≤ normalizer (N : Set G)) (hdisj : N ⊓ H = ⊥) :
    Nat.card (N ⊔ H : Subgroup G) = Nat.card N * Nat.card H := by
  rw [← Nat.card_prod]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun p : N × H => (⟨p.1 * p.2, mul_mem_sup p.1.2 p.2.2⟩ : (N ⊔ H : Subgroup G))) ⟨?_, ?_⟩)
  · rintro ⟨n, k⟩ ⟨n', k'⟩ he
    have he' : (n : G) * k = n' * k' := congrArg Subtype.val he
    have hmem : (n' : G)⁻¹ * n ∈ N ⊓ H := by
      refine ⟨N.mul_mem (N.inv_mem n'.2) n.2, ?_⟩
      have heq : (n' : G)⁻¹ * n = k' * (k : G)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← he', mul_inv_cancel_right]
      rw [heq]
      exact H.mul_mem k'.2 (H.inv_mem k.2)
    rw [hdisj, mem_bot, inv_mul_eq_one] at hmem
    have hn : n' = n := Subtype.ext hmem
    subst hn
    rw [Subtype.ext (mul_left_cancel he')]
  · rintro ⟨g, hg⟩
    have hg' : g ∈ (N : Set G) * (H : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left N H hle]
      exact hg
    obtain ⟨n, hn, k, hk, rfl⟩ := hg'
    exact ⟨(⟨n, hn⟩, ⟨k, hk⟩), rfl⟩

theorem pRank_eq_two [Finite X] (h : Config t L) : Open.pRank 2 (⊤ : Subgroup L) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := SectionRank.pRank_quotient_eq (G := L) (p := 2) (pPrimeCore 2 L) (by
    intro hdvd
    exact (Nat.not_even_iff_odd.mpr odd_card_pPrimeCore) (even_iff_two_dvd.mpr hdvd))
  rw [← h1, ← SectionRank.pRank_eq_open_pRank_top]
  exact h.pRank_eq

theorem three_le_twoRank [Finite X] (h : Config t L) : 3 ≤ Open.twoRank X := by
  obtain ⟨E, -, hE, hcard⟩ := SectionRank.exists_pRank (p := 2) (by norm_num) (⊤ : Subgroup L)
  rw [h.pRank_eq_two] at hcard
  set E' : Subgroup X := E.map L.subtype with hE'
  have hE'L : E' ≤ L := by
    rintro _ ⟨e, -, rfl⟩
    exact e.2
  have hcardE' : Nat.card E' = 4 := by
    rw [hE', card_map_of_injective L.subtype_injective, hcard]
    norm_num
  have ht2 : t ^ 2 = 1 := by rw [← h.orderOf_eq, pow_orderOf_eq_one]
  have hcomm : ∀ e ∈ E', e * t = t * e := fun e he =>
    mem_centralizer_singleton_iff.mp (h.le_centralizer (hE'L he))
  have htC : t ∈ centralizer (E' : Set X) :=
    mem_centralizer_iff.mpr fun e he => hcomm e he
  have hle : zpowers t ≤ normalizer (E' : Set X) :=
    zpowers_le.mpr (centralizer_le_normalizer _ htC)
  have hpow : ∀ k : ℤ, t ^ k = 1 ∨ t ^ k = t := by
    intro k
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · left
      rw [zpow_mul, show t ^ (2 : ℤ) = 1 by exact_mod_cast ht2, one_zpow]
    · right
      rw [zpow_add, zpow_mul, show t ^ (2 : ℤ) = 1 by exact_mod_cast ht2, one_zpow, one_mul,
        zpow_one]
  have hdisj : E' ⊓ zpowers t = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyE, hyt⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hyt
    rcases hpow k with h1 | h1
    · rw [h1]
      exact one_mem _
    · rw [h1] at hyE
      exact absurd (hE'L hyE) h.not_mem
  have hcardF : Nat.card (E' ⊔ zpowers t : Subgroup X) = 2 ^ 3 := by
    rw [card_sup_eq_mul hle hdisj, hcardE', Nat.card_zpowers, h.orderOf_eq]
    norm_num
  have hform : ∀ x ∈ E' ⊔ zpowers t, ∃ e ∈ E', x = e ∨ x = e * t := by
    intro x hx
    have hx' : x ∈ (E' : Set X) * (zpowers t : Set X) := by
      rw [← coe_mul_of_right_le_normalizer_left E' _ hle]
      exact hx
    obtain ⟨e, he, s, hs, rfl⟩ := hx'
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hs
    refine ⟨e, he, ?_⟩
    rcases hpow k with h1 | h1
    · left
      change e * t ^ k = e
      rw [h1, mul_one]
    · right
      change e * t ^ k = e * t
      rw [h1]
  have hEcomm : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have := hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg (fun x : E => ((x : L) : X)) this
  have hEsq : ∀ a ∈ E', a ^ 2 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    have := hE.2 a ha
    simp only [coe_subtype]
    exact congrArg Subtype.val this
  have hF : Open.IsElemAbelian 2 (E' ⊔ zpowers t) := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a, ha, hx⟩ := hform x x.2
      obtain ⟨b, hb, hy⟩ := hform y y.2
      have hab : Commute a b := hEcomm a ha b hb
      have hat : Commute a t := hcomm a ha
      have hbt : Commute b t := hcomm b hb
      simp only [coe_mul]
      rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy]
      · exact hab.eq
      · exact (hab.mul_right hat).eq
      · exact (hab.mul_left hbt.symm).eq
      · exact ((hab.mul_right hat).mul_left (hbt.symm.mul_right (Commute.refl t))).eq
    · obtain ⟨a, ha, hx⟩ := hform x hx
      rcases hx with rfl | rfl
      · exact hEsq x ha
      · rw [(show Commute a t from hcomm a ha).mul_pow, hEsq a ha, ht2, one_mul]
  exact SectionRank.le_pRank (by norm_num) le_top hF hcardF

end Config

end CFSG.ComponentClassification.HSFLit
