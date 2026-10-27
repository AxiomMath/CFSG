module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalDefs

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.RankTwoStandard
open CFSG.Quasithin (perfectCore derivedSeriesOf)
open scoped commutatorElement

section PerfectCore

variable {G : Type*} [Group G]

theorem mem_perfectCore_iff {H : Subgroup G} {x : G} :
    x ∈ perfectCore H ↔ ∀ j, x ∈ derivedSeriesOf H j :=
  Subgroup.mem_iInf

theorem conj_mem_perfectCore {C : Subgroup G} {c l : G} (hc : c ∈ C)
    (hl : l ∈ perfectCore C) : c * l * c⁻¹ ∈ perfectCore C := by
  have h := (CFSG.Quasithin.perfectCore_normal C).conj_mem
    ⟨l, CFSG.Quasithin.perfectCore_le C hl⟩ (Subgroup.mem_subgroupOf.2 hl) ⟨c, hc⟩
  exact Subgroup.mem_subgroupOf.1 h

theorem commutatorElement_mem_perfectCore {C : Subgroup G} {c l : G} (hc : c ∈ C)
    (hl : l ∈ perfectCore C) : ⁅c, l⁆ ∈ perfectCore C := by
  rw [commutatorElement_def]
  exact mul_mem (conj_mem_perfectCore hc hl) (inv_mem hl)

theorem commutatorElement_mem_perfectCore' {C : Subgroup G} {c l : G} (hc : c ∈ C)
    (hl : l ∈ perfectCore C) : ⁅l, c⁆ ∈ perfectCore C := by
  rw [commutatorElement_def, show l * c * l⁻¹ * c⁻¹ = l * (c * l⁻¹ * c⁻¹) by group]
  exact mul_mem hl (conj_mem_perfectCore hc (inv_mem hl))

theorem map_mem_perfectCore_of_le {P : Type*} [Group P] (φ : G →* P) {C : Subgroup G}
    {K : Subgroup P} (hle : C.map φ ≤ K) {t : G} (ht : t ∈ perfectCore C) :
    φ t ∈ perfectCore K := by
  rw [mem_perfectCore_iff] at ht ⊢
  intro j
  refine CFSG.Quasithin.derivedSeriesOf_mono hle j ?_
  rw [← CFSG.Quasithin.map_derivedSeriesOf]
  exact mem_map_of_mem φ (ht j)

theorem map_centralizer_le {P : Type*} [Group P] (φ : G →* P) (t : G) :
    (centralizer ({t} : Set G)).map φ ≤ centralizer ({φ t} : Set P) := by
  rintro _ ⟨c, hc, rfl⟩
  rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
    mem_centralizer_singleton_iff.1 hc]

theorem map_subtype_centralizer {K : Subgroup G} (k : K) :
    (centralizer ({k} : Set K)).map K.subtype = K ⊓ centralizer ({(k : G)} : Set G) := by
  ext g
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact mem_inf.2 ⟨c.2, mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hc))⟩
  · intro hg
    obtain ⟨hgK, hgc⟩ := mem_inf.1 hg
    exact ⟨⟨g, hgK⟩, mem_centralizer_singleton_iff.2
      (Subtype.ext (mem_centralizer_singleton_iff.1 hgc)), rfl⟩

theorem mem_perfectCore_centralizer_subtype {K : Subgroup G} (k : K)
    (h : (k : G) ∈ perfectCore (K ⊓ centralizer ({(k : G)} : Set G))) :
    k ∈ perfectCore (centralizer ({k} : Set K)) := by
  rw [mem_perfectCore_iff] at h ⊢
  intro j
  have hj := h j
  rw [← map_subtype_centralizer, ← CFSG.Quasithin.map_derivedSeriesOf] at hj
  obtain ⟨y, hy, hyk⟩ := hj
  rwa [K.subtype_injective hyk] at hy

theorem mem_perfectCore_of_quotient {P : Type*} [Group P] {A : Subgroup G}
    (θ : ↥A →* P) (hθ : Function.Surjective θ) (hker : θ.ker = center ↥A)
    (hodd : Odd (Nat.card (center ↥A))) {x : G} (hxA : x ∈ A) (hx2 : x ^ 2 = 1)
    (h : θ ⟨x, hxA⟩ ∈ perfectCore (centralizer ({θ ⟨x, hxA⟩} : Set P))) :
    x ∈ perfectCore (A ⊓ centralizer ({x} : Set G)) := by
  have hx2' : (⟨x, hxA⟩ : ↥A) ^ 2 = 1 := Subtype.ext (by simpa using hx2)
  have hoddZ : ∀ z ∈ center ↥A, Odd (orderOf z) := fun z hz => by
    have h1 := orderOf_dvd_natCard (⟨z, hz⟩ : center ↥A)
    rw [Subgroup.orderOf_mk] at h1
    exact hodd.of_dvd_nat h1
  have honto : centralizer ({θ ⟨x, hxA⟩} : Set P) ≤
      (centralizer ({(⟨x, hxA⟩ : ↥A)} : Set ↥A)).map θ := by
    intro c hc
    obtain ⟨a, rfl⟩ := hθ c
    rw [mem_centralizer_singleton_iff] at hc
    have hzc : ⁅a, (⟨x, hxA⟩ : ↥A)⁆ ∈ center ↥A := by
      rw [← hker, MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hc
    have hzx : a * ⟨x, hxA⟩ * a⁻¹ = ⁅a, (⟨x, hxA⟩ : ↥A)⁆ * ⟨x, hxA⟩ := by
      rw [commutatorElement_def, inv_mul_cancel_right]
    have hcomm : Commute ⁅a, (⟨x, hxA⟩ : ↥A)⁆ ⟨x, hxA⟩ :=
      ((Subgroup.mem_center_iff.1 hzc) ⟨x, hxA⟩).symm
    have hz2 : ⁅a, (⟨x, hxA⟩ : ↥A)⁆ ^ 2 = 1 := by
      have h1 : (a * ⟨x, hxA⟩ * a⁻¹) ^ 2 = 1 := by
        rw [sq, show a * ⟨x, hxA⟩ * a⁻¹ * (a * ⟨x, hxA⟩ * a⁻¹) =
          a * (⟨x, hxA⟩ * ⟨x, hxA⟩) * a⁻¹ by group, ← sq, hx2', mul_one, mul_inv_cancel]
      rw [hzx, hcomm.mul_pow, hx2', mul_one] at h1
      exact h1
    have hz1 : ⁅a, (⟨x, hxA⟩ : ↥A)⁆ = 1 := by
      have hd := orderOf_dvd_of_pow_eq_one hz2
      rcases (Nat.dvd_prime Nat.prime_two).1 hd with h1 | h1
      · exact orderOf_eq_one_iff.mp h1
      · exact absurd (h1 ▸ hoddZ _ hzc) (by decide)
    exact ⟨a, mem_centralizer_singleton_iff.2 (commutatorElement_eq_one_iff_mul_comm.mp hz1), rfl⟩
  rw [mem_perfectCore_iff] at h ⊢
  intro j
  have hj : θ ⟨x, hxA⟩ ∈ (derivedSeriesOf (centralizer ({(⟨x, hxA⟩ : ↥A)} : Set ↥A)) j).map θ := by
    rw [CFSG.Quasithin.map_derivedSeriesOf]
    exact CFSG.Quasithin.derivedSeriesOf_mono honto j (h j)
  obtain ⟨y, hy, hyx⟩ := hj
  obtain ⟨w, hwdef⟩ : ∃ w : ↥A, w = (⟨x, hxA⟩ : ↥A)⁻¹ * y := ⟨_, rfl⟩
  have hw : w ∈ center ↥A := by
    rw [hwdef, ← hker, MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
  have hyeq : y = ⟨x, hxA⟩ * w := by rw [hwdef]; group
  obtain ⟨t, ht⟩ := hoddZ _ hw
  have hpow : y ^ orderOf w = ⟨x, hxA⟩ := by
    have hcomm : Commute (⟨x, hxA⟩ : ↥A) w := (Subgroup.mem_center_iff.1 hw) ⟨x, hxA⟩
    rw [hyeq, hcomm.mul_pow, pow_orderOf_eq_one, mul_one, ht, pow_succ, pow_mul, hx2', one_pow,
      one_mul]
  have hxj : (⟨x, hxA⟩ : ↥A) ∈ derivedSeriesOf (centralizer ({(⟨x, hxA⟩ : ↥A)} : Set ↥A)) j := by
    have h1 := pow_mem hy (orderOf w)
    rwa [hpow] at h1
  have e := map_subtype_centralizer (⟨x, hxA⟩ : ↥A)
  rw [Subgroup.coe_mk] at e
  rw [← e, ← CFSG.Quasithin.map_derivedSeriesOf]
  exact mem_map_of_mem A.subtype hxj

theorem mem_perfectCore_of_represents {G : Type} [Group G] {A : Subgroup G} {ι K : Type}
    [Fintype ι] [DecidableEq ι]
    [Field K] {H : Subgroup (GL ι K)} (e : rankTwoQuot A ≃* StatedProj H)
    (hodd : Odd (Nat.card (center ↥A))) {x : G} (hx2 : x ^ 2 = 1) {M : GL ι K}
    (hM : Represents e x M) (hMp : M ∈ perfectCore (H ⊓ centralizer ({M} : Set (GL ι K)))) :
    x ∈ perfectCore (A ⊓ centralizer ({x} : Set G)) := by
  obtain ⟨hxA, hMH, he⟩ := hM
  have hθ : Function.Surjective (e.toMonoidHom.comp (QuotientGroup.mk' (center ↥A))) :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : (e.toMonoidHom.comp (QuotientGroup.mk' (center ↥A))).ker = center ↥A := by
    ext a
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  refine mem_perfectCore_of_quotient _ hθ hker hodd hxA hx2 ?_
  have hθx : (e.toMonoidHom.comp (QuotientGroup.mk' (center ↥A))) ⟨x, hxA⟩ =
      QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H) ⟨M, hMH⟩ := he
  rw [hθx]
  exact map_mem_perfectCore_of_le _ (map_centralizer_le _ _)
    (mem_perfectCore_centralizer_subtype ⟨M, hMH⟩ hMp)

end PerfectCore

end CFSG.ComponentClassification.RankTwoClassical
