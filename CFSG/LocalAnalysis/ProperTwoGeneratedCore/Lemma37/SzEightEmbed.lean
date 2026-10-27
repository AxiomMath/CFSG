module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SzEightSetup
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.BenderCoverStatement
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.Statement
public import CFSG.StronglyEmbedded

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)}

namespace SzEightSetting

variable (hs : SzEightSetting S H z J)
include hs

theorem center_le_subgroupOf : Subgroup.center J ≤ (escapingImage H z).subgroupOf J := by
  intro c hc
  rw [Subgroup.mem_subgroupOf]
  rcases hs.center c hc with h | h
  · rw [h]
    exact Subgroup.one_mem _
  · rw [h]
    exact hs.quotientData.bar_mem_image

theorem mk_mem_componentImage_iff (v : J) :
    (v : J ⧸ Subgroup.center J) ∈ TheoremC.componentImage (escapingImage H z) J ↔
      (v : EscapingQuotient z) ∈ escapingImage H z := by
  constructor
  · rintro ⟨w, hw, hwv⟩
    have hc : w⁻¹ * v ∈ Subgroup.center J := QuotientGroup.eq.mp hwv
    have h := ((escapingImage H z).subgroupOf J).mul_mem hw (hs.center_le_subgroupOf hc)
    rw [mul_inv_cancel_left] at h
    exact h
  · intro hv
    exact ⟨v, hv, rfl⟩

omit [Finite G] hs in
theorem orderOf_mk_eq_two {v : J} (hv : v * v ∈ Subgroup.center J)
    (hvZ : v ∉ Subgroup.center J) : orderOf (v : J ⧸ Subgroup.center J) = 2 := by
  refine orderOf_eq_prime ?_ fun h => hvZ ((QuotientGroup.eq_one_iff v).mp h)
  rw [pow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
  exact hv

theorem false_of_mem_conj {j v : J} (hj : (j : EscapingQuotient z) ∉ escapingImage H z)
    (hv : (v : EscapingQuotient z) ∈ escapingImage H z)
    (hvj : (j : EscapingQuotient z)⁻¹ * v * j ∈ escapingImage H z)
    (hvv : v * v ∈ Subgroup.center J) (hvZ : v ∉ Subgroup.center J) : False := by
  have hq := hs.quotientData
  obtain ⟨k, hkS, hkC, hk2⟩ := hs.exists_root
  have hkH : k ∈ escapingImage H z := escapingSylowImage_le_image hs.square.core.sylow_le hkS
  have hm : (j : EscapingQuotient z)⁻¹ ∉ escapingImage H z := fun h =>
    hj (by simpa using (escapingImage H z).inv_mem h)
  have hkc : ∀ w ∈ J, w * k = k * w := Subgroup.mem_centralizer_iff.mp hkC
  set w : EscapingQuotient z := (v : EscapingQuotient z) with hw
  have hwZ : ∀ c ∈ Subgroup.centralizer (J : Set (EscapingQuotient z)), w ≠ c := by
    rintro c hc rfl
    exact hvZ (mem_center_of_mem_centralizer hc)
  have hbarC : escapingBar z ∈ Subgroup.centralizer (J : Set (EscapingQuotient z)) :=
    Subgroup.mem_centralizer_iff.mpr fun g _ => (hq.commute_bar g).eq
  rcases hs.center _ hvv with h | h
  ·
    have hw2 : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact h)
      (hwZ 1 (Subgroup.one_mem _))
    exact hwZ _ hbarC (hq.eq_bar_of_conj_mem hm hv (by simpa using hvj) hw2)
  ·
    have hkw : w * k = k * w := hkc w v.2
    have hkj : (j : EscapingQuotient z) * k = k * j := hkc j j.2
    have hbb : escapingBar z * escapingBar z = 1 := by
      rw [← pow_two]
      have h2 := pow_orderOf_eq_one (escapingBar z)
      rwa [hq.bar_order] at h2
    have hww : w * w = escapingBar z := h
    have hee : k * w * (k * w) = 1 := by
      calc k * w * (k * w) = k ^ 2 * (w * w) := by
            rw [pow_two, mul_assoc, ← mul_assoc w k w, hkw]
            group
        _ = 1 := by rw [hk2, hww, hbb]
    have he1 : k * w ≠ 1 := fun he => hwZ k⁻¹ (Subgroup.inv_mem _ hkC)
      (eq_inv_of_mul_eq_one_right he)
    have he2 : orderOf (k * w) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hee) he1
    have heH : k * w ∈ escapingImage H z := (escapingImage H z).mul_mem hkH hv
    have hej : (j : EscapingQuotient z)⁻¹⁻¹⁻¹ * (k * w) * (j : EscapingQuotient z)⁻¹⁻¹ ∈
        escapingImage H z := by
      have hkj' : (j : EscapingQuotient z)⁻¹ * k = k * (j : EscapingQuotient z)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hkj, mul_assoc, mul_inv_cancel, mul_one]
      have hjk : (j : EscapingQuotient z)⁻¹ * (k * w) * j =
          k * ((j : EscapingQuotient z)⁻¹ * w * j) := by
        calc (j : EscapingQuotient z)⁻¹ * (k * w) * j
            = ((j : EscapingQuotient z)⁻¹ * k) * w * j := by group
          _ = (k * (j : EscapingQuotient z)⁻¹) * w * j := by rw [hkj']
          _ = k * ((j : EscapingQuotient z)⁻¹ * w * j) := by group
      rw [inv_inv, inv_inv, hjk]
      exact (escapingImage H z).mul_mem hkH hvj
    have hebar := hq.eq_bar_of_conj_mem hm heH (by simpa using hej) he2
    exact hwZ (k⁻¹ * escapingBar z) ((Subgroup.centralizer _).mul_mem
      (Subgroup.inv_mem _ hkC) hbarC) (by rw [← hebar]; group)

theorem isStronglyEmbeddedOrder :
    CFSG.BenderSuzuki.IsStronglyEmbeddedOrder (TheoremC.componentImage (escapingImage H z) J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨fun htop => hs.not_le fun j hj => ?_, ?_, fun g hg => ?_⟩
  · have h : ((⟨j, hj⟩ : J) : J ⧸ Subgroup.center J) ∈
        TheoremC.componentImage (escapingImage H z) J := htop ▸ Subgroup.mem_top _
    exact (hs.mk_mem_componentImage_iff _).mp h
  · obtain ⟨x, hxJ, hx, hxne, hxS⟩ := hs.exists_involution_mem_sylow
    have hxH : x ∈ escapingImage H z := escapingSylowImage_le_image hs.square.core.sylow_le hxS
    have hxx : (⟨x, hxJ⟩ * ⟨x, hxJ⟩ : J) = 1 := Subtype.ext (by
      change x * x = 1
      rw [← pow_two]
      have h2 := pow_orderOf_eq_one x
      rwa [hx] at h2)
    have hxZ : (⟨x, hxJ⟩ : J) ∉ Subgroup.center J := by
      rw [hs.mem_center_iff]
      rintro (h | h)
      · rw [show x = 1 from h, orderOf_one] at hx
        exact absurd hx (by decide)
      · exact hxne h
    have hy2 := orderOf_mk_eq_two (hxx ▸ Subgroup.one_mem _) hxZ
    have hyM := (hs.mk_mem_componentImage_iff ⟨x, hxJ⟩).mpr hxH
    refine even_iff_two_dvd.mpr ?_
    have h := Subgroup.orderOf_dvd_natCard _ hyM
    rwa [hy2] at h
  · by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    obtain ⟨y', hy⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hodd)
    rw [← Subgroup.orderOf_coe] at hy
    set y : J ⧸ Subgroup.center J := (y' : J ⧸ Subgroup.center J) with hydef
    have hyM := (Subgroup.mem_inf.mp y'.2).1
    have hyg := (Subgroup.mem_inf.mp y'.2).2
    obtain ⟨b₀, hb₀, hb₀y⟩ := Subgroup.mem_map.mp hyg
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hb₀
    have hj : (j : EscapingQuotient z) ∉ escapingImage H z := fun h =>
      hg ((hs.mk_mem_componentImage_iff j).mpr h)
    set v : J := j * b * j⁻¹ with hvdef
    have hvy : (v : J ⧸ Subgroup.center J) = y := by
      rw [hydef, ← hb₀y]
      simp [v, MulAut.conj_apply, QuotientGroup.mk'_apply]
    have hvH : (v : EscapingQuotient z) ∈ escapingImage H z :=
      (hs.mk_mem_componentImage_iff v).mp (hvy ▸ hyM)
    have hvj : (j : EscapingQuotient z)⁻¹ * v * j ∈ escapingImage H z := by
      have h : (j : EscapingQuotient z)⁻¹ * v * j = b := by
        rw [hvdef]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [h]
      exact hb
    have hvZ : v ∉ Subgroup.center J := fun h => by
      rw [← hvy, (QuotientGroup.eq_one_iff v).mpr h, orderOf_one] at hy
      exact absurd hy (by decide)
    have hvv : v * v ∈ Subgroup.center J := by
      have h2 := pow_orderOf_eq_one y
      rw [hy] at h2
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, hvy, ← pow_two, h2]
    exact hs.false_of_mem_conj hj hvH hvj hvv hvZ

theorem isBenderGroup :
    CFSG.BenderSuzuki.IsBenderGroup (J ⧸ Subgroup.center J) := by
  have : IsSimpleGroup (J ⧸ Subgroup.center J) := hs.component.1.2.1
  exact CFSG.BenderSuzuki.bender_suzuki _ hs.isStronglyEmbeddedOrder

theorem commutator_eq_top : commutator J = ⊤ := hs.component.1.1.commutator_eq_top

theorem cover (hcov : BenderCoverStatement) :
    Nonempty ((J ⧸ Subgroup.center J) ≃* CFSG.Theory.Comparator.PSL2Model 2) ∨
      Nonempty ((J ⧸ Subgroup.center J) ≃* ↥(CFSG.Theory.Comparator.SzModel 1)) :=
  hcov J hs.commutator_eq_top hs.card_center hs.isBenderGroup

end SzEightSetting

end CFSG.ProperTwoGeneratedCore.Lemma37
