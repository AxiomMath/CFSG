module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrCover
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem oddCore_le_center_of_center_card_two {A : Type*} [Group A] [Finite A]
    (hq : CFSG.IsQuasisimple A)
    (hcard : Nat.card (Subgroup.center (A ⧸ CFSG.oddCore A)) = 2) :
    CFSG.oddCore A ≤ Subgroup.center A := by
  have hne : CFSG.oddCore A ≠ ⊤ := by
    intro htop
    haveI : Subsingleton (A ⧸ CFSG.oddCore A) := by
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    have h1 : Nat.card (Subgroup.center (A ⧸ CFSG.oddCore A)) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
    exact absurd (h1.symm.trans hcard) (by decide)
  exact CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top
    (⟨hq.1.commutator_eq_top, hq.2.1⟩ : CFSG.Open.IsQuasisimple A) (CFSG.oddCore A) hne

private theorem oddCentralCover_mk_oddCore {A : Type*} [Group A] [Finite A]
    (hle : CFSG.oddCore A ≤ Subgroup.center A) :
    OddCentralCover (QuotientGroup.mk' (CFSG.oddCore A)) := by
  refine ⟨QuotientGroup.mk'_surjective _, ?_, ?_⟩
  · rw [QuotientGroup.ker_mk']; exact hle
  · rw [QuotientGroup.ker_mk']
    exact CFSG.ComponentClassification.OddCore.odd_card A

private theorem map_center_mem_center_of_surjective {A P : Type*} [Group A] [Group P]
    (f : A →* P) (hf : Function.Surjective f) {x : A} (hx : x ∈ Subgroup.center A) :
    f x ∈ Subgroup.center P := by
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨m, rfl⟩ := hf y
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx m]

private theorem mem_center_of_commutator_mem_center {A : Type*} [Group A] [Group.IsPerfect A]
    {N : Subgroup A} (hN : N ≤ Subgroup.center A) {g : A} (hg : ∀ h : A, ⁅g, h⁆ ∈ N) :
    g ∈ Subgroup.center A := by
  have h1 : QuotientGroup.mk' (Subgroup.center A) g ∈
      Subgroup.center (A ⧸ Subgroup.center A) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ y
    have h2 : QuotientGroup.mk' (Subgroup.center A) ⁅g, h⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (hN (hg h))
    rw [map_commutatorElement] at h2
    exact (commutatorElement_eq_one_iff_mul_comm.mp h2).symm
  rw [Group.IsPerfect.center_quotient_center_eq_bot A, Subgroup.mem_bot] at h1
  exact (QuotientGroup.eq_one_iff _).mp h1

private theorem eq_of_ne_one_of_mem_center_card_two {A : Type*} [Group A]
    (hcard : Nat.card (Subgroup.center A) = 2) {x y : A} (hx : x ∈ Subgroup.center A)
    (hx1 : x ≠ 1) (hy : y ∈ Subgroup.center A) (hy1 : y ≠ 1) : x = y := by
  obtain ⟨u, _, huniq⟩ := (Nat.card_eq_two_iff' (α := Subgroup.center A) 1).mp hcard
  have hx' : (⟨x, hx⟩ : Subgroup.center A) = u :=
    huniq ⟨x, hx⟩ (fun h => hx1 (Subtype.ext_iff.mp h))
  have hy' : (⟨y, hy⟩ : Subgroup.center A) = u :=
    huniq ⟨y, hy⟩ (fun h => hy1 (Subtype.ext_iff.mp h))
  exact Subtype.ext_iff.mp (hx'.trans hy'.symm)

theorem t5_exists_central_involution (hL : IsOm6Z2 L) : ∃ t ∈ centerIn L, orderOf t = 2 := by
  have hq : CFSG.IsQuasisimple ↥L := hL.1
  have hcard : Nat.card (Subgroup.center (↥L ⧸ CFSG.oddCore ↥L)) = 2 := hL.2.1
  have hcore : CFSG.oddCore ↥L ≤ Subgroup.center ↥L :=
    oddCore_le_center_of_center_card_two hq hcard
  haveI : Group.IsPerfect ↥L := hq.1
  let ρ : ↥L →* (↥L ⧸ CFSG.oddCore ↥L) := QuotientGroup.mk' (CFSG.oddCore ↥L)
  have hρ : OddCentralCover ρ := oddCentralCover_mk_oddCore hcore
  obtain ⟨cZ, hcZ2⟩ := exists_prime_orderOf_dvd_card'
    (G := Subgroup.center (↥L ⧸ CFSG.oddCore ↥L)) 2 (by rw [hcard])
  have hcZsq : cZ ^ 2 = 1 := by rw [← hcZ2]; exact pow_orderOf_eq_one cZ
  have hc2 : (cZ : ↥L ⧸ CFSG.oddCore ↥L) * (cZ : ↥L ⧸ CFSG.oddCore ↥L) = 1 := by
    have h1 : (Subgroup.center (↥L ⧸ CFSG.oddCore ↥L)).subtype (cZ ^ 2) = 1 := by
      rw [hcZsq, map_one]
    rw [map_pow] at h1
    simpa [pow_two] using h1
  obtain ⟨w, hww, hwρ⟩ := hρ.exists_mul_self_eq_one_lift hc2
  have hwcomm : ∀ m : ↥L, ⁅w, m⁆ ∈ CFSG.oddCore ↥L := by
    intro m
    apply (QuotientGroup.eq_one_iff (⁅w, m⁆)).mp
    change ρ ⁅w, m⁆ = 1
    rw [map_commutatorElement]
    change ⁅ρ w, ρ m⁆ = 1
    rw [hwρ, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp cZ.2 (ρ m)).symm
  have hwcenter : w ∈ Subgroup.center ↥L := mem_center_of_commutator_mem_center hcore hwcomm
  have hc_ne : (cZ : ↥L ⧸ CFSG.oddCore ↥L) ≠ 1 := by
    intro h
    have hord1 : orderOf (cZ : ↥L ⧸ CFSG.oddCore ↥L) = 1 := by rw [h, orderOf_one]
    have hord2 : orderOf (cZ : ↥L ⧸ CFSG.oddCore ↥L) = 2 := by
      have h' := orderOf_injective (Subgroup.center (↥L ⧸ CFSG.oddCore ↥L)).subtype
        (Subgroup.center (↥L ⧸ CFSG.oddCore ↥L)).subtype_injective cZ
      rw [hcZ2] at h'
      exact h'
    exact absurd (hord2.symm.trans hord1) (by decide)
  have hw_ne : w ≠ 1 := by
    intro hw1
    exact hc_ne (by rw [← hwρ, hw1, map_one])
  refine ⟨(w : G), Subgroup.mem_map_of_mem L.subtype hwcenter, ?_⟩
  have hword : orderOf (w : G) = orderOf w :=
    orderOf_injective L.subtype L.subtype_injective w
  rw [hword]
  exact orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hww) hw_ne

theorem t5_central_involution_unique (hL : IsOm6Z2 L) {t t' : G} (ht : t ∈ centerIn L)
    (ht2 : orderOf t = 2) (ht' : t' ∈ centerIn L) (ht2' : orderOf t' = 2) : t' = t := by
  have hq : CFSG.IsQuasisimple ↥L := hL.1
  have hcard : Nat.card (Subgroup.center (↥L ⧸ CFSG.oddCore ↥L)) = 2 := hL.2.1
  have hcore : CFSG.oddCore ↥L ≤ Subgroup.center ↥L :=
    oddCore_le_center_of_center_card_two hq hcard
  haveI : Group.IsPerfect ↥L := hq.1
  let ρ : ↥L →* (↥L ⧸ CFSG.oddCore ↥L) := QuotientGroup.mk' (CFSG.oddCore ↥L)
  have hρ : OddCentralCover ρ := oddCentralCover_mk_oddCore hcore
  obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp ht
  obtain ⟨b, hb, hbeq⟩ := Subgroup.mem_map.mp ht'
  have ha_ord : orderOf a = 2 := by
    have h := orderOf_injective L.subtype L.subtype_injective a
    rw [haeq, ht2] at h
    exact h.symm
  have hb_ord : orderOf b = 2 := by
    have h := orderOf_injective L.subtype L.subtype_injective b
    rw [hbeq, ht2'] at h
    exact h.symm
  have ha2 : a * a = 1 := by rw [← pow_two, ← ha_ord, pow_orderOf_eq_one]
  have hb2 : b * b = 1 := by rw [← pow_two, ← hb_ord, pow_orderOf_eq_one]
  have hρa : ρ a ∈ Subgroup.center (↥L ⧸ CFSG.oddCore ↥L) :=
    map_center_mem_center_of_surjective ρ hρ.surjective ha
  have hρb : ρ b ∈ Subgroup.center (↥L ⧸ CFSG.oddCore ↥L) :=
    map_center_mem_center_of_surjective ρ hρ.surjective hb
  have hρa_ne : ρ a ≠ 1 := by
    intro h
    have ha1 : a = 1 := hρ.eq_one_of_mul_self_eq_one (MonoidHom.mem_ker.mpr h) ha2
    rw [ha1, orderOf_one] at ha_ord
    exact absurd ha_ord (by decide)
  have hρb_ne : ρ b ≠ 1 := by
    intro h
    have hb1 : b = 1 := hρ.eq_one_of_mul_self_eq_one (MonoidHom.mem_ker.mpr h) hb2
    rw [hb1, orderOf_one] at hb_ord
    exact absurd hb_ord (by decide)
  have hab : a = b :=
    hρ.eq_of_mul_self_eq_one ha2 hb2
      (eq_of_ne_one_of_mem_center_card_two hcard hρa hρa_ne hρb hρb_ne)
  rw [← hbeq, ← haeq, hab]

theorem t5_normalizer_commute (hL : IsOm6Z2 L) {t n : G} (ht : t ∈ centerIn L)
    (ht2 : orderOf t = 2) (hn : n ∈ normalizer (L : Set G)) : n * t = t * n := by
  obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp ht
  have ha_ord : orderOf a = 2 := by
    have h := orderOf_injective L.subtype L.subtype_injective a
    rw [haeq, ht2] at h
    exact h.symm
  let σ : MulAut ↥L := Subgroup.normalizerMonoidHom L ⟨n, hn⟩
  have hσ_coe : ∀ x : ↥L, ((σ x : ↥L) : G) = n * (x : G) * n⁻¹ := by
    intro x
    simp [σ]
  have hmap : (Subgroup.center ↥L).map (σ : ↥L →* ↥L) = Subgroup.center ↥L :=
    (Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (Subgroup.center ↥L).Characteristic)) σ
  have hσa_center : σ a ∈ Subgroup.center ↥L := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem (σ : ↥L →* ↥L) ha
  have hσa_ord : orderOf ((σ a : ↥L) : G) = 2 := by
    have h' : orderOf ((σ a : ↥L) : G) = orderOf (σ a) :=
      orderOf_injective L.subtype L.subtype_injective (σ a)
    rw [h', MulEquiv.orderOf_eq σ a, ha_ord]
  have hσa_G : ((σ a : ↥L) : G) = t :=
    t5_central_involution_unique hL ht ht2
      (Subgroup.mem_map_of_mem L.subtype hσa_center) hσa_ord
  have hconj : n * t * n⁻¹ = t := by
    have hcoe : n * t * n⁻¹ = ((σ a : ↥L) : G) := by
      rw [← haeq]
      exact (hσ_coe a).symm
    exact hcoe.trans hσa_G
  calc n * t = n * t * n⁻¹ * n := by group
    _ = t * n := by rw [hconj]

theorem t5_centerIn_eq (hL : IsOm6Z2 L) {t : G} (ht : t ∈ centerIn L) (ht2 : orderOf t = 2) :
    centerIn L = zpowers t ⊔ oddCoreIn L ∧ zpowers t ⊓ oddCoreIn L = ⊥ := by
  have hq : CFSG.IsQuasisimple ↥L := hL.1
  have hcard : Nat.card (Subgroup.center (↥L ⧸ CFSG.oddCore ↥L)) = 2 := hL.2.1
  have hcore : CFSG.oddCore ↥L ≤ Subgroup.center ↥L :=
    oddCore_le_center_of_center_card_two hq hcard
  haveI : Group.IsPerfect ↥L := hq.1
  let ρ : ↥L →* (↥L ⧸ CFSG.oddCore ↥L) := QuotientGroup.mk' (CFSG.oddCore ↥L)
  have hρ : OddCentralCover ρ := oddCentralCover_mk_oddCore hcore
  obtain ⟨w, hw, hweq⟩ := Subgroup.mem_map.mp ht
  have hw_ord : orderOf w = 2 := by
    have h := orderOf_injective L.subtype L.subtype_injective w
    rw [hweq, ht2] at h
    exact h.symm
  have hww : w * w = 1 := by rw [← pow_two, ← hw_ord, pow_orderOf_eq_one]
  have hρw : ρ w ∈ Subgroup.center (↥L ⧸ CFSG.oddCore ↥L) :=
    map_center_mem_center_of_surjective ρ hρ.surjective hw
  have hρw_ne : ρ w ≠ 1 := by
    intro h
    have hw1 : w = 1 := hρ.eq_one_of_mul_self_eq_one (MonoidHom.mem_ker.mpr h) hww
    rw [hw1, orderOf_one] at hw_ord
    exact absurd hw_ord (by decide)
  refine ⟨?_, ?_⟩
  · apply le_antisymm
    · intro z hz
      obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp hz
      have hρa : ρ a ∈ Subgroup.center (↥L ⧸ CFSG.oddCore ↥L) :=
        map_center_mem_center_of_surjective ρ hρ.surjective ha
      by_cases ha1 : ρ a = 1
      · have ha_ker : a ∈ CFSG.oddCore ↥L := (QuotientGroup.eq_one_iff a).mp ha1
        have hz_odd : z ∈ oddCoreIn L := by
          rw [← haeq]
          exact Subgroup.mem_map_of_mem L.subtype ha_ker
        exact Subgroup.mem_sup_right hz_odd
      · have hρa_eq : ρ a = ρ w :=
          eq_of_ne_one_of_mem_center_card_two hcard hρa ha1 hρw hρw_ne
        have hker : w⁻¹ * a ∈ CFSG.oddCore ↥L := by
          apply (QuotientGroup.eq_one_iff (w⁻¹ * a)).mp
          change ρ (w⁻¹ * a) = 1
          rw [map_mul, map_inv, hρa_eq, inv_mul_cancel]
        have hk_mem : L.subtype (w⁻¹ * a) ∈ oddCoreIn L :=
          Subgroup.mem_map_of_mem L.subtype hker
        have hprod : t * L.subtype (w⁻¹ * a) ∈ zpowers t ⊔ oddCoreIn L :=
          mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
            (Subgroup.mem_sup_right hk_mem)
        have heq : t * L.subtype (w⁻¹ * a) = z := by
          rw [← hweq, ← map_mul, (by group : w * (w⁻¹ * a) = a), haeq]
        rwa [heq] at hprod
    · apply sup_le
      · exact Subgroup.zpowers_le.mpr ht
      · simpa only [oddCoreIn, centerIn, CFSG.inSubgroup] using Subgroup.map_mono hcore
  · apply le_antisymm _ bot_le
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxz, hxo⟩ := hx
    rw [Subgroup.mem_bot]
    obtain ⟨b, hb, hbeq⟩ := Subgroup.mem_map.mp hxo
    have hxx : x * x = 1 := by
      classical
      have hxr : x ∈ (Finset.range (orderOf t)).image (t ^ ·) :=
        mem_zpowers_iff_mem_range_orderOf.mp hxz
      rw [ht2] at hxr
      obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hxr
      rw [Finset.mem_range] at hi
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · rw [← hix]; simp
      · rw [← hix, pow_one, ← pow_two, ← ht2, pow_orderOf_eq_one]
    have hbb : b * b = 1 := by
      apply Subtype.ext
      have h : (b : G) * (b : G) = 1 := by
        have hb_eq : (b : G) = x := hbeq
        rw [hb_eq]; exact hxx
      simpa using h
    have hb1 : b = 1 := hρ.eq_one_of_mul_self_eq_one (MonoidHom.mem_ker.mpr
      ((QuotientGroup.eq_one_iff b).mpr hb)) hbb
    rw [← hbeq, hb1]
    simp

theorem t5_centralizes_of_central_comm (hL : CFSG.IsQuasisimple ↥L) {Z : Subgroup G}
    (hZ : Z ≤ centerIn L) {s : G} (hs : s ∈ normalizer (L : Set G))
    (h : ∀ l ∈ L, s * l * s⁻¹ * l⁻¹ ∈ Z) : s ∈ centralizer (L : Set G) := by
  haveI : Group.IsPerfect ↥L := hL.1
  have hZle : centerIn L ≤ L := Subgroup.map_subtype_le _
  have hfL : ∀ l : ↥L, s * (l : G) * s⁻¹ * (l : G)⁻¹ ∈ L :=
    fun l => hZle (hZ (h (l : G) l.2))
  have hf_center : ∀ l : ↥L, (⟨s * (l : G) * s⁻¹ * (l : G)⁻¹, hfL l⟩ : ↥L) ∈
      Subgroup.center ↥L := by
    intro l
    obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp (hZ (h (l : G) l.2))
    have hone : (⟨s * (l : G) * s⁻¹ * (l : G)⁻¹, hfL l⟩ : ↥L) = a := Subtype.ext haeq.symm
    rw [hone]; exact ha
  have hcentral : ∀ l m : ↥L,
      (l : G) * (s * (m : G) * s⁻¹ * (m : G)⁻¹) * (l : G)⁻¹ =
        s * (m : G) * s⁻¹ * (m : G)⁻¹ := by
    intro l m
    have hcomm : (l : G) * (s * (m : G) * s⁻¹ * (m : G)⁻¹) =
        (s * (m : G) * s⁻¹ * (m : G)⁻¹) * (l : G) :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp (hf_center m) l)
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  let F : ↥L →* ↥L :=
    { toFun := fun l => ⟨s * (l : G) * s⁻¹ * (l : G)⁻¹, hfL l⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro l m
        apply Subtype.ext
        change s * ((l : G) * (m : G)) * s⁻¹ * ((l : G) * (m : G))⁻¹ =
          (s * (l : G) * s⁻¹ * (l : G)⁻¹) * (s * (m : G) * s⁻¹ * (m : G)⁻¹)
        calc s * ((l : G) * (m : G)) * s⁻¹ * ((l : G) * (m : G))⁻¹
            = (s * (l : G) * s⁻¹ * (l : G)⁻¹) *
                ((l : G) * (s * (m : G) * s⁻¹ * (m : G)⁻¹) * (l : G)⁻¹) := by group
          _ = (s * (l : G) * s⁻¹ * (l : G)⁻¹) *
                (s * (m : G) * s⁻¹ * (m : G)⁻¹) := by rw [hcentral l m] }
  have hFker : commutator ↥L ≤ F.ker := by
    change ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ ≤ F.ker
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hf_center a) (F b)).symm
  have htriv : ∀ l : ↥L, F l = 1 := by
    intro l
    have hl : l ∈ F.ker :=
      hFker (by rw [hL.1.commutator_eq_top]; exact Subgroup.mem_top l)
    simpa [MonoidHom.mem_ker] using hl
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h1 : s * l * s⁻¹ * l⁻¹ = 1 := congrArg Subtype.val (htriv ⟨l, hl⟩)
  have h2 : s * l * s⁻¹ = l := by
    have h := congrArg (· * l) h1
    simpa [mul_assoc] using h
  calc l * s = (s * l * s⁻¹) * s := by rw [h2]
    _ = s * l := by group
end CFSG.OddStandard.SmallF3.Omega
