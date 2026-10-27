module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6AutData
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6KFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3FusionLines
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowLift
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Lemma42
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem a6qs_mk_inj {C : Type*} [Group C] [Finite C] {T : Subgroup C}
    (hT : IsPGroup 3 T) {a b : C} (ha : a ∈ T) (hb : b ∈ T)
    (h : QuotientGroup.mk' (primeComplementCore (G := C) 3) a =
      QuotientGroup.mk' (primeComplementCore (G := C) 3) b) : a = b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hO : a⁻¹ * b ∈ primeComplementCore (G := C) 3 := QuotientGroup.eq.mp h
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hT ⟨a⁻¹ * b, T.mul_mem (T.inv_mem ha) hb⟩
  rw [Subgroup.orderOf_mk] at hk
  have h1 : orderOf (a⁻¹ * b) = 1 := Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_left k (primeComplementCore_coprime 3)) (dvd_of_eq hk)
    (Subgroup.orderOf_dvd_natCard _ hO)
  rwa [orderOf_eq_one_iff, inv_mul_eq_one] at h1

private theorem a6qs_key (hK2 : A6AutData) {P : Sylow 3 G} {M : Subgroup G} {x : G}
    {J : Subgroup G} (hJ : IsA6Normal M x J)
    (hcard : Nat.card ↥((P : Subgroup G) ⊓ J) = 3 ^ 2) :
    ∀ c : ↥(centralizer ({x} : Set G)), (c : G) ∈ (P : Subgroup G) →
      ∃ t : ↥(centralizer ({x} : Set G)), (t : G) ∈ (P : Subgroup G) ⊓ J ∧
        QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3) (t⁻¹ * c) ∈
          reducedCentralizerOfJ x J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJC := hJ.le_centralizer
  have hJbn : (r1sBar x J).Normal := r1sBar_normal_a6 hJ
  have hbot := a6_bar_inf_reducedCentralizer_eq_bot hJ
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set ρ : C →* GenericReduced 3 x := QuotientGroup.mk' (primeComplementCore (G := C) 3) with hρ
  have hP'p : IsPGroup 3 ((P : Subgroup G).subgroupOf C) := P.isPGroup'.comap_subtype
  have hTP : ((P : Subgroup G) ⊓ J).subgroupOf C ≤ (P : Subgroup G).subgroupOf C :=
    fun t ht => mem_subgroupOf.mpr (mem_subgroupOf.mp ht).1
  set χ : C →* MulAut ↥(r1sBar x J) := (MulAut.conjNormal (H := r1sBar x J)).comp ρ with hχ
  have hχD : ∀ c : C, χ c = 1 → ρ c ∈ reducedCentralizerOfJ x J := by
    intro c hc1
    rw [r1s_reducedCentralizerOfJ_eq, mem_centralizer_iff]
    intro h hh
    have h1 := congrArg (fun φ : MulAut ↥(r1sBar x J) =>
      ((φ ⟨h, hh⟩ : ↥(r1sBar x J)) : GenericReduced 3 x)) hc1
    simp only [hχ, MonoidHom.coe_comp, Function.comp_apply, MulAut.conjNormal_apply,
      MulAut.one_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  have hinj : Function.Injective (χ.comp (((P : Subgroup G) ⊓ J).subgroupOf C).subtype) := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have h1 : ρ t ∈ reducedCentralizerOfJ x J := hχD t ht
    have h2 : ρ t ∈ r1sBar x J := ⟨t, mem_subgroupOf.mpr (mem_subgroupOf.mp t.2).2, rfl⟩
    have h3 : ρ t = ρ 1 := by
      have h4 : ρ t ∈ r1sBar x J ⊓ reducedCentralizerOfJ x J := ⟨h2, h1⟩
      rw [hbot, mem_bot] at h4
      rw [h4, map_one]
    exact Subtype.ext (a6qs_mk_inj hP'p (hTP t.2) (one_mem _) h3)
  have hcardT : Nat.card ↥((((P : Subgroup G) ⊓ J).subgroupOf C).map χ) = 3 ^ 2 := by
    have e1 : (χ.comp (((P : Subgroup G) ⊓ J).subgroupOf C).subtype).range =
        (((P : Subgroup G) ⊓ J).subgroupOf C).map χ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← e1, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hJC)).toEquiv, hcard]
  have hA : (((P : Subgroup G) ⊓ J).subgroupOf C).map χ =
      ((P : Subgroup G).subgroupOf C).map χ := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.map_mono hTP) ?_
    rw [hcardT]
    exact Nat.le_of_dvd (by norm_num) (hK2 _ (r1sBar_isA6 hJ) _ (hP'p.map χ))
  intro c hc
  have hc' : χ c ∈ (((P : Subgroup G) ⊓ J).subgroupOf C).map χ := by
    rw [hA]
    exact mem_map_of_mem χ (mem_subgroupOf.mpr hc)
  obtain ⟨t, ht, htc⟩ := hc'
  refine ⟨t, mem_subgroupOf.mp ht, hχD _ ?_⟩
  rw [map_mul, map_inv, htc, inv_mul_cancel]

theorem a6_qstruct (hS : Setting G) (hU0 : FullCoreLocal G) (hK1 : A6SylowData)
    (hK2 : A6AutData) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 3 P M) {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G}
    (hJ : IsA6Normal M x J) :
    Nat.card ((P : Subgroup G) ⊓ J : Subgroup G) = 3 ^ 2 ∧
      IsElemAbelian 3 ((P : Subgroup G) ⊓ J : Subgroup G) ∧
      ∃ Z : Subgroup G, IsCyclic Z ∧ x ∈ Z ∧
        (∀ t ∈ (P : Subgroup G) ⊓ J, ∀ c ∈ Z, t * c = c * t) ∧
        ((P : Subgroup G) ⊓ J) ⊓ Z = ⊥ ∧
        (P : Subgroup G) ⊓ centralizer ({x} : Set G) = ((P : Subgroup G) ⊓ J) ⊔ Z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJC := hJ.le_centralizer
  have hcard := (a6_T_data hS hU0 hK1 hp hM hgen hJ).2.2
  have hel := a6_inf_isElemAbelian hK1 hgen hJ
  have hDc := a6_reducedCentralizer_isCyclic hS hU0 hK1 hp hM hgen hJ
  have hxD := (a6_xbar_facts hS hU0 hp hM hgen J).1
  have hbot := a6_bar_inf_reducedCentralizer_eq_bot hJ
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set ρ : C →* GenericReduced 3 x := QuotientGroup.mk' (primeComplementCore (G := C) 3) with hρ
  have hP'p : IsPGroup 3 ((P : Subgroup G).subgroupOf C) := P.isPGroup'.comap_subtype
  obtain ⟨W, hW⟩ : ∃ W : Subgroup C,
      W = (P : Subgroup G).subgroupOf C ⊓ (reducedCentralizerOfJ x J).comap ρ := ⟨_, rfl⟩
  have hWm : ∀ w : C, w ∈ W ↔ (w : G) ∈ (P : Subgroup G) ∧ ρ w ∈ reducedCentralizerOfJ x J := by
    intro w
    rw [hW, mem_inf, mem_subgroupOf, mem_comap]
  refine ⟨hcard, hel, W.map C.subtype, ?_, ?_, ?_, ?_, ?_⟩
  ·
    let f : W →* reducedCentralizerOfJ x J :=
      (ρ.comp W.subtype).codRestrict _ fun w => ((hWm w).mp w.2).2
    have hfi : Function.Injective f := fun a b hab => Subtype.ext
      (a6qs_mk_inj hP'p (mem_subgroupOf.mpr ((hWm a).mp a.2).1)
        (mem_subgroupOf.mpr ((hWm b).mp b.2).1) (congrArg Subtype.val hab))
    have : IsCyclic W := isCyclic_of_injective f hfi
    exact isCyclic_of_surjective (W.equivMapOfInjective C.subtype C.subtype_injective)
      (W.equivMapOfInjective C.subtype C.subtype_injective).surjective
  ·
    exact ⟨⟨x, mem_centralizer_singleton_iff.mpr rfl⟩, (hWm _).mpr ⟨hgen.1, hxD⟩, rfl⟩
  ·
    rintro t ht _ ⟨w, hw, rfl⟩
    obtain ⟨hwP, hwD⟩ := (hWm w).mp hw
    have htC : t ∈ C := hJC ht.2
    have htP : (⟨t, htC⟩ : C) ∈ (P : Subgroup G).subgroupOf C := mem_subgroupOf.mpr ht.1
    have hwP' : w ∈ (P : Subgroup G).subgroupOf C := mem_subgroupOf.mpr hwP
    have htJ : ρ ⟨t, htC⟩ ∈ r1sBar x J := ⟨⟨t, htC⟩, mem_subgroupOf.mpr ht.2, rfl⟩
    rw [r1s_reducedCentralizerOfJ_eq, mem_centralizer_iff] at hwD
    have h1 : ρ ⟨t, htC⟩ * ρ w = ρ w * ρ ⟨t, htC⟩ := hwD _ htJ
    have h2 : (⟨t, htC⟩ : C) * w = w * ⟨t, htC⟩ :=
      a6qs_mk_inj hP'p (mul_mem htP hwP') (mul_mem hwP' htP) (by rw [map_mul, map_mul, h1])
    exact congrArg Subtype.val h2
  ·
    refine eq_bot_iff.mpr ?_
    rintro _ ⟨hgT, w, hw, rfl⟩
    obtain ⟨hwP, hwD⟩ := (hWm w).mp hw
    have hwJ : ρ w ∈ r1sBar x J := ⟨w, mem_subgroupOf.mpr hgT.2, rfl⟩
    have h1 : ρ w = ρ 1 := by
      have h2 : ρ w ∈ r1sBar x J ⊓ reducedCentralizerOfJ x J := ⟨hwJ, hwD⟩
      rw [hbot, mem_bot] at h2
      rw [h2, map_one]
    have h3 : w = 1 := a6qs_mk_inj hP'p (mem_subgroupOf.mpr hwP) (one_mem _) h1
    rw [mem_bot, h3]
    rfl
  ·
    refine le_antisymm (fun g hg => ?_) (sup_le (le_inf inf_le_left (inf_le_right.trans hJC)) ?_)
    · obtain ⟨t, ht, htD⟩ := a6qs_key hK2 hJ hcard ⟨g, hg.2⟩ hg.1
      have hw : t⁻¹ * ⟨g, hg.2⟩ ∈ W := by
        refine (hWm _).mpr ⟨?_, htD⟩
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
        exact mul_mem (inv_mem ht.1) hg.1
      have hg' : g = (t : G) * ((t⁻¹ * ⟨g, hg.2⟩ : C) : G) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
      rw [hg']
      exact mul_mem_sup ht ⟨_, hw, rfl⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact ⟨((hWm w).mp hw).1, w.2⟩

theorem a6_prop34_abel (hS : Setting G) (hU0 : FullCoreLocal G) (hK1 : A6SylowData)
    (hK2 : A6AutData) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 3 P M) {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G}
    (hJ : IsA6Normal M x J) :
    IsMulCommutative ((P : Subgroup G) ⊓ centralizer ({x} : Set G) : Subgroup G) ∧
      ∀ y ∈ (P : Subgroup G) ⊓ centralizer ({x} : Set G), y ^ 3 = 1 →
        y ∈ ((P : Subgroup G) ⊓ J) ⊔ zpowers x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hel, Z, hZc, hxZ, hZcomm, -, hQeq⟩ := a6_qstruct hS hU0 hK1 hK2 hp hM hgen hJ
  obtain ⟨-, hx1, hx3, -, -⟩ := hgen.2.1
  have hZab : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : Z) ⟨b, hb⟩)
  have hTab : ∀ a ∈ (P : Subgroup G) ⊓ J, ∀ b ∈ (P : Subgroup G) ⊓ J, a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val (hel.1.is_comm.comm (⟨a, ha⟩ : ↥((P : Subgroup G) ⊓ J))
      ⟨b, hb⟩)
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hyQ hy3 => ?_⟩
  · obtain ⟨t₁, ht₁, z₁, hz₁, ha⟩ := u3l42_decomp hZcomm (by rw [← hQeq]; exact a.2)
    obtain ⟨t₂, ht₂, z₂, hz₂, hb⟩ := u3l42_decomp hZcomm (by rw [← hQeq]; exact b.2)
    change (a : G) * b = b * a
    rw [ha, hb]
    calc t₁ * z₁ * (t₂ * z₂) = t₁ * (z₁ * t₂) * z₂ := by group
      _ = t₁ * (t₂ * z₁) * z₂ := by rw [← hZcomm t₂ ht₂ z₁ hz₁]
      _ = (t₁ * t₂) * (z₁ * z₂) := by group
      _ = (t₂ * t₁) * (z₂ * z₁) := by rw [hTab t₁ ht₁ t₂ ht₂, hZab z₁ hz₁ z₂ hz₂]
      _ = t₂ * (t₁ * z₂) * z₁ := by group
      _ = t₂ * (z₂ * t₁) * z₁ := by rw [hZcomm t₁ ht₁ z₂ hz₂]
      _ = t₂ * z₂ * (t₁ * z₁) := by group
  · obtain ⟨t, ht, z, hz, rfl⟩ := u3l42_decomp hZcomm (by rw [← hQeq]; exact hyQ)
    have ht3 : t ^ 3 = 1 := hel.2 t ht
    have hz3 : z ^ 3 = 1 := by
      have h := (Commute.mul_pow (show Commute t z from hZcomm t ht z hz) 3).symm.trans hy3
      rwa [ht3, one_mul] at h
    exact mul_mem_sup ht (mem_zpowers_of_isCyclic_of_pow_three hZc hxZ hz hx1 hx3 hz3)

end CFSG.LocalAnalysis.RankThreeTheoremC
