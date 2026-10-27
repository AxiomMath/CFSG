module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3KFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Struct
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem u3q_mk_inj {C : Type*} [Group C] [Finite C] {T : Subgroup C} (hT : IsPGroup 3 T)
    {a b : C} (ha : a ∈ T) (hb : b ∈ T)
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

private theorem u3q_sylow_facts (hK1 : U3SylowData) {P : Sylow 3 G} {M : Subgroup G} {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsU3Normal M x J)
    (hPC : (P : Subgroup G) ≤ centralizer ({x} : Set G)) :
    (∀ t ∈ (P : Subgroup G) ⊓ J, t ^ 3 = 1) ∧ ¬ IsMulCommutative ↥((P : Subgroup G) ⊓ J) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJC := hJ.le_centralizer
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hP'p : IsPGroup 3 ((P : Subgroup G).subgroupOf C) := P.isPGroup'.comap_subtype
  have hSylJ : IsSylowOf 3 (((P : Subgroup G) ⊓ C) ⊓ J) J :=
    hgen.2.2.1.inf_of_le_normalizer hJC hJ.centralizer_le
  have hPJ : ((P : Subgroup G) ⊓ C) ⊓ J = (P : Subgroup G) ⊓ J := by
    rw [inf_assoc, inf_eq_right.mpr hJC]
  rw [hPJ] at hSylJ
  obtain ⟨T, hT⟩ := hSylJ
  set T' : Sylow 3 ↥(r1sBar x J) := T.mapSurjective (r1sHom_surjective x hJC) with hT'
  obtain ⟨-, hT'e, hT'n, -⟩ := hK1 _ (r1sBar_isU3 hJ) T'
  have hmem : ∀ t (ht : t ∈ (P : Subgroup G) ⊓ J),
      r1sHom x hJC ⟨t, ht.2⟩ ∈ (T' : Subgroup ↥(r1sBar x J)) := by
    intro t ht
    have ht' : t ∈ (T : Subgroup ↥J).map J.subtype := by rw [hT]; exact ht
    obtain ⟨j, hj, hjt⟩ := ht'
    have hj' : (⟨t, ht.2⟩ : ↥J) = j := Subtype.ext hjt.symm
    rw [hj', hT', Sylow.coe_mapSurjective]
    exact mem_map_of_mem _ hj
  have hexp : ∀ t ∈ (P : Subgroup G) ⊓ J, t ^ 3 = 1 := by
    intro t ht
    have h3 := congrArg Subtype.val (hT'e _ (hmem t ht))
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one] at h3
    have h4 : QuotientGroup.mk' (primeComplementCore (G := C) 3) ((⟨t, hPC ht.1⟩ : C) ^ 3) =
        QuotientGroup.mk' (primeComplementCore (G := C) 3) 1 := by
      rw [map_pow, map_one]
      exact h3
    have h5 := u3q_mk_inj hP'p (pow_mem (mem_subgroupOf.mpr ht.1) 3) (one_mem _) h4
    exact congrArg Subtype.val h5
  refine ⟨hexp, fun hcomm => hT'n ⟨⟨fun a b => Subtype.ext ?_⟩⟩⟩
  have hpre : ∀ a : ↥(T' : Subgroup ↥(r1sBar x J)),
      ∃ j : ↥J, (j : G) ∈ (P : Subgroup G) ⊓ J ∧ r1sHom x hJC j = a := by
    intro a
    have ha : (a : ↥(r1sBar x J)) ∈ (T : Subgroup ↥J).map (r1sHom x hJC) := by
      rw [← Sylow.coe_mapSurjective]
      exact a.2
    obtain ⟨j, hj, hja⟩ := ha
    exact ⟨j, by rw [← hT]; exact mem_map_of_mem _ hj, hja⟩
  obtain ⟨j₁, hj₁, h₁⟩ := hpre a
  obtain ⟨j₂, hj₂, h₂⟩ := hpre b
  have hc : j₁ * j₂ = j₂ * j₁ := by
    have h := congrArg Subtype.val
      (hcomm.is_comm.comm (⟨j₁, hj₁⟩ : ↥((P : Subgroup G) ⊓ J)) ⟨j₂, hj₂⟩)
    exact Subtype.ext h
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← h₁, ← h₂, ← map_mul, ← map_mul, hc]

private theorem u3q_key (hK2 : U3AutData) {P : Sylow 3 G} {M : Subgroup G} {x : G}
    {J : Subgroup G} (hJ : IsU3Normal M x J) (hPC : (P : Subgroup G) ≤ centralizer ({x} : Set G))
    (hcard : Nat.card ↥((P : Subgroup G) ⊓ J) = 3 ^ 3) :
    ∀ c : ↥(centralizer ({x} : Set G)), (c : G) ∈ (P : Subgroup G) →
      ∃ t : ↥(centralizer ({x} : Set G)), (t : G) ∈ (P : Subgroup G) ⊓ J ∧
        QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3) (t⁻¹ * c) ∈
          reducedCentralizerOfJ x J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJbn : (r1sBar x J).Normal := r1sBar_normal_u3 hJ
  have hbot := u3_bar_inf_reducedCentralizer_eq_bot hJ
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
    exact Subtype.ext (u3q_mk_inj hP'p (hTP t.2) (one_mem _) h3)
  have hcardT : Nat.card ↥((((P : Subgroup G) ⊓ J).subgroupOf C).map χ) = 3 ^ 3 := by
    have e1 : (χ.comp (((P : Subgroup G) ⊓ J).subgroupOf C).subtype).range =
        (((P : Subgroup G) ⊓ J).subgroupOf C).map χ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← e1, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hPC)).toEquiv, hcard]
  have hA : (((P : Subgroup G) ⊓ J).subgroupOf C).map χ =
      ((P : Subgroup G).subgroupOf C).map χ := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.map_mono hTP) ?_
    rw [hcardT]
    exact Nat.le_of_dvd (by norm_num) (hK2 _ (r1sBar_isU3 hJ) _ (hP'p.map χ))
  intro c hc
  have hc' : χ c ∈ (((P : Subgroup G) ⊓ J).subgroupOf C).map χ := by
    rw [hA]
    exact mem_map_of_mem χ (mem_subgroupOf.mpr hc)
  obtain ⟨t, ht, htc⟩ := hc'
  refine ⟨t, mem_subgroupOf.mp ht, hχD _ ?_⟩
  rw [map_mul, map_inv, htc, inv_mul_cancel]

theorem u3_prop34_of_fusion (hS : Setting G) (hU0 : FullCoreLocal G) (hK1 : U3SylowData)
    (hK2 : U3AutData) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 3 P M) {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G}
    (hJ : IsU3Normal M x J) (hPC : (P : Subgroup G) ≤ centralizer ({x} : Set G))
    (hwc : LineWeaklyClosed x (P : Subgroup G)) : U3Prop34 3 P J x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard := (u3_T_data hS hU0 hK1 hp hM hgen hJ).2.2
  obtain ⟨hexp, hnc⟩ := u3q_sylow_facts hK1 hgen hJ hPC
  have hDc := u3_reducedCentralizer_isCyclic hS hU0 hK1 hp hM hgen hJ
  have hxD := (u3_xbar_facts hS hU0 hp hM hgen J).1
  have hbot := u3_bar_inf_reducedCentralizer_eq_bot hJ
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set ρ : C →* GenericReduced 3 x := QuotientGroup.mk' (primeComplementCore (G := C) 3) with hρ
  have hP'p : IsPGroup 3 ((P : Subgroup G).subgroupOf C) := P.isPGroup'.comap_subtype
  obtain ⟨W, hW⟩ : ∃ W : Subgroup C,
      W = (P : Subgroup G).subgroupOf C ⊓ (reducedCentralizerOfJ x J).comap ρ := ⟨_, rfl⟩
  have hWm : ∀ w : C, w ∈ W ↔ (w : G) ∈ (P : Subgroup G) ∧ ρ w ∈ reducedCentralizerOfJ x J := by
    intro w
    rw [hW, mem_inf, mem_subgroupOf, mem_comap]
  refine ⟨hPC, hcard, hexp, hnc, ⟨W.map C.subtype, ?_, ?_, ?_, ?_, ?_⟩, hwc⟩
  ·
    let f : W →* reducedCentralizerOfJ x J :=
      (ρ.comp W.subtype).codRestrict _ fun w => ((hWm w).mp w.2).2
    have hfi : Function.Injective f := fun a b hab => Subtype.ext
      (u3q_mk_inj hP'p (mem_subgroupOf.mpr ((hWm a).mp a.2).1)
        (mem_subgroupOf.mpr ((hWm b).mp b.2).1) (congrArg Subtype.val hab))
    have : IsCyclic W := isCyclic_of_injective f hfi
    exact isCyclic_of_surjective (W.equivMapOfInjective C.subtype C.subtype_injective)
      (W.equivMapOfInjective C.subtype C.subtype_injective).surjective
  ·
    exact ⟨⟨x, mem_centralizer_singleton_iff.mpr rfl⟩, (hWm _).mpr ⟨hgen.1, hxD⟩, rfl⟩
  ·
    rintro t ht _ ⟨w, hw, rfl⟩
    obtain ⟨hwP, hwD⟩ := (hWm w).mp hw
    have htC : t ∈ C := hPC ht.1
    have htP : (⟨t, htC⟩ : C) ∈ (P : Subgroup G).subgroupOf C := mem_subgroupOf.mpr ht.1
    have hwP' : w ∈ (P : Subgroup G).subgroupOf C := mem_subgroupOf.mpr hwP
    have htJ : ρ ⟨t, htC⟩ ∈ r1sBar x J := ⟨⟨t, htC⟩, mem_subgroupOf.mpr ht.2, rfl⟩
    rw [r1s_reducedCentralizerOfJ_eq, mem_centralizer_iff] at hwD
    have h1 : ρ ⟨t, htC⟩ * ρ w = ρ w * ρ ⟨t, htC⟩ := hwD _ htJ
    have h2 : (⟨t, htC⟩ : C) * w = w * ⟨t, htC⟩ :=
      u3q_mk_inj hP'p (mul_mem htP hwP') (mul_mem hwP' htP) (by rw [map_mul, map_mul, h1])
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
    have h3 : w = 1 := u3q_mk_inj hP'p (mem_subgroupOf.mpr hwP) (one_mem _) h1
    rw [mem_bot, h3]
    rfl
  ·
    refine le_antisymm (fun g hg => ?_) (sup_le inf_le_left ?_)
    · obtain ⟨t, ht, htD⟩ := u3q_key hK2 hJ hPC hcard ⟨g, hPC hg⟩ hg
      have hw : t⁻¹ * ⟨g, hPC hg⟩ ∈ W := by
        refine (hWm _).mpr ⟨?_, htD⟩
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
        exact mul_mem (inv_mem ht.1) hg
      have hg' : g = (t : G) * ((t⁻¹ * ⟨g, hPC hg⟩ : C) : G) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
      rw [hg']
      exact mul_mem_sup ht ⟨_, hw, rfl⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact ((hWm w).mp hw).1

end CFSG.LocalAnalysis.RankThreeTheoremC
