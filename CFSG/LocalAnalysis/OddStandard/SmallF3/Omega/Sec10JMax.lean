module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10JCent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10JWb

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G]

private lemma mem_centerIn_iff {K : Subgroup G} (a : G) :
    a ∈ centerIn K ↔ a ∈ K ∧ ∀ k ∈ K, a * k = k * a := by
  rw [centerIn, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, fun k hk => (congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨k, hk⟩)).symm⟩
  · rintro ⟨haK, hcent⟩
    exact ⟨⟨a, haK⟩, Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext (hcent (y : G) y.2).symm, rfl⟩

private theorem exists_mul_of_le_normalizer {V W : Subgroup G}
    (h : ∀ v ∈ V, ∀ w ∈ W, v * w * v⁻¹ ∈ W) {x : G} (hx : x ∈ V ⊔ W) :
    ∃ v ∈ V, ∃ w ∈ W, x = v * w := by
  let D : Subgroup G :=
    { carrier := {x | ∃ v ∈ V, ∃ w ∈ W, x = v * w}
      one_mem' := ⟨1, V.one_mem, 1, W.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨v1, hv1, w1, hw1, rfl⟩ ⟨v2, hv2, w2, hw2, rfl⟩
        refine ⟨v1 * v2, V.mul_mem hv1 hv2, (v2⁻¹ * w1 * v2) * w2, W.mul_mem ?_ hw2, ?_⟩
        · simpa using h v2⁻¹ (V.inv_mem hv2) w1 hw1
        · group
      inv_mem' := by
        rintro _ ⟨v, hv, w, hw, rfl⟩
        refine ⟨v⁻¹, V.inv_mem hv, v * w⁻¹ * v⁻¹, h v hv w⁻¹ (W.inv_mem hw), ?_⟩
        group }
  have hle : V ⊔ W ≤ D :=
    sup_le (fun v hv => ⟨v, hv, 1, W.one_mem, by simp⟩)
      (fun w hw => ⟨1, V.one_mem, w, hw, by simp⟩)
  exact hle hx

private theorem commutator_sq_mem_of_sup_normal {U N V : Subgroup G}
    (hNU : N ≤ U) (hVU : V ≤ U) (hUV : U = V ⊔ N)
    (hNnorm : ∀ u ∈ U, ∀ n ∈ N, u * n * u⁻¹ ∈ N)
    (hc : ∀ a ∈ V, ∀ b ∈ V, a * b * a⁻¹ * b⁻¹ ∈ N)
    (hs : ∀ a ∈ V, a * a ∈ N) :
    ∀ x ∈ U, ∀ y ∈ U, x * y * x⁻¹ * y⁻¹ ∈ N ∧ x * x ∈ N := by
  let N' : Subgroup ↥U := N.subgroupOf U
  let V' : Subgroup ↥U := V.subgroupOf U
  have hN'norm : N'.Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNU]
    exact Subgroup.le_normalizer_iff.mpr hNnorm
  haveI : N'.Normal := hN'norm
  let q : ↥U →* ↥U ⧸ N' := QuotientGroup.mk' N'
  have hmem_iff : ∀ x : ↥U, x ∈ N' ↔ (x : G) ∈ N := by
    intro x
    change x ∈ N.subgroupOf U ↔ (x : G) ∈ N
    exact Subgroup.mem_subgroupOf
  have hq1 : ∀ (x : G) (hx : x ∈ U), q ⟨x, hx⟩ = 1 ↔ x ∈ N := by
    intro x hx
    rw [show q ⟨x, hx⟩ = ((⟨x, hx⟩ : ↥U) : ↥U ⧸ N') from rfl, QuotientGroup.eq_one_iff,
      hmem_iff]
  have hq_mul : ∀ (v : G) (hv : v ∈ U) (n : G) (hn : n ∈ N) (hm : v * n ∈ U),
      q ⟨v * n, hm⟩ = q ⟨v, hv⟩ := by
    intro v hv n hn hm
    rw [show (⟨v * n, hm⟩ : ↥U) = (⟨v, hv⟩ : ↥U) * (⟨n, hNU hn⟩ : ↥U) from Subtype.ext rfl,
      map_mul, (hq1 n (hNU hn)).mpr hn, mul_one]
  have hVq_comm : ∀ (a b : G) (ha : a ∈ V) (hb : b ∈ V),
      q ⟨a, hVU ha⟩ * q ⟨b, hVU hb⟩ = q ⟨b, hVU hb⟩ * q ⟨a, hVU ha⟩ := by
    intro a b ha hb
    rw [← commutatorElement_eq_one_iff_mul_comm]
    have hmem : ⁅(⟨a, hVU ha⟩ : ↥U), (⟨b, hVU hb⟩ : ↥U)⁆ ∈ N' := by
      rw [hmem_iff]
      change U.subtype ⁅(⟨a, hVU ha⟩ : ↥U), (⟨b, hVU hb⟩ : ↥U)⁆ ∈ N
      rw [map_commutatorElement]
      exact hc a ha b hb
    calc ⁅q ⟨a, hVU ha⟩, q ⟨b, hVU hb⟩⁆
        = q ⁅(⟨a, hVU ha⟩ : ↥U), (⟨b, hVU hb⟩ : ↥U)⁆ :=
          (map_commutatorElement q _ _).symm
      _ = 1 := by
          rw [show q ⁅(⟨a, hVU ha⟩ : ↥U), (⟨b, hVU hb⟩ : ↥U)⁆
                = ((⁅(⟨a, hVU ha⟩ : ↥U), (⟨b, hVU hb⟩ : ↥U)⁆ : ↥U) : ↥U ⧸ N') from rfl,
              QuotientGroup.eq_one_iff]
          exact hmem
  have hVq_sq : ∀ (a : G) (ha : a ∈ V), q ⟨a, hVU ha⟩ * q ⟨a, hVU ha⟩ = 1 := by
    intro a ha
    have hmem : (⟨a, hVU ha⟩ * ⟨a, hVU ha⟩ : ↥U) ∈ N' := by
      rw [hmem_iff]
      exact hs a ha
    have hq : q (⟨a, hVU ha⟩ * ⟨a, hVU ha⟩ : ↥U) = 1 := by
      rw [show q (⟨a, hVU ha⟩ * ⟨a, hVU ha⟩ : ↥U)
            = ((⟨a, hVU ha⟩ * ⟨a, hVU ha⟩ : ↥U) : ↥U ⧸ N') from rfl,
          QuotientGroup.eq_one_iff]
      exact hmem
    rwa [map_mul] at hq
  have decomp : ∀ (x : G) (hx : x ∈ U), ∃ v ∈ V, ∃ n ∈ N, x = v * n := by
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥U) ∈ V' ⊔ N' := by
      have htop : V' ⊔ N' = ⊤ := by
        change (V.subgroupOf U) ⊔ (N.subgroupOf U) = ⊤
        rw [← Subgroup.subgroupOf_sup hVU hNU, ← hUV, Subgroup.subgroupOf_self]
      rw [htop]; trivial
    obtain ⟨v, hv, n, hn, hvn⟩ := Subgroup.mem_sup_of_normal_right.mp hx'
    exact ⟨(v : G), Subgroup.mem_subgroupOf.mp hv, (n : G), Subgroup.mem_subgroupOf.mp hn,
      (congrArg Subtype.val hvn).symm⟩
  intro x hx y hy
  obtain ⟨v1, hv1V, n1, hn1N, hxe⟩ := decomp x hx
  obtain ⟨v2, hv2V, n2, hn2N, hye⟩ := decomp y hy
  subst hxe
  subst hye
  constructor
  · have hxy : (v1 * n1) * (v2 * n2) * (v1 * n1)⁻¹ * (v2 * n2)⁻¹ ∈ U :=
      U.mul_mem (U.mul_mem (U.mul_mem hx hy) (U.inv_mem hx)) (U.inv_mem hy)
    refine (hq1 _ hxy).mp ?_
    have h1 : q ⟨(v1 * n1) * (v2 * n2) * (v1 * n1)⁻¹ * (v2 * n2)⁻¹, hxy⟩
        = ⁅q ⟨v1, hVU hv1V⟩, q ⟨v2, hVU hv2V⟩⁆ := by
      rw [show (⟨(v1 * n1) * (v2 * n2) * (v1 * n1)⁻¹ * (v2 * n2)⁻¹, hxy⟩ : ↥U)
            = ⁅(⟨v1 * n1, U.mul_mem (hVU hv1V) (hNU hn1N)⟩ : ↥U),
              (⟨v2 * n2, U.mul_mem (hVU hv2V) (hNU hn2N)⟩ : ↥U)⁆ from Subtype.ext rfl,
          map_commutatorElement]
      rw [hq_mul v1 (hVU hv1V) n1 hn1N (U.mul_mem (hVU hv1V) (hNU hn1N)),
        hq_mul v2 (hVU hv2V) n2 hn2N (U.mul_mem (hVU hv2V) (hNU hn2N))]
    rw [h1, commutatorElement_eq_one_iff_mul_comm.mpr (hVq_comm v1 v2 hv1V hv2V)]
  · have hsq : (v1 * n1) * (v1 * n1) ∈ U := U.mul_mem hx hx
    refine (hq1 _ hsq).mp ?_
    have h1 : q ⟨(v1 * n1) * (v1 * n1), hsq⟩
        = q ⟨v1, hVU hv1V⟩ * q ⟨v1, hVU hv1V⟩ := by
      rw [show (⟨(v1 * n1) * (v1 * n1), hsq⟩ : ↥U)
            = (⟨v1 * n1, U.mul_mem (hVU hv1V) (hNU hn1N)⟩ : ↥U) *
              (⟨v1 * n1, U.mul_mem (hVU hv1V) (hNU hn1N)⟩ : ↥U) from Subtype.ext rfl,
          map_mul]
      rw [hq_mul v1 (hVU hv1V) n1 hn1N (U.mul_mem (hVU hv1V) (hNU hn1N))]
    rw [h1, hVq_sq v1 hv1V]

theorem sec10J_key [Finite G] (h102 : Asc82Lemma102) (hP5 : Asc82FactPockets5)
    (hC5 : Asc82FactCentZ5) (hF : Asc82Fact1051) (hb : Asc82Basic10) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2)
    {V : Subgroup G} (hVS : V ≤ S) (hzV : z ∈ V) (hV : IsElemAbelianMod z V) :
    V ≤ secW t K1 K2 ∨ Nat.card ↥V < Nat.card ↥(secW t K1 K2) := by
  obtain ⟨hpsp, htC, _, _, hSnormL, hSyl⟩ := hb G t L S z hctx.toSec10Z
  have hWelem := sec10J_W_elem hP5 hC5 hb hctx
  have hzW : z ∈ secW t K1 K2 := hWelem.1
  have hzpW : zpowers z ≤ secW t K1 K2 := Subgroup.zpowers_le.mpr hzW
  have hWS : secW t K1 K2 ≤ S := sec10J_W_le hP5 hb hctx
  have hWnormal : ∀ s ∈ S, ∀ w ∈ secW t K1 K2, s * w * s⁻¹ ∈ secW t K1 K2 :=
    sec10J_W_normal hP5 hb hctx
  have hUS : V ⊔ secW t K1 K2 ≤ S := sup_le hVS hWS
  have hNormVW : ∀ v ∈ V, ∀ w ∈ secW t K1 K2, v * w * v⁻¹ ∈ secW t K1 K2 :=
    fun v hv w hw => hWnormal v (hVS hv) w hw
  have hNnorm : ∀ u ∈ V ⊔ secW t K1 K2, ∀ n ∈ secW t K1 K2,
      u * n * u⁻¹ ∈ secW t K1 K2 :=
    fun u hu n hn => hWnormal u (hUS hu) n hn
  have hc : ∀ a ∈ V, ∀ b ∈ V, a * b * a⁻¹ * b⁻¹ ∈ secW t K1 K2 :=
    fun a ha b hb => hzpW (hV a ha b hb).1
  have hs : ∀ a ∈ V, a * a ∈ secW t K1 K2 := fun a ha => hzpW (hV a ha a ha).2
  have hcomm18 : ∀ x ∈ V ⊔ secW t K1 K2, ∀ y ∈ V ⊔ secW t K1 K2,
      x * y * x⁻¹ * y⁻¹ ∈ secW t K1 K2 ∧ x * x ∈ secW t K1 K2 :=
    commutator_sq_mem_of_sup_normal (U := V ⊔ secW t K1 K2) (N := secW t K1 K2) (V := V)
      le_sup_right le_sup_left rfl hNnorm hc hs
  have hcentU : centralizer (L : Set G) ⊓ (V ⊔ secW t K1 K2) = zpowers t :=
    sec10J_cent_eq h102 hP5 hC5 hb hctx hVS hzV hV
  have hzL : z ∈ L := (Subgroup.mem_inf.mp (hctx.pocket1.2.1 hctx.pocket1.1)).1
  have hzSL : z ∈ S ⊓ L := ⟨hctx.mem_S, hzL⟩
  have hzC : z ∈ centerIn (S ⊓ L) :=
    (mem_centerIn_iff z).mpr ⟨hzSL, fun k hk => (hctx.central k hk.1).symm⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUp : IsPGroup 2 ↥(V ⊔ secW t K1 K2) := hctx.sylow.2.1.to_le hUS
  obtain ⟨k0, hcardU⟩ := (IsPGroup.iff_card).mp hUp
  have hdvd : (secW t K1 K2).relIndex (V ⊔ secW t K1 K2) ∣ Nat.card ↥(V ⊔ secW t K1 K2) :=
    Subgroup.relIndex_dvd_card (H := secW t K1 K2) (K := V ⊔ secW t K1 K2)
  obtain ⟨m, _, hrel⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (hcardU ▸ hdvd)
  have hSnormW : S ≤ Subgroup.normalizer (secW t K1 K2 : Set G) :=
    Subgroup.le_normalizer_iff.mpr hWnormal
  have hrelV : (V ⊓ secW t K1 K2).relIndex V = 2 ^ m := by
    have hsup : (V.subgroupOf S) ⊔ ((secW t K1 K2).subgroupOf S) =
        (V ⊔ secW t K1 K2).subgroupOf S := (Subgroup.subgroupOf_sup hVS hWS).symm
    haveI : ((secW t K1 K2).subgroupOf S).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hWS).mpr hSnormW
    have h3 : (secW t K1 K2).relIndex (V ⊔ secW t K1 K2) = (secW t K1 K2).relIndex V := by
      have h := Subgroup.relIndex_sup_right (H := V.subgroupOf S) (K := (secW t K1 K2).subgroupOf S)
      rw [hsup] at h
      rw [Subgroup.relIndex_subgroupOf (show V ⊔ secW t K1 K2 ≤ S from hUS)] at h
      rw [Subgroup.relIndex_subgroupOf hVS] at h
      exact h
    rw [Subgroup.inf_relIndex_left, ← h3, hrel]
  have hcardV : Nat.card ↥V = 2 ^ m * Nat.card ↥(V ⊓ secW t K1 K2) := by
    have h := Subgroup.relIndex_mul_card (H := V ⊓ secW t K1 K2) (K := V)
    rw [inf_eq_left.mpr inf_le_left, hrelV] at h
    exact h.symm
  have hcardC : Nat.card ↥(V ⊓ secW t K1 K2) ≤
      Nat.card {w : G // w ∈ secW t K1 K2 ∧
        ∀ u ∈ V ⊔ secW t K1 K2, w * u * w⁻¹ * u⁻¹ ∈ zpowers z} := by
    let f : ↥(V ⊓ secW t K1 K2) →
        {w : G // w ∈ secW t K1 K2 ∧
          ∀ u ∈ V ⊔ secW t K1 K2, w * u * w⁻¹ * u⁻¹ ∈ zpowers z} :=
      fun a => ⟨(a : G), (Subgroup.mem_inf.mp a.2).2, by
        intro u hu
        obtain ⟨v, hvV, n, hnW, rfl⟩ := exists_mul_of_le_normalizer hNormVW hu
        have haV : (a : G) ∈ V := (Subgroup.mem_inf.mp a.2).1
        have haW : (a : G) ∈ secW t K1 K2 := (Subgroup.mem_inf.mp a.2).2
        have h1 : (a : G) * v * (a : G)⁻¹ * v⁻¹ ∈ zpowers z := (hV a haV v hvV).1
        have h2 : (a : G) * n * (a : G)⁻¹ * n⁻¹ ∈ zpowers z := (hWelem.2 a haW n hnW).1
        obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h2
        have hcomm : v * (z ^ i) * v⁻¹ = z ^ i := by
          have hvz : v * z = z * v := hctx.central v (hVS hvV)
          have hc' : Commute v (z ^ i) := (show Commute v z from hvz).zpow_right i
          rw [hc'.eq, mul_assoc, mul_inv_cancel, mul_one]
        rw [show (a : G) * (v * n) * (a : G)⁻¹ * (v * n)⁻¹ =
              ((a : G) * v * (a : G)⁻¹ * v⁻¹) *
                (v * ((a : G) * n * (a : G)⁻¹ * n⁻¹) * v⁻¹) from by group, ← hi, hcomm]
        exact Subgroup.mul_mem _ h1 (Subgroup.zpow_mem_zpowers z i)⟩
    exact Nat.card_le_card_of_injective f fun a b hab =>
      Subtype.ext (by have h := congrArg Subtype.val hab; exact h)
  by_cases hm0 : m = 0
  · left
    have hrel1 : (secW t K1 K2).relIndex (V ⊔ secW t K1 K2) = 1 := by
      rw [hrel, hm0, pow_zero]
    exact le_trans le_sup_left (Subgroup.relIndex_eq_one.mp hrel1)
  · right
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
    obtain ⟨hle2, hlt⟩ := hF G L (S ⊓ L) S t z K1 K2 (V ⊔ secW t K1 K2) hpsp hSyl
      inf_le_left hSnormL hctx.sylow.2.1 hctx.involution htC hctx.sylow.1 hzC hctx.pocket.1
      hctx.central hctx.pocket1 hctx.pocket2 hctx.ne le_sup_right hUS hcentU hcomm18 m hm1 hrel
    refine lt_of_le_of_lt ?_ hlt
    calc Nat.card ↥V = 2 ^ m * Nat.card ↥(V ⊓ secW t K1 K2) := hcardV
      _ ≤ 2 ^ m * Nat.card {w : G // w ∈ secW t K1 K2 ∧
            ∀ u ∈ V ⊔ secW t K1 K2, w * u * w⁻¹ * u⁻¹ ∈ zpowers z} :=
          Nat.mul_le_mul_left _ hcardC

end CFSG.OddStandard.SmallF3.Omega
