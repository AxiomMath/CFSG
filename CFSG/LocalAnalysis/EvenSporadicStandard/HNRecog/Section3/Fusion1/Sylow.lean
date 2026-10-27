module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SuborbitFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.OddIndex
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.NotConj

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog Subgroup

private theorem natCard_Elem2 (n : ℕ) : Nat.card (Elem2 n) = 2 ^ n := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

private theorem natCard_perm_fin_five : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
  rw [Nat.card_perm, Nat.card_fin]
  norm_num

private theorem factorization_two_pow_eleven_mul_fifteen :
    Nat.factorization (2 ^ 11 * 15) 2 = 11 := by
  rw [Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow_self (by norm_num : Nat.Prime 2),
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 15)]

private theorem zpow_eq_one_or_self_of_sq_eq_one {H : Type*} [Group H] {x : H}
    (hx : x ^ 2 = 1) (k : ℤ) : x ^ k = 1 ∨ x ^ k = x := by
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · left
    rw [hm, zpow_mul, show x ^ (2 : ℤ) = 1 by simpa using hx, one_zpow]
  · right
    rw [hm, zpow_add, zpow_mul, show x ^ (2 : ℤ) = 1 by simpa using hx,
      one_zpow, one_mul, zpow_one]

private theorem mem_sup_zpowers_two {H : Type*} [Group H] {x y w : H}
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hcomm : x * y = y * x)
    (hw : w ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y) :
    w = 1 ∨ w = x ∨ w = y ∨ w = x * y := by
  have hxcent : x ∈ Subgroup.centralizer (Subgroup.zpowers y : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact (Commute.zpow_right hcomm n).eq.symm
  have hle : Subgroup.zpowers x ≤ Subgroup.normalizer (Subgroup.zpowers y : Set H) :=
    Subgroup.zpowers_le.mpr
      (Subgroup.centralizer_le_normalizer (Subgroup.zpowers y : Set H) hxcent)
  change w ∈ (↑(Subgroup.zpowers x ⊔ Subgroup.zpowers y) : Set H) at hw
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle, Set.mem_mul] at hw
  obtain ⟨a, ha, b, hb, hab⟩ := hw
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  rw [← hab]
  rcases zpow_eq_one_or_self_of_sq_eq_one hx m with h1 | h1 <;>
    rcases zpow_eq_one_or_self_of_sq_eq_one hy n with h2 | h2 <;>
    rw [h1, h2] <;> simp

private theorem natCard_of_isShapeTwoTwoSixS5 {X : Type*} [Group X]
    (h : IsShapeTwoTwoSixS5 X) : Nat.card X = 2 ^ 11 * 15 := by
  obtain ⟨V, N, hVnorm, hNnorm, hVN, hVE, hNVE, hXNE⟩ := h
  haveI : V.Normal := hVnorm
  haveI : N.Normal := hNnorm
  haveI : (V.subgroupOf N).Normal := hVnorm.subgroupOf N
  have hcardV : Nat.card V = 2 ^ 2 := by
    rw [Nat.card_congr (Classical.choice hVE).toEquiv, natCard_Elem2]
  have hcardNV : Nat.card (N ⧸ V.subgroupOf N) = 2 ^ 6 := by
    rw [Nat.card_congr (Classical.choice hNVE).toEquiv, natCard_Elem2]
  have hcardN : Nat.card N = 2 ^ 8 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (V.subgroupOf N), hcardNV,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVN).toEquiv, hcardV]
    norm_num
  have hcardXN : Nat.card (X ⧸ N) = 120 := by
    rw [Nat.card_congr (Classical.choice hXNE).toEquiv, natCard_perm_fin_five]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hcardXN, hcardN]
  norm_num

theorem exists_isConj_z_of_labelled (hI : TwoHSInterface) (hS : SuborbitFacts) {G : Type} [Group G]
    [Finite G] {a z : G} (h : IsF5Type a z) {z' b' u' : ↥(Gx a)}
    (hF : TwoHSFacts ↥(Gx a) (GxSelf a) z' b' u') :
    IsConj z (z' : G) ∨ IsConj z (a * (z' : G)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hE⟩ := h.cent_a
  set Xsub : Subgroup ↥(Gx a) := Subgroup.centralizer ({z'} : Set ↥(Gx a)) with hXsub
  have hcardX : Nat.card Xsub = 2 ^ 11 * 15 := by
    rw [hXsub]
    exact natCard_of_isShapeTwoTwoSixS5 hF.cent_z
  let T₀ : Sylow 2 Xsub := Classical.choice (inferInstance : Nonempty (Sylow 2 Xsub))
  have hcardT₀ : Nat.card T₀ = 2 ^ 11 := by
    rw [Sylow.card_eq_multiplicity T₀, hcardX, factorization_two_pow_eleven_mul_fifteen]
  let T : Subgroup ↥(Gx a) := (T₀ : Subgroup Xsub).map Xsub.subtype
  have hTp : IsPGroup 2 T := (T₀.isPGroup').map Xsub.subtype
  have hcardT : Nat.card T = 2 ^ 11 := by
    change Nat.card ((T₀ : Subgroup Xsub).map Xsub.subtype) = 2 ^ 11
    rw [Subgroup.card_subtype, hcardT₀]
  have hT_le : T ≤ Subgroup.centralizer ({z'} : Set ↥(Gx a)) := by
    change (T₀ : Subgroup Xsub).map Xsub.subtype ≤ Xsub
    exact Subgroup.map_subtype_le _
  have hcenterT : centerOf T = Subgroup.zpowers (GxSelf a) ⊔ Subgroup.zpowers z' :=
    hS.sylow_centre ↥(Gx a) E hE (GxSelf a) z' b' u' hF T hT_le hcardT
  have hfacH : (Nat.card ↥(Gx a)).factorization 2 = 11 := by
    rw [hF.card_eq, show 2 ^ 11 * 3 ^ 2 * 5 ^ 3 * 7 * 11 = 2 ^ 11 * (3 ^ 2 * 5 ^ 3 * 7 * 11)
        by ring,
      Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self (by norm_num : Nat.Prime 2),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3 ^ 2 * 5 ^ 3 * 7 * 11)]
  have hcardfacT : Nat.card T = 2 ^ (Nat.card ↥(Gx a)).factorization 2 := by
    rw [hcardT, hfacH]
  let TG : Subgroup G := T.map (Gx a).subtype
  have hTGp : IsPGroup 2 TG := hTp.map (Gx a).subtype
  obtain ⟨P, hTGP⟩ := hTGp.exists_le_sylow
  obtain ⟨w, hConj_zw, hcenterP⟩ := exists_isConj_centerOf_sylow h.orderOf_z h.cent_z P
  have haH_centerT : GxSelf a ∈ centerOf T := by
    rw [hcenterT]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have haH_T : GxSelf a ∈ T := (Subgroup.mem_inf.1 haH_centerT).1
  have ha_TG : a ∈ TG := by
    have hmem : ((GxSelf a : ↥(Gx a)) : G) ∈ TG :=
      Subgroup.mem_map_of_mem (Gx a).subtype haH_T
    simpa [GxSelf] using hmem
  have ha_P : a ∈ (P : Subgroup G) := hTGP ha_TG
  have hwcenterP : w ∈ centerOf (P : Subgroup G) := hcenterP ▸ Subgroup.mem_zpowers w
  have hwcentP : w ∈ Subgroup.centralizer (P : Set G) := (Subgroup.mem_inf.1 hwcenterP).2
  have hwa : w ∈ Gx a := by
    rw [mem_Gx]
    exact Subgroup.mem_centralizer_iff.1 hwcentP a ha_P
  let w' : ↥(Gx a) := ⟨w, hwa⟩
  have hw'_cent : w' ∈ Subgroup.centralizer (T : Set ↥(Gx a)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    apply Subtype.ext
    change (t : G) * w = w * (t : G)
    exact Subgroup.mem_centralizer_iff.1 hwcentP (t : G)
      (hTGP (Subgroup.mem_map_of_mem (Gx a).subtype ht))
  have horder_w : orderOf w = 2 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 hConj_zw
    rw [← hc]
    simpa [MulAut.conj_apply] using
      (MulEquiv.orderOf_eq (MulAut.conj c) z).trans h.orderOf_z
  have horder_w' : orderOf w' = 2 := by
    change orderOf (⟨w, hwa⟩ : ↥(Gx a)) = 2
    rw [Subgroup.orderOf_mk, horder_w]
  have hw'_p : IsPGroup 2 (Subgroup.zpowers w') := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, horder_w']
    norm_num
  have hnormalizer : Subgroup.zpowers w' ≤ Subgroup.normalizer (T : Set ↥(Gx a)) :=
    Subgroup.zpowers_le.mpr
      (Subgroup.centralizer_le_normalizer (T : Set ↥(Gx a)) hw'_cent)
  have hsup_p : IsPGroup 2 (T ⊔ Subgroup.zpowers w' : Subgroup ↥(Gx a)) :=
    IsPGroup.to_sup_of_normal_left' hTp hw'_p hnormalizer
  have hsup_eq : T ⊔ Subgroup.zpowers w' = T := by
    have h := (Sylow.ofCard T hcardfacT).is_maximal' hsup_p le_sup_left
    simpa using h
  have hw'_mem_T : w' ∈ T := by
    rw [← hsup_eq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers w')
  have hw'_inZ : w' ∈ centerOf T := ⟨hw'_mem_T, hw'_cent⟩
  have hw'join : w' ∈ Subgroup.zpowers (GxSelf a) ⊔ Subgroup.zpowers z' :=
    hcenterT ▸ hw'_inZ
  have haH2 : (GxSelf a) ^ 2 = 1 := by
    rw [← hF.orderOf_a]
    exact pow_orderOf_eq_one _
  have hz'2 : z' ^ 2 = 1 := by
    rw [← hF.orderOf_z]
    exact pow_orderOf_eq_one _
  have haHcenter : GxSelf a ∈ Subgroup.center ↥(Gx a) :=
    hF.center_eq ▸ Subgroup.mem_zpowers _
  have hcomm : GxSelf a * z' = z' * GxSelf a :=
    (Subgroup.mem_center_iff.1 haHcenter z').symm
  have hcase : w' = 1 ∨ w' = GxSelf a ∨ w' = z' ∨ w' = GxSelf a * z' :=
    mem_sup_zpowers_two haH2 hz'2 hcomm hw'join
  have hw'_ne_one : w' ≠ 1 := by
    intro hh
    have : (2 : ℕ) = 1 := by rw [← horder_w', hh, orderOf_one]
    omega
  have hw'_ne_aH : w' ≠ GxSelf a := by
    intro hh
    have hwa' : w = a := by
      have h2 := congrArg (fun x : ↥(Gx a) => (x : G)) hh
      simpa [w', GxSelf] using h2
    exact not_isConj_of_isF5Type hI h ((hwa' ▸ hConj_zw).symm)
  rcases hcase with hh | hh | hh | hh
  · exact absurd hh hw'_ne_one
  · exact absurd hh hw'_ne_aH
  · left
    have hwz : w = (z' : G) := by
      have h2 := congrArg (fun x : ↥(Gx a) => (x : G)) hh
      simpa [w'] using h2
    exact hwz ▸ hConj_zw
  · right
    have hwaz : w = a * (z' : G) := by
      have h2 := congrArg (fun x : ↥(Gx a) => (x : G)) hh
      simpa [w', GxSelf] using h2
    exact hwaz ▸ hConj_zw

end CFSG.EvenSporadicStandard.HNRecog.Section3
