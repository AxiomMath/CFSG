module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.C25Abs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.C25Inner
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.C25Quasi
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.C25One
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce

public section

namespace CFSG.QuasithinUnique.A5.C25

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native
  CFSG.QuasithinUnique.Ch1

variable {G : Type} [Group G] [Finite G] {Gi L SI U : Subgroup G}

theorem false_of_central_odd
    (h36 : A36ForSQTKCat) (S : Setting Gi L SI U) {K : Subgroup G}
    (hK : K ∈ cComp Gi) (hLK : L ≤ K) (hn : (K.subgroupOf Gi).Normal)
    {TI : Subgroup G} {z : G} (hTI : IsSylowTwoOf TI Gi) (hzTI : z ∈ TI)
    (hzc : z ∈ Subgroup.centralizer (TI : Set G)) (hz2 : z * z = 1)
    (hinv : ∀ y ∈ oddCoreIn Gi, z⁻¹ * y * z = y⁻¹) {y : G} (hyK : y ∈ K)
    (hyp : (orderOf y).Prime) (hy2 : orderOf y ≠ 2) (hyc : ∀ k ∈ K, y * k = k * y) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKGi : K ≤ Gi := le_of_mem_cComp hK
  have hyGi : y ∈ Gi := hKGi hyK
  have hzGi : z ∈ Gi := hTI.1 hzTI
  have hQ := sqtkHypCat_quotient_of_pCoreOf_ne_bot S.qtke S.gi_core
  have hFin : Finite (Quo Gi) := hQ.finite
  have hyodd : Odd (orderOf (⟨y, hyK⟩ : ↥K)) := by
    rw [Subgroup.orderOf_mk]
    exact hyp.odd_of_ne_two hy2
  have hycen : (⟨y, hyK⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hyc g g.2).symm
  have hyO : y ∈ oddCoreIn Gi :=
    mem_oddCoreIn_of_central hKGi (subgroupOf_isSubnormal_of_open (subnormal_of_mem_cComp hK))
      hycen hyodd
  have hzy : z⁻¹ * y * z = y⁻¹ := hinv y hyO
  obtain ⟨zb, hzb⟩ : ∃ zb : Quo Gi, zb = mkO2 Gi ⟨z, hzGi⟩ := ⟨_, rfl⟩
  obtain ⟨yb, hyb⟩ : ∃ yb : Quo Gi, yb = mkO2 Gi ⟨y, hyGi⟩ := ⟨_, rfl⟩
  have hzb2 : zb * zb = 1 := by
    have h1 : (⟨z, hzGi⟩ * ⟨z, hzGi⟩ : ↥Gi) = 1 := Subtype.ext hz2
    rw [hzb, ← map_mul, h1, map_one]
  have hybz : zb⁻¹ * yb * zb = yb⁻¹ := by
    have h1 : (⟨z, hzGi⟩ : ↥Gi)⁻¹ * ⟨y, hyGi⟩ * ⟨z, hzGi⟩ = (⟨y, hyGi⟩ : ↥Gi)⁻¹ :=
      Subtype.ext hzy
    have h2 := congrArg (mkO2 Gi) h1
    rw [map_mul, map_mul, map_inv, map_inv] at h2
    rw [hzb, hyb]
    exact h2
  have hybL : yb ∈ modO2Image Gi K := by
    rw [hyb]
    exact P134.mk_mem_modO2Image hyK hyGi
  have hyb1 : yb ≠ 1 := by
    intro h
    rw [hyb] at h
    obtain ⟨k, hk⟩ := exists_two_pow_of_mkO2_eq_one ⟨y, hyGi⟩ h
    have hy2k : y ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hdvd : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hy2k
    exact hy2 ((Nat.prime_dvd_prime_iff_eq hyp Nat.prime_two).1 (hyp.dvd_of_dvd_pow hdvd))
  have hybcen : (⟨yb, hybL⟩ : ↥(modO2Image Gi K)) ∈ Subgroup.center ↥(modO2Image Gi K) := by
    rw [Subgroup.mem_center_iff]
    rintro ⟨a, g, hg, rfl⟩
    apply Subtype.ext
    show mkO2 Gi g * yb = yb * mkO2 Gi g
    rw [hyb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hyc (g : G) hg).symm
  obtain ⟨hconc, hcommon, -⟩ := lemma_1_2_1_four_strong S.qtke h36 S.gi_core hK
  have hqm : CFSG.IsQuasisimple ↥(modO2Image Gi K) :=
    isQuasisimple_modO2Image h36.core S hK hLK
  have hnonab : ∃ a b : ↥(modO2Image Gi K), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hqm.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a', b', fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩
  rcases hconc with ⟨-, hsimple, -⟩ | ⟨-, hZ3, h2list⟩ | h3 | h4
  ·
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(modO2Image Gi K)) with hb | ht
    · rw [hb, Subgroup.mem_bot] at hybcen
      exact hyb1 (congrArg Subtype.val hybcen)
    · obtain ⟨a, b, hab⟩ := hnonab
      have : a ∈ Subgroup.center ↥(modO2Image Gi K) := ht ▸ Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.1 this b).symm
  ·
    have hA : SylowCentralizingInvolInner (↥(modO2Image Gi K) ⧸ Subgroup.center ↥(modO2Image Gi K)) :=
      sylowInvolInner_of_case2 hZ3 (exists_elemAbelian_modO2Image S hLK) h2list
    have hTI2 : IsPGroup 2 ↥(TI.subgroupOf Gi) :=
      hTI.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTI.1).symm
    let P : Sylow 2 ↥Gi := hTI2.toSylow hTI.2.2
    let Sb : Sylow 2 (Quo Gi) := P.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Gi))
    have hzbS : zb ∈ Subgroup.centralizer ((Sb : Subgroup (Quo Gi)) : Set (Quo Gi)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      rw [Sylow.coe_mapSurjective] at hq
      obtain ⟨t, ht, rfl⟩ := hq
      have htTI : (t : G) ∈ TI := ht
      have hcomm : (t : G) * z = z * (t : G) := Subgroup.mem_centralizer_iff.1 hzc _ htTI
      rw [hzb, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hcomm
    have hLn : (modO2Image Gi K).Normal := hn.map (mkO2 Gi) (QuotientGroup.mk'_surjective _)
    have hperfL : Group.IsPerfect ↥(modO2Image Gi K) :=
      Subgroup.isPerfect_iff.2 (perfect_of_mem_cComp (modO2Image_mem_cComp hK))
    obtain ⟨x, hxL, hx⟩ := exists_inner_of_sylow_invol (L := modO2Image Gi K) Sb hperfL hA hzb2 hzbS
    have hcx : x * yb = yb * x := by
      have := Subgroup.mem_center_iff.1 hybcen ⟨x, hxL⟩
      exact congrArg Subtype.val this
    have hcen : zb⁻¹ * yb * zb = yb := by
      rw [hx yb hybL]
      calc x⁻¹ * yb * x = x⁻¹ * (x * yb) := by rw [hcx]; group
        _ = yb := by group
    have hsq : yb * yb = 1 := by
      have : yb⁻¹ = yb := by rw [← hybz, hcen]
      calc yb * yb = yb⁻¹ * yb := by rw [this]
        _ = 1 := inv_mul_cancel yb
    have hd1 : orderOf yb ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
    have hd2 : orderOf yb ∣ orderOf y := by
      apply orderOf_dvd_of_pow_eq_one
      rw [hyb, ← map_pow]
      have : (⟨y, hyGi⟩ : ↥Gi) ^ orderOf y = 1 := Subtype.ext (pow_orderOf_eq_one y)
      rw [this, map_one]
    have hcop : Nat.Coprime 2 (orderOf y) :=
      (Nat.coprime_primes Nat.prime_two hyp).2 (fun h => hy2 h.symm)
    have h1 : orderOf yb = 1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
    exact hyb1 (orderOf_eq_one_iff.1 h1)
  · exact not_case34 S hLK hcommon (Or.inl h3)
  · exact not_case34 S hLK hcommon (Or.inr h4)

theorem isQuasisimple_of_inv
    (h36 : A36ForSQTKCat) (S : Setting Gi L SI U) {K : Subgroup G}
    (hK : K ∈ cComp Gi) (hLK : L ≤ K) (hn : (K.subgroupOf Gi).Normal) (hnc : ¬ CharTwo K)
    {TI : Subgroup G} {z : G} (hTI : IsSylowTwoOf TI Gi) (hzTI : z ∈ TI)
    (hzc : z ∈ Subgroup.centralizer (TI : Set G)) (hz2 : z * z = 1)
    (hinv : ∀ y ∈ oddCoreIn Gi, z⁻¹ * y * z = y⁻¹) : CFSG.IsQuasisimple ↥K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hqm := isQuasisimple_modO2 h36.core S hK hLK
  have hperf : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 (perfect_of_mem_cComp hK)
  have hR : IsPGroup 2 ↥(CFSG.pCore 2 ↥K) := CFSG.pCore_isPGroup (p := 2) (G := ↥K)
  have hRmax : ∀ N : Subgroup ↥K, N.Normal → IsPGroup 2 ↥N → N ≤ CFSG.pCore 2 ↥K :=
    fun N hN hp => le_sSup ⟨hN, hp⟩
  have hbar : ∀ D : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K), D.Normal →
      D = ⊤ ∨ D ≤ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) :=
    fun D hD => CFSG.LocalCores.quasisimple_normal_subgroups hqm hD
  have hnc' : ¬ Subgroup.centralizer ((CFSG.pCore 2 ↥K : Subgroup ↥K) : Set ↥K) ≤
      CFSG.pCore 2 ↥K := by
    intro h
    apply hnc
    rw [charTwo_iff_internal]
    assumption
  rcases quasisimple_or_central_odd (CFSG.pCore 2 ↥K) hR hRmax hperf hbar hqm.2.1 hqm.2.2 hnc' with
    ⟨hs, hnab⟩ | ⟨y, hycen, hyp, hy2⟩
  · exact ⟨hperf, hs, hnab⟩
  · exfalso
    refine false_of_central_odd h36 S hK hLK hn hTI hzTI hzc hz2 hinv (y := (y : G)) y.2
      (by rw [Subgroup.orderOf_coe]; exact hyp) (by rw [Subgroup.orderOf_coe]; exact hy2) ?_
    intro k hk
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hycen ⟨k, hk⟩)).symm

end CFSG.QuasithinUnique.A5.C25
