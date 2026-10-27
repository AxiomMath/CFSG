module

public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977StandardCyclic
public import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Sylow
public import CFSG.GroupTheory.SylowCentralCoprimeQuotient
public import CFSG.GroupTheory.ConjKerCenter
public import CFSG.GroupTheory.InvolutionFixedCentralSylow
public import CFSG.GroupTheory.TwoCentralInvolutionConj
public import CFSG.GroupTheory.ABGLocalTools.PStabilityCoreGW

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem mem_of_isSylowTwoIn_of_commute {X : Type} [Group X] [Finite X]
    {S H : Subgroup X} (hS : IsSylowTwoIn S H) {t : X} (htH : t ∈ H)
    (htc : ∀ s ∈ S, s * t = t * s) (ht2 : orderOf t = 2) : t ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := CFSG.ComponentClassification.GrSLit.GrS5.IsSylowTwoIn.isPGroup hS
  have htP : IsPGroup 2 (Subgroup.zpowers t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ht2, pow_one]
  have htCen : t ∈ Subgroup.centralizer (S : Set X) :=
    Subgroup.mem_centralizer_iff.mpr fun s hs => htc s hs
  have hSleC : S ≤ Subgroup.centralizer (Subgroup.zpowers t : Set X) :=
    Subgroup.le_centralizer_iff.mpr (Subgroup.zpowers_le.mpr htCen)
  have hSleN : S ≤ Subgroup.normalizer (Subgroup.zpowers t : Set X) :=
    hSleC.trans (Subgroup.centralizer_le_normalizer _)
  set U : Subgroup X := S ⊔ Subgroup.zpowers t with hU
  have hsup : IsPGroup 2 U := hS2.to_sup_of_normal_right' htP hSleN
  have hsupH : U ≤ H := sup_le hS.1 (Subgroup.zpowers_le.mpr htH)
  have heq : U = S :=
    CFSG.ComponentClassification.GrSLit.IsSylowTwoIn.eq_of_le hS le_sup_left hsupH hsup
  exact heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers t)

private theorem card_center_inf_of_isStandardSubgroup
    {J : Subgroup G} (hst : IsStandardSubgroup J) (hZ : Odd (Nat.card (center ↥J)))
    (hZT : ∀ T : Sylow 2 (↥J ⧸ center ↥J),
      Nat.card (center (T : Subgroup (↥J ⧸ center ↥J))) = 2)
    {t : G} (ht : orderOf t = 2) (htJ : t ∈ centralizer (J : Set G)) {S : Subgroup G}
    (hS : IsSylowTwoIn S (centralizer ({t} : Set G))) :
    Nat.card (center ↥(S ⊓ J : Subgroup G)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := centralizer ({t} : Set G) with hCdef
  obtain ⟨hTC, hCT, hCn, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
      (CFSG.IsStandardSubgroup.assembly hst) htJ ht
  have : Group.IsPerfect ↥J := hst.1.1
  have hJsub : (J.subgroupOf C).IsSubnormal := hCn.isSubnormal
  obtain ⟨hTleJ, P, hP⟩ :=
    CFSG.ComponentClassification.GrSLit.GrS5.isSylowTwoIn_inf_of_isSubnormal
      (P := S) (K := J) hS hCT hJsub
  let π : ↥J →* (↥J ⧸ center ↥J) := QuotientGroup.mk' (center ↥J)
  let Tbar : Sylow 2 (↥J ⧸ center ↥J) :=
    P.mapSurjective (QuotientGroup.mk'_surjective (center ↥J))
  have hbar : (Tbar : Subgroup (↥J ⧸ center ↥J)) = (P : Subgroup ↥J).map π :=
    Sylow.coe_mapSurjective _ P
  have hNodd : ¬ 2 ∣ Nat.card (Subgroup.center ↥J) := hZ.not_two_dvd_nat
  have hPp : IsPGroup 2 (P : Subgroup ↥J) := P.isPGroup'
  have hcardmap : Nat.card (center ↥((P : Subgroup ↥J).map π)) =
      Nat.card (center ↥(P : Subgroup ↥J)) :=
    CFSG.GroupTheory.card_center_map_mk_of_isPGroup (p := 2) (N := Subgroup.center ↥J) hNodd hPp
  have hcardP : Nat.card (center ↥(P : Subgroup ↥J)) = 2 := by
    rw [← hcardmap, ← hbar]
    exact hZT Tbar
  have hcardTsub : Nat.card (center ↥((S ⊓ J).subgroupOf J)) = 2 := by
    rw [← hP]
    exact hcardP
  have e : ↥((S ⊓ J).subgroupOf J) ≃* ↥(S ⊓ J : Subgroup G) :=
    Subgroup.subgroupOfEquivOfLe inf_le_right
  calc Nat.card (center ↥(S ⊓ J : Subgroup G))
      = Nat.card (center ↥((S ⊓ J).subgroupOf J)) :=
        (Nat.card_congr (Subgroup.centerCongr e).toEquiv).symm
    _ = 2 := hcardTsub

theorem exists_mem_inf_center_of_card_center_sylow {J : Subgroup G}
    (hst : IsStandardSubgroup J) (hZ : Odd (Nat.card (center ↥J)))
    (hZT : ∀ T : Sylow 2 (↥J ⧸ center ↥J), Nat.card (center (T : Subgroup (↥J ⧸ center ↥J))) = 2)
    {t : G} (ht : orderOf t = 2) (htJ : t ∈ centralizer (J : Set G)) {S : Subgroup G}
    (hS : IsSylowTwoIn S (centralizer ({t} : Set G))) :
    ∃ z ∈ S ⊓ J, (∀ s ∈ S, s * z = z * s) ∧ orderOf z = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := centralizer ({t} : Set G) with hCdef
  obtain ⟨hTC, hCT, hCn, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
      (CFSG.IsStandardSubgroup.assembly hst) htJ ht
  have : Group.IsPerfect ↥J := hst.1.1
  have hJsub : (J.subgroupOf C).IsSubnormal := hCn.isSubnormal
  have hTsyl : IsSylowTwoIn (S ⊓ J) J :=
    CFSG.ComponentClassification.GrSLit.GrS5.isSylowTwoIn_inf_of_isSubnormal
      (P := S) (K := J) hS hCT hJsub
  have hcardT : Nat.card (center ↥(S ⊓ J : Subgroup G)) = 2 :=
    card_center_inf_of_isStandardSubgroup hst hZ hZT ht htJ hS
  set T : Subgroup G := S ⊓ J with hTdef
  have hAleT : (center ↥T).map T.subtype ≤ T := Subgroup.map_subtype_le _
  have hAcard : Nat.card ((center ↥T).map T.subtype) = 2 := by
    rw [Subgroup.card_map_of_injective T.subtype_injective, hcardT]
  have hAeven : Even (Nat.card ((center ↥T).map T.subtype)) := by
    rw [hAcard]
    norm_num
  have hSleNT : S ≤ Subgroup.normalizer (T : Set G) := by
    refine (le_inf (Subgroup.le_normalizer) (hS.1.trans hTC)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hSleNA : S ≤ Subgroup.normalizer ((center ↥T).map T.subtype : Set G) :=
    hSleNT.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (center ↥T))
  have hS2 : IsPGroup 2 S := CFSG.ComponentClassification.GrSLit.GrS5.IsSylowTwoIn.isPGroup hS
  obtain ⟨z, hzA, hz2, hzc⟩ :=
    CFSG.GroupTheory.exists_involution_commute_of_isPGroup_le_normalizer (A := (center ↥T).map T.subtype)
      (P := S) hS2 hSleNA hAeven
  exact ⟨z, hAleT hzA, hzc, hz2⟩

omit [Finite G] in
private theorem exists_conj_of_automizer_fixes_sylow {J : Subgroup G}
    (hfix : ∀ (T : Sylow 2 (↥J ⧸ center ↥J)) (α : MulAut (↥J ⧸ center ↥J)),
      (∀ x ∈ (T : Subgroup (↥J ⧸ center ↥J)), α x = x) →
        α ∈ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range)
    (Tbar : Sylow 2 (↥J ⧸ center ↥J)) {r : G}
    (hrN : r ∈ normalizer (J : Set G))
    (hfixT : ∀ x ∈ (Tbar : Subgroup (↥J ⧸ center ↥J)),
      CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.automizer J ⟨r, hrN⟩ x = x) :
    ∃ f : (↥J ⧸ center ↥J),
      MulAut.conj f = CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.automizer J ⟨r, hrN⟩ ∧
        ∀ x ∈ (Tbar : Subgroup (↥J ⧸ center ↥J)), x * f = f * x := by
  obtain ⟨f, hf⟩ := hfix Tbar _ hfixT
  refine ⟨f, hf, ?_⟩
  intro x hx
  have h := hfixT x hx
  rw [← hf, MulAut.conj_apply] at h
  calc x * f = (f * x * f⁻¹) * f := by rw [h]
    _ = f * x := by group

omit [Finite G] in
private theorem automizer_eq_conj_mk {J : Subgroup G} (j : ↥J) :
    CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.automizer J
        ⟨j, Subgroup.le_normalizer j.2⟩ =
      MulAut.conj (QuotientGroup.mk' (center ↥J) j) := by
  ext x
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
  rw [CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.automizer_apply_mk, MulAut.conj_apply]
  apply congrArg (QuotientGroup.mk' (center ↥J))
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]

omit [Finite G] in
private theorem automizer_apply_eq_of_commutes {J : Subgroup G}
    (P : Sylow 2 ↥J) (Tbar : Sylow 2 (↥J ⧸ center ↥J))
    (hbar : (Tbar : Subgroup (↥J ⧸ center ↥J)) =
      (P : Subgroup ↥J).map (QuotientGroup.mk' (center ↥J)))
    {r : G} (hrN : r ∈ normalizer (J : Set G))
    (hrP : ∀ p : ↥J, p ∈ (P : Subgroup ↥J) → r * (p : G) = (p : G) * r) :
    ∀ x ∈ (Tbar : Subgroup (↥J ⧸ center ↥J)),
      CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.automizer J ⟨r, hrN⟩ x = x := by
  intro x hx
  rw [hbar] at hx
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
  change CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.automizer J ⟨r, hrN⟩
      ((p : ↥J) : (↥J ⧸ center ↥J)) = ((p : ↥J) : (↥J ⧸ center ↥J))
  rw [CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.automizer_apply_mk]
  apply congrArg (QuotientGroup.mk' (center ↥J))
  apply Subtype.ext
  calc r * (p : G) * r⁻¹ = (p : G) * r * r⁻¹ := by rw [hrP p hp]
    _ = (p : G) := by group

theorem eq_or_eq_or_eq_of_mem_center_of_sylow_fix {J : Subgroup G}
    (hst : IsStandardSubgroup J) (hZ : Odd (Nat.card (center ↥J)))
    (hcen : center (↥J ⧸ center ↥J) = ⊥)
    (hfix : ∀ (T : Sylow 2 (↥J ⧸ center ↥J)) (α : MulAut (↥J ⧸ center ↥J)),
      (∀ x ∈ (T : Subgroup (↥J ⧸ center ↥J)), α x = x) →
        α ∈ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range)
    (hZT : ∀ T : Sylow 2 (↥J ⧸ center ↥J), Nat.card (center (T : Subgroup (↥J ⧸ center ↥J))) = 2)
    (hcyc : ∀ P : Subgroup G, P ≤ centralizer (J : Set G) → IsPGroup 2 P → IsCyclic P)
    {t : G} (ht : orderOf t = 2) (htJ : t ∈ centralizer (J : Set G)) {S : Subgroup G}
    (hS : IsSylowTwoIn S (centralizer ({t} : Set G))) {z : G} (hzS : z ∈ S ⊓ J)
    (hzc : ∀ s ∈ S, s * z = z * s) (hz : orderOf z = 2) {w : G} (hwS : w ∈ S)
    (hwc : ∀ s ∈ S, s * w = w * s) (hw : orderOf w = 2) : w = z ∨ w = t ∨ w = z * t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := centralizer ({t} : Set G) with hCdef
  obtain ⟨hTC, hCT, hCn, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
      (CFSG.IsStandardSubgroup.assembly hst) htJ ht
  have : Group.IsPerfect ↥J := hst.1.1
  have hJsub : (J.subgroupOf C).IsSubnormal := hCn.isSubnormal
  have hTsyl : IsSylowTwoIn (S ⊓ J) J :=
    CFSG.ComponentClassification.GrSLit.GrS5.isSylowTwoIn_inf_of_isSubnormal
      (P := S) (K := J) hS hCT hJsub
  obtain ⟨hTleJ, P, hP⟩ := hTsyl
  let π : ↥J →* (↥J ⧸ center ↥J) := QuotientGroup.mk' (center ↥J)
  let Tbar : Sylow 2 (↥J ⧸ center ↥J) :=
    P.mapSurjective (QuotientGroup.mk'_surjective (center ↥J))
  have hbar : (Tbar : Subgroup (↥J ⧸ center ↥J)) = (P : Subgroup ↥J).map π :=
    Sylow.coe_mapSurjective _ P
  have hPmap : (P : Subgroup ↥J).map J.subtype = S ⊓ J := by
    rw [hP, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right]
  have htC : t ∈ C := by
    rw [hCdef, Subgroup.mem_centralizer_singleton_iff]
  have htS : t ∈ S :=
    mem_of_isSylowTwoIn_of_commute hS htC
      (fun s hs => Subgroup.mem_centralizer_singleton_iff.mp (hS.1 hs)) ht
  have hzJ : z ∈ J := hzS.2
  have hzN : z ∈ normalizer (J : Set G) := Subgroup.le_normalizer hzJ
  have hwN : w ∈ normalizer (J : Set G) := hTC (hS.1 hwS)
  let zN : Subgroup.normalizer (J : Set G) := ⟨z, hzN⟩
  let wN : Subgroup.normalizer (J : Set G) := ⟨w, hwN⟩
  let zbar : (↥J ⧸ center ↥J) := QuotientGroup.mk' (center ↥J) ⟨z, hzJ⟩
  have hzbarP : zbar ∈ (Tbar : Subgroup (↥J ⧸ center ↥J)) := by
    rw [hbar]
    refine Subgroup.mem_map.mpr ⟨⟨z, hzJ⟩, ?_, rfl⟩
    rw [hP, Subgroup.mem_subgroupOf]
    exact hzS
  have hzJord : orderOf (⟨z, hzJ⟩ : ↥J) = 2 := by
    rw [← Subgroup.orderOf_coe (⟨z, hzJ⟩ : ↥J), hz]
  have hzbar_ord : orderOf zbar = 2 :=
    CFSG.LocalAnalysis.ComponentInitial.orderOf_mk_center_eq_two hZ hzJord
  have hzbar_ne : zbar ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzbar_ord
    norm_num at hzbar_ord
  have hzbar_center :
      (⟨zbar, hzbarP⟩ : ↥(Tbar : Subgroup (↥J ⧸ center ↥J))) ∈
        center ↥(Tbar : Subgroup (↥J ⧸ center ↥J)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hy : (y : (↥J ⧸ center ↥J)) ∈ (P : Subgroup ↥J).map π := by
      rw [← hbar]
      exact y.2
    obtain ⟨p, hpP, hpval⟩ := Subgroup.mem_map.mp hy
    have hpT : (p : G) ∈ S ⊓ J := by
      have hmem : (p : G) ∈ (P : Subgroup ↥J).map J.subtype :=
        Subgroup.mem_map_of_mem J.subtype hpP
      rwa [hPmap] at hmem
    have hcomm : z * (p : G) = (p : G) * z := (hzc (p : G) hpT.1).symm
    change (y : (↥J ⧸ center ↥J)) * zbar = zbar * (y : (↥J ⧸ center ↥J))
    rw [← hpval]
    change π p * π ⟨z, hzJ⟩ = π ⟨z, hzJ⟩ * π p
    calc π p * π ⟨z, hzJ⟩ = π (p * ⟨z, hzJ⟩) := (map_mul π _ _).symm
      _ = π (⟨z, hzJ⟩ * p) := by
          congr 1
          apply Subtype.ext
          exact hcomm.symm
      _ = π ⟨z, hzJ⟩ * π p := map_mul π _ _
  have hfixT : ∀ x ∈ (Tbar : Subgroup (↥J ⧸ center ↥J)),
      CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.automizer J wN x = x :=
    automizer_apply_eq_of_commutes P Tbar hbar hwN (fun p hpP => by
      have hpT : (p : G) ∈ S ⊓ J := hPmap ▸ Subgroup.mem_map_of_mem J.subtype hpP
      exact (hwc (p : G) hpT.1).symm)
  obtain ⟨f, hf, hfcent⟩ := exists_conj_of_automizer_fixes_sylow hfix Tbar hwN hfixT
  have hw2 : w * w = 1 := by
    have h := pow_orderOf_eq_one w
    rwa [hw, pow_two] at h
  have hwN2 : wN * wN = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one]
    exact hw2
  have hf2 : f * f = 1 := by
    have hconj : MulAut.conj (f * f) = 1 := by
      rw [map_mul]
      rw [hf]
      rw [← map_mul, hwN2, map_one]
    have hker : f * f ∈ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).ker :=
      MonoidHom.mem_ker.mpr hconj
    rw [CFSG.GroupTheory.ker_conj_eq_center] at hker
    rw [hcen] at hker
    exact Subgroup.mem_bot.mp hker
  have hfP : f ∈ (Tbar : Subgroup (↥J ⧸ center ↥J)) := by
    have hf2' : f ^ 2 = 1 := by rw [pow_two]; exact hf2
    have hfp : IsPGroup 2 (Subgroup.zpowers f) := by
      refine IsPGroup.of_card_dvd_pow (n := 1) ?_
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_of_pow_eq_one hf2'
    have hcent : (Tbar : Subgroup (↥J ⧸ center ↥J)) ≤
        Subgroup.normalizer (Subgroup.zpowers f : Set (↥J ⧸ center ↥J)) := by
      refine (Subgroup.le_centralizer_iff.mpr (Subgroup.zpowers_le.mpr ?_)).trans
        (Subgroup.centralizer_le_normalizer _)
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact hfcent x hx
    set U : Subgroup (↥J ⧸ center ↥J) := (Tbar : Subgroup _) ⊔ Subgroup.zpowers f with hU
    have hUp : IsPGroup 2 U := Tbar.isPGroup'.to_sup_of_normal_right' hfp hcent
    have heq : U = (Tbar : Subgroup (↥J ⧸ center ↥J)) := Tbar.is_maximal' hUp le_sup_left
    exact heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers f)
  have hf_center :
      (⟨f, hfP⟩ : ↥(Tbar : Subgroup (↥J ⧸ center ↥J))) ∈
        center ↥(Tbar : Subgroup (↥J ⧸ center ↥J)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact hfcent (y : (↥J ⧸ center ↥J)) y.2
  by_cases hf1 : f = 1
  ·
    have hwCJ : w ∈ centralizer (J : Set G) := by
      have haut : CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.automizer J wN = 1 := by
        rw [← hf, hf1, map_one]
      exact (CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.automizer_eq_one_iff J wN).mp haut
    let R : Subgroup G := S ⊓ centralizer (J : Set G)
    have hR2 : IsPGroup 2 R := (CFSG.ComponentClassification.GrSLit.GrS5.IsSylowTwoIn.isPGroup hS).to_le inf_le_left
    have hRcyc : IsCyclic ↥R := hcyc R inf_le_right hR2
    let : IsCyclic ↥R := hRcyc
    have hwR : w ∈ R := ⟨hwS, hwCJ⟩
    have htR : t ∈ R := ⟨htS, htJ⟩
    have hword : orderOf (⟨w, hwR⟩ : ↥R) = 2 := by
      rw [← Subgroup.orderOf_coe (⟨w, hwR⟩ : ↥R), hw]
    have htord : orderOf (⟨t, htR⟩ : ↥R) = 2 := by
      rw [← Subgroup.orderOf_coe (⟨t, htR⟩ : ↥R), ht]
    have heq : (⟨w, hwR⟩ : ↥R) = ⟨t, htR⟩ :=
      CFSG.ABGLocalTools.eq_of_orderOf_eq_two_of_isCyclic hword htord
    exact Or.inr (Or.inl (congrArg Subtype.val heq))
  ·
    have hfz : f = zbar :=
      CFSG.GroupTheory.eq_of_mem_center_of_card_center_eq_two Tbar (hZT Tbar)
        hfP hzbarP hf_center hzbar_center hf1 hzbar_ne
    have hzNbar : CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.automizer J zN =
        MulAut.conj zbar := by
      have h := automizer_eq_conj_mk (J := J) ⟨z, hzJ⟩
      simpa [zN, zbar] using h
    have hauto : CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.automizer J (wN * zN⁻¹) = 1 := by
      rw [map_mul, map_inv, ← hf, hzNbar, hfz]
      group
    have hwzCJ : w * z ∈ centralizer (J : Set G) := by
      have h := (CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.automizer_eq_one_iff J (wN * zN⁻¹)).mp hauto
      have hz2 : z * z = 1 := by
        have h := pow_orderOf_eq_one z
        rwa [hz, pow_two] at h
      have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
      simpa [wN, zN, hzi] using h
    have hwzS : w * z ∈ S := S.mul_mem hwS hzS.1
    have hwz2 : (w * z) * (w * z) = 1 := by
      have hcomm : w * z = z * w := hzc w hwS
      have hz2 : z * z = 1 := by
        have h := pow_orderOf_eq_one z
        rwa [hz, pow_two] at h
      calc (w * z) * (w * z) = w * (z * w) * z := by group
        _ = w * (w * z) * z := by rw [← hcomm]
        _ = (w * w) * (z * z) := by group
        _ = 1 := by rw [hw2, hz2, mul_one]
    let R : Subgroup G := S ⊓ centralizer (J : Set G)
    have hR2 : IsPGroup 2 R := (CFSG.ComponentClassification.GrSLit.GrS5.IsSylowTwoIn.isPGroup hS).to_le inf_le_left
    have hRcyc : IsCyclic ↥R := hcyc R inf_le_right hR2
    let : IsCyclic ↥R := hRcyc
    by_cases hwz1 : w * z = 1
    · left
      calc w = (w * z) * z := by
            rw [mul_assoc, show z * z = 1 from by
              have h := pow_orderOf_eq_one z
              rwa [hz, pow_two] at h]
            rw [mul_one]
        _ = z := by rw [hwz1, one_mul]
    · have hwzord : orderOf (w * z) = 2 := by
        refine orderOf_eq_prime ?_ hwz1
        rw [pow_two]
        exact hwz2
      have hwzR : w * z ∈ R := ⟨hwzS, hwzCJ⟩
      have htR : t ∈ R := ⟨htS, htJ⟩
      have hwzordR : orderOf (⟨w * z, hwzR⟩ : ↥R) = 2 := by
        rw [← Subgroup.orderOf_coe (⟨w * z, hwzR⟩ : ↥R), hwzord]
      have htordR : orderOf (⟨t, htR⟩ : ↥R) = 2 := by
        rw [← Subgroup.orderOf_coe (⟨t, htR⟩ : ↥R), ht]
      have heq : (⟨w * z, hwzR⟩ : ↥R) = ⟨t, htR⟩ :=
        CFSG.ABGLocalTools.eq_of_orderOf_eq_two_of_isCyclic hwzordR htordR
      have hwzt : w * z = t := congrArg Subtype.val heq
      right; right
      calc w = (w * z) * z := by
            rw [mul_assoc, show z * z = 1 from by
              have h := pow_orderOf_eq_one z
              rwa [hz, pow_two] at h]
            rw [mul_one]
        _ = t * z := by rw [hwzt]
        _ = z * t := by rw [hzc t htS]

private theorem inf_eq_bot_of_isCyclic_card_four_of_involution_notMem
    {X : Type} [Group X] [Finite X] {A B : Subgroup X}
    (hBcyc : IsCyclic ↥B) (hBcard : Nat.card B = 4) {b : X}
    (hbB : b ∈ B) (hbord : orderOf b = 2) (hbA : b ∉ A) : A ⊓ B = ⊥ := by
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial ↥(A ⊓ B) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  have hdvd : Nat.card ↥(A ⊓ B) ∣ 4 := by
    have h := Subgroup.card_dvd_of_le (inf_le_right : A ⊓ B ≤ B)
    rwa [hBcard] at h
  have h1lt : 1 < Nat.card ↥(A ⊓ B) := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have h2dvd : 2 ∣ Nat.card ↥(A ⊓ B) := by
    obtain ⟨j, hjle, hj⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two (m := 2)).mp (by simpa using hdvd)
    have hjpos : j ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hj
      have hj1 : Nat.card ↥(A ⊓ B) = 1 := by simpa using hj
      rw [hj1] at h1lt
      exact lt_irrefl 1 h1lt
    have hj' : Nat.card ↥(A ⊓ B) = 2 ^ j := by simpa using hj
    rw [hj']
    exact dvd_pow_self 2 hjpos
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(A ⊓ B)) 2 h2dvd
  let yB : ↥B := ⟨(y : X), (y.2).2⟩
  have hyBord : orderOf yB = 2 := by
    rw [← Subgroup.orderOf_coe yB]
    exact (Subgroup.orderOf_coe y).trans hyord
  let bB : ↥B := ⟨b, hbB⟩
  have hbBord : orderOf bB = 2 := by
    rw [← Subgroup.orderOf_coe bB]
    exact hbord
  let : IsCyclic ↥B := hBcyc
  have heq : yB = bB :=
    CFSG.ABGLocalTools.eq_of_orderOf_eq_two_of_isCyclic hyBord hbBord
  have hyb : (y : X) = b := congrArg Subtype.val heq
  exact hbA (hyb ▸ (y.2).1)

private theorem sq_eq_one_of_mem_center_of_card_two
    {X : Type} [Group X] [Finite X] {P : Sylow 2 X}
    (hZ : Nat.card (center ↥(P : Subgroup X)) = 2) {f : X}
    (hfP : f ∈ (P : Subgroup X))
    (hfc : ∀ x ∈ (P : Subgroup X), x * f = f * x) : f * f = 1 := by
  let g : ↥(center ↥(P : Subgroup X)) :=
    ⟨⟨f, hfP⟩, by
      rw [Subgroup.mem_center_iff]
      intro x
      apply Subtype.ext
      exact hfc (x : X) x.2⟩
  have hgg : g * g = 1 := by
    by_cases h1 : g = 1
    · rw [h1, mul_one]
    · have hdvd : orderOf g ∣ 2 := by
        have h := orderOf_dvd_natCard g
        rwa [hZ] at h
      have hord : orderOf g = 2 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) h1
        · exact h
      have hpow : g ^ orderOf g = 1 := pow_orderOf_eq_one g
      calc g * g = g ^ 2 := by rw [pow_two]
        _ = 1 := by rwa [hord] at hpow
  have h := congrArg (fun z : ↥(center ↥(P : Subgroup X)) =>
    (((z : ↥(P : Subgroup X)) : X))) hgg
  simpa using h

theorem false_of_shear_of_card_four {J : Subgroup G} (hst : IsStandardSubgroup J)
    (hZ : Odd (Nat.card (center ↥J))) (hcen : center (↥J ⧸ center ↥J) = ⊥)
    (hfix : ∀ (T : Sylow 2 (↥J ⧸ center ↥J)) (α : MulAut (↥J ⧸ center ↥J)),
      (∀ x ∈ (T : Subgroup (↥J ⧸ center ↥J)), α x = x) →
        α ∈ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range)
    (hZT : ∀ T : Sylow 2 (↥J ⧸ center ↥J), Nat.card (center (T : Subgroup (↥J ⧸ center ↥J))) = 2)
    (hcyc : ∀ P : Subgroup G, P ≤ centralizer (J : Set G) → IsPGroup 2 P → IsCyclic P)
    {t z x : G} (ht : orderOf t = 2) (htJ : t ∈ centralizer (J : Set G)) {S : Subgroup G}
    (hS : IsSylowTwoIn S (centralizer ({t} : Set G)))
    (hSC : Nat.card ↥(S ⊓ centralizer (J : Set G)) = 4) (hzS : z ∈ S ⊓ J)
    (hz : orderOf z = 2) (hxS : x ∈ normalizer (S : Set G)) (hxt : x⁻¹ * t * x = z * t) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := centralizer ({t} : Set G) with hCdef
  obtain ⟨hTC, hCT, hCn, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
      (CFSG.IsStandardSubgroup.assembly hst) htJ ht
  have : Group.IsPerfect ↥J := hst.1.1
  have hJsub : (J.subgroupOf C).IsSubnormal := hCn.isSubnormal
  have hTsyl : IsSylowTwoIn (S ⊓ J) J :=
    CFSG.ComponentClassification.GrSLit.GrS5.isSylowTwoIn_inf_of_isSubnormal
      (P := S) (K := J) hS hCT hJsub
  obtain ⟨hTleJ, P, hP⟩ := hTsyl
  let π : ↥J →* (↥J ⧸ center ↥J) := QuotientGroup.mk' (center ↥J)
  let Tbar : Sylow 2 (↥J ⧸ center ↥J) :=
    P.mapSurjective (QuotientGroup.mk'_surjective (center ↥J))
  have hbar : (Tbar : Subgroup (↥J ⧸ center ↥J)) = (P : Subgroup ↥J).map π :=
    Sylow.coe_mapSurjective _ P
  set T : Subgroup G := S ⊓ J with hTdef
  have hPmap : (P : Subgroup ↥J).map J.subtype = T := by
    rw [hP, hTdef, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right]
  have htC : t ∈ C := by
    rw [hCdef, Subgroup.mem_centralizer_singleton_iff]
  have htS : t ∈ S :=
    mem_of_isSylowTwoIn_of_commute hS htC
      (fun s hs => Subgroup.mem_centralizer_singleton_iff.mp (hS.1 hs)) ht
  have ht_notJ : t ∉ J := by
    intro htJmem
    have htZ : (⟨t, htJmem⟩ : ↥J) ∈ center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro j
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp htJ (j : G) j.2
    have hdvd : orderOf (⟨t, htJmem⟩ : ↥J) ∣ Nat.card (center ↥J) :=
      Subgroup.orderOf_dvd_natCard _ htZ
    rw [← Subgroup.orderOf_coe (⟨t, htJmem⟩ : ↥J), ht] at hdvd
    exact hZ.not_two_dvd_nat hdvd
  let R : Subgroup G := S ⊓ centralizer (J : Set G)
  have hRcard : Nat.card R = 4 := hSC
  have hR2 : IsPGroup 2 R := (CFSG.ComponentClassification.GrSLit.GrS5.IsSylowTwoIn.isPGroup hS).to_le inf_le_left
  have hRcyc : IsCyclic ↥R := hcyc R inf_le_right hR2
  have htR : t ∈ R := ⟨htS, htJ⟩
  have hSNCJ : S ≤ Subgroup.normalizer (centralizer (J : Set G)) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      exact CFSG.ComponentClassification.GrSLit.GrS5.conj_mem_centralizer
        (hTC (hS.1 hs)) hc
    · intro hc
      have hs'inv : s⁻¹ ∈ normalizer (J : Set G) := inv_mem (hTC (hS.1 hs))
      have h := CFSG.ComponentClassification.GrSLit.GrS5.conj_mem_centralizer hs'inv hc
      simpa [mul_assoc] using h
  have hRn : S ≤ Subgroup.normalizer (R : Set G) := by
    have hSK : S ≤ Subgroup.normalizer ((centralizer (J : Set G)) ⊓ C) :=
      (le_inf hSNCJ (fun s hs => Subgroup.le_normalizer (hS.1 hs))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hReq : R = S ⊓ ((centralizer (J : Set G)) ⊓ C) := by
      ext y
      constructor
      · rintro ⟨hyS, hyC⟩
        exact ⟨hyS, hyC, hS.1 hyS⟩
      · rintro ⟨hyS, hyC, -⟩
        exact ⟨hyS, hyC⟩
    rw [hReq]
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyS, hyK⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hs) y).mp hyS,
        (Subgroup.mem_normalizer_iff.mp (hSK hs) y).mp hyK⟩
    · rintro ⟨hyS, hyK⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hs) y).mpr hyS,
        (Subgroup.mem_normalizer_iff.mp (hSK hs) y).mpr hyK⟩
  let R₁ : Subgroup G := R.map (MulAut.conj x⁻¹).toMonoidHom
  have hR₁leS : R₁ ≤ S := by
    intro y hy
    obtain ⟨r, hrR, rfl⟩ := Subgroup.mem_map.mp hy
    exact (Subgroup.mem_normalizer_iff.mp (inv_mem hxS) r).mp hrR.1
  have hR₁card : Nat.card R₁ = 4 := by
    rw [show R₁ = R.map (MulAut.conj x⁻¹).toMonoidHom from rfl,
      Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective, hRcard]
  have hR₁cyc : IsCyclic ↥R₁ := by
    exact isCyclic_of_surjective ((MulAut.conj x⁻¹).toMonoidHom.subgroupMap R)
      ((MulAut.conj x⁻¹).toMonoidHom.subgroupMap_surjective R)
  have hconj_mem : ∀ s ∈ S, ∀ y ∈ R₁, s * y * s⁻¹ ∈ R₁ := by
    intro s hs y hy
    obtain ⟨r, hrR, rfl⟩ := Subgroup.mem_map.mp hy
    have hs' : x * s * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hxS s).mp hs
    have hr' : x * s * x⁻¹ * r * (x * s * x⁻¹)⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp (hRn hs') r).mp hrR
    refine Subgroup.mem_map.mpr ⟨x * s * x⁻¹ * r * (x * s * x⁻¹)⁻¹, hr', ?_⟩
    change (MulAut.conj x⁻¹) (x * s * x⁻¹ * r * (x * s * x⁻¹)⁻¹) =
      s * (MulAut.conj x⁻¹) r * s⁻¹
    rw [MulAut.conj_apply, MulAut.conj_apply, inv_inv]
    group
  have hR₁n : S ≤ Subgroup.normalizer (R₁ : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hconj_mem s hs y
    · intro hy
      have h := hconj_mem s⁻¹ (S.inv_mem hs) (s * y * s⁻¹) hy
      simpa [mul_assoc] using h
  have hz2 : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hz, pow_two] at h
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht, pow_two] at h
  have hzt_comm : t * z = z * t := (Subgroup.mem_centralizer_iff.mp htJ z hzS.2).symm
  have hztR1 : z * t ∈ R₁ := by
    refine Subgroup.mem_map.mpr ⟨t, ⟨htS, htJ⟩, ?_⟩
    change (MulAut.conj x⁻¹) t = z * t
    rw [MulAut.conj_apply, inv_inv]
    exact hxt
  have hzt_sq : (z * t) * (z * t) = 1 := by
    calc (z * t) * (z * t) = z * (t * z) * t := by group
      _ = z * (z * t) * t := by rw [hzt_comm]
      _ = (z * z) * (t * t) := by group
      _ = 1 := by rw [hz2, ht2, mul_one]
  have hzt_ne1 : z * t ≠ 1 := by
    intro h
    have ht_eq_z : t = z := by
      have h1 : t = z⁻¹ * (z * t) := by group
      rw [h1, h, mul_one]
      exact inv_eq_of_mul_eq_one_right hz2
    exact ht_notJ (ht_eq_z ▸ hzS.2)
  have hzt_ord : orderOf (z * t) = 2 := by
    refine orderOf_eq_prime ?_ hzt_ne1
    rwa [pow_two]
  have hzt_notT : z * t ∉ T := by
    intro hztT
    have htJmem : t ∈ J := by
      have h1 : t = z⁻¹ * (z * t) := by group
      rw [h1]
      exact J.mul_mem (J.inv_mem hzS.2) hztT.2
    exact ht_notJ htJmem
  have hTn : S ≤ Subgroup.normalizer (T : Set G) :=
    (le_inf Subgroup.le_normalizer (hS.1.trans hTC)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hTinfR₁ : T ⊓ R₁ = ⊥ :=
    inf_eq_bot_of_isCyclic_card_four_of_involution_notMem hR₁cyc hR₁card hztR1 hzt_ord hzt_notT
  have hTcommR₁ : ⁅T, R₁⁆ = ⊥ := by
    have hTn' : (T.subgroupOf S).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hTn
    have hR₁n' : (R₁.subgroupOf S).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hR₁leS).mpr hR₁n
    have hle := Subgroup.commutator_le_inf (H₁ := T.subgroupOf S) (H₂ := R₁.subgroupOf S)
    have hsub : (T.subgroupOf S) ⊓ (R₁.subgroupOf S) = (T ⊓ R₁).subgroupOf S := by
      ext y
      simp [Subgroup.mem_subgroupOf]
    rw [hsub, hTinfR₁, Subgroup.bot_subgroupOf] at hle
    have hbot : ⁅T.subgroupOf S, R₁.subgroupOf S⁆ = ⊥ := le_bot_iff.mp hle
    have hmap := Subgroup.map_mono (f := S.subtype) hbot.le
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le inf_le_left,
      Subgroup.map_subgroupOf_eq_of_le hR₁leS, Subgroup.map_bot] at hmap
    exact le_bot_iff.mp hmap
  let : IsCyclic ↥R₁ := hR₁cyc
  obtain ⟨r₁, hr₁ord0⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥R₁)
  have hr₁ord : orderOf r₁ = 4 := by rw [hr₁ord0, hR₁card]
  have hr₁G_ord : orderOf ((r₁ : ↥R₁) : G) = 4 := by
    rw [Subgroup.orderOf_coe, hr₁ord]
  have hr₁S : ((r₁ : ↥R₁) : G) ∈ S := hR₁leS r₁.2
  have hr₁C : ((r₁ : ↥R₁) : G) ∈ C := hS.1 hr₁S
  have hr₁N : ((r₁ : ↥R₁) : G) ∈ normalizer (J : Set G) := hTC (by rwa [hCdef] at hr₁C)
  let r₁N : Subgroup.normalizer (J : Set G) := ⟨((r₁ : ↥R₁) : G), hr₁N⟩
  have hr₁Tcomm : ∀ p : ↥J, p ∈ (P : Subgroup ↥J) →
      ((r₁ : ↥R₁) : G) * (p : G) = (p : G) * ((r₁ : ↥R₁) : G) := by
    intro p hpP
    have hpT : (p : G) ∈ T := hPmap ▸ Subgroup.mem_map_of_mem J.subtype hpP
    have hTleC : T ≤ Subgroup.centralizer (R₁ : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hTcommR₁
    exact Subgroup.mem_centralizer_iff.mp (hTleC hpT) ((r₁ : ↥R₁) : G) r₁.2
  have hfixT : ∀ y ∈ (Tbar : Subgroup (↥J ⧸ center ↥J)),
      CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.automizer J r₁N y = y :=
    automizer_apply_eq_of_commutes P Tbar hbar hr₁N hr₁Tcomm
  obtain ⟨f, hf, hfcent⟩ := exists_conj_of_automizer_fixes_sylow hfix Tbar hr₁N hfixT
  have hr₁sqOrd : orderOf (r₁ ^ 2) = 2 := by
    rw [orderOf_pow, hr₁ord]
    norm_num
  have hztR₁ord : orderOf (⟨z * t, hztR1⟩ : ↥R₁) = 2 := by
    rw [← Subgroup.orderOf_coe (⟨z * t, hztR1⟩ : ↥R₁), hzt_ord]
  have hr₁sq_eq : r₁ ^ 2 = ⟨z * t, hztR1⟩ :=
    CFSG.ABGLocalTools.eq_of_orderOf_eq_two_of_isCyclic hr₁sqOrd hztR₁ord
  have hr₁sq : ((r₁ : ↥R₁) : G) ^ 2 = z * t := by
    have h := congrArg (fun y : ↥R₁ => (y : G)) hr₁sq_eq
    simpa [Subgroup.coe_pow] using h
  have hzN : z ∈ normalizer (J : Set G) := Subgroup.le_normalizer hzS.2
  have htN : t ∈ normalizer (J : Set G) := Subgroup.centralizer_le_normalizer _ htJ
  let zN : Subgroup.normalizer (J : Set G) := ⟨z, hzN⟩
  let tN : Subgroup.normalizer (J : Set G) := ⟨t, htN⟩
  let zbar : (↥J ⧸ center ↥J) := QuotientGroup.mk' (center ↥J) ⟨z, hzS.2⟩
  have hzJord : orderOf (⟨z, hzS.2⟩ : ↥J) = 2 := by
    rw [← Subgroup.orderOf_coe (⟨z, hzS.2⟩ : ↥J), hz]
  have hzbar_ord : orderOf zbar = 2 :=
    CFSG.LocalAnalysis.ComponentInitial.orderOf_mk_center_eq_two hZ hzJord
  have hzbar_ne : zbar ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzbar_ord
    norm_num at hzbar_ord
  have hzNbar : CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.automizer J zN =
      MulAut.conj zbar := by
    have h := automizer_eq_conj_mk (J := J) ⟨z, hzS.2⟩
    simpa [zN, zbar] using h
  have hztN : z * t ∈ normalizer (J : Set G) :=
    (normalizer (J : Set G)).mul_mem hzN htN
  have hztN_eq : (⟨z * t, hztN⟩ : Subgroup.normalizer (J : Set G)) = zN * tN := by
    apply Subtype.ext
    rfl
  have hauto_zt : CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.automizer J
      ⟨z * t, hztN⟩ = MulAut.conj zbar := by
    rw [hztN_eq, map_mul]
    have htNaut : CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.automizer J tN = 1 :=
      (CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.automizer_eq_one_iff J tN).mpr htJ
    rw [htNaut, mul_one]
    exact hzNbar
  have hr₁N_sq : r₁N * r₁N = ⟨z * t, hztN⟩ := by
    apply Subtype.ext
    simpa [pow_two] using hr₁sq
  have hconj_ff : MulAut.conj (f * f) = MulAut.conj zbar := by
    rw [map_mul, hf, ← map_mul, hr₁N_sq, hauto_zt]
  have hff_zbar : f * f = zbar := by
    have hker : f * f * zbar⁻¹ ∈
        (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hconj_ff]
      group
    rw [CFSG.GroupTheory.ker_conj_eq_center, hcen] at hker
    have h1 : f * f * zbar⁻¹ = 1 := Subgroup.mem_bot.mp hker
    rwa [mul_inv_eq_one] at h1
  have hr₁N4 : r₁N ^ 4 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    simpa [hr₁G_ord] using pow_orderOf_eq_one ((r₁ : ↥R₁) : G)
  have hf4 : f ^ 4 = 1 := by
    have hconj4 : (MulAut.conj f) ^ 4 = 1 := by
      rw [hf, ← map_pow, hr₁N4, map_one]
    have hker : f ^ 4 ∈
        (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).ker := by
      rw [MonoidHom.mem_ker, map_pow, hconj4]
    rw [CFSG.GroupTheory.ker_conj_eq_center, hcen] at hker
    exact Subgroup.mem_bot.mp hker
  have hfP : f ∈ (Tbar : Subgroup (↥J ⧸ center ↥J)) := by
    have hfp : IsPGroup 2 (Subgroup.zpowers f) := by
      refine IsPGroup.of_card_dvd_pow (n := 2) ?_
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hf4
    have hcent : (Tbar : Subgroup (↥J ⧸ center ↥J)) ≤
        Subgroup.normalizer (Subgroup.zpowers f : Set (↥J ⧸ center ↥J)) := by
      refine (Subgroup.le_centralizer_iff.mpr (Subgroup.zpowers_le.mpr ?_)).trans
        (Subgroup.centralizer_le_normalizer _)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact hfcent y hy
    set U : Subgroup (↥J ⧸ center ↥J) := (Tbar : Subgroup _) ⊔ Subgroup.zpowers f with hU
    have hUp : IsPGroup 2 U := Tbar.isPGroup'.to_sup_of_normal_right' hfp hcent
    have heq : U = (Tbar : Subgroup (↥J ⧸ center ↥J)) := Tbar.is_maximal' hUp le_sup_left
    exact heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers f)
  have hf_sq_one : f * f = 1 :=
    sq_eq_one_of_mem_center_of_card_two (P := Tbar) (hZT Tbar) hfP hfcent
  rw [hff_zbar] at hf_sq_one
  exact hzbar_ne hf_sq_one

end CFSG.ComponentClassification.GrSLit.L34Sec5S

end
