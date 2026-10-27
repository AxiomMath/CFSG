module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SSuzCore
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5STwoSuzActive
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5STwoSuzConfig
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34PairIndex
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.FS79Suz
public import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
public import CFSG.LocalAnalysis.OddStandard.ChildHeHeld
public import CFSG.LocalAnalysis.OddStandard.OddLieHarris82Mult
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5SwapLift
public import CFSG.RankThree.Classical2.TwistedE6Phi3Torus
public import CFSG.LocalAnalysis.ComponentClassification.GSTopExclusion

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open scoped commutatorElement
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

private theorem mem_commutator_of_mem_center_of_coprime_index {A : Type*} [Group A] [Finite A]
    (hA : Group.IsPerfect A) {K : Subgroup A} {t : A} (ht : t ∈ center A)
    (hcop : Nat.Coprime K.index (orderOf t)) : t ∈ ⁅K, K⁆ := by
  have hkey : ∀ (k : ℕ) (g₀ : A), g₀⁻¹ * t ^ k * g₀ ∈ K → g₀⁻¹ * t ^ k * g₀ = t ^ k := by
    intro k g₀ _
    rw [mul_assoc, ← Subgroup.mem_center_iff.mp (pow_mem ht k) g₀, ← mul_assoc,
      inv_mul_cancel, one_mul]
  let φ : ↥K →* Abelianization ↥K := Abelianization.of
  have htriv : MonoidHom.transfer φ t = 1 :=
    Abelianization.commutator_subset_ker (MonoidHom.transfer φ)
      (by rw [hA.commutator_eq_top]; exact Subgroup.mem_top t)
  have hpow : MonoidHom.transfer φ t = φ ⟨t ^ K.index, MonoidHom.transfer_eq_pow_aux t hkey⟩ :=
    MonoidHom.transfer_eq_pow φ t hkey
  rw [hpow] at htriv
  have hmem : t ^ K.index ∈ ⁅K, K⁆ := by
    have hker : (⟨t ^ K.index, MonoidHom.transfer_eq_pow_aux t hkey⟩ : ↥K) ∈
        commutator ↥K := by
      rw [← Abelianization.ker_of]
      rw [MonoidHom.mem_ker]
      exact htriv
    have hmap := Subgroup.mem_map_of_mem K.subtype hker
    rwa [Subgroup.map_subtype_commutator] at hmap
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact Subgroup.pow_mem _ hmem m

private theorem commutator_sup_eq_of_le_center {G : Type*} [Group G] {H Z : Subgroup G}
    (hZ : Z ≤ Subgroup.center G) : ⁅H ⊔ Z, H ⊔ Z⁆ = ⁅H, H⁆ := by
  refine le_antisymm ?_ (Subgroup.commutator_mono le_sup_left le_sup_left)
  have : Z.Normal :=
    ⟨fun z hz g => by
      have hc := Subgroup.mem_center_iff.mp (hZ hz) g
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
      exact hz⟩
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨h1, h1H, z1, z1Z, rfl⟩ :=
    Subgroup.mem_sup_of_normal_right (s := H) (t := Z) |>.mp hx
  obtain ⟨h2, h2H, z2, z2Z, rfl⟩ :=
    Subgroup.mem_sup_of_normal_right (s := H) (t := Z) |>.mp hy
  have hz1c : z1 ∈ Subgroup.center G := hZ z1Z
  have hz2c : z2 ∈ Subgroup.center G := hZ z2Z
  have h1' : ⁅z1, h2 * z2⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz1c _).symm
  have h2' : ⁅h1, z2⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz2c h1)
  have e1 : ⁅h1 * z1, h2 * z2⁆ = ⁅h1, h2 * z2⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul, h1']
    group
  have e2 : ⁅h1, h2 * z2⁆ = ⁅h1, h2⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj, h2']
    group
  rw [e1, e2]
  exact Subgroup.commutator_mem_commutator h1H h2H

section Setting

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

omit [Finite G] in
private theorem le_centralizer_of_mem_map_center {t : G}
    (htA : t ∈ (center ↥A).map A.subtype) : A ≤ centralizer ({t} : Set G) := by
  intro a ha
  obtain ⟨c, hc, hct⟩ := Subgroup.mem_map.mp htA
  have h1 := Subgroup.mem_center_iff.mp hc ⟨a, ha⟩
  rw [mem_centralizer_singleton_iff, ← hct]
  exact congrArg Subtype.val h1

omit [Finite G] in
private theorem centralizer_le_normalizer_of_mem_map_center (hA : IsStandardSubgroup A) {t : G}
    (ht : orderOf t = 2) (htA : t ∈ (center ↥A).map A.subtype) :
    centralizer ({t} : Set G) ≤ normalizer (A : Set G) := by
  have hPt := le_centralizer_of_mem_map_center (A := A) htA
  have htCA : t ∈ centralizer (A : Set G) :=
    mem_centralizer_iff.mpr fun a ha => mem_centralizer_singleton_iff.mp (hPt ha)
  intro y hy
  exact (CFSG.isStandardSubgroup_iff_standardComponentIsStandard.1 hA).mem_normalizer_of_commute
    htCA ht (mem_centralizer_singleton_iff.mp hy)

private theorem normal_isPComponent_subgroupOf_centralizer
    (hA : IsStandardSubgroup A) {t : G} (ht : orderOf t = 2)
    (htA : t ∈ (center ↥A).map A.subtype) :
    (A.subgroupOf (centralizer ({t} : Set G))).Normal ∧
      IsPComponent 2 (A.subgroupOf (centralizer ({t} : Set G))) := by
  have hPt := le_centralizer_of_mem_map_center (A := A) htA
  have hnorm := centralizer_le_normalizer_of_mem_map_center hA ht htA
  have hN : (A.subgroupOf (centralizer ({t} : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hPt).mpr hnorm
  refine ⟨hN, ?_⟩
  have hQ : CFSG.IsQuasisimple ↥(A.subgroupOf (centralizer ({t} : Set G))) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hPt).symm hA.1
  have hcomp : CFSG.IsComponent (A.subgroupOf (centralizer ({t} : Set G))) :=
    ⟨hQ, hN.isSubnormal⟩
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥(centralizer ({t} : Set G)))) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2))
  exact CFSG.LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2 hcomp
    (CFSG.LocalAnalysis.ComponentInitial.not_le_of_isComponent_of_isSolvable hcomp
      (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd))

private theorem isSporadic_fusionZStar_of_standard (hA : IsStandardSubgroup A)
    (hSuz : Blueprint.NativeSporadic.IsSporadic (↥A ⧸ center ↥A) .Suz) :
    Blueprint.NativeSporadic.IsSporadic (↥A ⧸ Open.fusionZStar ↥A) .Suz := by
  have hZ := CFSG.OddStandard.fusionZStar_eq_center_of_standard
    (CFSG.isStandardSubgroup_iff_standardComponentIsStandard.1 hA)
  obtain ⟨e⟩ := hSuz
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans e⟩

private theorem oddIn_centralizer_le_centralizer
    (hA : IsStandardSubgroup A) {t : G} (ht : orderOf t = 2)
    (htA : t ∈ (center ↥A).map A.subtype) :
    oddIn (centralizer ({t} : Set G)) ≤ centralizer (A : Set G) := by
  set C := centralizer ({t} : Set G) with hC
  have hPt : A ≤ C := le_centralizer_of_mem_map_center htA
  have hQ : CFSG.IsQuasisimple ↥(A.subgroupOf C) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hPt).symm hA.1
  have hN : (A.subgroupOf C).Normal :=
    (normal_subgroupOf_iff_le_normalizer hPt).mpr
      (centralizer_le_normalizer_of_mem_map_center hA ht htA)
  have hEq : (oddIn C).subgroupOf C = pPrimeCore 2 C :=
    comap_map_eq_self_of_injective C.subtype_injective _
  have : ((oddIn C).subgroupOf C).Normal := by
    rw [hEq]
    exact CFSG.pPrimeCore_normal
  have hodd' : Odd (Nat.card ↥((oddIn C).subgroupOf C)) := by
    rw [hEq]
    exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2))
  have hle := CFSG.RankThree.Classical2.le_centralizer_of_isSolvable_normal
    (D := ↥C) (P := A.subgroupOf C) (V := (oddIn C).subgroupOf C) hQ
    (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd')
  have hcen : centralizer ((A.subgroupOf C : Subgroup C) : Set C) =
      (centralizer (A : Set G)).subgroupOf C :=
    CFSG.StandardSubgroupAPI.centralizer_subgroupOf hPt
  intro x hx
  have hxC : x ∈ C := map_subtype_le _ hx
  have hx' : (⟨x, hxC⟩ : ↥C) ∈ centralizer ((A.subgroupOf C : Subgroup C) : Set C) :=
    hle (Subgroup.mem_subgroupOf.mpr hx)
  rw [hcen] at hx'
  exact Subgroup.mem_subgroupOf.mp hx'

private theorem mem_centralizer_of_zStarAct_eq_one
    (hA : IsStandardSubgroup A) {t : G} (ht : orderOf t = 2)
    (htA : t ∈ (center ↥A).map A.subtype) (x : ↥(centralizer ({t} : Set G)))
    (hx : GSThmB.A10T.zStarAct A
      ⟨(x : G), centralizer_le_normalizer_of_mem_map_center hA ht htA x.2⟩ = 1) :
    (x : G) ∈ centralizer (A : Set G) := by
  have hPt := le_centralizer_of_mem_map_center (A := A) htA
  have hPc := (normal_isPComponent_subgroupOf_centralizer hA ht htA).2
  have hxN : (x : G) ∈ normalizer (A : Set G) :=
    centralizer_le_normalizer_of_mem_map_center hA ht htA x.2
  have hcak : (x : G) ∈ UnbalancedLayer.coreActionKernel A :=
    (GSThmB.A10T.zStarAct_eq_one_iff hPt hPc ⟨(x : G), hxN⟩).mp hx
  have hcen : pPrimeCore 2 ↥A ≤ center ↥A :=
    CFSG.OddStandard.Residual.pPrimeCore_le_center_of_quasisimple hA.1
      (even_iff_two_dvd.1 (CFSG.OddStandard.even_card_of_standard
        (CFSG.isStandardSubgroup_iff_standardComponentIsStandard.1 hA)))
  set φ : MulAut ↥A := A.normalizerMonoidHom ⟨(x : G)⁻¹, inv_mem hxN⟩ with hφ
  have hmem : ∀ a : ↥A, a⁻¹ * φ a ∈ center ↥A := by
    intro a
    have h1 : (a : G)⁻¹ * (x : G)⁻¹ * (a : G) * (x : G) ∈
        (pPrimeCore 2 ↥A).map A.subtype := (UnbalancedLayer.mem_coreActionKernel.mp hcak).2 a a.2
    obtain ⟨o, ho, hoo⟩ := mem_map.mp h1
    have hcoeq : ((φ a : ↥A) : G) = (x : G)⁻¹ * (a : G) * (x : G) := by
      rw [hφ]
      simp
    have hEq : a⁻¹ * φ a = o := by
      apply Subtype.ext
      have e : ((a⁻¹ * φ a : ↥A) : G) =
          (a : G)⁻¹ * (x : G)⁻¹ * (a : G) * (x : G) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hcoeq]
        group
      rw [e, ← hoo]
      rfl
    rw [hEq]
    exact hcen ho
  have : Group.IsPerfect ↥A := hA.1.1
  have hquot : PerfectAutomorphisms.onCenterQuotient φ = 1 := by
    refine MulEquiv.ext fun q => ?_
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥A) q
    rw [PerfectAutomorphisms.onCenterQuotient_apply_mk]
    exact (QuotientGroup.eq.mpr (hmem a)).symm
  have hid := PerfectAutomorphisms.onCenterQuotient_eq_one_imp φ hquot
  rw [mem_centralizer_iff]
  intro a ha
  have h1 : φ ⟨a, ha⟩ = ⟨a, ha⟩ := by
    rw [hid]
    rfl
  have h2 : (x : G)⁻¹ * a * (x : G) = a := by
    have h1' : ((φ ⟨a, ha⟩ : ↥A) : G) = a := congrArg Subtype.val h1
    rw [hφ] at h1'
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe A] at h1'
    simpa using h1'
  calc a * (x : G) = (x : G) * ((x : G)⁻¹ * a * (x : G)) := by group
    _ = (x : G) * a := by rw [h2]

private theorem pRank_centralizer_le_eight
    (hA : IsStandardSubgroup A)
    (hτ : Blueprint.NativeSporadic.IsSporadic (↥A ⧸ Open.fusionZStar ↥A) .Suz)
    {t : G} (ht : orderOf t = 2) (htA : t ∈ (center ↥A).map A.subtype)
    (hrank : pRank 2 ↥(centralizer (A : Set G)) ≤ 1) :
    pRank 2 ↥(centralizer ({t} : Set G)) ≤ 8 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({t} : Set G) with hC
  have hnorm : C ≤ normalizer (A : Set G) := centralizer_le_normalizer_of_mem_map_center hA ht htA
  let φ : ↥C →* MulAut (↥A ⧸ Open.fusionZStar ↥A) :=
    (GSThmB.A10T.zStarAct A).comp (Subgroup.inclusion hnorm)
  have hφeq : ∀ x : ↥C, φ x = GSThmB.A10T.zStarAct A ⟨(x : G), hnorm x.2⟩ := fun x => rfl
  have hker : pRank 2 ↥φ.ker ≤ 1 := by
    let ψ : ↥φ.ker →* ↥(centralizer (A : Set G)) :=
      { toFun := fun x => ⟨((x : ↥C) : G),
          mem_centralizer_of_zStarAct_eq_one hA ht htA x.1 x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hinjψ : Function.Injective ψ := by
      intro x y h
      have h1 : ((x : ↥C) : G) = ((y : ↥C) : G) :=
        congrArg (fun z : ↥(centralizer (A : Set G)) => (z : G)) h
      exact Subtype.ext (Subtype.ext h1)
    exact (RankThree.OddKernel.pRank_le_of_injective (by norm_num) ψ hinjψ).trans hrank
  have himg : pRank 2 (↥C ⧸ φ.ker) ≤ 6 := by
    have hFin : Finite (MulAut (↥A ⧸ Open.fusionZStar ↥A)) :=
      Finite.of_injective (fun f : MulAut (↥A ⧸ Open.fusionZStar ↥A) =>
        (f : ↥A ⧸ Open.fusionZStar ↥A → ↥A ⧸ Open.fusionZStar ↥A))
        fun f g h => MulEquiv.ext (congrFun h)
    have hinj : Function.Injective ((φ.range.subtype).comp
        (QuotientGroup.quotientKerEquivRange φ).toMonoidHom) :=
      (Subgroup.subtype_injective _).comp (QuotientGroup.quotientKerEquivRange φ).injective
    exact (RankThree.OddKernel.pRank_le_of_injective (by norm_num) _ hinj).trans
      (twoSuzAutTwoRank_holds (X := ↥A ⧸ Open.fusionZStar ↥A) hτ)
  calc pRank 2 ↥C ≤ pRank 2 ↥φ.ker + pRank 2 (↥C ⧸ φ.ker) :=
        RankThree.OddKernel.pRank_le_add_of_normal Nat.prime_two φ.ker
    _ ≤ 1 + 6 := Nat.add_le_add hker himg
    _ ≤ 8 := by norm_num

private theorem center_quotient_ne_bot {t : G} (ht : orderOf t = 2)
    (htA : t ∈ (center ↥A).map A.subtype) :
    center (↥A ⧸ pPrimeCore 2 ↥A) ≠ ⊥ := by
  obtain ⟨c, hc, hct⟩ := Subgroup.mem_map.mp htA
  intro hbot
  have hmem : QuotientGroup.mk' (pPrimeCore 2 ↥A) c ∈ center (↥A ⧸ pPrimeCore 2 ↥A) := by
    rw [mem_center_iff]
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥A) q
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hc a]
  rw [hbot, Subgroup.mem_bot] at hmem
  have hcO : c ∈ pPrimeCore 2 ↥A := (QuotientGroup.eq_one_iff c).mp hmem
  have hct' : (c : G) = t := hct
  have hord : orderOf c = 2 := by rw [← Subgroup.orderOf_coe, hct', ht]
  have hc2 : c * c = 1 := by
    have h := pow_orderOf_eq_one c
    rwa [hord, pow_two] at h
  have hc1 : c = 1 := CFSG.GH74.Uniqueness.eq_one_of_mem_of_sq_eq_one
    (Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2))) hcO hc2
  have h1 : (c : G) = 1 := congrArg Subtype.val hc1
  rw [hct'] at h1
  rw [h1, orderOf_one] at ht
  norm_num at ht

private theorem card_center_quotient_eq_two
    (hperf : Group.IsPerfect ↥A)
    (hτ : Blueprint.NativeSporadic.IsSporadic (↥A ⧸ Open.fusionZStar ↥A) .Suz)
    (hc : center (↥A ⧸ pPrimeCore 2 ↥A) ≠ ⊥) :
    Nat.card (center (↥A ⧸ pPrimeCore 2 ↥A)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperfΛ : Group.IsPerfect (↥A ⧸ pPrimeCore 2 ↥A) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (pPrimeCore 2 ↥A))
      (QuotientGroup.mk'_surjective (pPrimeCore 2 ↥A))
  obtain ⟨eS⟩ := CFSG.ComponentClassification.GrSLit.nonempty_quotient_center_equiv_fusionZStar ↥A
  obtain ⟨eZ⟩ := hτ
  have hΛS : Blueprint.NativeSporadic.IsSporadic
      ((↥A ⧸ pPrimeCore 2 ↥A) ⧸ center (↥A ⧸ pPrimeCore 2 ↥A)) .Suz := ⟨eS.trans eZ⟩
  have hsimple : IsSimpleGroup
      ((↥A ⧸ pPrimeCore 2 ↥A) ⧸ center (↥A ⧸ pPrimeCore 2 ↥A)) :=
    CFSG.EvenSporadicStandard.Solomon78.suz_isSimpleGroup_of_isSporadic hΛS
  have hq : CFSG.Assembly.IsQuasisimple (↥A ⧸ pPrimeCore 2 ↥A) :=
    ⟨Group.isPerfect_def.mp hperfΛ, hsimple⟩
  have hZ2 : IsPGroup 2 (center (↥A ⧸ pPrimeCore 2 ↥A)) :=
    CFSG.Holt.General.isPGroup_center_quotient_pPrimeCore ↥A
  have hle : Nat.card (center (↥A ⧸ pPrimeCore 2 ↥A)) ≤ 2 :=
    CFSG.ComponentClassification.GrSLit.L34Sec5S.suzCentralTwoGroupOrderBound_holds
      (↥A ⧸ pPrimeCore 2 ↥A) hq hZ2 hΛS
  have hgt : 1 < Nat.card (center (↥A ⧸ pPrimeCore 2 ↥A)) :=
    (Subgroup.one_lt_card_iff_ne_bot _).mpr hc
  have h2 : 2 ∣ Nat.card (center (↥A ⧸ pPrimeCore 2 ↥A)) := by
    rcases hZ2.card_eq_or_dvd with h | h
    · omega
    · exact h
  omega

private theorem card_centralizer_center_quotient
    {X : Type} [Group X] [Finite X] (hperf : Group.IsPerfect X)
    (hS : Blueprint.NativeSporadic.IsSporadic (X ⧸ center X) .Suz)
    (hcard : Nat.card (center X) = 2) {y : X} (hy2 : y * y = 1) (hy : y ∉ center X) :
    Nat.card (centralizer ({(QuotientGroup.mk y : X ⧸ center X)} : Set (X ⧸ center X))) =
      3317760 := by
  obtain ⟨hCperf, hC3⟩ := twoSuzCentralizerFacts_holds X hperf hS hcard y hy2 hy
  have hy2' : orderOf (QuotientGroup.mk y : X ⧸ center X) = 2 := by
    have hsq : (QuotientGroup.mk' (center X)) y * (QuotientGroup.mk' (center X)) y = 1 := by
      rw [← map_mul, hy2, map_one]
    have hne : (QuotientGroup.mk y : X ⧸ center X) ≠ 1 := fun h =>
      hy ((QuotientGroup.eq_one_iff y).mp h)
    exact orderOf_eq_prime (by simpa [pow_two] using hsq) hne
  rcases CFSG.EvenSporadicStandard.M12Std.card_centralizer_of_isSporadic_suz hS hy2' with h | h
  · exfalso
    obtain ⟨M, hMn, hMs, hMsimp, hMdvd⟩ := hC3
    have hdiv : 3 ^ 4 ∣ Nat.card (centralizer ({(QuotientGroup.mk y : X ⧸ center X)} :
        Set (X ⧸ center X))) := hMdvd.trans (Subgroup.card_quotient_dvd_card M)
    rw [h] at hdiv
    norm_num at hdiv
  · exact h

private theorem centralizer_eq_comap_center
    {X : Type} [Group X] [Finite X] (hperf : Group.IsPerfect X)
    (hS : Blueprint.NativeSporadic.IsSporadic (X ⧸ center X) .Suz)
    (hcard : Nat.card (center X) = 2) {y : X} (hy2 : y * y = 1) (hy : y ∉ center X) :
    centralizer ({y} : Set X) =
      (centralizer ({(QuotientGroup.mk y : X ⧸ center X)} : Set (X ⧸ center X))).comap
        (QuotientGroup.mk' (center X)) := by
  obtain ⟨hCperf, -⟩ := twoSuzCentralizerFacts_holds X hperf hS hcard y hy2 hy
  ext g
  rw [Subgroup.mem_comap, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro hg
    have h2 : (QuotientGroup.mk' (center X)) (g * y) =
        (QuotientGroup.mk' (center X)) (y * g) := by rw [hg]
    rwa [map_mul, map_mul] at h2
  · intro hg
    have hmem : ⁅g, y⁆ ∈ center X := by
      have h1 : (QuotientGroup.mk' (center X)) ⁅g, y⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact hg
      exact (QuotientGroup.eq_one_iff ⁅g, y⁆).mp h1
    have h2 := commutator_eq_one_of_perfect_centralizer (Z := center X) le_rfl hCperf hmem
    rwa [commutatorElement_eq_one_iff_mul_comm] at h2

private theorem not_two_dvd_index_centralizer
    (hperf : Group.IsPerfect ↥A)
    (hτ : Blueprint.NativeSporadic.IsSporadic (↥A ⧸ Open.fusionZStar ↥A) .Suz)
    (hZc : Open.fusionZStar ↥A = center ↥A)
    (hOc : pPrimeCore 2 ↥A ≤ center ↥A)
    (hcardZ : Nat.card (center (↥A ⧸ pPrimeCore 2 ↥A)) = 2)
    {u : ↥A} (hu2 : u * u = 1) (hu : u ∉ center ↥A) :
    ¬ 2 ∣ (centralizer ({u} : Set ↥A)).index := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 ↥A with hO
  set Λ := ↥A ⧸ O with hΛ
  set π : ↥A →* Λ := QuotientGroup.mk' O with hπ
  have hperfΛ : Group.IsPerfect Λ :=
    Group.IsPerfect.ofSurjective (f := π) (QuotientGroup.mk'_surjective O)
  obtain ⟨eS⟩ := CFSG.ComponentClassification.GrSLit.nonempty_quotient_center_equiv_fusionZStar ↥A
  obtain ⟨eZ⟩ := hτ
  have hΛS : Blueprint.NativeSporadic.IsSporadic (Λ ⧸ center Λ) .Suz := ⟨eS.trans eZ⟩
  have hcardZ' : Nat.card (center Λ) = 2 := hcardZ
  set y : Λ := π u with hy
  have hy2 : y * y = 1 := by rw [hy, ← map_mul, hu2, map_one]
  have hyZ : y ∉ center Λ := by
    intro h
    apply hu
    have h1 : u ∈ Open.fusionZStar ↥A := by
      rw [GrS4.fusionZStar_eq_comap_pPrimeCore]
      exact h
    rwa [hZc] at h1
  have hDcard : Nat.card (centralizer ({(QuotientGroup.mk y : Λ ⧸ center Λ)} :
      Set (Λ ⧸ center Λ))) = 3317760 :=
    card_centralizer_center_quotient hperfΛ hΛS hcardZ' hy2 hyZ
  set D : Subgroup (Λ ⧸ center Λ) := centralizer ({(QuotientGroup.mk y : Λ ⧸ center Λ)} :
    Set (Λ ⧸ center Λ)) with hD
  have hpre := centralizer_eq_comap_center hperfΛ hΛS hcardZ' hy2 hyZ
  have hmap : (centralizer ({u} : Set ↥A)).map π = centralizer ({y} : Set Λ) := by
    rw [hy, hπ]
    exact CFSG.OddStandard.Solomon75.map_centralizer_pPrimeCore_of_involution hu2
  have hidx1 : (centralizer ({y} : Set Λ)).index = (centralizer ({u} : Set ↥A)).index := by
    have h := Subgroup.index_map_eq (H := centralizer ({u} : Set ↥A)) (f := π)
      (QuotientGroup.mk'_surjective O)
      (show π.ker ≤ centralizer ({u} : Set ↥A) from by
        rw [hπ, QuotientGroup.ker_mk']
        intro o ho
        rw [mem_centralizer_singleton_iff]
        exact Subtype.ext (congrArg Subtype.val
          (Subgroup.mem_center_iff.mp (hOc ho) u).symm))
    rw [hmap] at h
    exact h
  have hidx2 : (centralizer ({y} : Set Λ)).index = D.index := by
    rw [hpre, ← hD]
    exact Subgroup.index_comap_of_surjective (H := D) (f := QuotientGroup.mk' (center Λ))
      (QuotientGroup.mk'_surjective (center Λ))
  have hquotcard : Nat.card (Λ ⧸ center Λ) = 448345497600 := by
    obtain ⟨e⟩ := CFSG.EvenSporadicStandard.Solomon78.suz_equiv_of_isSporadic hΛS
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.SuzOddCore.suzM_card_chain]
  have hmul : Nat.card D * D.index = Nat.card (Λ ⧸ center Λ) := Subgroup.card_mul_index D
  have hDindex : D.index = 135135 := by
    rw [hDcard, hquotcard] at hmul
    omega
  have hidx : (centralizer ({u} : Set ↥A)).index = 135135 := by
    rw [← hidx1, hidx2, hDindex]
  rw [hidx]
  norm_num

private theorem mem_commutator_centralizer
    (hperf : Group.IsPerfect ↥A)
    (hτ : Blueprint.NativeSporadic.IsSporadic (↥A ⧸ Open.fusionZStar ↥A) .Suz)
    (hZc : Open.fusionZStar ↥A = center ↥A)
    (hOc : pPrimeCore 2 ↥A ≤ center ↥A)
    (hcardZ : Nat.card (center (↥A ⧸ pPrimeCore 2 ↥A)) = 2)
    {u : ↥A} (hu2 : u * u = 1) (hu : u ∉ center ↥A)
    {c : ↥A} (hc : c ∈ center ↥A) (hc2 : orderOf c = 2) :
    c ∈ ⁅centralizer ({u} : Set ↥A), centralizer ({u} : Set ↥A)⁆ := by
  have hodd := not_two_dvd_index_centralizer hperf hτ hZc hOc hcardZ hu2 hu
  refine mem_commutator_of_mem_center_of_coprime_index hperf hc ?_
  rw [hc2]
  exact ((Nat.prime_two.coprime_iff_not_dvd).mpr hodd).symm

omit [Finite G] in
private theorem mem_perfect_of_centralizer {u : ↥A}
    (hZc : Open.fusionZStar ↥A = center ↥A)
    {H : Subgroup ↥A} (hHc : ∀ h ∈ H, h * u = u * h)
    (hHp : ⁅H, H⁆ = H)
    (hHgen : ∀ g : ↥A, ⁅g, u⁆ ∈ Open.fusionZStar ↥A → g ∈ H ⊔ Open.fusionZStar ↥A)
    {c : ↥A}
    (hcomm : c ∈ ⁅centralizer ({u} : Set ↥A), centralizer ({u} : Set ↥A)⁆) :
    c ∈ H := by
  have hZc' : Open.fusionZStar ↥A ≤ Subgroup.center ↥A := by rw [hZc]
  have hZK : Open.fusionZStar ↥A ≤ centralizer ({u} : Set ↥A) :=
    hZc' |>.trans (Subgroup.center_le_centralizer _)
  have hHK : H ≤ centralizer ({u} : Set ↥A) := by
    intro h hh
    rw [mem_centralizer_singleton_iff]
    exact hHc h hh
  have hKH : centralizer ({u} : Set ↥A) ≤ H ⊔ Open.fusionZStar ↥A := by
    intro g hg
    refine hHgen g ?_
    have h1 : ⁅g, u⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (mem_centralizer_singleton_iff.mp hg)
    rw [h1]
    exact Subgroup.one_mem _
  have hEq : H ⊔ Open.fusionZStar ↥A = centralizer ({u} : Set ↥A) :=
    le_antisymm (sup_le hHK hZK) hKH
  have hK' : ⁅centralizer ({u} : Set ↥A), centralizer ({u} : Set ↥A)⁆ ≤ H := by
    rw [← hEq, commutator_sup_eq_of_le_center hZc', hHp]
  exact hK' hcomm

private theorem normalSettingAt_of_standard (hS : SchreierFor Blueprint.Catalog)
    (hC4 : SuzONanNotProperFixedCatalog) (hbase : L34BaseSetting G) (hA : IsStandardSubgroup A)
    (hSuz : Blueprint.NativeSporadic.IsSporadic (↥A ⧸ center ↥A) .Suz)
    {t : G} (ht : orderOf t = 2) (htA : t ∈ (center ↥A).map A.subtype) :
    L34NormalSettingAt (fun X _ => Blueprint.NativeSporadic.IsSporadic X .Suz) G t A := by
  have : IsSimpleGroup G := hbase.1
  obtain ⟨hN, hPc⟩ := normal_isPComponent_subgroupOf_centralizer hA ht htA
  have hτ := isSporadic_fusionZStar_of_standard hA hSuz
  exact ⟨hbase, ht, le_centralizer_of_mem_map_center htA, hPc, hN,
    Foote5.SolMax.gsMirrorMaximal_of_suzONan hS hC4 hbase.2.1 hbase.2.2.1 (Or.inl hτ), hτ⟩

end Setting

section TestData

open CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

private theorem exists_mem_not_mem_zStar {X : Type} [Group X] [Finite X] {z : X}
    {E : Subgroup X}
    (hE : CFSG.ComponentClassification.GrSLit.IsElemTwo E) (hE8 : 8 ≤ Nat.card E)
    (hzE : z ∈ E)
    (hAZ : ∀ a ∈ E, a ∈ Open.fusionZStar X → a = 1 ∨ a = z) :
    ∃ u ∈ E, u ∉ Open.fusionZStar X := by
  by_contra h
  push Not at h
  have hEsub : E ≤ Open.fusionZStar X := fun x hx => h x hx
  have hcard : Nat.card E ≤ 2 := by
    have hsub : E ≤ zpowers z := by
      intro x hx
      rcases hAZ x hx (hEsub hx) with h1 | h1
      · rw [h1]; exact one_mem _
      · rw [h1]; exact mem_zpowers z
    have h1 : Nat.card E ≤ Nat.card (zpowers z) := Subgroup.card_le_of_le hsub
    rw [Nat.card_zpowers] at h1
    have h2 : orderOf z ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hE.2 z hzE)
    exact h1.trans (Nat.le_of_dvd (by norm_num) h2)
  omega

private theorem exists_suz_even_testConfig
    (hZ : CFSG.ComponentClassification.RankTwoSporadic.Suz.SuzCentralTwoGroupOrderBound)
    (hperf : Group.IsPerfect ↥A)
    (hτ : Blueprint.NativeSporadic.IsSporadic (↥A ⧸ Open.fusionZStar ↥A) .Suz)
    (hr : 3 ≤ pRank 2 ↥A) (hc : center (↥A ⧸ pPrimeCore 2 ↥A) ≠ ⊥) :
    ∃ (z u : ↥A) (E : Subgroup ↥A), z * z = 1 ∧ u * u = 1 ∧ u * z = z * u ∧
      z ∈ Open.fusionZStar ↥A ∧ u ∉ Open.fusionZStar ↥A ∧
      CFSG.ComponentClassification.GrSLit.IsElemTwo E ∧ z ∈ E ∧ u ∈ E ∧
      8 ≤ Nat.card E ∧
      (∀ a ∈ E, a ∈ Open.fusionZStar ↥A → a = 1 ∨ a = z) := by
  obtain ⟨z, E, hz2, hzZ, -, hE, hzE, hE8, hAZ⟩ :=
    exists_twoSuz_testConfig hZ hperf hτ hr hc
  obtain ⟨u, huE, huZ⟩ := exists_mem_not_mem_zStar hE hE8 hzE hAZ
  exact ⟨z, u, E, hz2, hE.2 u huE, hE.1 u huE z hzE, hzZ, huZ, hE, hzE, huE, hE8, hAZ⟩

private theorem exists_perfect_doubleCentralizer_contains_center
    (hA : IsStandardSubgroup A)
    (hZ : CFSG.ComponentClassification.RankTwoSporadic.Suz.SuzCentralTwoGroupOrderBound)
    (hC : TwoSuzCentralizerFacts)
    (hτ : Blueprint.NativeSporadic.IsSporadic (↥A ⧸ Open.fusionZStar ↥A) .Suz)
    (hc : center (↥A ⧸ pPrimeCore 2 ↥A) ≠ ⊥)
    {z u c : ↥A} (hu2 : u * u = 1) (hz2 : z * z = 1) (huz : u * z = z * u)
    (hzZ : z ∈ Open.fusionZStar ↥A) (huZ : u ∉ Open.fusionZStar ↥A)
    (hcA : c ∈ center ↥A) (hc2 : orderOf c = 2) :
    ∃ H : Subgroup ↥A, (∀ h ∈ H, h * u = u * h ∧ h * z = z * h) ∧ ⁅H, H⁆ = H ∧
      HasSimpleQuotient3Quart ↥H ∧
      (∀ g : ↥A, ⁅g, u⁆ ∈ Open.fusionZStar ↥A → g ∈ H ⊔ Open.fusionZStar ↥A) ∧
      c ∈ H := by
  obtain ⟨H, hHc, hHp, hH3, hHgen⟩ :=
    exists_doubleCentralizer_subgroup hZ hC hA.1.1 hτ hc hu2 hz2 huz hzZ huZ
  have hZc : Open.fusionZStar ↥A = center ↥A :=
    CFSG.OddStandard.fusionZStar_eq_center_of_standard
      (CFSG.isStandardSubgroup_iff_standardComponentIsStandard.1 hA)
  have hOc : pPrimeCore 2 ↥A ≤ center ↥A :=
    CFSG.OddStandard.Residual.pPrimeCore_le_center_of_quasisimple hA.1
      (even_iff_two_dvd.1 (CFSG.OddStandard.even_card_of_standard
        (CFSG.isStandardSubgroup_iff_standardComponentIsStandard.1 hA)))
  have hcardZ : Nat.card (center (↥A ⧸ pPrimeCore 2 ↥A)) = 2 :=
    card_center_quotient_eq_two hA.1.1 hτ hc
  have huc : u ∉ center ↥A := fun h => huZ (hZc ▸ h)
  have hcomm := mem_commutator_centralizer hA.1.1 hτ hZc hOc hcardZ hu2 huc hcA hc2
  refine ⟨H, hHc, hHp, hH3, hHgen, ?_⟩
  exact mem_perfect_of_centralizer hZc (fun h hh => (hHc h hh).1) hHp hHgen hcomm

private theorem activeTwoComponents_ncard_le_eight
    (hbase : L34BaseSetting G) {t a : G} (ht : orderOf t = 2) (ha : orderOf a = 2)
    (hta : t * a = a * t) (hrank : pRank 2 ↥(centralizer ({t} : Set G)) ≤ 8)
    {Y : Subgroup G}
    (hY : Y ≤ oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({a} : Set G)) :
    (activeTwoComponents a Y).ncard ≤ 8 := by
  have h1 := l34ActiveSupportCount_holds G t a ht ha hta
    (fun J hJ => hbase.2.2.2.2.2.2.2 a t J hJ) Y hY
  exact h1.trans ((pRank_two_le_of_le inf_le_left).trans hrank)

private theorem activeTwoComponents_eq_empty_of_perfect {t a : G} {H D : Subgroup G}
    (ht : orderOf t = 2) (ha : orderOf a = 2) (hta : t * a = a * t)
    (htypes : ∀ J : Subgroup G, GSUnbalancingTriple a t J →
      IsL2Type 5 (J ⧸ pPrimeCore 2 J) ∨ IsL2Type 7 (J ⧸ pPrimeCore 2 J) ∨
      IsL34Type (J ⧸ Open.fusionZStar J))
    (hHt : H ≤ centralizer ({t} : Set G)) (hHa : H ≤ centralizer ({a} : Set G))
    (hHp : ⁅H, H⁆ = H) (hH3 : HasSimpleQuotient3Quart ↥H)
    (hcnt : (activeTwoComponents a (oddIn (centralizer ({t} : Set G)) ⊓
      centralizer ({a} : Set G))).ncard ≤ 8)
    (htH : t ∈ H) (hD : D = oddIn (centralizer ({t} : Set G)))
    (hDa : D ≤ centralizer ({a} : Set G)) :
    activeTwoComponents a D = ∅ := by
  have hYeq : oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({a} : Set G) = D :=
    (inf_eq_left.mpr ((le_of_eq hD.symm).trans hDa)).trans hD.symm
  rw [Set.eq_empty_iff_forall_notMem]
  intro J hJ
  have hJH : J ≤ centralizer ({a} : Set G) := hJ.1
  have hJc : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))) := hJ.2.1
  have hJY : J ∈ activeTwoComponents a (oddIn (centralizer ({t} : Set G)) ⊓
      centralizer ({a} : Set G)) := by
    rw [hYeq]; exact hJ
  have hT : GSUnbalancingTriple a t J :=
    GrS5.gsUnbalancingTriple_of_not_le solomonCommutingCoreInput ht ha hta hJH hJc
      (le_inf (le_of_eq hD) hDa) hJ.2.2
  have htJ : ⁅J, zpowers t⁆ = J :=
    (UnbalancedLayer.gsUnbalancingTriple_iff.mp hT).2.2.2.2.2.1
  have hhz := zStarAct_eq_one_of_perfect_active ht ha hta htypes hHt hHa hHp hH3 hcnt
  obtain ⟨hgn, hz⟩ := hhz J hJY t htH
  have htK : t ∈ UnbalancedLayer.coreActionKernel J :=
    (GSThmB.A10T.zStarAct_eq_one_iff hJH hJc ⟨t, hgn⟩).mp hz
  have hJle : J ≤ oddIn J := by
    have h1 := CFSG.ComponentClassification.HSFLit.L34Uniq.commutator_le_oddIn_of_le
      (zpowers_le.mpr htK)
    rwa [htJ] at h1
  have hnt : Nontrivial (↥J ⧸ pPrimeCore 2 ↥J) := by
    have hJq : CFSG.IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J) :=
      ((CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J
        (centralizer ({a} : Set G)) hJH).mp hJc).2.2
    exact CFSG.LocalCores.isQuasisimple_nontrivial hJq
  exact (CFSG.ComponentClassification.GSThmB.CorC.not_le_oddIn_of_nontrivial
    (C := J) (T := J) hnt) hJle

private theorem exists_wGroup_eq_bot_of_testConfig {t : G}
    (hSV : L34SuzSignalizerVanishing)
    (hsetting : L34NormalSettingAt (fun X _ => Blueprint.NativeSporadic.IsSporadic X .Suz)
      G t A)
    (hPt : A ≤ centralizer ({t} : Set G)) (ht2 : t * t = 1)
    {E : Subgroup ↥A} (hE : CFSG.ComponentClassification.GrSLit.IsElemTwo E)
    (hE8 : 8 ≤ Nat.card E) :
    ∃ B : Subgroup G, t ∈ B ∧ (∀ u ∈ E, (u : G) ∈ B) ∧
      B ≤ centralizer ({t} : Set G) ∧ 8 ≤ Nat.card B ∧
      @CFSG.ComponentClassification.GrSLit.wGroup G _ B = ⊥ := by
  classical
  set EG : Subgroup G := E.map A.subtype with hEG
  have hEG2 : CFSG.ComponentClassification.GrSLit.IsElemTwo EG := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact congrArg Subtype.val (hE.1 a ha b hb)
    · rintro _ ⟨a, ha, rfl⟩
      exact congrArg Subtype.val (hE.2 a ha)
  set B : Subgroup G := zpowers t ⊔ EG with hBdef
  have hcomm : ∀ x ∈ zpowers t, ∀ y ∈ EG, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
    exact (Commute.zpow_left
      (mem_centralizer_singleton_iff.mp (hPt a.2)).symm i).eq
  have hB2 : CFSG.ComponentClassification.GrSLit.IsElemTwo B :=
    (isElemTwo_zpowers ht2).sup (F' := EG) hEG2 hcomm
  have hBle : B ≤ centralizer ({t} : Set G) :=
    sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
      ((map_subtype_le E).trans hPt)
  have hB8 : 8 ≤ Nat.card B := by
    have h1 : Nat.card EG = Nat.card E := Subgroup.card_map_of_injective A.subtype_injective
    have h2 : Nat.card EG ≤ Nat.card B := Subgroup.card_le_of_le le_sup_right
    omega
  have hBab : Open.IsElemAbelian 2 B :=
    ⟨isMulCommutative_iff_of_setLike.mpr hB2.1, fun x hx => by
      rw [pow_two]; exact hB2.2 x hx⟩
  have hWB : @CFSG.ComponentClassification.GrSLit.wGroup G _ B = ⊥ :=
    hSV G t A hsetting B hBle hBab hB8
  exact ⟨B, mem_sup_left (mem_zpowers t), fun u hu => mem_sup_right ⟨u, hu, rfl⟩,
    hBle, hB8, hWB⟩

omit [Finite G] in
private theorem exists_map_perfect_doubleCentralizer {t : G}
    (hPt : A ≤ centralizer ({t} : Set G))
    {u z c : ↥A} {H : Subgroup ↥A}
    (hHc : ∀ h ∈ H, h * u = u * h ∧ h * z = z * h)
    (hHp : ⁅H, H⁆ = H) (hH3 : HasSimpleQuotient3Quart ↥H)
    (hcH : c ∈ H) (hct : (c : G) = t) :
    ∃ HG : Subgroup G, HG ≤ centralizer ({t} : Set G) ∧
      HG ≤ centralizer ({(u : G)} : Set G) ∧ ⁅HG, HG⁆ = HG ∧
      HasSimpleQuotient3Quart ↥HG ∧ t ∈ HG := by
  refine ⟨H.map A.subtype, (map_subtype_le H).trans hPt, ?_, ?_, ?_, ⟨c, hcH, hct⟩⟩
  · rintro _ ⟨h, hh, rfl⟩
    exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (hHc h hh).1)
  · rw [← Subgroup.map_commutator, hHp]
  · exact HasSimpleQuotient3Quart.of_mulEquiv
      (Subgroup.equivMapOfInjective H A.subtype A.subtype_injective) hH3

omit [Finite G] in
private theorem le_centralizer_mul {t u : G} {H : Subgroup G}
    (hHt : H ≤ centralizer ({t} : Set G)) (hHu : H ≤ centralizer ({u} : Set G)) :
    H ≤ centralizer ({(t * u)} : Set G) := by
  intro h hh
  have h1 : Commute h t := mem_centralizer_singleton_iff.mp (hHt hh)
  have h2 : Commute h u := mem_centralizer_singleton_iff.mp (hHu hh)
  exact mem_centralizer_singleton_iff.mpr (h1.mul_right h2).eq

omit [Finite G] in
private theorem oddIn_eq_bot_of_component_bounds {t u : G} {D : Subgroup G}
    (hD : D = oddIn (centralizer ({t} : Set G)))
    (hDle : D ≤ oddIn (centralizer ({t} : Set G)))
    (hleu : D ≤ oddIn (centralizer ({u} : Set G)))
    (hletu : D ≤ oddIn (centralizer ({t * u} : Set G)))
    (htri : oddIn (centralizer ({t} : Set G)) ⊓ oddIn (centralizer ({u} : Set G)) ⊓
      oddIn (centralizer ({t * u} : Set G)) = ⊥) :
    oddIn (centralizer ({t} : Set G)) = ⊥ := by
  have hDbot : D ≤ ⊥ := by
    rw [← htri]
    exact le_inf (le_inf hDle hleu) hletu
  rw [← hD]
  exact eq_bot_iff.mpr hDbot

private theorem oddIn_eq_bot_of_active_data
    (hbase : L34BaseSetting G) {t u : G} {H B : Subgroup G}
    (ht : orderOf t = 2) (hu : orderOf u = 2) (htu : t * u = u * t) (hne : t ≠ u)
    (htu2 : orderOf (t * u) = 2) (ht_tu : t * (t * u) = (t * u) * t)
    (hHt : H ≤ centralizer ({t} : Set G)) (hHu : H ≤ centralizer ({u} : Set G))
    (hHp : ⁅H, H⁆ = H) (hH3 : HasSimpleQuotient3Quart ↥H) (htH : t ∈ H)
    (htB : t ∈ B) (huB : u ∈ B) (hWB : wGroup B = ⊥)
    (hrank : pRank 2 ↥(centralizer ({t} : Set G)) ≤ 8)
    (hDu : oddIn (centralizer ({t} : Set G)) ≤ centralizer ({u} : Set G))
    (hDtu : oddIn (centralizer ({t} : Set G)) ≤ centralizer ({t * u} : Set G)) :
    oddIn (centralizer ({t} : Set G)) = ⊥ := by
  set D : Subgroup G := oddIn (centralizer ({t} : Set G)) with hDdef
  have hDle : D ≤ oddIn (centralizer ({t} : Set G)) := le_of_eq hDdef
  have hDu' : D ≤ centralizer ({u} : Set G) := hDle.trans hDu
  have hDtu' : D ≤ centralizer ({t * u} : Set G) := hDle.trans hDtu
  have htypesu : ∀ J : Subgroup G, GSUnbalancingTriple u t J →
      IsL2Type 5 (J ⧸ pPrimeCore 2 J) ∨ IsL2Type 7 (J ⧸ pPrimeCore 2 J) ∨
      IsL34Type (J ⧸ Open.fusionZStar J) :=
    fun J hJ => hbase.2.2.2.2.2.2.2 u t J hJ
  have htypestu : ∀ J : Subgroup G, GSUnbalancingTriple (t * u) t J →
      IsL2Type 5 (J ⧸ pPrimeCore 2 J) ∨ IsL2Type 7 (J ⧸ pPrimeCore 2 J) ∨
      IsL34Type (J ⧸ Open.fusionZStar J) :=
    fun J hJ => hbase.2.2.2.2.2.2.2 (t * u) t J hJ
  have hcntu : (activeTwoComponents u (oddIn (centralizer ({t} : Set G)) ⊓
      centralizer ({u} : Set G))).ncard ≤ 8 :=
    activeTwoComponents_ncard_le_eight hbase ht hu htu hrank (le_refl _)
  have hcnttu : (activeTwoComponents (t * u) (oddIn (centralizer ({t} : Set G)) ⊓
      centralizer ({t * u} : Set G))).ncard ≤ 8 :=
    activeTwoComponents_ncard_le_eight hbase ht htu2 ht_tu hrank (le_refl _)
  have hemptyu : activeTwoComponents u D = ∅ :=
    activeTwoComponents_eq_empty_of_perfect ht hu htu htypesu hHt hHu hHp hH3 hcntu htH
      hDdef hDu'
  have hHtu : H ≤ centralizer ({(t * u)} : Set G) := le_centralizer_mul hHt hHu
  have hemptytu : activeTwoComponents (t * u) D = ∅ :=
    activeTwoComponents_eq_empty_of_perfect ht htu2 ht_tu htypestu hHt hHtu hHp hH3 hcnttu
      htH hDdef hDtu'
  have hleu : D ≤ oddIn (centralizer ({u} : Set G)) :=
    le_oddIn_centralizer_of_trivial_on_active ht hu htu (le_inf hDle hDu') le_rfl
      (by rw [hemptyu]; simp)
  have hletu : D ≤ oddIn (centralizer ({t * u} : Set G)) :=
    le_oddIn_centralizer_of_trivial_on_active ht htu2 ht_tu (le_inf hDle hDtu') le_rfl
      (by rw [hemptytu]; simp)
  exact oddIn_eq_bot_of_component_bounds hDdef hDle hleu hletu
    (inf_oddIn_eq_bot_of_wGroup_eq_bot ht hu htu hne htB huB hWB)


private theorem ne_of_not_mem_zStar (hA : IsStandardSubgroup A) {t : G}
    (htA : t ∈ (center ↥A).map A.subtype) {u : ↥A}
    (huZ : u ∉ Open.fusionZStar ↥A) : t ≠ (u : G) := by
  intro h
  apply huZ
  have hZc : Open.fusionZStar ↥A = center ↥A :=
    CFSG.OddStandard.fusionZStar_eq_center_of_standard
      (CFSG.isStandardSubgroup_iff_standardComponentIsStandard.1 hA)
  rw [hZc]
  have hmem : (u : G) ∈ (center ↥A).map A.subtype := by
    rw [← h]
    exact htA
  obtain ⟨c', hc', hc'u⟩ := Subgroup.mem_map.mp hmem
  rw [← Subtype.ext hc'u]
  exact hc'

private theorem suz_even_commuting_involution_data
    (hA : IsStandardSubgroup A) {t : G} (ht : orderOf t = 2)
    (htA : t ∈ (center ↥A).map A.subtype) {u c : ↥A} (hu2 : u * u = 1)
    (huZ : u ∉ Open.fusionZStar ↥A) (hct : (c : G) = t) :
    orderOf (u : G) = 2 ∧ t * (u : G) = (u : G) * t ∧ t ≠ (u : G) ∧
      orderOf (t * (u : G)) = 2 ∧ t * (t * (u : G)) = (t * u) * t ∧
      oddIn (centralizer ({t} : Set G)) ≤ centralizer ({(u : G)} : Set G) ∧
      oddIn (centralizer ({t} : Set G)) ≤ centralizer ({(t * (u : G))} : Set G) := by
  have hPt : A ≤ centralizer ({t} : Set G) := le_centralizer_of_mem_map_center htA
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have htu : t * (u : G) = (u : G) * t :=
    (mem_centralizer_singleton_iff.mp (hPt u.2)).symm
  have huG2 : (u : G) * (u : G) = 1 := by
    rw [← Subgroup.coe_mul, hu2, Subgroup.coe_one]
  have huo2 : orderOf (u : G) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact huG2) (fun h => by
      have hu1 : u = 1 := Subtype.ext h
      exact huZ (hu1 ▸ one_mem _))
  have hne : t ≠ (u : G) := ne_of_not_mem_zStar hA htA huZ
  have htu2 : orderOf (t * (u : G)) = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two, show t * (u : G) * (t * u) = t * t * (u * u) from by
        rw [mul_assoc, ← mul_assoc (u : G) t u, ← htu]
        group]
      rw [ht2, huG2, one_mul]
    · intro h
      apply hne
      calc t = t * ((u : G) * (u : G)) := by rw [huG2, mul_one]
        _ = t * (u : G) * (u : G) := by rw [mul_assoc]
        _ = (u : G) := by rw [h, one_mul]
  have ht_tu : t * (t * (u : G)) = (t * u) * t :=
    ((Commute.refl t).mul_right (show Commute t (u : G) from htu)).eq
  have hDA : oddIn (centralizer ({t} : Set G)) ≤ centralizer (A : Set G) :=
    oddIn_centralizer_le_centralizer hA ht htA
  have hDu : oddIn (centralizer ({t} : Set G)) ≤ centralizer ({(u : G)} : Set G) := by
    intro d hd
    exact mem_centralizer_singleton_iff.mpr
      ((mem_centralizer_iff.mp (hDA hd)) (u : G) u.2).symm
  have htuA : ((c * u : ↥A) : G) = t * (u : G) := by
    rw [Subgroup.coe_mul, hct]
  have hDtu : oddIn (centralizer ({t} : Set G)) ≤
      centralizer ({(t * (u : G))} : Set G) := by
    intro d hd
    exact mem_centralizer_singleton_iff.mpr (by
      have h1 := (mem_centralizer_iff.mp (hDA hd)) ((c * u : ↥A) : G) (c * u).2
      rw [htuA] at h1
      exact h1.symm)
  exact ⟨huo2, htu, hne, htu2, ht_tu, hDu, hDtu⟩

end TestData

section Certified

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

private theorem exists_suz_even_test
    (hA : IsStandardSubgroup A) {t : G} (ht : orderOf t = 2)
    (htA : t ∈ (center ↥A).map A.subtype)
    (hSuz : Blueprint.NativeSporadic.IsSporadic (↥A ⧸ center ↥A) .Suz) :
    ∃ (z u c : ↥A) (E : Subgroup ↥A),
      z * z = 1 ∧ u * u = 1 ∧ u * z = z * u ∧ z ∈ Open.fusionZStar ↥A ∧
      u ∉ Open.fusionZStar ↥A ∧ CFSG.ComponentClassification.GrSLit.IsElemTwo E ∧
      z ∈ E ∧ u ∈ E ∧ 8 ≤ Nat.card E ∧
      (∀ a ∈ E, a ∈ Open.fusionZStar ↥A → a = 1 ∨ a = z) ∧
      c ∈ center ↥A ∧ orderOf c = 2 ∧ (c : G) = t := by
  have hperf : Group.IsPerfect ↥A := hA.1.1
  have hτ : Blueprint.NativeSporadic.IsSporadic (↥A ⧸ Open.fusionZStar ↥A) .Suz :=
    isSporadic_fusionZStar_of_standard hA hSuz
  have hc : center (↥A ⧸ pPrimeCore 2 ↥A) ≠ ⊥ := center_quotient_ne_bot ht htA
  have hr : 3 ≤ pRank 2 ↥A := three_le_pRank_of_sporadic_suz_fusionZStar hτ
  obtain ⟨z, u, E, hz2, hu2, huz, hzZ, huZ, hE, hzE, huE, hE8, hAZ⟩ :=
    exists_suz_even_testConfig suzCentralTwoGroupOrderBound_holds hperf hτ hr hc
  obtain ⟨c, hcA, hct⟩ := Subgroup.mem_map.mp htA
  have hc2 : orderOf c = 2 := by
    rw [← Subgroup.orderOf_coe]
    have h : (c : G) = t := hct
    rw [h, ht]
  exact ⟨z, u, c, E, hz2, hu2, huz, hzZ, huZ, hE, hzE, huE, hE8, hAZ, hcA, hc2, hct⟩

theorem oddIn_centralizer_eq_bot_of_suz_even (hS : SchreierFor Blueprint.Catalog)
    (hC4 : SuzONanNotProperFixedCatalog) (hSV : L34SuzSignalizerVanishing) {G : Type}
    [Group G] [Finite G] (hbase : L34BaseSetting G) {A : Subgroup G} (hA : IsStandardSubgroup A)
    (hSuz : Blueprint.NativeSporadic.IsSporadic (↥A ⧸ center ↥A) .Suz)
    (hrank : pRank 2 ↥(centralizer (A : Set G)) ≤ 1) {t : G} (ht : orderOf t = 2)
    (htA : t ∈ (center ↥A).map A.subtype) : oddIn (centralizer ({t} : Set G)) = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, u, c, E, hz2, hu2, huz, hzZ, huZ, hE, hzE, huE, hE8, hAZ, hcA, hc2, hct⟩ :=
    exists_suz_even_test hA ht htA hSuz
  have hτ : Blueprint.NativeSporadic.IsSporadic (↥A ⧸ Open.fusionZStar ↥A) .Suz :=
    isSporadic_fusionZStar_of_standard hA hSuz
  have hc : center (↥A ⧸ pPrimeCore 2 ↥A) ≠ ⊥ := center_quotient_ne_bot ht htA
  obtain ⟨H, hHc, hHp, hH3, hHgen, hcH⟩ :=
    exists_perfect_doubleCentralizer_contains_center hA suzCentralTwoGroupOrderBound_holds
      twoSuzCentralizerFacts_holds hτ hc hu2 hz2 huz hzZ huZ hcA hc2
  have hPt : A ≤ centralizer ({t} : Set G) := le_centralizer_of_mem_map_center htA
  obtain ⟨HG, hHGt, hHGu, hHGp, hHG3, htHG⟩ :=
    exists_map_perfect_doubleCentralizer hPt hHc hHp hH3 hcH hct
  obtain ⟨huo2, htu, hne, htu2, ht_tu, hDu, hDtu⟩ :=
    suz_even_commuting_involution_data hA ht htA hu2 huZ hct
  have hsetting : L34NormalSettingAt
      (fun X _ => Blueprint.NativeSporadic.IsSporadic X .Suz) G t A :=
    normalSettingAt_of_standard hS hC4 hbase hA hSuz ht htA
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  obtain ⟨B, htB, huB, -, -, hWB⟩ :=
    exists_wGroup_eq_bot_of_testConfig hSV hsetting hPt ht2 hE hE8
  have hrank8 : pRank 2 ↥(centralizer ({t} : Set G)) ≤ 8 :=
    pRank_centralizer_le_eight hA hτ ht htA hrank
  exact oddIn_eq_bot_of_active_data hbase ht huo2 htu hne htu2 ht_tu hHGt hHGu hHGp
    hHG3 htHG htB (huB u huE) hWB hrank8 hDu hDtu

end Certified

end CFSG.ComponentClassification.GrSLit.L34Sec5S
