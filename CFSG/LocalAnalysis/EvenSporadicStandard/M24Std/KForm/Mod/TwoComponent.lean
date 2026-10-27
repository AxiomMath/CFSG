module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.CatZ2S6Basic
public import CFSG.Open.FusionDefs
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.Milestones.OO_odd_order_solvable

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open Subgroup CFSG CFSG.Open

private theorem exists_mul_ne_mul_of_four_dvd' {K : Type*} [Group K] [Finite K] [IsSimpleGroup K]
    (h4 : 4 ∣ Nat.card K) : ∃ a b : K, a * b ≠ b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hc
  push Not at hc
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 (dvd_trans (by norm_num) h4)
  have hN : (Subgroup.zpowers x).Normal :=
    ⟨fun n hn g => by rw [hc g n, mul_inv_cancel_right]; exact hn⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers x) with h | h
  · have hx1 : x = 1 := by
      have hx' : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
      rwa [h, Subgroup.mem_bot] at hx'
    rw [hx1, orderOf_one] at hx
    omega
  · have hcard : Nat.card K = 2 := by
      rw [← Subgroup.card_top (G := K), ← h, Nat.card_zpowers, hx]
    rw [hcard] at h4
    norm_num at h4

private theorem isQuasisimple_alternatingGroup_six :
    CFSG.IsQuasisimple (alternatingGroup (Fin 6)) := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  refine (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ?_).1
  have h4 : 4 ∣ Nat.card (alternatingGroup (Fin 6)) := by
    rw [card_alternatingGroup_six]; norm_num
  exact exists_mul_ne_mul_of_four_dvd' h4

private theorem fusionOddCore_eq_pPrimeCore (X : Type*) [Group X] :
    CFSG.Open.fusionOddCore X = CFSG.pPrimeCore 2 X := by
  unfold CFSG.Open.fusionOddCore CFSG.pPrimeCore
  congr 1
  ext K
  simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]

private theorem odd_natCard_fusionOddCore (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.Open.fusionOddCore X)) := by
  rw [fusionOddCore_eq_pPrimeCore]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

private theorem odd_natCard_pPrimeCore (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.pPrimeCore 2 X)) :=
  Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

private theorem le_fusionOddCore_of_odd {X : Type*} [Group X] {N : Subgroup X} [N.Normal]
    (hN : Odd (Nat.card N)) : N ≤ CFSG.Open.fusionOddCore X :=
  le_sSup ⟨inferInstance, hN⟩

private theorem le_perfectResidual_of_perfect {H : Type*} [Group H] (Q : Subgroup H)
    (hQ : ⁅Q, Q⁆ = Q) :
    Q ≤ CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual H := by
  refine le_iInf fun n => ?_
  induction n with
  | zero => exact le_top
  | succ n ih =>
    rw [derivedSeries_succ]
    calc Q = ⁅Q, Q⁆ := hQ.symm
      _ ≤ ⁅derivedSeries H n, derivedSeries H n⁆ := Subgroup.commutator_mono ih ih

private theorem le_perfectResidualOf' {A : Type*} [Group A] {H Q : Subgroup A} (hQH : Q ≤ H)
    (hQ : ⁅Q, Q⁆ = Q) : Q ≤ CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf H := by
  have hQ' : (Q.subgroupOf H).map H.subtype = Q := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hQH]
  have hperf : ⁅Q.subgroupOf H, Q.subgroupOf H⁆ = Q.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, hQ', hQ]
  have h1 := le_perfectResidual_of_perfect (Q.subgroupOf H) hperf
  calc Q = (Q.subgroupOf H).map H.subtype := hQ'.symm
    _ ≤ CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf H := by
        simpa [CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf] using
          Subgroup.map_mono (f := H.subtype) h1

private theorem eq_top_of_isSubnormal_of_sup_eq_top' {P : Type*} [Group P] [Group.IsPerfect P]
    {K M : Subgroup P} (hK : K.IsSubnormal) (hM : M.Normal) (hMs : Group.IsSolvable M)
    (hKM : K ⊔ M = ⊤) : K = ⊤ := by
  revert hKM
  induction hK with
  | top => intro _; rfl
  | step K T hKT _ hN ih =>
    intro hKM
    have hTM : T ⊔ M = ⊤ := by
      rw [eq_top_iff, ← hKM]
      exact sup_le_sup_right hKT M
    have hT' : T = ⊤ := ih hTM
    subst hT'
    have hKn : K.Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKT, top_le_iff,
        Subgroup.normalizer_eq_top_iff] at hN
      exact hN
    have hf : Function.Surjective ((QuotientGroup.mk' K).comp M.subtype) := by
      intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      have hg : g ∈ K ⊔ M := by
        rw [hKM]
        exact Subgroup.mem_top g
      obtain ⟨k, hk, m, hm, rfl⟩ := (Subgroup.mem_sup_of_normal_right (s := K) (t := M)).mp hg
      refine ⟨⟨m, hm⟩, ?_⟩
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
      rw [QuotientGroup.eq]
      simpa [mul_assoc] using hKn.conj_mem' k hk m
    have hsolv : Group.IsSolvable (P ⧸ K) := Group.isSolvable_of_surjective hf
    have hsub : Subsingleton (P ⧸ K) := by
      by_contra hns
      rw [not_subsingleton_iff_nontrivial] at hns
      exact Group.IsPerfect.not_isSolvable (P ⧸ K) hsolv
    refine top_le_iff.mp fun g _ => ?_
    have h1 : (g : P ⧸ K) = ((1 : P) : P ⧸ K) := Subsingleton.elim _ _
    rw [QuotientGroup.eq] at h1
    simpa using h1

private theorem map_perfectResidualOf_comap {F : Type*} [Group F] [Finite F] (Φ : F →* Z2S6)
    (hA : a6Factor ≤ Φ.range) :
    (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf (a6Factor.comap Φ)).map Φ =
      a6Factor := by
  let D : Subgroup F := a6Factor.comap Φ
  have hD : D.map Φ = a6Factor := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.2 hA
  haveI : Group.IsPerfect (alternatingGroup (Fin 6)) := isQuasisimple_alternatingGroup_six.1
  haveI : Group.IsPerfect ↥a6Factor :=
    Group.IsPerfect.ofSurjective (G := alternatingGroup (Fin 6)) (G' := ↥a6Factor)
      (f := a6FactorEquiv.symm.toMonoidHom) a6FactorEquiv.symm.surjective
  let f : ↥D →* ↥a6Factor := (Φ.comp D.subtype).codRestrict a6Factor fun x => x.2
  have hf : Function.Surjective f := by
    intro y
    have hy : (y : Z2S6) ∈ D.map Φ := by rw [hD]; exact y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hres :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_surjects_to_perfect_image f hf
  have hcomp :
      ((CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥D).map (Φ.comp D.subtype)) =
        a6Factor := by
    have h := congrArg (Subgroup.map (a6Factor.subtype)) hres
    rw [Subgroup.map_map] at h
    have hfg : a6Factor.subtype.comp f = Φ.comp D.subtype := MonoidHom.ext fun x => rfl
    rw [hfg] at h
    simpa [Subgroup.map_top, Subgroup.range_subtype] using h
  rw [CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf, Subgroup.map_map]
  exact hcomp

theorem exists_twoComponent {F : Type} [Group F] [Finite F] (Φ : F →* Z2S6)
    (hodd : Odd (Nat.card Φ.ker)) (hA : a6Factor ≤ Φ.range) :
    ∃ J : Subgroup F, J.Normal ∧ ⁅J, J⁆ = J ∧ J.map Φ = a6Factor ∧
      (∀ P : Subgroup F, ⁅P, P⁆ = P → P ≤ J) ∧ IsPComponent 2 J ∧
      Nonempty (↥J ⧸ fusionOddCore ↥J ≃* alternatingGroup (Fin 6)) := by
  classical
  let D : Subgroup F := a6Factor.comap Φ
  let J : Subgroup F := CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf D
  have hDnormal : D.Normal := inferInstance
  have hJD : J ≤ D := Subgroup.map_subtype_le _
  have hJnormal : J.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    apply top_le_iff.1
    intro g _
    exact CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf_normalizer_contains D
      (by rw [Subgroup.normalizer_eq_top_iff.2 hDnormal]; trivial)
  haveI : J.Normal := hJnormal
  have hJperfect : ⁅J, J⁆ = J :=
    Subgroup.isPerfect_iff.mp
      (CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidualOf_isPerfect D)
  have hJmap : J.map Φ = a6Factor := by
    simpa [J, D] using map_perfectResidualOf_comap Φ hA
  have hJcontains : ∀ P : Subgroup F, ⁅P, P⁆ = P → P ≤ J := by
    intro P hP
    have hPD : P ≤ D := by
      apply Subgroup.map_le_iff_le_comap.1
      calc P.map Φ = ⁅P, P⁆.map Φ := by rw [hP]
        _ = ⁅P.map Φ, P.map Φ⁆ := Subgroup.map_commutator _ _ _
        _ ≤ a6Factor := commutator_le_a6Factor _ _
    exact le_perfectResidualOf' hPD hP
  let φJ : ↥J →* ↥a6Factor := (Φ.comp J.subtype).codRestrict a6Factor fun x => hJD x.2
  have hφJ_surj : Function.Surjective φJ := by
    intro y
    have hy : (y : Z2S6) ∈ J.map Φ := by rw [hJmap]; exact y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hker1 : φJ.ker = (J ⊓ Φ.ker).subgroupOf J := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      exact ⟨x.2, MonoidHom.mem_ker.mpr (Subtype.ext_iff.mp (MonoidHom.mem_ker.mp hx))⟩
    · rintro ⟨-, hx⟩
      exact MonoidHom.mem_ker.mpr (Subtype.ext (MonoidHom.mem_ker.mp hx))
  have hker_le_pcore : Φ.ker ≤ CFSG.pPrimeCore 2 F :=
    le_sSup ⟨inferInstance, Nat.coprime_two_left.mpr hodd⟩
  have hcore : fusionOddCore ↥J = (J ⊓ Φ.ker).subgroupOf J := by
    apply le_antisymm
    · intro x hx
      have hmapbot : (fusionOddCore ↥J).map φJ = ⊥ := by
        haveI : IsSimpleGroup (alternatingGroup (Fin 6)) :=
          alternatingGroup.isSimpleGroup (by simp)
        haveI : IsSimpleGroup ↥a6Factor := a6FactorEquiv.isSimpleGroup
        haveI : ((fusionOddCore ↥J).map φJ).Normal :=
          (inferInstance : (fusionOddCore ↥J).Normal).map φJ hφJ_surj
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((fusionOddCore ↥J).map φJ) with h | h
        · exact h
        · exfalso
          have hoddim : Odd (Nat.card ((fusionOddCore ↥J).map φJ)) :=
            Odd.of_dvd_nat (odd_natCard_fusionOddCore ↥J)
              (Subgroup.card_map_dvd (H := fusionOddCore ↥J) φJ)
          have hodd' : Odd (Nat.card ↥a6Factor) := by
            simpa [h, Subgroup.card_top] using hoddim
          rw [card_a6Factor] at hodd'
          norm_num at hodd'
      have hxker : φJ x = 1 := by
        have hmem : φJ x ∈ (fusionOddCore ↥J).map φJ := ⟨x, hx, rfl⟩
        rw [hmapbot] at hmem
        simpa using hmem
      have hmemker : x ∈ φJ.ker := MonoidHom.mem_ker.mpr hxker
      rwa [hker1] at hmemker
    · apply le_fusionOddCore_of_odd
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
      exact Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_right)
  have hφJ_ker : φJ.ker = fusionOddCore ↥J := hker1.trans hcore.symm
  have eJ : ↥J ⧸ fusionOddCore ↥J ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.quotientMulEquivOfEq hφJ_ker).symm.trans
      ((QuotientGroup.quotientKerEquivOfSurjective φJ hφJ_surj).trans a6FactorEquiv)
  refine ⟨J, hJnormal, hJperfect, hJmap, hJcontains, ?_, ⟨eJ⟩⟩
  let q : F →* F ⧸ CFSG.pPrimeCore 2 F := QuotientGroup.mk' (CFSG.pPrimeCore 2 F)
  let K : Subgroup (F ⧸ CFSG.pPrimeCore 2 F) := J.map q
  let res : ↥J →* ↥K :=
    (q.domRestrict J).codRestrict K fun x => Subgroup.mem_map_of_mem q x.2
  have hres_surj : Function.Surjective res := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hres_ker : res.ker = (CFSG.pPrimeCore 2 F).subgroupOf J := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : q (x : F) = 1 := congrArg Subtype.val hx
      have h2 : (x : F) ∈ q.ker := MonoidHom.mem_ker.mpr h1
      rwa [QuotientGroup.ker_mk'] at h2
    · intro hx
      apply Subtype.ext
      change q (x : F) = 1
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact hx
  have hker2 : (CFSG.pPrimeCore 2 F).subgroupOf J = fusionOddCore ↥J := by
    apply le_antisymm
    · apply le_fusionOddCore_of_odd
      have hcard : Nat.card ((CFSG.pPrimeCore 2 F).subgroupOf J) =
          Nat.card (J ⊓ CFSG.pPrimeCore 2 F : Subgroup F) := by
        rw [← Subgroup.card_map_of_injective (f := J.subtype) J.subtype_injective,
          Subgroup.subgroupOf_map_subtype, inf_comm]
      rw [hcard]
      exact Odd.of_dvd_nat (odd_natCard_pPrimeCore F) (Subgroup.card_dvd_of_le inf_le_right)
    · rw [hcore]
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hker_le_pcore (Subgroup.mem_inf.mp hx).2
  have hKq : CFSG.IsQuasisimple K := by
    have eJK : ↥J ⧸ fusionOddCore ↥J ≃* ↥K :=
      (QuotientGroup.quotientMulEquivOfEq (hres_ker.trans hker2)).symm.trans
        (QuotientGroup.quotientKerEquivOfSurjective res hres_surj)
    exact CFSG.IsQuasisimple.of_mulEquiv eJK.symm
      (CFSG.IsQuasisimple.of_mulEquiv eJ isQuasisimple_alternatingGroup_six)
  have hKsub : K.IsSubnormal :=
    hJnormal.isSubnormal.map (QuotientGroup.mk'_surjective (CFSG.pPrimeCore 2 F))
  refine ⟨K, ⟨hKq, hKsub⟩, hJnormal.isSubnormal, rfl, ?_⟩
  intro J' hJ'lt hJ'sub hJ'map
  have hJ'le : J' ≤ J := hJ'lt.le
  have hsup : J'.subgroupOf J ⊔ (J ⊓ CFSG.pPrimeCore 2 F).subgroupOf J = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : (res x).val ∈ J'.map q := by rw [hJ'map]; exact (res x).2
    obtain ⟨y, hyJ', hyq⟩ := Subgroup.mem_map.mp hx
    have hyq' : q y = q (x : F) := hyq
    have hm : (⟨y, hJ'le hyJ'⟩ : ↥J)⁻¹ * x ∈ (J ⊓ CFSG.pPrimeCore 2 F).subgroupOf J := by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      refine ⟨mul_mem (inv_mem (hJ'le hyJ')) x.2, ?_⟩
      have hyq1 : q (y⁻¹ * (x : F)) = 1 := by
        rw [map_mul, map_inv, hyq', inv_mul_cancel]
      have hmem : y⁻¹ * (x : F) ∈ q.ker := MonoidHom.mem_ker.mpr hyq1
      rwa [QuotientGroup.ker_mk'] at hmem
    refine Subgroup.mem_sup_of_normal_right.mpr
      ⟨⟨y, hJ'le hyJ'⟩, ?_, (⟨y, hJ'le hyJ'⟩ : ↥J)⁻¹ * x, hm, ?_⟩
    · rw [Subgroup.mem_subgroupOf]; exact hyJ'
    · group
  have hMnorm : ((J ⊓ CFSG.pPrimeCore 2 F).subgroupOf J).Normal := inferInstance
  have hMsolv : Group.IsSolvable ((J ⊓ CFSG.pPrimeCore 2 F).subgroupOf J) := by
    apply CFSG.Milestones.odd_order_solvable
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
    exact Odd.of_dvd_nat (odd_natCard_pPrimeCore F) (Subgroup.card_dvd_of_le inf_le_right)
  haveI : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr hJperfect
  have htop := eq_top_of_isSubnormal_of_sup_eq_top' hJ'sub.subgroupOf hMnorm hMsolv hsup
  have hEq : J' = J := by
    have hmap := congrArg (Subgroup.map J.subtype) htop
    rw [Subgroup.map_subgroupOf_eq_of_le hJ'le, Subgroup.map_top, Subgroup.range_subtype] at hmap
    exact hmap
  exact (ne_of_lt hJ'lt) hEq

end CFSG.EvenSporadicStandard.M24Std.KForm.Mod
