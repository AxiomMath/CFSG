module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SzEightExcl
public import CFSG.LocalAnalysis.PreuniquenessRankFour.Nongeneration
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.Statements

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

@[expose] def QuasisimpleProperCoreClassification : Prop :=
  ∀ (J : Type) [Group J] [Finite J], Group.IsPerfect J → IsSimpleGroup (J ⧸ Subgroup.center J) →
    Nat.card (Subgroup.center J) = 2 → 2 ≤ twoRank J →
    ∀ (Q : Sylow 2 J) (B : Subgroup J), (Q : Subgroup J) ≤ B → B ≠ ⊤ →
      properTwoGenCoreGamma (Q : Subgroup J) 2 ≤ B →
      Nonempty ((J ⧸ Subgroup.center J) ≃* alternatingGroup (Fin 9)) ∨
        Nonempty ((J ⧸ Subgroup.center J) ≃* ↥(CFSG.Theory.Comparator.SzModel 1))

@[expose] def QuasisimpleQuaternionCore (J : Type) [Group J] [Finite J] : Prop :=
  Group.IsPerfect J → IsSimpleGroup (J ⧸ Subgroup.center J) →
    Nat.card (Subgroup.center J) = 2 → 2 ≤ twoRank J →
    ∀ (Q : Sylow 2 J) (B : Subgroup J), (Q : Subgroup J) ≤ B → B ≠ ⊤ →
      properTwoGenCoreGamma (Q : Subgroup J) 2 ≤ B →
      (∃ j : J, j ∉ B ∧ ∃ P : Subgroup J, IsPGroup 2 P ∧ ¬ IsCyclic P ∧
        ∀ p ∈ P, p ∈ B ∧ j⁻¹ * p * j ∈ B) →
      Nonempty ((J ⧸ Subgroup.center J) ≃* alternatingGroup (Fin 9)) ∨
        Nonempty ((J ⧸ Subgroup.center J) ≃* ↥(CFSG.Theory.Comparator.SzModel 1))

@[expose] def QuasisimpleQuaternionCoreClassification : Prop :=
  ∀ (J : Type) [Group J] [Finite J], QuasisimpleQuaternionCore J

variable {G : Type} [Group G] [Finite G] {H : Subgroup G} {z : G}

omit [Finite G] in
theorem card_center_eq_two_of_not_isCyclic {K : Type*} [Group K] [Finite K] (hK : IsPGroup 2 K)
    (hrank : twoRank K ≤ 1) (hcyc : ¬ IsCyclic K) : Nat.card (Subgroup.center K) = 2 := by
  refine CFSG.TwoRankLowerBound.Helpers.center_card_eq_two_of_nonabelian_rank_one_two_group K hK
    hrank ?_
  by_contra hab
  push Not at hab
  let : CommGroup K := { (inferInstance : Group K) with mul_comm := hab }
  exact hcyc (CFSG.TwoRankLowerBound.Helpers.abelian_rank_one_two_group_isCyclic K hK hrank)

theorem card_center_eq_two_of_not_twoPointCyclic (hq : EscapingQuotientData H z)
    {J : Subgroup (EscapingQuotient z)} (hJ : CFSG.IsComponent J) (hzJ : escapingBar z ∈ J)
    (hnc : ¬ TwoPointCyclic H z J) : Nat.card (Subgroup.center J) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold TwoPointCyclic at hnc
  push Not at hnc
  obtain ⟨j, hjJ, hjH, P, hP, hPB, hPc⟩ := hnc
  set Zc : Subgroup (EscapingQuotient z) := (Subgroup.center J).map J.subtype with hZc
  have hZ2 : IsPGroup 2 Zc := (component_center_le_twoCore hq.oddCore_eq_bot hJ).1.map _
  have hZcomm : ∀ c ∈ Zc, ∀ x ∈ J, c * x = x * c := by
    rintro _ ⟨c, hc, rfl⟩ x hx
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨x, hx⟩).symm
  have hZN : Zc ≤ Subgroup.normalizer (P : Set (EscapingQuotient z)) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro p
    constructor
    · intro hp
      rw [hZcomm c hc p (hPB p hp).1, mul_inv_cancel_right]
      exact hp
    · intro hp
      have hcJ : c ∈ J := by
        obtain ⟨c', -, rfl⟩ := hc
        exact c'.2
      have hpJ : p ∈ J := by
        have h1 : c * p * c⁻¹ ∈ J := (hPB _ hp).1
        have h2 : p = c⁻¹ * (c * p * c⁻¹) * c := by group
        rw [h2]
        exact J.mul_mem (J.mul_mem (J.inv_mem hcJ) h1) hcJ
      rwa [hZcomm c hc p hpJ, mul_inv_cancel_right] at hp
  set K := P ⊔ Zc with hK
  have hK2 : IsPGroup 2 K := IsPGroup.to_sup_of_normal_left' hP hZ2 hZN
  have hjinv : j⁻¹ ∉ escapingImage H z := fun h => hjH (by simpa using (escapingImage H z).inv_mem h)
  set L : Subgroup (EscapingQuotient z) := escapingImage H z ⊓
    (escapingImage H z).map (MulAut.conj j).toMonoidHom with hL
  have hmemL : ∀ y, y ∈ escapingImage H z → j⁻¹ * y * j ∈ escapingImage H z → y ∈ L := by
    intro y hy hyj
    refine ⟨hy, ⟨j⁻¹ * y * j, hyj, ?_⟩⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  obtain ⟨U, hUH, -⟩ := hq.sylow
  obtain ⟨Q, hQ⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal U hJ.2
  have hZcH : Zc ≤ escapingImage H z := by
    rintro _ ⟨c, hc, rfl⟩
    have hcQ : c ∈ (Q : Subgroup J) :=
      IsPGroup.le_sylow_of_normal (component_center_le_twoCore hq.oddCore_eq_bot hJ).1 Q hc
    have h := Subgroup.mem_map_of_mem J.subtype hcQ
    rw [hQ] at h
    exact hUH h.1
  have hKL : K ≤ L := by
    refine sup_le (fun p hp => hmemL p (hPB p hp).2.1 (hPB p hp).2.2) fun c hc => ?_
    refine hmemL c (hZcH hc) ?_
    rw [show j⁻¹ * c * j = c by rw [mul_assoc, hZcomm c hc j hjJ]; group]
    exact hZcH hc
  have hunique : ∀ y ∈ K, orderOf y = 2 → y = escapingBar z := by
    intro y hy hy2
    obtain ⟨hyH, ⟨w, hwH, hw⟩⟩ := hKL hy
    refine hq.eq_bar_of_conj_mem hjinv hyH ?_ hy2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hw
    rw [← hw, show j⁻¹ * (j * w * j⁻¹) * j⁻¹⁻¹ = w by group]
    exact hwH
  have hrank : twoRank K ≤ 1 := by
    rw [twoRank, CFSG.RankThreeEvenClassification.Helpers.pRank_top_subgroup 2 Nat.prime_two]
    exact pRank_two_le_one_of_forall_involution_eq hq.bar_order hunique
  have hKc : ¬ IsCyclic K := by
    intro hcyc
    apply hPc
    have : IsCyclic (P.subgroupOf K) := inferInstance
    exact isCyclic_of_surjective
      (Subgroup.subgroupOfEquivOfLe (show P ≤ K from le_sup_left)).toMonoidHom
      (MulEquiv.surjective _)
  have hcenter := card_center_eq_two_of_not_isCyclic hK2 hrank hKc
  have hZK : Zc.subgroupOf K ≤ Subgroup.center K := by
    intro c hc
    rw [Subgroup.mem_subgroupOf] at hc
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have hkK : (k : EscapingQuotient z) ∈ P ⊔ Zc := k.2
    have hsup : P ⊔ Zc ≤ Subgroup.centralizer ({(c : EscapingQuotient z)} : Set _) := by
      refine sup_le (fun p hp => ?_) (fun d hd => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hZcomm _ hc p (hPB p hp).1).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        obtain ⟨d', -, rfl⟩ := hd
        exact (hZcomm _ hc _ d'.2).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hsup hkK)
  have hle : Nat.card (Subgroup.center J) ≤ 2 := by
    calc Nat.card (Subgroup.center J) = Nat.card Zc :=
          (Subgroup.card_map_of_injective J.subtype_injective).symm
      _ = Nat.card (Zc.subgroupOf K) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv).symm
      _ ≤ Nat.card (Subgroup.center K) := Subgroup.card_le_of_le hZK
      _ = 2 := hcenter
  have hbar : (⟨escapingBar z, hzJ⟩ : J) ∈ Subgroup.center J :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (Subgroup.mem_center_iff.mp hq.bar_mem_center g)
  have hne : (⟨escapingBar z, hzJ⟩ : J) ≠ 1 := fun h1 => by
    have h2 := hq.bar_order
    rw [show escapingBar z = 1 from congrArg Subtype.val h1, orderOf_one] at h2
    exact absurd h2 (by decide)
  have hge : 2 ≤ Nat.card (Subgroup.center J) := by
    have h1 : 1 < Nat.card (Subgroup.center J) :=
      Subgroup.one_lt_card_iff_ne_bot _ |>.mpr fun hbot => hne (by
        have := hbar
        rw [hbot, Subgroup.mem_bot] at this
        exact this)
    omega
  omega

theorem false_of_quaternionCore
    {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G}
    {z : G} (hsq : SquareCaseSetting G S H z) {J : Subgroup (EscapingQuotient z)}
    (hJ : CFSG.IsComponent J) (hJH : ¬ J ≤ escapingImage H z)
    (hrank : ∃ x ∈ J, orderOf x = 2 ∧ x ≠ escapingBar z)
    (hK : (∀ k ∈ escapingSylowImage S z, k ∈ Subgroup.centralizer (J : Set (EscapingQuotient z)) →
        k = 1 ∨ k = escapingBar z) ∨
      (∃ c ∈ Subgroup.center J, (c : EscapingQuotient z) ≠ 1 ∧
        (c : EscapingQuotient z) ≠ escapingBar z))
    (hnc : ¬ TwoPointCyclic H z J) (hL : QuasisimpleQuaternionCore J)
    (hG : TwoANine.NoTwoANineQuaternionComponent) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : EscapingQuotientData H z :=
    escapingQuotientData hsq.core (hsq.core.sylow_le hsq.central.1) hsq.central.2.1 hsq.escape
  have hzJ : escapingBar z ∈ J := hsq.caseTwo J hJ
  have hZ := card_center_eq_two_of_not_twoPointCyclic hq hJ hzJ hnc
  have hrk : 2 ≤ twoRank J := by
    obtain ⟨x, hxJ, hx2, hxz⟩ := hrank
    have h2 : 2 ≤ CFSG.Open.pRank 2 J :=
      two_le_pRank_of_commuting_involutions hxJ hzJ hx2 hq.bar_order hxz (hq.commute_bar x)
    rwa [twoRank, CFSG.RankThreeEvenClassification.Helpers.pRank_top_subgroup 2 Nat.prime_two]
  obtain ⟨U, hUH, -⟩ := hq.sylow
  obtain ⟨Q, hQ⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal U hJ.2
  have hQH : (Q : Subgroup J).map J.subtype ≤ escapingImage H z := by
    rw [hQ]
    exact inf_le_left.trans hUH
  have hQB : (Q : Subgroup J) ≤ (escapingImage H z).subgroupOf J := fun q hq' =>
    Subgroup.mem_subgroupOf.mpr (hQH (Subgroup.mem_map_of_mem _ hq'))
  have hB : (escapingImage H z).subgroupOf J ≠ ⊤ := fun h => hJH fun x hx => by
    have hx' : (⟨x, hx⟩ : J) ∈ (escapingImage H z).subgroupOf J := h ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hx'
  have hΓ : properTwoGenCoreGamma (Q : Subgroup J) 2 ≤ (escapingImage H z).subgroupOf J := by
    refine iSup_le fun X => iSup_le fun hXQ => iSup_le fun hX => ?_
    intro n hn
    have hXH : X.map J.subtype ≤ escapingImage H z :=
      (Subgroup.map_mono hXQ).trans hQH
    have hXr : 2 ≤ CFSG.Open.pRank 2 (X.map J.subtype) := by
      rwa [CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective 2 Nat.prime_two J.subtype
        J.subtype_injective]
    have hnN : (n : EscapingQuotient z) ∈
        Subgroup.normalizer ((X.map J.subtype : Subgroup _) : Set (EscapingQuotient z)) :=
      Subgroup.le_normalizer_map J.subtype (Subgroup.mem_map_of_mem _ hn)
    exact Subgroup.mem_subgroupOf.mpr (hq.normalizer_le _ hXH hXr hnN)
  have hnc' : ∃ j : J, j ∉ (escapingImage H z).subgroupOf J ∧ ∃ P : Subgroup J, IsPGroup 2 P ∧
      ¬ IsCyclic P ∧ ∀ p ∈ P, p ∈ (escapingImage H z).subgroupOf J ∧
        j⁻¹ * p * j ∈ (escapingImage H z).subgroupOf J := by
    unfold TwoPointCyclic at hnc
    push Not at hnc
    obtain ⟨j, hjJ, hjH, P, hP, hPB, hPc⟩ := hnc
    have hPJ : P ≤ J := fun p hp => (hPB p hp).1
    refine ⟨⟨j, hjJ⟩, fun h => hjH (Subgroup.mem_subgroupOf.mp h), P.subgroupOf J,
      ?_, fun hcyc => hPc ?_, fun p hp => ⟨Subgroup.mem_subgroupOf.mpr
        (hPB _ (Subgroup.mem_subgroupOf.mp hp)).2.1,
        Subgroup.mem_subgroupOf.mpr (hPB _ (Subgroup.mem_subgroupOf.mp hp)).2.2⟩⟩
    · exact hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPJ).symm
    · exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hPJ).toMonoidHom
        (MulEquiv.surjective _)
  rcases hL hJ.1.1 hJ.1.2.1 hZ hrk Q _ hQB hB hΓ hnc' with e | e
  · exact hG G S H z hsq J hJ hJH hK hZ e
  · exact squareCaseSzEightExcluded G S H z hsq J hJ hJH hrank hK e

end CFSG.ProperTwoGeneratedCore.Lemma37
