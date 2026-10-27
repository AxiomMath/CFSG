module

public import CFSG.LocalAnalysis.RankThreeUC.ClauseC
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.RankThree.PartOne.S12.Sec15Final
import CFSG.LocalAnalysis.RankThreeTheoremC.WreathThompson
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.Helpers
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S10.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem quaternionGroup_two_eq_of_forall_mul_comm (q : QuaternionGroup 2)
    (h : ∀ g, g * q = q * g) : q = 1 ∨ q = QuaternionGroup.a 2 := by
  revert q
  decide

private theorem mem_of_forall_mul_comm_of_card_eq_two {A D : Subgroup G}
    (e : A ≃* QuaternionGroup 2) (hDA : D ≤ A) (hD : Nat.card D = 2)
    (hDc : ∀ d ∈ D, ∀ a ∈ A, a * d = d * a) {x : G} (hxA : x ∈ A)
    (hx : ∀ a ∈ A, a * x = x * a) : x ∈ D := by
  have hcentral : ∀ y : A, (∀ a ∈ A, a * (y : G) = (y : G) * a) →
      ∀ g : QuaternionGroup 2, g * e y = e y * g := by
    intro y hy g
    have h : e.symm g * y = y * e.symm g := Subtype.ext (hy (e.symm g : A) (e.symm g).2)
    simpa using congrArg e h
  have : Nontrivial D := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨d, hd1⟩ := exists_ne (1 : D)
  have hdA : (d : G) ∈ A := hDA d.2
  have hd := quaternionGroup_two_eq_of_forall_mul_comm _
    (hcentral ⟨d, hdA⟩ fun a ha => hDc d d.2 a ha)
  have hd' : e ⟨d, hdA⟩ ≠ 1 := by
    intro h
    apply hd1
    have h' : (⟨d, hdA⟩ : A) = 1 := e.injective (by rw [h, map_one])
    exact Subtype.ext (congrArg Subtype.val h' : (d : G) = 1)
  rcases quaternionGroup_two_eq_of_forall_mul_comm _ (hcentral ⟨x, hxA⟩ hx) with h | h
  · have h' : (⟨x, hxA⟩ : A) = 1 := e.injective (by rw [h, map_one])
    have hx1 : x = 1 := congrArg Subtype.val h'
    rw [hx1]
    exact D.one_mem
  · have h' : (⟨x, hxA⟩ : A) = ⟨d, hdA⟩ := e.injective (h.trans (hd.resolve_left hd').symm)
    have hxd : x = d := congrArg Subtype.val h'
    rw [hxd]
    exact d.2

private theorem isCyclic_of_le_of_isQ8CentralCyclic {H Z : Subgroup G} {m : ℕ}
    (hH : rankThreeIsQ8CentralCyclic H m) (hZH : Z ≤ H)
    (hZ : ∀ z ∈ Z, ∀ h ∈ H, h * z = z * h) : IsCyclic Z := by
  obtain ⟨A, B, ⟨e⟩, hB, -, hAB, rfl, hcard⟩ := hH
  have hAN : A ≤ normalizer (B : Set G) := fun a ha =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun b hb => (hAB a ha b hb).symm)
  have hZB : Z ≤ B := by
    intro z hz
    have hzAB : z ∈ (↑(A ⊔ B) : Set G) := hZH hz
    rw [coe_mul_of_left_le_normalizer_right A B hAN] at hzAB
    obtain ⟨a, ha, b, hb, rfl⟩ := hzAB
    have hab : a * b ∈ Z := hz
    have haD : a ∈ A ⊓ B := by
      refine mem_of_forall_mul_comm_of_card_eq_two e inf_le_left hcard
        (fun d hd a' ha' => hAB a' ha' d hd.2) ha fun a' ha' => ?_
      have h1 := hZ _ hab a' ((le_sup_left : A ≤ A ⊔ B) ha')
      have h2 := hAB a' ha' b hb
      refine mul_right_cancel (b := b) ?_
      calc a' * a * b = a' * (a * b) := mul_assoc _ _ _
        _ = a * b * a' := h1
        _ = a * (b * a') := mul_assoc _ _ _
        _ = a * (a' * b) := by rw [h2]
        _ = a * a' * b := (mul_assoc _ _ _).symm
    exact B.mul_mem haD.2 hb
  exact Subgroup.isCyclic_of_le hZB

private theorem le_rankThreePrimeCore_of_isPGroup_two {M Z : Subgroup G} (hZM : Z ≤ M)
    (hZ : M ≤ normalizer (Z : Set G)) (hZ2 : IsPGroup 2 Z) : Z ≤ rankThreePrimeCore 3 M := by
  refine le_sSup ⟨hZM, (normal_subgroupOf_iff_le_normalizer hZM).mpr hZ, ?_⟩
  obtain ⟨k, hk⟩ := hZ2.exists_card_eq
  rw [hk]
  exact Nat.Coprime.pow_right k (by norm_num)

omit [Finite G] in
private theorem rankThreePrimeCore_le (p : ℕ) (M : Subgroup G) : rankThreePrimeCore p M ≤ M :=
  sSup_le fun _ hN => hN.1

omit [Finite G] in
private theorem le_of_normalized_of_not_dvd_index {p : ℕ} [Fact p.Prime] {K Z Q : Subgroup G}
    (hZK : Z ≤ K) (hKZ : K ≤ normalizer (Z : Set G)) (hZ : IsPGroup p Z) (hQ : IsPGroup p Q)
    (hQK : ¬ p ∣ (Q.subgroupOf K).index) : Z ≤ Q := by
  have : (Z.comap K.subtype).Normal := (normal_subgroupOf_iff_le_normalizer hZK).mpr hKZ
  let S : Sylow p K := (hQ.comap_subtype (K := K)).toSylow hQK
  have h := (hZ.comap_subtype (K := K)).le_sylow_of_normal S
  intro z hz
  exact h (show (⟨z, hZK hz⟩ : K) ∈ Z.subgroupOf K from hz)

omit [Finite G] in
private theorem le_of_isPGroup_of_not_dvd_relIndex {p : ℕ} [Fact p.Prime] {M C Q : Subgroup G}
    (hCM : C ≤ M) (hMC : M ≤ normalizer (C : Set G)) (hQM : Q ≤ M) (hQ : IsPGroup p Q)
    (hC : ¬ p ∣ C.relIndex M) : Q ≤ C := by
  have : (C.subgroupOf M).Normal := (normal_subgroupOf_iff_le_normalizer hCM).mpr hMC
  intro q hq
  let x : M := ⟨q, hQM hq⟩
  have h1 : orderOf (QuotientGroup.mk' (C.subgroupOf M) x) ∣ orderOf x :=
    orderOf_map_dvd _ _
  have h2 : orderOf (QuotientGroup.mk' (C.subgroupOf M) x) ∣ C.relIndex M :=
    orderOf_dvd_natCard _
  have h3 : (orderOf x).Coprime (C.relIndex M) := by
    have h := hQ.orderOf_coprime ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hC) ⟨q, hq⟩
    rw [Subgroup.orderOf_mk q hq] at h
    rwa [show orderOf x = orderOf q from Subgroup.orderOf_mk q (hQM hq)]
  have h4 : orderOf (QuotientGroup.mk' (C.subgroupOf M) x) = 1 :=
    Nat.Coprime.eq_one_of_dvd (h3.coprime_dvd_left h1) h2
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp h4)

omit [Finite G] in
private theorem le_normalizer_inf_centralizer {M Z : Subgroup G}
    (hZ : M ≤ normalizer (Z : Set G)) :
    M ≤ normalizer ((M ⊓ centralizer (Z : Set G) : Subgroup G) : Set G) := by
  have key : ∀ m ∈ M, ∀ h : G, h ∈ M ⊓ centralizer (Z : Set G) →
      m * h * m⁻¹ ∈ M ⊓ centralizer (Z : Set G) := by
    intro m hm h ⟨hhM, hhc⟩
    refine ⟨M.mul_mem (M.mul_mem hm hhM) (M.inv_mem hm), mem_centralizer_iff.mpr fun z hz => ?_⟩
    have hz' : m⁻¹ * z * m ∈ Z := by
      have := (mem_normalizer_iff.mp (hZ (M.inv_mem hm)) z).mp hz
      simpa using this
    have hc := mem_centralizer_iff.mp hhc _ hz'
    calc z * (m * h * m⁻¹) = m * ((m⁻¹ * z * m) * h) * m⁻¹ := by group
      _ = m * (h * (m⁻¹ * z * m)) * m⁻¹ := by rw [hc]
      _ = m * h * m⁻¹ * z := by group
  intro m hm
  refine mem_normalizer_iff.mpr fun h => ⟨key m hm h, fun h' => ?_⟩
  simpa [mul_assoc] using key m⁻¹ (M.inv_mem hm) _ h'

theorem IsWitness.false_of_clauseC_of_normal_omegaOneCenter (hS : Standing G)
    (hUC : rankThreeUC G) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G}
    (hw : IsWitness 3 P M) (hc : rankThreeClauseC M (P : Subgroup G)) {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hZM : M ≤ normalizer ((CFSG.RankThree.PartOne.omegaOneCenterIn T : Subgroup G) : Set G))
    (hZ : ¬ IsCyclic (CFSG.RankThree.PartOne.omegaOneCenterIn T)) : False := by
  obtain ⟨hTM, hT2, hTodd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hT
  set Z := CFSG.RankThree.PartOne.omegaOneCenterIn T
  have hZT : Z ≤ T := CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_le T
  have hZ2 : IsPGroup 2 Z := hT2.to_le hZT
  have hTC : T ≤ M ⊓ centralizer (Z : Set G) := fun t ht =>
    ⟨hTM ht, mem_centralizer_iff.mpr fun z hz =>
      ((CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp hz).2.1 t ht).symm⟩
  have hodd2 : ¬ 2 ∣ (M ⊓ centralizer (Z : Set G)).relIndex M := fun h =>
    hTodd (h.trans (relIndex_dvd_of_le_left M hTC))
  have hodd : Odd ((M ⊓ centralizer (Z : Set G)).relIndex M) := Nat.odd_iff.mpr (by omega)
  refine hw.false_of_clauseC_of_odd_index hS hUC hp hc inf_le_left
    (le_normalizer_inf_centralizer hZM) hodd fun hPC => ?_
  obtain ⟨-, ⟨e⟩, -, hY⟩ := hc
  obtain ⟨y, hyP, hy3, hyJ⟩ := exists_orderOf_eq_three_not_mem_thompsonSubgroup e
  obtain ⟨Q, hQK, hQ2, hQodd, -, m, -, hQ8⟩ := hY (zpowers y) ((zpowers_le).mpr hyP)
    (by rw [Nat.card_zpowers, hy3]) fun h => hyJ (h (mem_zpowers y))
  have hKM := rankThreePrimeCore_le 3 M
  have hZK : Z ≤ rankThreePrimeCore 3 M :=
    le_rankThreePrimeCore_of_isPGroup_two (hZT.trans hTM) hZM hZ2
  have hZQ : Z ≤ Q := le_of_normalized_of_not_dvd_index hZK (hKM.trans hZM) hZ2 hQ2 hQodd
  have hQC : Q ≤ M ⊓ centralizer (Z : Set G) :=
    le_of_isPGroup_of_not_dvd_relIndex inf_le_left (le_normalizer_inf_centralizer hZM)
      (hQK.trans hKM) hQ2 hodd2
  have hyc : ∀ z ∈ Z, Commute y z := fun z hz =>
    (mem_centralizer_iff.mp (hPC hyP).2 z hz).symm
  have hZy : Z ≤ centralizer (zpowers y : Set G) := by
    intro z hz
    rw [mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    exact ((hyc z hz).zpow_left k).eq
  exact hZ (isCyclic_of_le_of_isQ8CentralCyclic hQ8 (le_inf hZQ hZy) fun z hz h hh =>
    (mem_centralizer_iff.mp (hQC hh.1).2 z hz).symm)

end CFSG.LocalAnalysis.RankThreeUC
