module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SolvableLinearCosetNormalizerCore
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SolvableLinearCosetNormalizerSylowQuotient

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
open CFSG.ProperTwoGeneratedCore.CosetNormalizer CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger
open scoped IsMulCommutative Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]

theorem solvable_linear_coset_normalizer_produces_cyclic_sylow_quotient
    (hgen : RankOnePair.PairCommutatorGenerationTheorem G)
    (hPK : LinearSuzukiPointKernelRootProduct G) (hOC : LinearSuzukiHullOddCoreTrivial G)
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hrank : twoRank (pairPointStabilizer H beta) = 1)
    {u : G} (huD : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2)
    (huz : Commute u z) (hut : Commute u t)
    (hdeg : Nat.card (elementFixedSet H u) =
      Nat.card ({1} ∪ distinguishedRoots H z u : Set G) + 1)
    (hn : Nat.card (pointRightCosetSpace H) =
      Nat.card ({1} ∪ distinguishedRoots H z u : Set G) ^ 2 + 1)
    (hsolv : Group.IsSolvable (cosetNormalizerPerm (rootCoset H z u)).range) :
    let M := Subgroup.centralizer ({u} : Set G)
    let D := pairPointStabilizer H beta
    let q := Nat.card ({1} ∪ distinguishedRoots H z u : Set G)
    let Δ := rootCoset H z u
    let N := Subgroup.normalizer Δ
    let A := N ⊓ D
    (∃ f : ℕ, 2 ≤ f ∧ q = 2 ^ f) ∧ ¬ IsConj u z ∧
    ∃ (U : Subgroup G) (_ : IsElementaryAbelian 2 U),
      (U : Set G) = {1} ∪ distinguishedRoots H z u ∧ (∀ x ∈ U, x ≠ 1 → IsConj z x) ∧
      ∃ j : Additive U ≃ Δ, (∀ v : U, (j (Additive.ofMul v) : G) = u * v) ∧
        (∀ g ∈ translationGroup (Additive U),
          j.permCongr g.toEquiv ∈ (cosetNormalizerPerm Δ).range) ∧
        let Q := N ⊓ Subgroup.centralizer (U : Set G)
        (∀ n : N, (∃ g ∈ translationGroup (Additive U),
            cosetNormalizerPerm Δ n = j.permCongr g.toEquiv) ↔ (n : G) ∈ Q) ∧
        (Q.subgroupOf N).Normal ∧ IsPGroup 2 Q ∧ Nat.card Q = 2 * q ^ 2 ∧
        U ≤ Q ∧ U.subgroupOf Q ≤ Subgroup.center Q ∧
        A = D ⊓ M ∧ (N : Set G) = (Q : Set G) * (A : Set G) ∧ Q ⊓ A = Subgroup.zpowers u ∧
        ∃ _ : (U.subgroupOf Q).Normal, IsElementaryAbelian 2 (Q ⧸ U.subgroupOf Q) ∧
          let W : Subgroup (Q ⧸ U.subgroupOf Q) :=
            Subgroup.closure {w : Q ⧸ U.subgroupOf Q | ∃ a ∈ A, ∃ x y : Q, (y : G) = a * x * a⁻¹ ∧
              w = (QuotientGroup.mk y : Q ⧸ U.subgroupOf Q) *
                (QuotientGroup.mk x : Q ⧸ U.subgroupOf Q)⁻¹}
          IsCompl (((Subgroup.zpowers u).subgroupOf Q).map
            (QuotientGroup.mk' (U.subgroupOf Q))) W ∧
          let V := (W.comap (QuotientGroup.mk' (U.subgroupOf Q))).map Q.subtype
          (V.subgroupOf N).Normal ∧ Nat.card V = q ^ (2 : ℕ) ∧ U ≤ V ∧
          U.subgroupOf V ≤ Subgroup.center V ∧ u ∉ V ∧
          (∀ x ∈ V, x ∉ U → ∀ y ∈ V, y ∉ U → ∃ a ∈ A, y⁻¹ * (a * x * a⁻¹) ∈ U) ∧
          (∀ P : Sylow 2 A,
            IsCyclic ((P : Subgroup A).map A.subtype) ∧ u ∈ (P : Subgroup A).map A.subtype ∧
            ∃ S : Sylow 2 G,
              (S : Set G) = (Q : Set G) * ((P : Subgroup A).map A.subtype : Set G) ∧
              (S : Set G) = (V : Set G) * ((P : Subgroup A).map A.subtype : Set G) ∧
              V ⊓ (P : Subgroup A).map A.subtype = ⊥ ∧
              ∃ _ : (V.subgroupOf (S : Subgroup G)).Normal,
                Nonempty (↥(S : Subgroup G) ⧸ V.subgroupOf (S : Subgroup G) ≃*
                  (P : Subgroup A).map A.subtype)) ∧
          (∃ x ∈ V, IsConj u x) ∧ (∀ x ∈ V, IsConj u x → ∀ y ∈ U, IsConj u (x * y)) ∧
          ∀ x y : G, IsConj u x → IsConj u y → x ≠ y → Commute x y → IsConj z (x * y) := by
  intro M D q Δ N A
  classical
  obtain ⟨⟨hsimple, hnonab⟩, hnconj, f, hf, hqf, U, hUel, hUset, hUz, j, hj, htr, hQchar,
      hcore⟩ :=
    solvable_linear_coset_normalizer_core hgen hPK hOC h hbeta ht hrank huD hu huz hut hdeg hn
      hsolv
  obtain ⟨hUQ, huQ, hQcard, hsq, hQcomm, hNQ, hAeq, hNQA, hQA, hVQ, hNV, huV, hVcard, htrans,
      hQeqV, hNcard, hlift, hLn, ⟨e, he, hFe, ⟨eL⟩⟩, hKu, hLA, hsat, hprod⟩ := hcore
  have hu2 : u * u = 1 := mul_self_eq_one_of_orderOf_eq_two hu
  have hLM : localInvolutionPointHull z u ≤ M := localInvolutionPointHull_le_centralizer z u
  refine ⟨⟨f, hf, hqf⟩, hnconj, U, hUel, hUset, hUz, j, hj, htr, ?_⟩
  intro Q
  have hQN : Q ≤ N := inf_le_left
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := fun a ha => hNQ ha.1
  have hAeq' : A = D ⊓ M := hAeq
  have hAM : A ≤ M := by
    rw [hAeq']
    exact inf_le_right
  have hcommQ : ⁅A, Q⁆ ≤ Q := by
    rw [Subgroup.commutator_le]
    intro a ha x hx
    rw [commutatorElement_def]
    exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAQ ha) x).mp hx) (Q.inv_mem hx)
  have hcenter : ∀ K : Subgroup G, U ≤ K → K ≤ Q → U.subgroupOf K ≤ Subgroup.center K := by
    intro K _ hKQ x hx
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hKQ g.2).2 x
      (Subgroup.mem_subgroupOf.mp hx)).symm
  have hUQn : (U.subgroupOf Q).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hc : (g : G) * x = x * g := (Subgroup.mem_centralizer_iff.mp g.2.2 x hx).symm
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hc, mul_inv_cancel_right]
    exact hx⟩
  have hVcard' : Nat.card (U ⊔ ⁅A, Q⁆ : Subgroup G) = 2 ^ (2 * f) := by
    rw [hVcard, hqf, ← pow_mul, mul_comm]
  have hSyl := fun P : Sylow 2 A =>
    cyclic_sylow_quotient_of_translation_complement hNcard hlift hQN inf_le_left hVQ hVcard' hNV
      hNQ huV hQA hu hQeqV hLM hLn he hFe eL hKu hAM hAM inf_le_right hrank.le hLA P
  have hconjV : ∃ x ∈ U ⊔ ⁅A, Q⁆, IsConj u x := by
    obtain ⟨P⟩ : Nonempty (Sylow 2 A) := inferInstance
    obtain ⟨hcycP, huP, S, -, hSV, -, hVn, ⟨eSV⟩⟩ := hSyl P
    have : IsCyclic (↥(S : Subgroup G) ⧸ (U ⊔ ⁅A, Q⁆).subgroupOf (S : Subgroup G)) :=
      (MulEquiv.isCyclic eSV).mpr hcycP
    have huS : u ∈ (S : Subgroup G) := by
      have h1 : u ∈ (S : Set G) := by
        rw [hSV]
        exact Set.mem_mul.mpr ⟨1, Subgroup.one_mem _, u, huP, one_mul u⟩
      exact h1
    obtain ⟨g, hg⟩ := exists_conj_mem_of_isCyclic_sylow_quotient hsimple hnonab S huS huV hu
    exact ⟨g⁻¹ * u * g, hg, isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]⟩⟩
  refine ⟨fun n => (hQchar n).trans ⟨fun h' => ⟨n.2, h'⟩, fun h' => h'.2⟩,
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQN).mpr hNQ,
    IsPGroup.of_card (n := 2 * f + 1) (hQcard.trans (by rw [hqf]; ring)), hQcard, hUQ,
    hcenter Q hUQ le_rfl, hAeq, ?_, hQA, hUQn, isElementaryAbelian_quotient hsq hQcomm, ?_⟩
  · calc (N : Set G) = ((Q ⊔ A : Subgroup G) : Set G) := congrArg _ hNQA
      _ = (Q : Set G) * (A : Set G) := Subgroup.coe_mul_of_right_le_normalizer_left Q A hAQ
  intro W
  have hW : W = ((U ⊔ ⁅A, Q⁆).subgroupOf Q).map (QuotientGroup.mk' (U.subgroupOf Q)) := by
    rw [map_mk'_sup_eq hUQ hcommQ]
    exact closure_commutators_quotient_eq hAQ
  rw [hW]
  refine ⟨isCompl_quotient_of_sup_eq le_sup_left hVQ hu2 huQ huV hQeqV, ?_⟩
  intro V
  have hV : V = U ⊔ ⁅A, Q⁆ := map_comap_map_mk'_eq le_sup_left hVQ
  rw [hV]
  exact ⟨(Subgroup.normal_subgroupOf_iff_le_normalizer (hVQ.trans hQN)).mpr hNV, hVcard,
    le_sup_left, hcenter _ le_sup_left hVQ, huV, htrans, hSyl, hconjV,
    fun x hx => hsat x (hVQ hx), hprod⟩

theorem solvableLinearCosetNormalizerTheorem_of_parts
    (hgen : RankOnePair.PairCommutatorGenerationTheorem G)
    (hPK : LinearSuzukiPointKernelRootProduct G) (hOC : LinearSuzukiHullOddCoreTrivial G) :
    SolvableLinearCosetNormalizerTheorem G := by
  intro H z h beta hbeta t ht hrank w hwB hw hwz hwt hdeg hn hsolv
  obtain ⟨⟨f, hf, hqf⟩, hnconj, U, hUel, hUset, hUz, j, -, -, hrest⟩ :=
    solvable_linear_coset_normalizer_produces_cyclic_sylow_quotient hgen hPK hOC h hbeta ht
      hrank hwB hw hwz hwt hdeg hn hsolv
  dsimp only at hrest
  obtain ⟨-, -, -, -, -, -, -, -, -, hUQn, -, -, hVn, hVcard, hUV, -, -, htrans, -, hconj, hsat,
    hprod⟩ := hrest
  have hsqU : ∀ x ∈ U, x * x = 1 := fun x hx => by
    have h1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) x hx
    rwa [pow_two] at h1
  have hqU : Nat.card U = Nat.card ({1} ∪ distinguishedRoots H z w : Set G) := by
    change Nat.card (U : Set G) = _
    rw [hUset]
  have hrel : ∀ K : Subgroup G, U ≤ K →
      Nat.card K = Nat.card ({1} ∪ distinguishedRoots H z w : Set G) ^ (2 : ℕ) →
        4 ≤ U.relIndex K := by
    intro K hUK hK
    have h1 := Subgroup.relIndex_mul_card (H := U) (K := K)
    rw [inf_eq_left.mpr hUK, hK, hqU] at h1
    have hq4 : 4 ≤ Nat.card ({1} ∪ distinguishedRoots H z w : Set G) := by
      rw [hqf]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    nlinarith
  refine ⟨hnconj, _, U, Subgroup.normalizer (rootCoset H z w) ⊓ pairPointStabilizer H beta,
    hUset, hsqU, hrel _ hUV hVcard, hUz, ?_, htrans, hsat, hprod, hconj⟩
  exact inf_le_left.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
    ((Subgroup.map_subtype_le _).trans inf_le_left)).mp hVn)

end CFSG.ProperTwoGeneratedCore.HighRankPair
