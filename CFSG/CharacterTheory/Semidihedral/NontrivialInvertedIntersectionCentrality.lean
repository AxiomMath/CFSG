module

public import CFSG.CharacterTheory.Semidihedral.LocalInvertedLiftContainment

public noncomputable section

namespace CFSG.Semidihedral.NontrivialInvertedIntersectionCentrality

open scoped Pointwise commutatorElement
open CFSG.Open CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.OrderedPairLocalTransport
open CFSG.Semidihedral.LocalInvertedLiftContainment

universe u v
variable {G : Type u} [Group G]

theorem core_factorization_implies_quotient_centrality {B : Type v} [Group B] (i : B)
    (hfactor : CFSG.pPrimeCore 2 B ⊔ Subgroup.centralizer ({i} : Set B) = ⊤) :
    QuotientGroup.mk' (CFSG.pPrimeCore 2 B) i ∈
      Subgroup.center (B ⧸ CFSG.pPrimeCore 2 B) := by
  let q := QuotientGroup.mk' (CFSG.pPrimeCore 2 B)
  apply Subgroup.mem_center_iff.mpr
  intro z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 2 B) z
  obtain ⟨r, hr, c, hc, hrc⟩ := Subgroup.mem_sup_of_normal_left.mp
    (hfactor ▸ Subgroup.mem_top x)
  have hrq : q r = 1 := (QuotientGroup.eq_one_iff r).mpr hr
  have hci : c * i = i * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  change q x * q i = q i * q x
  rw [← hrc, map_mul, hrq, one_mul]
  simpa only [map_mul] using congrArg q hci

@[expose] def originalOddCorePullback (K A : Subgroup G) (hKA : K ≤ A) : Subgroup K :=
  (CFSG.pPrimeCore 2 A).comap (Subgroup.inclusion hKA)

theorem original_odd_core_pullback_facts [Finite G]
    (K A : Subgroup G) (hKA : K ≤ A) :
    let P := originalOddCorePullback K A hKA
    P.Normal ∧ Odd (Nat.card P) ∧ P ≤ CFSG.pPrimeCore 2 K ∧
      P.map K.subtype = K ⊓ (CFSG.pPrimeCore 2 A).map A.subtype := by
  intro P
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPnormal : P.Normal :=
    (inferInstance : (CFSG.pPrimeCore 2 A).Normal).comap (Subgroup.inclusion hKA)
  have hPodd : Odd (Nat.card P) := by
    have hRodd : Odd (Nat.card (CFSG.pPrimeCore 2 A)) :=
      Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := A))
    have hmap : P.map (Subgroup.inclusion hKA) ≤ CFSG.pPrimeCore 2 A :=
      Subgroup.map_comap_le _ _
    have hdiv := Subgroup.card_dvd_of_le hmap
    rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hKA)] at hdiv
    exact hRodd.of_dvd_nat hdiv
  have hPcore : P ≤ CFSG.pPrimeCore 2 K :=
    le_sSup ⟨hPnormal, Nat.coprime_two_left.mpr hPodd⟩
  refine ⟨hPnormal, hPodd, hPcore, ?_⟩
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    change Subgroup.inclusion hKA k ∈ CFSG.pPrimeCore 2 A at hk
    exact ⟨k.property, Subgroup.mem_map_of_mem A.subtype hk⟩
  · rintro ⟨hxK, a, ha, hax⟩
    refine ⟨⟨x, hxK⟩, ?_, rfl⟩
    change Subgroup.inclusion hKA (⟨x, hxK⟩ : K) ∈ CFSG.pPrimeCore 2 A
    have h : Subgroup.inclusion hKA (⟨x, hxK⟩ : K) = a := Subtype.ext hax.symm
    exact h ▸ ha

theorem original_subgroup_commutators_from_overgroup_centrality [Finite G]
    (K A : Subgroup G) (hKA : K ≤ A) (i : G) (hiK : i ∈ K)
    (hcentral : QuotientGroup.mk' (CFSG.pPrimeCore 2 A) (⟨i, hKA hiK⟩ : A) ∈
      Subgroup.center (A ⧸ CFSG.pPrimeCore 2 A)) :
    let P := originalOddCorePullback K A hKA
    ⁅K, Subgroup.zpowers i⁆ ≤ P.map K.subtype ∧
      ⁅K, Subgroup.zpowers i⁆ ≤ (CFSG.pPrimeCore 2 K).map K.subtype ∧
      (∀ k ∈ K, ∀ z ∈ Subgroup.zpowers i, ⁅k, z⁆ ∈ P.map K.subtype) ∧
      ∀ k ∈ K, ∀ z ∈ Subgroup.zpowers i,
        ⁅k, z⁆ ∈ (CFSG.pPrimeCore 2 K).map K.subtype := by
  intro P
  let q := QuotientGroup.mk' (CFSG.pPrimeCore 2 A)
  let phi := q.comp (Subgroup.inclusion hKA)
  let iK : K := ⟨i, hiK⟩
  have hcenter : (Subgroup.zpowers iK).map phi ≤
      Subgroup.center (A ⧸ CFSG.pPrimeCore 2 A) := by
    rw [MonoidHom.map_zpowers]
    exact Subgroup.zpowers_le.mpr hcentral
  have hbracket : ⁅(⊤ : Subgroup K), Subgroup.zpowers iK⁆ ≤ P := by
    apply Subgroup.commutator_le.mpr
    intro k _ z hz
    have hzcenter := hcenter (Subgroup.mem_map_of_mem phi hz)
    have hcomm : Commute (phi k) (phi z) := Subgroup.mem_center_iff.mp hzcenter (phi k)
    change Subgroup.inclusion hKA ⁅k, z⁆ ∈ CFSG.pPrimeCore 2 A
    apply (QuotientGroup.eq_one_iff (Subgroup.inclusion hKA ⁅k, z⁆)).mp
    change phi ⁅k, z⁆ = 1
    rw [map_commutatorElement]
    exact hcomm.commutator_eq
  have hambient : ⁅K, Subgroup.zpowers i⁆ ≤ P.map K.subtype := by
    have h := Subgroup.map_mono (f := K.subtype) hbracket
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype,
      MonoidHom.map_zpowers] at h
    exact h
  have hcore : ⁅K, Subgroup.zpowers i⁆ ≤ (CFSG.pPrimeCore 2 K).map K.subtype :=
    hambient.trans (Subgroup.map_mono (original_odd_core_pullback_facts K A hKA).2.2.1)
  exact ⟨hambient, hcore,
    fun k hk z hz => hambient (Subgroup.commutator_mem_commutator hk hz),
    fun k hk z hz => hcore (Subgroup.commutator_mem_commutator hk hz)⟩

@[expose] def OriginalNontrivialIntersectionCentralityFacts
    (i t : G) (U W : Subgroup G) : Prop :=
  let F := W ⊓ U
  let V := Subgroup.closure ({i, t} : Set G)
  let A := Subgroup.normalizer (F : Set G)
  let K := Subgroup.centralizer (W : Set G)
  let J := originalCentralizingResidual i
  let R := CFSG.pPrimeCore 2 A
  F ≤ U ∧ Odd (Nat.card F) ∧ (F.subgroupOf A).Normal ∧
    V ≤ Subgroup.normalizer (U : Set G) ∧ V ≤ A ∧
    J.map (C i).subtype ≤ Subgroup.centralizer (F : Set G) ∧
    K ≤ Subgroup.centralizer (F : Set G) ∧ K ≤ A ∧ U ≤ K ∧
    ∃ hiA : i ∈ A, ∃ hiK : i ∈ K, ∃ hKA : K ≤ A,
      let P := originalOddCorePullback K A hKA
      R ≠ ⊥ ∧ A < ⊤ ∧ Odd (Nat.card R) ∧ F ≤ R.map A.subtype ∧
      J ≤ A.subgroupOf (C i) ⊓ originalLayerPreimage i ∧
      (A.subgroupOf (C i) ⊓ originalLayerPreimage i).map (nu i) = originalSection i ∧
      R.map A.subtype ⊔ (A ⊓ C i) = A ∧
      R.map A.subtype ⊓ C i = (N i).map (C i).subtype ⊓ A ∧
      R ⊔ Subgroup.centralizer ({(⟨i, hiA⟩ : A)} : Set A) = ⊤ ∧
      QuotientGroup.mk' R (⟨i, hiA⟩ : A) ∈ Subgroup.center (A ⧸ R) ∧
      P.Normal ∧ Odd (Nat.card P) ∧ P ≤ CFSG.pPrimeCore 2 K ∧
      P.map K.subtype = K ⊓ R.map A.subtype ∧
      ⁅K, Subgroup.zpowers i⁆ ≤ P.map K.subtype ∧
      ⁅K, Subgroup.zpowers i⁆ ≤ (CFSG.pPrimeCore 2 K).map K.subtype ∧
      (∀ k ∈ K, ∀ z ∈ Subgroup.zpowers i, ⁅k, z⁆ ∈ P.map K.subtype) ∧
      (∀ k ∈ K, ∀ z ∈ Subgroup.zpowers i,
        ⁅k, z⁆ ∈ (CFSG.pPrimeCore 2 K).map K.subtype) ∧
      ∀ k : K, QuotientGroup.mk' R
        (Subgroup.inclusion hKA ⁅k, (⟨i, hiK⟩ : K)⁆) = 1

theorem original_all_prime_stationary_nontrivial_inverted_intersection_centrality
    [Finite G] [IsSimpleGroup G]
    (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (hrecognition : PerfectLayerNormalization.OriginalSmallerSimpleRecognition G)
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (i t : G) (hi : orderOf i = 2) (ht : orderOf t = 2) (htC : t ∈ C i) (hit : i ≠ t)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma i))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma i), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma i) : Set (Gamma i)) = ⊥)
    (hnc : ∀ Q : Sylow 2 (CFSG.generalizedFitting (Gamma i)), ¬ IsCyclic Q)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma i) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)))
    (hprimes : OriginalAllPrimeStationaryCover i t) :
    OriginalCentralizingLiftFacts i ∧
      ∃ U : Subgroup G, OriginalInvertedHallFacts i t U ∧
        OriginalLiftHallQuotientFacts i t htC U ∧
        ∀ (W : Subgroup G) (hWC : W ≤ C i), Odd (Nat.card W) →
          (∀ w ∈ W, t * w * t⁻¹ = w⁻¹) →
          W ≤ (originalLayerPreimage i).map (C i).subtype →
          Subgroup.closure ({i, t} : Set G) ≤ Subgroup.normalizer (W : Set G) →
          OriginalInvertedSubgroupConclusion i U W hWC ∧
            (W ⊓ U ≠ ⊥ → OriginalNontrivialIntersectionCentralityFacts i t U W) := by
  obtain ⟨hLift, U, hHall, hQuotient, hConfine⟩ :=
    original_all_prime_stationary_inverted_subgroups_lie_in_lift_join_hall
      hGnonab hrecognition n hn S0 f0 i t hi ht htC hit
      hnonab hcentral hnc p f hp hpodd hf hq hmodel hprimes
  have hU := hHall.2.2.2.2
  rcases hU with ⟨hUmem, hUset, hUcomm, hUN, hUab, hUchar, hUhall, hUn,
    hNgen, hdisj, hfixed, hcard, hsupport, hunique, hnorm, hbotN, hbotA, hbotU, hsemi⟩
  let J := originalCentralizingResidual i
  let Na := (N i).map (C i).subtype
  let Ui := U.subgroupOf (C i)
  have hUiN : Ui ≤ N i := by
    intro x hx
    exact (Subgroup.mem_map_iff_mem (f := (C i).subtype) Subtype.val_injective).mp (hUN hx)
  have hUC : U ≤ C i := hUN.trans (Subgroup.map_subtype_le _)
  have hUmap : Ui.map (C i).subtype = U := Subgroup.map_subgroupOf_eq_of_le hUC
  have hJU : ⁅J, Ui⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (Subgroup.commutator_mono le_rfl hUiN).trans
      (show ⁅J, N i⁆ = ⊥ from hLift.2.2.2.2.1).le
  have hJUambient : ⁅J.map (C i).subtype, U⁆ = ⊥ := by
    rw [← hUmap, ← Subgroup.map_commutator, hJU, Subgroup.map_bot]
  have hCU : C i ≤ Subgroup.normalizer (U : Set G) :=
    (StationaryOddLocalization.actual_centralizer_core_normalized i (C i) le_rfl).trans hnorm
  let V := Subgroup.closure ({i, t} : Set G)
  have hVC : V ≤ C i := by
    apply (Subgroup.closure_le (C i)).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · have hx := Set.mem_singleton_iff.mp hx
      subst x
      exact htC

  have hVU : V ≤ Subgroup.normalizer (U : Set G) := hVC.trans hCU
  refine ⟨hLift, U, hHall, hQuotient, ?_⟩
  intro W hWC hWodd hWinv hWY hVW
  have hWconclusion := hConfine W hWC hWodd hWinv hWY
  refine ⟨hWconclusion, ?_⟩
  intro hFbot
  let F := W ⊓ U
  let A := Subgroup.normalizer (F : Set G)
  let K := Subgroup.centralizer (W : Set G)
  have hVF : V ≤ A :=
    (le_inf hVW hVU).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hJF : J.map (C i).subtype ≤ Subgroup.centralizer (F : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJUambient).trans
      (Subgroup.centralizer_le (show (F : Set G) ⊆ U from inf_le_right))
  have hJA : J.map (C i).subtype ≤ A :=
    hJF.trans (Subgroup.centralizer_le_normalizer _)
  have hKF : K ≤ Subgroup.centralizer (F : Set G) :=
    Subgroup.centralizer_le (show (F : Set G) ⊆ W from inf_le_left)
  have hKA : K ≤ A := hKF.trans (Subgroup.centralizer_le_normalizer _)
  have hiK : i ∈ K := Subgroup.mem_centralizer_iff.mpr fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mp (hWC hw)
  have hFodd : Odd (Nat.card F) := hHall.1.of_dvd_nat
    (Subgroup.card_dvd_of_le (inf_le_right.trans hUN))
  have hFA : F ≤ A := F.le_normalizer
  have hFnormal : (F.subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFA).mpr le_rfl
  have hFAodd : Odd (Nat.card (F.subgroupOf A)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFA).toEquiv]
    exact hFodd
  have hFAcore : F.subgroupOf A ≤ CFSG.pPrimeCore 2 A :=
    le_sSup ⟨hFnormal, Nat.coprime_two_left.mpr hFAodd⟩
  have hFcore : F ≤ (CFSG.pPrimeCore 2 A).map A.subtype := by
    have h := Subgroup.map_mono (f := A.subtype) hFAcore
    rw [Subgroup.map_subgroupOf_eq_of_le hFA] at h
    exact h
  have hRbot : CFSG.pPrimeCore 2 A ≠ ⊥ := by
    intro hbot
    have h := hFcore
    rw [hbot, Subgroup.map_bot] at h
    exact hFbot (le_bot_iff.mp h)
  obtain ⟨hiA, _, hAproper, hRodd, hJcover, hcover⟩ :=
    PerfectLayerNormalization.original_layer_containing_subgroup_cover_inputs
      i t hi A hVF hRbot J hJA (show J.map (nu i) = originalSection i from hLift.2.2.2.1)
  obtain ⟨hfactor, hinter⟩ :=
    PerfectLayerNormalization.original_full_layer_cover_forces_core_centralizer_factorization
      hGnonab hrecognition n hn S0 f0 i t hi ht htC hit.symm
      hnonab hcentral hnc p f hp hpodd hf hq hmodel A hVF hRbot hcover
  have hintrinsic :=
    (PerfectLayerNormalization.original_core_centralizer_factorization_iff A i hiA).mpr hfactor
  have hcentralA := core_factorization_implies_quotient_centrality (⟨i, hiA⟩ : A) hintrinsic
  obtain ⟨hPnormal, hPodd, hPcore, hPmap⟩ := original_odd_core_pullback_facts K A hKA
  obtain ⟨hbracketP, hbracketCore, hmemP, hmemCore⟩ :=
    original_subgroup_commutators_from_overgroup_centrality K A hKA i hiK hcentralA
  refine ⟨inf_le_right, hFodd, hFnormal, hVU, hVF, hJF, hKF, hKA, hWconclusion.2.1,
    hiA, hiK, hKA, hRbot, hAproper, hRodd, hFcore, hJcover, hcover,
    hfactor, hinter, hintrinsic, hcentralA, hPnormal, hPodd, hPcore, hPmap,
    hbracketP, hbracketCore, hmemP, hmemCore, ?_⟩
  intro k
  have h := hmemP k k.property i (Subgroup.mem_zpowers i)
  have hmem : ⁅k, (⟨i, hiK⟩ : K)⁆ ∈ originalOddCorePullback K A hKA :=
    (Subgroup.mem_map_iff_mem (f := K.subtype) Subtype.val_injective).mp h
  exact (QuotientGroup.eq_one_iff _).mpr hmem

end CFSG.Semidihedral.NontrivialInvertedIntersectionCentrality
