module

public import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedTransport
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerCommonActionKernel
public import CFSG.GroupTheory.Fitting.GeneralizedFittingComponents
public import CFSG.GroupTheory.Fitting.PPrimeCoreGeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleFull
public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigSpA
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34UniqComp
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma413Tools
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.ComponentClassification.FooteMarked

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
open scoped commutatorElement Pointwise

variable {W : Type*} [Group W] [Finite W]

omit [Finite W] in
theorem centralizer_le_coreActionKernel (D : Subgroup W) :
    Subgroup.centralizer (D : Set W) ≤ UnbalancedLayer.coreActionKernel D := by
  intro g hg
  refine UnbalancedLayer.mem_coreActionKernel.mpr
    ⟨(Subgroup.centralizer_le_normalizer (D : Set W)) hg, fun d hd => ?_⟩
  have hcomm : d * g = g * d := (Subgroup.mem_centralizer_iff.mp hg) d hd
  have h1 : d⁻¹ * g⁻¹ * d * g = 1 := by
    calc d⁻¹ * g⁻¹ * d * g = (g * d)⁻¹ * (d * g) := by group
      _ = (d * g)⁻¹ * (d * g) := by rw [hcomm]
      _ = 1 := inv_mul_cancel _
  rw [h1]
  exact Subgroup.one_mem _

theorem coreActionKernel_eq_centralizer_of_pPrimeCore_eq_bot {D : Subgroup W}
    (hO : pPrimeCore 2 W = ⊥) (hD : D.Normal) :
    UnbalancedLayer.coreActionKernel D = Subgroup.centralizer (D : Set W) := by
  have hOD : (pPrimeCore 2 ↥D).map D.subtype = ⊥ := by
    rw [CFSG.ABGLocalTools.pPrimeCore_map_subtype_eq_inf (p := 2) hD, hO, inf_bot_eq]
  refine le_antisymm ?_ (centralizer_le_coreActionKernel D)
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have h1 : d⁻¹ * g⁻¹ * d * g ∈ (pPrimeCore 2 ↥D).map D.subtype :=
    (UnbalancedLayer.mem_coreActionKernel.mp hg).2 d hd
  rw [hOD, Subgroup.mem_bot] at h1
  have h2 : g⁻¹ * d * g = d := by
    calc g⁻¹ * d * g = d * (d⁻¹ * g⁻¹ * d * g) := by group
      _ = d * 1 := by rw [h1]
      _ = d := by simp
  calc d * g = g * (g⁻¹ * d * g) := by group
    _ = g * d := by rw [h2]

theorem coreActionKernel_subgroupOf {G : Type*} [Group G] {L H : Subgroup G} (hL : L ≤ H) :
    UnbalancedLayer.coreActionKernel (L.subgroupOf H) =
      (UnbalancedLayer.coreActionKernel L).subgroupOf H := by
  have hO : ∀ y : ↥H, y ∈ (pPrimeCore 2 ↥(L.subgroupOf H)).map (L.subgroupOf H).subtype ↔
      (y : G) ∈ (pPrimeCore 2 ↥L).map L.subtype := by
    intro y
    rw [← CFSG.pPrimeCore_map_subgroupOf 2 L H hL]
    exact (Subgroup.mem_map_iff_mem H.subtype_injective).symm
  ext x
  rw [Subgroup.mem_subgroupOf, UnbalancedLayer.mem_coreActionKernel,
    UnbalancedLayer.mem_coreActionKernel]
  have hN : x ∈ Subgroup.normalizer ((L.subgroupOf H : Subgroup ↥H) : Set ↥H) ↔
      (x : G) ∈ Subgroup.normalizer (L : Set G) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hL, Subgroup.mem_subgroupOf]
  rw [hN]
  constructor
  · rintro ⟨hP, h2⟩
    refine ⟨hP, fun j hj => ?_⟩
    have h1 : ((⟨j, hL hj⟩ : ↥H)⁻¹ * x⁻¹ * ⟨j, hL hj⟩ * x) ∈
        (pPrimeCore 2 ↥(L.subgroupOf H)).map (L.subgroupOf H).subtype :=
      h2 ⟨j, hL hj⟩ hj
    exact (hO (⟨j, hL hj⟩⁻¹ * x⁻¹ * ⟨j, hL hj⟩ * x)).mp (by simpa using h1)
  · rintro ⟨hP, h2⟩
    refine ⟨hP, fun j hj => ?_⟩
    have h1 : (j : G)⁻¹ * (x : G)⁻¹ * (j : G) * (x : G) ∈
        (pPrimeCore 2 ↥L).map L.subtype :=
      h2 (j : G) (Subgroup.mem_subgroupOf.mp hj)
    exact (hO (j⁻¹ * x⁻¹ * j * x)).mpr (by simpa using h1)

theorem even_card_coreActionKernel_inf_generalizedFitting {D A B B0 : Subgroup W}
    (hO : pPrimeCore 2 W = ⊥) (hD : D.Normal)
    (hA : IsComponent A) (hB : IsComponent B) (hne : A ≠ B)
    (hZA : Subgroup.center A = ⊥) (hZB : Subgroup.center B = ⊥)
    (hDAB : D = A ⊔ B) (hB0nt : Nontrivial ↥B0)
    (hB0Q : B0 ≤ UnbalancedLayer.coreActionKernel D) :
    Even (Nat.card ↥(UnbalancedLayer.coreActionKernel D ⊓ generalizedFitting W)) := by
  classical
  have : D.Normal := hD
  let X : Subgroup W := Subgroup.centralizer ((A ⊔ B : Subgroup W) : Set W)
  have hQX : UnbalancedLayer.coreActionKernel D = X := by
    rw [coreActionKernel_eq_centralizer_of_pPrimeCore_eq_bot hO hD]
    rw [hDAB]
  have hABnormal : (A ⊔ B).Normal := by
    simpa [hDAB] using hD
  have hXnormal : X.Normal := by
    dsimp [X]
    have : (A ⊔ B).Normal := hABnormal
    exact Subgroup.normal_centralizer
  have hntX : Nontrivial ↥X := by
    have hB0X : B0 ≤ X := hB0Q.trans (le_of_eq hQX)
    exact (Subgroup.inclusion_injective hB0X).nontrivial
  have hOX : pPrimeCore 2 X = ⊥ := by
    let K : Subgroup ↥X := pPrimeCore 2 ↥X
    have : X.Normal := hXnormal
    have : K.Characteristic := CFSG.pPrimeCore_characteristic (p := 2) (G := ↥X)
    have hKnormalW : (K.map X.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
    have hcopW : Nat.Coprime 2 (Nat.card (K.map X.subtype)) := by
      rw [Subgroup.card_map_of_injective X.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    have hle : K.map X.subtype ≤ pPrimeCore 2 W := le_sSup ⟨hKnormalW, hcopW⟩
    rw [hO] at hle
    exact (Subgroup.map_eq_bot_iff_of_injective (H := K) X.subtype_injective).mp
      (le_bot_iff.mp hle)
  have hEvenFX : Even (Nat.card (generalizedFitting X)) :=
    CFSG.even_card_generalizedFitting_of_pPrimeCore_two_eq_bot hOX hntX
  have hF : generalizedFitting W = D ⊔ (generalizedFitting X).map X.subtype := by
    have h := CFSG.generalizedFitting_eq_sup_of_two_components (D := D) (X := X) hA hB
      hDAB hD (by rw [hDAB])
    simpa [hDAB] using h
  have hdisj : D ⊓ X = ⊥ := by
    rw [hDAB]
    change (A ⊔ B) ⊓ Subgroup.centralizer ((A ⊔ B : Subgroup W) : Set W) = ⊥
    exact CFSG.disjoint_sup_centralizer_of_two_components hA hB hne hZA hZB
  have hcomm : ∀ d ∈ D, ∀ f ∈ (generalizedFitting X).map X.subtype, d * f = f * d := by
    intro d hd f hf
    have hfX : f ∈ X := Subgroup.map_subtype_le (generalizedFitting X) hf
    have hdAB : d ∈ A ⊔ B := by rwa [← hDAB]
    exact (Subgroup.mem_centralizer_iff.mp hfX) d hdAB
  have hInter : UnbalancedLayer.coreActionKernel D ⊓ generalizedFitting W =
      (generalizedFitting X).map X.subtype := by
    rw [hQX]
    refine le_antisymm ?_ ?_
    · rintro z ⟨hzX, hzF⟩
      rw [hF] at hzF
      obtain ⟨d, hd, f, hf, rfl⟩ :=
        (Subgroup.mem_sup_iff_of_forall_commute hcomm).mp hzF
      have hfX : f ∈ X := Subgroup.map_subtype_le (generalizedFitting X) hf
      have hdX : d ∈ X := by
        have hd_eq : d = (d * f) * f⁻¹ := by group
        rw [hd_eq]
        exact X.mul_mem hzX (X.inv_mem hfX)
      have hd_bot : d ∈ (⊥ : Subgroup W) := by
        rw [← hdisj]
        exact ⟨hd, hdX⟩
      have hd1 : d = 1 := Subgroup.mem_bot.mp hd_bot
      rw [hd1, one_mul]
      exact hf
    · intro z hz
      refine Subgroup.mem_inf.mpr ⟨Subgroup.map_subtype_le _ hz, ?_⟩
      rw [hF]
      exact Subgroup.mem_sup_right hz
  rw [hInter, Subgroup.card_map_of_injective X.subtype_injective]
  exact hEvenFX

variable {G : Type} [Group G] [Finite G]

theorem image_baseKernel_eq_centralizer_inf_generalizedFitting {H D : Subgroup G}
    (hDH : D ≤ H) (hD : (D.subgroupOf H).Normal) :
    (((base H ⊓ UnbalancedLayer.coreActionKernel D).subgroupOf H).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥H))) =
      Subgroup.centralizer ((D.subgroupOf H).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥H)) : Set (↥H ⧸ pPrimeCore 2 ↥H)) ⊓
        generalizedFitting (↥H ⧸ pPrimeCore 2 ↥H) := by
  let Hbar := ↥H ⧸ pPrimeCore 2 ↥H
  let π : ↥H →* Hbar := QuotientGroup.mk' (pPrimeCore 2 ↥H)
  let Dsub : Subgroup ↥H := D.subgroupOf H
  have hQsub : (UnbalancedLayer.coreActionKernel D).subgroupOf H =
      UnbalancedLayer.coreActionKernel Dsub := by
    dsimp [Dsub]
    exact (coreActionKernel_subgroupOf hDH).symm
  have hKsub : (base H ⊓ UnbalancedLayer.coreActionKernel D).subgroupOf H =
      (base H).subgroupOf H ⊓ UnbalancedLayer.coreActionKernel Dsub := by
    rw [Subgroup.subgroupOf, Subgroup.comap_inf]
    change (base H).subgroupOf H ⊓ (UnbalancedLayer.coreActionKernel D).subgroupOf H =
      (base H).subgroupOf H ⊓ UnbalancedLayer.coreActionKernel Dsub
    rw [hQsub]
  have hObar : pPrimeCore 2 Hbar = ⊥ :=
    CFSG.pPrimeCore_quotient_eq_bot (p := 2) Nat.prime_two
  have hmapBase : ((base H).subgroupOf H).map π = generalizedFitting Hbar := by
    have hbase : pCore 2 Hbar ⊔ layer Hbar = generalizedFitting Hbar := by
      rw [CFSG.generalizedFitting.eq_sup, CFSG.Fitting_eq_pcore Hbar 2 hObar]
    rw [← hbase]
    have h := Sol76T13.R12.map_oddTwoCoreIn_sup_twoLayerIn (G := G) H
    simpa [base, π, Hbar] using h
  have hmapQ : (UnbalancedLayer.coreActionKernel Dsub).map π =
      Subgroup.centralizer ((Dsub.map π : Subgroup Hbar) : Set Hbar) := by
    dsimp [Dsub, π, Hbar]
    exact UnbalancedLayer.map_coreActionKernel_eq_centralizer (W := ↥H) (D := D.subgroupOf H) hD
  have hker_le_base : π.ker ≤ (base H).subgroupOf H := by
    rw [show π.ker = pPrimeCore 2 ↥H from QuotientGroup.ker_mk' (pPrimeCore 2 ↥H)]
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hxOdd : (x : G) ∈ FooteLit.oddCoreIn H := ⟨x, hx, rfl⟩
    have hle : FooteLit.oddCoreIn H ≤ base H := by
      dsimp [base]
      refine le_sup_of_le_left ?_
      change (pPrimeCore 2 ↥H).map H.subtype ≤
        (((pCore 2 (↥H ⧸ pPrimeCore 2 ↥H)).comap
          (QuotientGroup.mk' (pPrimeCore 2 ↥H))).map H.subtype)
      exact Subgroup.map_mono CFSG.ABGLocalTools.pPrimeCore_le_Op_p'p
    exact hle hxOdd
  have hmapInf : ((base H).subgroupOf H ⊓ UnbalancedLayer.coreActionKernel Dsub).map π =
      ((base H).subgroupOf H).map π ⊓
        (UnbalancedLayer.coreActionKernel Dsub).map π := by
    refine le_antisymm (Subgroup.map_inf_le _ _ _) ?_
    rintro y ⟨⟨b, hb, rfl⟩, ⟨q, hq, hbq⟩⟩
    have hz : b⁻¹ * q ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      rw [hbq]
      group
    have hz' : b⁻¹ * q ∈ (base H).subgroupOf H := hker_le_base hz
    have hq' : q ∈ (base H).subgroupOf H := by
      have hq_eq : q = b * (b⁻¹ * q) := by group
      rw [hq_eq]
      exact ((base H).subgroupOf H).mul_mem hb hz'
    exact ⟨q, ⟨hq', hq⟩, hbq⟩
  rw [hKsub, hmapInf, hmapBase, hmapQ]
  exact inf_comm _ _

section InitialSection9

private theorem base_le_normalizer_of_isTwoComponentIn {N K : Subgroup G}
    (hK : IsTwoComponentIn K N) :
    K ≤ base N ∧ base N ≤ Subgroup.normalizer (K : Set G) := by
  constructor
  · change K ≤ FooteLit.oddTwoCoreIn N ⊔ FooteLit.twoLayerIn N
    exact (le_twoLayerIn_of_isTwoComponentIn hK).trans le_sup_right
  · refine sup_le ?_ ?_
    · exact (CFSG.ComponentClassification.Sol76.Sig.oddTwoCoreIn_le_coreActionKernel hK).trans
        (fun x hx => (UnbalancedLayer.mem_coreActionKernel.mp hx).1)
    · exact twoLayerIn_le_normalizer hK.1 hK.2

variable {T : Type} [Group T] [IsSimpleGroup T]
variable {family : Set (Subgroup G)} {N Ki Kj E F : Subgroup G}

private theorem center_quotient_eq_bot_of_marked
    (hfamily : IsomorphicFamily family T) {M : Subgroup G} (hM : Marked family T M) :
    Subgroup.center (M ⧸ pPrimeCore 2 M) = ⊥ := by
  obtain ⟨e⟩ := hM.2.1
  have hq : CFSG.IsQuasisimple (M ⧸ pPrimeCore 2 M) :=
    Marked.quotient_quasisimple hfamily hM
  have hperf : Group.IsPerfect (M ⧸ pPrimeCore 2 M) := hq.1
  have hsimple : IsSimpleGroup (M ⧸ pPrimeCore 2 M) := e.isSimpleGroup
  have hnt : Nontrivial (M ⧸ pPrimeCore 2 M) := hsimple.toNontrivial
  have hnc : ¬ IsMulCommutative (M ⧸ pPrimeCore 2 M) :=
    @Group.IsPerfect.not_isMulCommutative (M ⧸ pPrimeCore 2 M) _ hnt hperf
  have hwit : ∃ a b : M ⧸ pPrimeCore 2 M, a * b ≠ b * a := by
    by_contra h
    exact hnc (IsMulCommutative.of_comm fun a b => by
      by_contra hab
      exact h ⟨a, b, hab⟩)
  exact @CFSG.ComponentClassification.FooteLit.center_eq_bot_of_isSimpleGroup
    (M ⧸ pPrimeCore 2 M) _ hsimple hwit

theorem pair_kernel_facts_of_balanced
    (hfamily : IsomorphicFamily family T)
    (hN : Balanced family T N)
    (hKi : Ki ∈ markedComponents family T N)
    (hKj : Kj ∈ markedComponents family T N)
    (hne : Ki ≠ Kj) :
    base N ≤ Subgroup.normalizer
        ((base N ⊓ UnbalancedLayer.coreActionKernel (Ki ⊔ Kj) : Subgroup G) : Set G) ∧
      (base N ⊓ UnbalancedLayer.coreActionKernel (Ki ⊔ Kj)) ≤
        UnbalancedLayer.coreActionKernel Ki ⊓
          UnbalancedLayer.coreActionKernel Kj ∧
      (base N ⊓ UnbalancedLayer.coreActionKernel (Ki ⊔ Kj)) ⊓ (Ki ⊔ Kj) =
        FooteLit.oddCoreIn (Ki ⊔ Kj) ∧
      Even (Nat.card ↥(base N ⊓ UnbalancedLayer.coreActionKernel (Ki ⊔ Kj))) := by
  classical
  have hKiN : IsTwoComponentIn Ki N := hKi.1
  have hKjN : IsTwoComponentIn Kj N := hKj.1
  have hKiMarked : Marked family T Ki := hKi.2
  have hKjMarked : Marked family T Kj := hKj.2
  obtain ⟨hKiBase, hKiNorm⟩ := base_le_normalizer_of_isTwoComponentIn hKiN
  obtain ⟨hKjBase, hKjNorm⟩ := base_le_normalizer_of_isTwoComponentIn hKjN
  have hPairBase : Ki ⊔ Kj ≤ base N := sup_le hKiBase hKjBase
  have hPairN : Ki ⊔ Kj ≤ N := sup_le hKiN.1 hKjN.1
  have hPairNorm : base N ≤ normalizer ((Ki ⊔ Kj : Subgroup G) : Set G) :=
    (le_inf hKiNorm hKjNorm).trans (Subgroup.inf_normalizer_le_normalizer_sup Ki Kj)
  have hKernelNorm : base N ≤
      normalizer (UnbalancedLayer.coreActionKernel (Ki ⊔ Kj) : Set G) :=
    fun x hx => mem_normalizer_coreActionKernel (hPairNorm hx)
  have hBaseNormalizesQ : base N ≤ Subgroup.normalizer
      ((base N ⊓ UnbalancedLayer.coreActionKernel (Ki ⊔ Kj) : Subgroup G) : Set G) := by
    have hself : base N ≤ normalizer ((base N : Subgroup G) : Set G) :=
      Subgroup.le_normalizer
    exact (le_inf hself hKernelNorm).trans (Subgroup.inf_normalizer_le_normalizer_inf)
  have hQKernelKi : (base N ⊓ UnbalancedLayer.coreActionKernel (Ki ⊔ Kj)) ≤
      UnbalancedLayer.coreActionKernel Ki := by
    intro x hx
    exact mem_coreActionKernel_of_le (J := Ki ⊔ Kj) (T := Ki) le_sup_left
      (hKiNorm hx.1) hx.2
  have hQKernelKj : (base N ⊓ UnbalancedLayer.coreActionKernel (Ki ⊔ Kj)) ≤
      UnbalancedLayer.coreActionKernel Kj := by
    intro x hx
    exact mem_coreActionKernel_of_le (J := Ki ⊔ Kj) (T := Kj) le_sup_right
      (hKjNorm hx.1) hx.2
  have hQKernels : (base N ⊓ UnbalancedLayer.coreActionKernel (Ki ⊔ Kj)) ≤
      UnbalancedLayer.coreActionKernel Ki ⊓ UnbalancedLayer.coreActionKernel Kj :=
    le_inf hQKernelKi hQKernelKj
  have hKiPair : IsTwoComponentIn Ki (Ki ⊔ Kj) :=
    CFSG.ComponentClassification.Sol76.isTwoComponentIn_of_le hKiN le_sup_left hPairN
  have hKjPair : IsTwoComponentIn Kj (Ki ⊔ Kj) :=
    CFSG.ComponentClassification.Sol76.isTwoComponentIn_of_le hKjN le_sup_right hPairN
  have hOKiPair : FooteLit.oddCoreIn Ki ≤ FooteLit.oddCoreIn (Ki ⊔ Kj) :=
    FooteLit.oddCoreIn_le_of_isTwoComponentIn hKiPair
  have hOKjPair : FooteLit.oddCoreIn Kj ≤ FooteLit.oddCoreIn (Ki ⊔ Kj) :=
    FooteLit.oddCoreIn_le_of_isTwoComponentIn hKjPair
  have hOddLeQ : FooteLit.oddCoreIn (Ki ⊔ Kj) ≤
      base N ⊓ UnbalancedLayer.coreActionKernel (Ki ⊔ Kj) := by
    refine le_inf ?_ (CFSG.ComponentClassification.GSThmB.oddCoreIn_le_coreActionKernel (Ki ⊔ Kj))
    exact (map_subtype_le (pPrimeCore 2 ↥(Ki ⊔ Kj))).trans hPairBase
  have hOddLePair : FooteLit.oddCoreIn (Ki ⊔ Kj) ≤ Ki ⊔ Kj :=
    map_subtype_le _
  have hKjKernelKi : Kj ≤ UnbalancedLayer.coreActionKernel Ki :=
    CFSG.ComponentClassification.Foote5.SolMax.le_coreActionKernel_of_ne hKiN hKjN hne
  have hKiKernelKj : Ki ≤ UnbalancedLayer.coreActionKernel Kj :=
    CFSG.ComponentClassification.Foote5.SolMax.le_coreActionKernel_of_ne hKjN hKiN hne.symm
  have hKjNormalizesKi : Kj ≤ normalizer (Ki : Set G) :=
    hKjKernelKi.trans (fun x hx => (UnbalancedLayer.mem_coreActionKernel.mp hx).1)
  have hZi : Subgroup.center (Ki ⧸ pPrimeCore 2 Ki) = ⊥ :=
    center_quotient_eq_bot_of_marked hfamily hKiMarked
  have hZj : Subgroup.center (Kj ⧸ pPrimeCore 2 Kj) = ⊥ :=
    center_quotient_eq_bot_of_marked hfamily hKjMarked
  have hPairLeOdd : (base N ⊓ UnbalancedLayer.coreActionKernel (Ki ⊔ Kj)) ⊓ (Ki ⊔ Kj) ≤
      FooteLit.oddCoreIn (Ki ⊔ Kj) := by
    rintro x ⟨hxQ, hxPair⟩
    obtain ⟨i, hiKi, j, hjKj, rfl⟩ :=
      CFSG.ComponentClassification.Sol76.exists_mul_of_mem_sup_normalizer hKjNormalizesKi hxPair
    have hiKernel : i ∈ UnbalancedLayer.coreActionKernel Ki := by
      rw [show i = (i * j) * j⁻¹ by group]
      exact Subgroup.mul_mem _ (hQKernelKi hxQ) (Subgroup.inv_mem _ (hKjKernelKi hjKj))
    have hjKernel : j ∈ UnbalancedLayer.coreActionKernel Kj := by
      rw [show j = i⁻¹ * (i * j) by group]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hKiKernelKj hiKi)) (hQKernelKj hxQ)
    have hiOdd : i ∈ FooteLit.oddCoreIn Ki :=
      FooteLit.mem_oddCoreIn_of_mem_coreActionKernel hZi hiKi hiKernel
    have hjOdd : j ∈ FooteLit.oddCoreIn Kj :=
      FooteLit.mem_oddCoreIn_of_mem_coreActionKernel hZj hjKj hjKernel
    exact Subgroup.mul_mem _ (hOKiPair hiOdd) (hOKjPair hjOdd)
  have hPairInter : (base N ⊓ UnbalancedLayer.coreActionKernel (Ki ⊔ Kj)) ⊓ (Ki ⊔ Kj) =
      FooteLit.oddCoreIn (Ki ⊔ Kj) :=
    le_antisymm hPairLeOdd (le_inf hOddLeQ hOddLePair)
  have hEvenQ : Even (Nat.card ↥(base N ⊓ UnbalancedLayer.coreActionKernel (Ki ⊔ Kj))) := by
    by_cases h3 : 3 ≤ markedCount family T N
    ·
      have hlt : ({Ki, Kj} : Set (Subgroup G)).ncard <
          (markedComponents family T N).ncard := by
        rw [Set.ncard_pair hne]
        have : 2 < markedCount family T N := by omega
        simpa [markedCount] using this
      obtain ⟨M, hMmem, hMnot⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt
      have hMKi : M ≠ Ki := by
        intro h
        exact hMnot (by simp [h])
      have hMKj : M ≠ Kj := by
        intro h
        exact hMnot (by simp [h])
      have hMN : IsTwoComponentIn M N := hMmem.1
      obtain ⟨hMBase, -⟩ := base_le_normalizer_of_isTwoComponentIn hMN
      have hMKernelKi : M ≤ UnbalancedLayer.coreActionKernel Ki :=
        CFSG.ComponentClassification.Foote5.SolMax.le_coreActionKernel_of_ne hKiN hMN hMKi.symm
      have hMKernelKj : M ≤ UnbalancedLayer.coreActionKernel Kj :=
        CFSG.ComponentClassification.Foote5.SolMax.le_coreActionKernel_of_ne hKjN hMN hMKj.symm
      have hMNormKi : M ≤ normalizer (Ki : Set G) :=
        hMKernelKi.trans (fun x hx => (UnbalancedLayer.mem_coreActionKernel.mp hx).1)
      have hMNormKj : M ≤ normalizer (Kj : Set G) :=
        hMKernelKj.trans (fun x hx => (UnbalancedLayer.mem_coreActionKernel.mp hx).1)
      have hMNormPair : M ≤ normalizer ((Ki ⊔ Kj : Subgroup G) : Set G) :=
        (le_inf hMNormKi hMNormKj).trans (Subgroup.inf_normalizer_le_normalizer_sup Ki Kj)
      have hKiNormOdd : Ki ≤ normalizer (FooteLit.oddCoreIn (Ki ⊔ Kj) : Set G) :=
        le_sup_left.trans (CFSG.ComponentClassification.Sol76.le_normalizer_oddCoreIn (Ki ⊔ Kj))
      have hKjNormOdd : Kj ≤ normalizer (FooteLit.oddCoreIn (Ki ⊔ Kj) : Set G) :=
        le_sup_right.trans (CFSG.ComponentClassification.Sol76.le_normalizer_oddCoreIn (Ki ⊔ Kj))
      have hKiComm : ⁅Ki, M⁆ ≤ FooteLit.oddCoreIn (Ki ⊔ Kj) :=
        (CFSG.ComponentClassification.Sol76.Sig.commutator_le_oddCoreIn_of_le_coreActionKernel
          hMKernelKi).trans hOKiPair
      have hKjComm : ⁅Kj, M⁆ ≤ FooteLit.oddCoreIn (Ki ⊔ Kj) :=
        (CFSG.ComponentClassification.Sol76.Sig.commutator_le_oddCoreIn_of_le_coreActionKernel
          hMKernelKj).trans hOKjPair
      have hPairComm : ⁅Ki ⊔ Kj, M⁆ ≤ FooteLit.oddCoreIn (Ki ⊔ Kj) :=
        CFSG.ComponentClassification.Sol76.Sig.commutator_sup_le_of_le
          hKjNormalizesKi hKiNormOdd hKjNormOdd hKiComm hKjComm
      have hMPairComm : ⁅M, Ki ⊔ Kj⁆ ≤ FooteLit.oddCoreIn (Ki ⊔ Kj) :=
        (Subgroup.commutator_comm M (Ki ⊔ Kj)).le.trans hPairComm
      have hMKernelPair : M ≤ UnbalancedLayer.coreActionKernel (Ki ⊔ Kj) :=
        CFSG.ComponentClassification.Sol76.Sig.le_coreActionKernel_of_commutator_le_oddCoreIn hMPairComm
      have hMQ : M ≤ base N ⊓ UnbalancedLayer.coreActionKernel (Ki ⊔ Kj) :=
        le_inf hMBase hMKernelPair
      have hEvenMSub : Even (Nat.card ↥(M.subgroupOf N)) :=
        CFSG.ComponentClassification.CatFactsSp4.even_card_of_isPComponent hMN.2
      have hEvenM : Even (Nat.card ↥M) := by
        have hcard : Nat.card ↥(M.subgroupOf N) = Nat.card ↥M :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMN.1).toEquiv
        rwa [hcard] at hEvenMSub
      exact hEvenM.trans_dvd (Subgroup.card_dvd_of_le hMQ)
    ·
      have h2count : 2 ≤ markedCount family T N := hN.1
      have hcount : markedCount family T N = 2 := by omega
      have hset : markedComponents family T N = {Ki, Kj} := by
        have hsub : ({Ki, Kj} : Set (Subgroup G)) ⊆ markedComponents family T N := by
          intro K hK
          rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hK
          rcases hK with rfl | rfl
          · exact hKi
          · exact hKj
        have hpair : ({Ki, Kj} : Set (Subgroup G)).ncard = 2 := Set.ncard_pair hne
        have hle : (markedComponents family T N).ncard ≤
            ({Ki, Kj} : Set (Subgroup G)).ncard := by
          change markedCount family T N ≤ ({Ki, Kj} : Set (Subgroup G)).ncard
          rw [hcount, hpair]
        exact (Set.eq_of_subset_of_ncard_le hsub hle).symm
      have hlayer : markedLayer family T N = Ki ⊔ Kj := by
        unfold markedLayer
        rw [hset, sSup_pair]
      have hbaseKernel : baseKernel family T N =
          base N ⊓ UnbalancedLayer.coreActionKernel (Ki ⊔ Kj) := by
        unfold baseKernel
        rw [hlayer]
      rcases hN.2 with h3' | hEven
      · omega
      · rwa [hbaseKernel] at hEven
  exact ⟨hBaseNormalizesQ, hQKernels, hPairInter, hEvenQ⟩

theorem exists_central_sylow_admissible_pair
    (hfamily : IsomorphicFamily family T)
    (hN : Balanced family T N)
    (hKi : Ki ∈ markedComponents family T N)
    (hKj : Kj ∈ markedComponents family T N)
    (hne : Ki ≠ Kj)
    (hE : IsKleinFour E) (hF : IsKleinFour F)
    (hEKj : E ≤ Kj) (hFKi : F ≤ Ki)
    (hEF : E ≤ centralizer (F : Set G)) :
    ∃ (S : Sylow 2 ↥(base N)) (z : G),
      let S0 : Subgroup G := (S : Subgroup ↥(base N)).map (base N).subtype
      let Bz : Subgroup G := E ⊔ Subgroup.zpowers z
      E ≤ S0 ∧ F ≤ S0 ∧ z ∈ S0 ∧
        z ∈ (base N ⊓ UnbalancedLayer.coreActionKernel (Ki ⊔ Kj)) ∧
        orderOf z = 2 ∧
        (∀ s ∈ S0, s * z = z * s) ∧
        z ∉ Ki ⊔ Kj ∧
        CFSG.Open.IsElemAbelian 2 Bz ∧ Nat.card Bz = 8 ∧
        Bz ⊓ Kj = E ∧
        Bz ≤ S0 ∧ Bz ≤ UnbalancedLayer.coreActionKernel Ki ∧
        Bz ≤ centralizer (F : Set G) ∧
        (∀ Km : Subgroup G, IsTwoComponentIn Km N → Km ≠ Kj →
          Bz ≤ centralizer (((S0 ⊓ Km : Subgroup G) : Set G))) ∧
        (∀ Km : Subgroup G, IsTwoComponentIn Km N →
          CFSG.ABGLocalTools.IsSylowOf 2 (S0 ⊓ Km) Km) := by
  classical
  let X : Subgroup G := base N
  let P : Subgroup G := Ki ⊔ Kj
  let Q : Subgroup G := X ⊓ UnbalancedLayer.coreActionKernel P
  have hKiN : IsTwoComponentIn Ki N := hKi.1
  have hKjN : IsTwoComponentIn Kj N := hKj.1
  obtain ⟨hXnormQ₀, hQkernels₀, hQpair₀, hEvenQ₀⟩ :=
    pair_kernel_facts_of_balanced (family := family) (T := T) (N := N)
      (Ki := Ki) (Kj := Kj) hfamily hN hKi hKj hne
  have hXnormQ : X ≤ Subgroup.normalizer (Q : Set G) := by
    simpa [X, P, Q] using hXnormQ₀
  have hQkernels : Q ≤ UnbalancedLayer.coreActionKernel Ki ⊓
      UnbalancedLayer.coreActionKernel Kj := by
    simpa [X, P, Q] using hQkernels₀
  have hQpair : Q ⊓ P = FooteLit.oddCoreIn P := by
    simpa [X, P, Q] using hQpair₀
  have hEvenQ : Even (Nat.card ↥Q) := by
    simpa [X, P, Q] using hEvenQ₀
  have hQKi : Q ≤ UnbalancedLayer.coreActionKernel Ki := hQkernels.trans inf_le_left
  have hQKj : Q ≤ UnbalancedLayer.coreActionKernel Kj := hQkernels.trans inf_le_right
  obtain ⟨hKiX, -⟩ := base_le_normalizer_of_isTwoComponentIn hKiN
  obtain ⟨hKjX, -⟩ := base_le_normalizer_of_isTwoComponentIn hKjN
  have hEX : E ≤ X := hEKj.trans hKjX
  have hFX : F ≤ X := hFKi.trans hKiX
  have hEFX : E ⊔ F ≤ X := sup_le hEX hFX
  have hE2 : IsPGroup 2 E := CFSG.ComponentClassification.Sol76.Sig.isPGroup_of_isKleinFour hE
  have hF2 : IsPGroup 2 F := CFSG.ComponentClassification.Sol76.Sig.isPGroup_of_isKleinFour hF
  have hEFnorm : E ≤ Subgroup.normalizer (F : Set G) :=
    hEF.trans (Subgroup.centralizer_le_normalizer (F : Set G))
  have hEF2 : IsPGroup 2 ↥(E ⊔ F) := hE2.to_sup_of_normal_right' hF2 hEFnorm
  have hEFsub2 : IsPGroup 2 ((E ⊔ F).subgroupOf X) := hEF2.comap_subtype
  obtain ⟨S, hSle⟩ := hEFsub2.exists_le_sylow
  let S0 : Subgroup G := (S : Subgroup ↥X).map X.subtype
  have hS0p : IsPGroup 2 S0 := S.isPGroup'.map X.subtype
  have hEFS0 : E ⊔ F ≤ S0 := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hEFX]
    exact Subgroup.map_mono hSle
  have hES0 : E ≤ S0 := le_sup_left.trans hEFS0
  have hFS0 : F ≤ S0 := le_sup_right.trans hEFS0
  have hQleX : Q ≤ X := inf_le_left
  have hQsubNormal : (Q.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQleX).mpr hXnormQ
  have : (Q.subgroupOf X).Normal := hQsubNormal
  have hcardQsub : Nat.card ↥(Q.subgroupOf X) = Nat.card ↥Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQleX).toEquiv
  have h2dvdQsub : 2 ∣ Nat.card ↥(Q.subgroupOf X) := by
    rw [hcardQsub]
    exact even_iff_two_dvd.mp hEvenQ
  obtain ⟨zS, hzcenter, hzS1, hzSsq, hzQsub⟩ :=
    CFSG.ABGLocalTools.exists_central_involution_of_even (S := S)
      (L := Q.subgroupOf X) h2dvdQsub
  let z : G := ((zS : ↥X) : G)
  have hzS0 : z ∈ S0 :=
    Subgroup.mem_map.mpr ⟨(zS : ↥X), zS.2, rfl⟩
  have hzQ : z ∈ Q := Subgroup.mem_subgroupOf.mp hzQsub
  have hzS_order : orderOf zS = 2 := orderOf_eq_prime hzSsq hzS1
  have hzX_order : orderOf (zS : ↥X) = 2 := by
    rw [Subgroup.orderOf_coe, hzS_order]
  have hz_order : orderOf z = 2 := by
    change orderOf ((zS : ↥X) : G) = 2
    rw [Subgroup.orderOf_coe, hzX_order]
  have hzsq : z * z = 1 := by
    rw [← pow_two, ← hz_order]
    exact pow_orderOf_eq_one z
  have hzsq_pow : z ^ 2 = 1 := by
    rw [pow_two]
    exact hzsq
  have hzcentral : ∀ s ∈ S0, s * z = z * s := by
    intro s hs
    obtain ⟨sX, hsS, rfl⟩ := Subgroup.mem_map.mp hs
    have hcomm := Subgroup.mem_center_iff.mp hzcenter ⟨sX, hsS⟩
    have hcommX : sX * (zS : ↥X) = (zS : ↥X) * sX := by
      simpa using congrArg (fun y : ↥S => (y : ↥X)) hcomm
    simpa using congrArg (fun y : ↥X => (y : G)) hcommX
  have hKjP : Kj ≤ P := le_sup_right
  have hznotP : z ∉ P := by
    intro hzP
    have hzOdd : z ∈ FooteLit.oddCoreIn P := by
      rw [← hQpair]
      exact ⟨hzQ, hzP⟩
    have hdvd : orderOf z ∣ Nat.card (FooteLit.oddCoreIn P) :=
      Subgroup.orderOf_dvd_natCard _ hzOdd
    rw [hz_order] at hdvd
    exact (FooteLit.odd_card_oddCoreIn P).not_two_dvd_nat hdvd
  have hznotKj : z ∉ Kj := fun h => hznotP (hKjP h)
  have hznotE : z ∉ E := fun h => hznotKj (hEKj h)
  have hEz : E ≤ Subgroup.centralizer ({z} : Set G) := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzcentral e (hES0 he))
  have hBzea : CFSG.Open.IsElemAbelian 2 (E ⊔ Subgroup.zpowers z) := by
    have hEea : CFSG.Open.IsElemAbelian 2 E :=
      CFSG.ComponentClassification.Sol76.Sig.isElemAbelian_of_isKleinFour hE
    have hZea : CFSG.Open.IsElemAbelian 2 (Subgroup.zpowers z) :=
      CFSG.Open.isElemAbelian_zpowers (p := 2) hzsq_pow
    refine CFSG.Open.IsElemAbelian.sup_of_commute hEea hZea ?_
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (hzcentral a (hES0 ha)) k).eq
  have hBzcard : Nat.card ↥(E ⊔ Subgroup.zpowers z) = 8 := by
    have hcomm : ∀ w ∈ E, w * z = z * w := fun w hw => hzcentral w (hES0 hw)
    exact (sup_zpowers_spec hE hznotE hzsq_pow hcomm).2
  have hBzKj : (E ⊔ Subgroup.zpowers z) ⊓ Kj = E := by
    refine le_antisymm ?_ (le_inf le_sup_left hEKj)
    intro x hx
    have hx_or : x ∈ E ∨ x * z ∈ E :=
      mem_or_mul_mem_of_mem_sup_zpowers hEz hzsq hx.1
    rcases hx_or with hxE | hxzE
    · exact hxE
    · exfalso
      apply hznotKj
      rw [show z = x⁻¹ * (x * z) by group]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hx.2) (hEKj hxzE)
  have hBzS0 : E ⊔ Subgroup.zpowers z ≤ S0 :=
    sup_le hES0 (Subgroup.zpowers_le.mpr hzS0)
  have hBzKi : E ⊔ Subgroup.zpowers z ≤ UnbalancedLayer.coreActionKernel Ki := by
    have hKjKernelKi : Kj ≤ UnbalancedLayer.coreActionKernel Ki :=
      CFSG.ComponentClassification.Foote5.SolMax.le_coreActionKernel_of_ne hKiN hKjN hne
    exact sup_le (hEKj.trans hKjKernelKi) (Subgroup.zpowers_le.mpr (hQKi hzQ))
  have hBzF : E ⊔ Subgroup.zpowers z ≤ centralizer (F : Set G) := by
    have hzF : z ∈ Subgroup.centralizer (F : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      exact hzcentral f (hFS0 hf)
    exact sup_le hEF (Subgroup.zpowers_le.mpr hzF)
  have hBzCentralKm : ∀ Km : Subgroup G, IsTwoComponentIn Km N → Km ≠ Kj →
      E ⊔ Subgroup.zpowers z ≤
        Subgroup.centralizer (((S0 ⊓ Km : Subgroup G) : Set G)) := by
    intro Km hKm hKmne
    have hEcentral : E ≤
        Subgroup.centralizer (((S0 ⊓ Km : Subgroup G) : Set G)) := by
      intro e he
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      exact (CFSG.ComponentClassification.HSFLit.L34Uniq.commute_of_ne
        (C := N) (K := Kj) (K' := Km) (S := S0)
        hKjN.1 hKm.1 hKjN.2 hKm.2 hKmne.symm hS0p
        (hES0 he) (hEKj he) hm.1 hm.2).symm
    have hZcentral : Subgroup.zpowers z ≤
        Subgroup.centralizer (((S0 ⊓ Km : Subgroup G) : Set G)) := by
      refine Subgroup.zpowers_le.mpr ?_
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      exact hzcentral m hm.1
    exact sup_le hEcentral hZcentral
  have hFullSylow : ∀ Km : Subgroup G, IsTwoComponentIn Km N →
      CFSG.ABGLocalTools.IsSylowOf 2 (S0 ⊓ Km) Km := by
    intro Km hKm
    obtain ⟨hKmX, hKmNorm⟩ := base_le_normalizer_of_isTwoComponentIn hKm
    have hS0 : CFSG.ABGLocalTools.IsSylowOf 2 S0 X := ⟨S, rfl⟩
    exact @CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer G _ 2 _
      ⟨Nat.prime_two⟩ S0 X Km hS0 hKmX hKmNorm
  refine ⟨S, z, ?_⟩
  dsimp only
  exact ⟨hES0, hFS0, hzS0, hzQ, hz_order, hzcentral, hznotP, hBzea, hBzcard,
    hBzKj, hBzS0, hBzKi, hBzF, hBzCentralKm, hFullSylow⟩

end InitialSection9

end CFSG.ComponentClassification.FooteMarked
