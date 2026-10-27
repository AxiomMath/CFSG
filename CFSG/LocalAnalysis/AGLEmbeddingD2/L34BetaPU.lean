module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.L34Three
public import CFSG.LocalAnalysis.AGLEmbeddingD2.PerfectSchreier
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaL34PU
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallThreeOrders

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

theorem D2AlmostSimple.eq_or_eq_top_of_l34 (hI : KFactL34Inner) {d : TauCeti.ValidLieTypeIndex}
    (hd : IsL34Index d) {X : Type} [Group X] [Finite X] {R : Sylow 3 X} {A X₀ K : Subgroup X}
    (hK : D2AlmostSimple 3 X R A X₀ K) (he : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hAK : A ≤ K) : ∀ Y : Subgroup X, X₀ ≤ Y → Y = X₀ ∨ Y = ⊤ := by
  intro Y hY
  have hX₀ := hK.eq_normalizer_of_l34 hI hd he hAK
  rw [hX₀] at hY ⊢
  exact hI d hd X K hK.normal hK.centralizer_eq_bot he A hK.elem hK.card_A hAK Y hY

theorem isLinThreeFour_of_l34Index {d : TauCeti.ValidLieTypeIndex} (hd : IsL34Index d) {K : Type}
    [Group K] (he : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)) : IsLinThreeFour K :=
  ⟨d, hd, he⟩

section Escape

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M A H R : Subgroup G}

theorem D2Escape.le_or_le_of_maximal (h : D2Escape p P M A H R)
    (hmax : ∀ Y : Subgroup (H ⧸ primeComplementCore (G := H) p),
      ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤ Y →
        Y = ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ∨
          Y = ⊤)
    {Y : Subgroup G} (hHM : H ⊓ M ≤ Y) (hYH : Y ≤ H) : Y ≤ M ∨ H ≤ Y := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  set Yb := (Y.subgroupOf H).map π with hYdef
  have hXY : ((H ⊓ M).subgroupOf H).map π ≤ Yb := Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hHM (Subgroup.mem_subgroupOf.mp hx))
  have hcoreM : ∀ x : H, π x = 1 → (x : G) ∈ M := fun x h1 =>
    h.primeCore_le ((mk'_primeComplementCore_eq_one_iff p x).mp h1)
  have hcoreY : ∀ x : H, π x = 1 → (x : G) ∈ Y := fun x h1 =>
    hHM ⟨x.2, hcoreM x h1⟩
  rcases hmax Yb hXY with hY | hY
  · left
    intro j hj
    have hjH : j ∈ H := hYH hj
    have hjY : π ⟨j, hjH⟩ ∈ Yb := ⟨⟨j, hjH⟩, Subgroup.mem_subgroupOf.mpr hj, rfl⟩
    rw [hY] at hjY
    obtain ⟨m, hm, hmj⟩ := hjY
    have hm' : (m : G) ∈ M := (Subgroup.mem_subgroupOf.mp hm).2
    have h1 : π (m⁻¹ * ⟨j, hjH⟩) = 1 := by rw [map_mul, map_inv, hmj, inv_mul_cancel]
    have e : j = (m : G) * ((m⁻¹ * ⟨j, hjH⟩ : H) : G) := by simp
    rw [e]
    exact M.mul_mem hm' (hcoreM _ h1)
  · right
    intro x hx
    have hmem : π ⟨x, hx⟩ ∈ Yb := hY ▸ Subgroup.mem_top _
    obtain ⟨j, hj, hjx⟩ := hmem
    have h1 : π (j⁻¹ * ⟨x, hx⟩) = 1 := by rw [map_mul, map_inv, hjx, inv_mul_cancel]
    have hjY : (j : G) ∈ Y := Subgroup.mem_subgroupOf.mp hj
    have e : x = (j : G) * ((j⁻¹ * ⟨x, hx⟩ : H) : G) := by simp
    rw [e]
    exact Y.mul_mem hjY (hcoreY _ h1)

variable (hmax : ∀ Y : Subgroup (H ⧸ primeComplementCore (G := H) p),
      ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤ Y →
        Y = ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ∨
          Y = ⊤)
include hmax

theorem D2Escape.inf_normalizer_twoCore_inf (h : D2Escape p P M A H R)
    (hS : pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H) :
    H ⊓ Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) = H ⊓ M :=
  inf_normalizer_twoCore_inf_of_le_or_le h.twoCore_le
    (fun hHM hYH => h.le_or_le_of_maximal hmax hHM hYH) hS

theorem D2Escape.asc81bHyp_twoCore_inf (h : D2Escape p P M A H R) (hglob : AGLGlobal G)
    (hS : pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H)
    (hPU : ∀ C : Subgroup G, C ≤ pCoreOf 2 (H ⊓ M) → C ≠ ⊥ →
      (C.subgroupOf (pCoreOf 2 (H ⊓ M))).Characteristic → ¬ H ≤ Subgroup.normalizer (C : Set G)) :
    Asc81bHyp H (pCoreOf 2 (H ⊓ M)) :=
  asc81bHyp_twoCore_inf_of_le_or_le h.twoCore_le
    (fun hHM hYH => h.le_or_le_of_maximal hmax hHM hYH)
    (hglob.charTwo H h.maxTwoLocal_H.1) hS hPU

end Escape

section Block

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M A H R : Subgroup G}

theorem D2Escape.primeCore_map_le_centralizer {p : ℕ} {P : Sylow p G}
    (h : D2Escape p P M A H R) :
    (primeComplementCore (G := H) p).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ≤
      Subgroup.centralizer (barM H (pCoreOf 2 (H ⊓ M)) : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
  primeCore_map_le_centralizer_of_primeCore_le h.primeCore_le

variable {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem D2AlmostSimple.eq_bot_of_odd_normal {X : Type*} [Group X] [Finite X] {p : ℕ}
    {R : Sylow p X} {A X₀ K : Subgroup X} (hK : D2AlmostSimple p X R A X₀ K)
    (hK2 : 2 ∣ Nat.card K) {N : Subgroup X} [hN : N.Normal] (hNodd : Nat.Coprime 2 (Nat.card N)) :
    N = ⊥ := by
  have : IsSimpleGroup K := by
    have hq : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.component.2.2.2
    exact ((QuotientGroup.quotientMulEquivOfEq hK.center_eq_bot).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup
  have hKn : K.Normal := hK.normal
  have hNK : ∀ y ∈ N, y ∈ K → y = 1 := by
    have hn : (N.subgroupOf K).Normal := hN.subgroupOf K
    rcases hn.eq_bot_or_eq_top with h | h
    · intro y hyN hyK
      have : (⟨y, hyK⟩ : K) ∈ N.subgroupOf K := Subgroup.mem_subgroupOf.mpr hyN
      rw [h, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    · exfalso
      have hKN : K ≤ N := fun k hk => by
        have : (⟨k, hk⟩ : K) ∈ N.subgroupOf K := h ▸ Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.mp this
      have hdvd := Subgroup.card_dvd_of_le hKN
      have h2 : 2 ∣ Nat.card N := dvd_trans hK2 hdvd
      exact absurd (Nat.Coprime.coprime_dvd_right h2 hNodd) (by norm_num)
  rw [eq_bot_iff, ← hK.centralizer_eq_bot]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hc : x * k * x⁻¹ * k⁻¹ = 1 := by
    refine hNK _ ?_ ?_
    · have h1 : k * x⁻¹ * k⁻¹ ∈ N := hN.conj_mem _ (N.inv_mem hx) k
      have := N.mul_mem hx h1
      simpa [mul_assoc] using this
    · exact K.mul_mem (hKn.conj_mem k hk x) (K.inv_mem hk)
  have := congrArg (· * (k * x)) hc
  simp only [one_mul] at this
  calc k * x = x * k * x⁻¹ * k⁻¹ * (k * x) := this.symm
    _ = x * k := by group

theorem D2AlmostSimple.oddCore_le_primeCore_map
    {A' X₀' : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hK : D2AlmostSimple 3 (H ⧸ primeComplementCore (G := H) 3) Rbar A' X₀' K)
    (hK2 : 2 ∣ Nat.card K) :
    CFSG.pPrimeCore 2 (↥H ⧸ CFSG.pCore 2 ↥H) ≤
      (primeComplementCore (G := H) 3).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.pPrimeCore 2 (↥H ⧸ CFSG.pCore 2 ↥H) with hOdef
  set φ := twoPrimeMap H Nat.prime_three (by norm_num : (3 : ℕ) ≠ 2) with hφ
  have hOodd : Nat.Coprime 2 (Nat.card O) := CFSG.pPrimeCore_coprime_card
  have hNn : (O.map φ).Normal :=
    (CFSG.pPrimeCore_normal).map φ (twoPrimeMap_surjective Nat.prime_three (by norm_num))
  have hNodd : Nat.Coprime 2 (Nat.card (O.map φ)) :=
    hOodd.coprime_dvd_right (Subgroup.card_map_dvd O φ)
  have hbot : O.map φ = ⊥ := hK.eq_bot_of_odd_normal hK2 hNodd
  intro o ho
  apply mem_map_of_twoPrimeMap_eq_one Nat.prime_three (by norm_num)
  have : φ o ∈ O.map φ := Subgroup.mem_map_of_mem φ ho
  rwa [hbot, Subgroup.mem_bot] at this

end Block

section Theorem

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M A H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
  {A' X₀ : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem D2Escape.exists_weakBlock_twoCore_inf (h : D2Escape 3 P M A H R)
    (hK : D2AlmostSimple 3 (H ⧸ primeComplementCore (G := H) 3) Rbar A' X₀ K)
    (hK2 : 2 ∣ Nat.card K) (hS : pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H) :
    ∃ L : Subgroup G, IsWeakSBlock H (pCoreOf 2 (H ⊓ M)) L ∧
      ¬ barM H L ≤ (primeComplementCore (G := H) 3).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) :=
  exists_weakBlock_twoCore_inf_of_primeCore_le h.twoCore_le h.primeCore_le
    ((hK.oddCore_le_primeCore_map hK2).trans h.primeCore_map_le_centralizer) hS

theorem D2AlmostSimple.l34BlockFacts
    (hK : D2AlmostSimple 3 (H ⧸ primeComplementCore (G := H) 3) Rbar A' X₀ K)
    (hcard : Nat.card K = 20160)
    (hNH : H ⊓ Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) = H ⊓ M) {L : Subgroup G}
    (hLw : IsWeakSBlock H (pCoreOf 2 (H ⊓ M)) L)
    (hLW : ¬ barM H L ≤
      (primeComplementCore (G := H) 3).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) :
    L34BlockFacts M H L K (twoPrimeMap H Nat.prime_three (by norm_num)) :=
  l34BlockFacts_of_unique hK.unique hK.center_eq_bot hcard hNH hLw hLW

end Theorem

theorem factorization_20160_three : (20160 : ℕ).factorization 3 = 2 := by
  have h2 : 2 ≤ (20160 : ℕ).factorization 3 :=
    (Nat.prime_three.pow_dvd_iff_le_factorization (by norm_num)).1 (by norm_num)
  have h3 : ¬ 3 ≤ (20160 : ℕ).factorization 3 := fun h =>
    absurd ((Nat.prime_three.pow_dvd_iff_le_factorization (by norm_num)).2 h) (by norm_num)
  omega

theorem D2AlmostSimple.card_dvd_seventytwo_of_l34 (hI : KFactL34Inner)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsL34Index d) {X : Type} [Group X] [Finite X]
    {R : Sylow 3 X} {A X₀ K : Subgroup X} (hK : D2AlmostSimple 3 X R A X₀ K)
    (he : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)) (hAK : A ≤ K) {Y : Subgroup X}
    (hYX : Y ≤ X₀) (hYK : Y ≤ K) : Nat.card Y ∣ 72 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL : IsLinThreeFour K := isLinThreeFour_of_l34Index hd he
  have hcardK : Nat.card K = 20160 := (kFactSmallThreeOrders K).2.1 hL
  have hX₀ := hK.eq_normalizer_of_l34 hI hd he hAK
  have hAc : Nat.card (A.subgroupOf K) = 3 ^ (Nat.card K).factorization 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv, hK.card_A, hcardK,
      factorization_20160_three]
  let T : Sylow 3 K := Sylow.ofCard (A.subgroupOf K) hAc
  have hT : (T : Subgroup K) = A.subgroupOf K := rfl
  have hN := (KFactProofs.UPrimeExcL34.localData_of_isLinThreeFour hL T).card_normalizer
  have hYN : Y.subgroupOf K ≤ Subgroup.normalizer ((T : Subgroup K) : Set K) := by
    rw [hT, ← Subgroup.subgroupOf_normalizer_eq hAK]
    intro y hy
    exact Subgroup.mem_subgroupOf.mpr ((hX₀ ▸ hYX) (Subgroup.mem_subgroupOf.mp hy))
  have h1 := Subgroup.card_dvd_of_le hYN
  rw [hN, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYK).toEquiv] at h1
  exact h1

section Final

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M A H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

open CFSG.AGLEmbeddingD2 in
theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.false_of_l34_pu3 {P : Sylow 3 G}
    {M A H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hI : KFactL34Inner) (hNO : KFactL34NotOrthogonal)
    (h93 : Asc81bNineThree) (hNX : NoXBlockFor G) (h : D2Escape 3 P M A H R)
    (hglob : AGLGlobal G)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsL34Index d)
    (hK : D2AlmostSimple 3 (H ⧸ primeComplementCore (G := H) 3) Rbar
      ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))) K)
    (he : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hAK : (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)) ≤ K)
    (hS : pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H)
    (hPU : ∀ C : Subgroup G, C ≤ pCoreOf 2 (H ⊓ M) → C ≠ ⊥ →
      (C.subgroupOf (pCoreOf 2 (H ⊓ M))).Characteristic → ¬ H ≤ Subgroup.normalizer (C : Set G)) :
    False := by
  have hL : IsLinThreeFour K := isLinThreeFour_of_l34Index hd he
  have hcard : Nat.card K = 20160 := (kFactSmallThreeOrders K).2.1 hL
  have hK2 : 2 ∣ Nat.card K := by rw [hcard]; norm_num
  have hmax := hK.eq_or_eq_top_of_l34 hI hd he hAK
  have hNH := h.inf_normalizer_twoCore_inf hmax hS
  obtain ⟨L, hLw, hLW⟩ := h.exists_weakBlock_twoCore_inf hK hK2 hS
  have hB := hK.l34BlockFacts hcard hNH hLw hLW
  have h72 : ∀ Y : Subgroup (H ⧸ primeComplementCore (G := H) 3), Y ≤ d1X0 3 M H ⊓ K →
      Nat.card Y ∣ 72 := fun Y hY =>
    hK.card_dvd_seventytwo_of_l34 hI hd he hAK (hY.trans inf_le_left) (hY.trans inf_le_right)
  have hyp := h.asc81bHyp_twoCore_inf hmax hglob hS hPU
  have := hglob.simple
  have hHtop : H ≠ ⊤ :=
    CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top hglob.nonab h.maxTwoLocal_H.1
  have hKH : Open.IsKGroup ↥H :=
    isKGroup_of_catalogSimpleSections (catalogSimpleSections_of_isKProper hglob.kProper H hHtop)
  exact false_of_l34BlockFacts hNO h93 hL hKH hyp hLw
    (hNX H L h.maxTwoLocal_H hLw.le hLw.subnormal) hB h72

theorem D2Escape.false_of_l34_pu (hI : KFactL34Inner) (hNO : KFactL34NotOrthogonal)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (h : D2Escape 3 P M A H R) (hglob : AGLGlobal G)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsL34Index d)
    (hK : D2AlmostSimple 3 (H ⧸ primeComplementCore (G := H) 3) Rbar
      ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))) K)
    (he : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hAK : (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)) ≤ K)
    (hS : pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H)
    (hPU : ∀ C : Subgroup G, C ≤ pCoreOf 2 (H ⊓ M) → C ≠ ⊥ →
      (C.subgroupOf (pCoreOf 2 (H ⊓ M))).Characteristic → ¬ H ≤ Subgroup.normalizer (C : Set G)) :
    False :=
  CFSG.LocalAnalysis.RankThreeTheoremC.false_of_l34_pu3 hI hNO h93 (hD2 G hglob) h hglob hd hK he
    hAK hS hPU

end Final

theorem D2Escape.l34ResidueData (hI : KFactL34Inner) (hNO : KFactL34NotOrthogonal)
    (hSch : KFactCatalogSchreier) (hNS : KFactL34NormalizerSolvable)
    (h84 : Asc81bEightFour) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hS3 : D2PairStrongThree) {d : TauCeti.ValidLieTypeIndex} (hd : IsL34Index d) {G : Type}
    [Group G] [Finite G] (hglob : D2Global G) (hD1 : D1For G) {P : Sylow 3 G}
    {M A H R : Subgroup G} (hesc : D2Escape 3 P M A H R) (hmax : D2EscapeMax 3 P M R)
    (hβ : 3 ∈ GLBBetaFour G) {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hK : D2AlmostSimple 3 (H ⧸ primeComplementCore (G := H) 3) Rbar
      ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))) K)
    (he : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hAK : (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)) ≤ K) :
    pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H ∧
      Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) = H ⊓ M ∧
      ∃ C : Subgroup G, C ≤ pCoreOf 2 (H ⊓ M) ∧ C ≠ ⊥ ∧
        (C.subgroupOf (pCoreOf 2 (H ⊓ M))).Characteristic ∧
          H ≤ Subgroup.normalizer (C : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htwo : pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H := by
    intro htwo
    have hpr : AGLPair 3 M H R := hesc.toPair hglob.toAGLGlobal htwo
    have hNK := hNS d hd K he
      (((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))).subgroupOf K)
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv, hK.card_A])
    rw [← Subgroup.subgroupOf_normalizer_eq hAK, ← hK.eq_normalizer_of_l34 hI hd he hAK] at hNK
    exact hS3 G hglob hD1 P M A H R hesc hmax hβ hpr
      (hesc.stronglyEmbedded_of_pair hglob hβ hpr h84 (hD2.noXBlockFor hglob.toD1Global))
      (d2PerfectThreePrime_of_perfect_eq_bot
        (hK.perfect_eq_bot_of_isSolvable_inf hSch (isSolvable_inf_of_subgroupOf hNK)))
  by_cases hX : ∃ C : Subgroup G, C ≤ pCoreOf 2 (H ⊓ M) ∧ C ≠ ⊥ ∧
      (C.subgroupOf (pCoreOf 2 (H ⊓ M))).Characteristic ∧ H ≤ Subgroup.normalizer (C : Set G)
  · obtain ⟨C, hCU, hC1, hchar, hHC⟩ := hX
    have hNC : Subgroup.normalizer (C : Set G) = H :=
      hesc.maxTwoLocal_H.2 _
        ⟨C, hC1, (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 (H ⊓ M)).to_le hCU,
          rfl⟩ hHC
    have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := pCoreOf 2 (H ⊓ M)) (C.subgroupOf (pCoreOf 2 (H ⊓ M)))
    rw [Subgroup.map_subgroupOf_eq_of_le hCU] at h1
    have hNH : Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) ≤ H := h1.trans hNC.le
    have hmaxX := hK.eq_or_eq_top_of_l34 hI hd he hAK
    exact ⟨htwo, (inf_eq_right.mpr hNH).symm.trans (hesc.inf_normalizer_twoCore_inf hmaxX htwo),
      C, hCU, hC1, hchar, hHC⟩
  · exact (hesc.false_of_l34_pu hI hNO h93 hD2 hglob.toAGLGlobal hd hK he hAK htwo
      fun C hCU hC1 hchar hHC => hX ⟨C, hCU, hC1, hchar, hHC⟩).elim

end CFSG.AGLEmbeddingD2
