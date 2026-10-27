module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLK0
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallRankOneLinTwo
import CFSG.LocalAnalysis.AGLEmbedding.OneLieTorus
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosA
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosT
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPoszAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLHatAssembly

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.inf_comm_of_liftX_comm (hd : D1OneSmallData p P M H R Rbar K)
    (hXab : ∀ a ∈ d1LiftX p H R K, ∀ b ∈ d1LiftX p H R K, a * b = b * a) :
    ∀ a ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K,
      ∀ b ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K, a * b = b * a := by
  intro a ha b hb
  rw [← hd.cfg.map_d1LiftX_eq_inf] at ha hb
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  have h5 : a' * b' = b' * a' := Subtype.ext (by
    simpa using hXab _ (Subgroup.mem_subgroupOf.mp ha') _ (Subgroup.mem_subgroupOf.mp hb'))
  rw [← map_mul, ← map_mul, h5]

theorem D1OneSmallData.splPair_facts (hFi : KFactSPLNotFi22) (hUP : KFactUPrimeSmall)
    (hSTO : KFactSmallThreeOrders) (hKU2 : KFactUnitarySylowStructure)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hLA : IsSmallLinTwo p K ∨ (p = 3 ∧ IsAltTwoP 3 K)) (hSP : D1CzSP p z)
    (hVK : d1MapPCore p M H ⊓ K ≠ ⊥)
    (hVC : d1MapPCore p M H ⊓
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) = ⊥)
    (hN : ∀ (P' : Sylow p G) (Pbar : Sylow p (D1CzQuot p z)) (KC : Subgroup (D1CzQuot p z)),
      D1ReducedCentralizer p P' M z Pbar KC → R ≤ (P' : Subgroup G) → (P' : Subgroup G) ≤ M →
      Nat.card ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC : Subgroup _) = p ^ 6 ∧
      ((d1LiftX p H R K).subgroupOf (Subgroup.centralizer ({z} : Set G))).map
          (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)) =
        centerOf ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC)) :
    D1PhaseThree p P M H R ∧ pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥ ∧
      d1MapPCore p M H ≤ K ∧
      Subgroup.centralizer (d1MapPCore p M H : Set (H ⧸ primeComplementCore (G := H) p)) ≤
        ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) ⊔
          Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) ∧
      ∀ a ∈ d1LiftX p H R K, ∀ b ∈ d1LiftX p H R K, a * b = b * a := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hspl : IsSPLFamily p K := by
    rcases hLA with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  have hF5 : ¬ (p = 5 ∧ IsFi22 K) := by
    rintro ⟨rfl, hF⟩
    exact hFi K hspl hF
  have hL34 : ¬ (p = 3 ∧ IsLinThreeFour K) := by
    rintro ⟨rfl, hL⟩
    exact not_linThreeFour_of_spl hSTO hspl hL
  have h3 := hd.toPhaseThree hUP hL34 hF5
  obtain ⟨T₁, hT₁, hF⟩ := hd.pair_oneLieFacts hLA
  have hKn : K.Normal := hd.cfg.red.normal_of_rankOne hd.comp hd.noncyclic
  obtain ⟨hWp, hWR, hWn, -, hWiff⟩ := hd.d1MapPCore_facts h3 h84 hD2
  obtain ⟨hVT, hNV⟩ := hd.inf_ne_bot_and_normalizer_le h3 h84 hD2 hVK
  have hY := hWiff.mpr hVT
  have hWK : d1MapPCore p M H ≤ K := (le_of_inf_centralizer_eq_bot hp hd.center T₁ hT₁ hF hWp
    (le_sup_of_oneLieFacts hd.center T₁ hT₁ hF hWp hWR hWn) hWn hVC).trans inf_le_right
  set C := Subgroup.centralizer ({z} : Set G) with hCdef
  set mk := QuotientGroup.mk' (primeComplementCore (G := C) p) with hmk
  have hOC := primeComplementCore_coprime (G := C) p
  have hRC' : R ≤ C := hd.le_centralizer_czElt hz
  obtain ⟨P', Pbar, KC, -, hP'M, hRP', hRC⟩ := hd.exists_reducedCentralizer hz hSP
  obtain ⟨-, hXeq⟩ := hN P' Pbar KC hRC hRP' hP'M
  have hRCp : IsPGroup p (R.subgroupOf C) := hd.cfg.ext.isPGroup.comap_subtype
  have hXab : ∀ a ∈ d1LiftX p H R K, ∀ b ∈ d1LiftX p H R K, a * b = b * a := by
    intro a ha b hb
    have haC : a ∈ C := hRC' (d1LiftX_le p H R K ha)
    have hbC : b ∈ C := hRC' (d1LiftX_le p H R K hb)
    have hma : mk ⟨a, haC⟩ ∈ ((d1LiftX p H R K).subgroupOf C).map mk :=
      ⟨⟨a, haC⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    have hmb : mk ⟨b, hbC⟩ ∈ ((d1LiftX p H R K).subgroupOf C).map mk :=
      ⟨⟨b, hbC⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
    rw [hXeq] at hma hmb
    have hc : mk ⟨a, haC⟩ * mk ⟨b, hbC⟩ = mk ⟨b, hbC⟩ * mk ⟨a, haC⟩ :=
      Subgroup.mem_centralizer_iff.mp hmb.2 _ hma.1
    have haR : (⟨a, haC⟩ : C) ∈ R.subgroupOf C := d1LiftX_le p H R K ha
    have hbR : (⟨b, hbC⟩ : C) ∈ R.subgroupOf C := d1LiftX_le p H R K hb
    have h5 := eq_of_mk_eq_of_isPGroup hp _ hOC hRCp ((R.subgroupOf C).mul_mem haR hbR)
      ((R.subgroupOf C).mul_mem hbR haR) (by rw [map_mul, map_mul, hc])
    simpa using congrArg Subtype.val h5
  have hTab := hd.inf_comm_of_liftX_comm hXab
  have hnZ : ¬ D1SmallPosZ p M H Rbar K := by
    rintro ⟨-, hne⟩
    apply hne
    refine le_antisymm inf_le_left fun a ha => ⟨ha, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr fun b hb => hTab b hb a ha
  exact ⟨h3, hY, hWK, hd.centralizer_d1MapPCore_le hKU2 hT₁ hF hVT hNV hnZ, hXab⟩

theorem pair_inf_eq (hd : D1OneSmallData p P M H R Rbar K)
    (hLA : IsSmallLinTwo p K ∨ (p = 3 ∧ IsAltTwoP 3 K))
    (hVT : d1MapPCore p M H ⊓
      ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) ≠ ⊥)
    (hNV : K ⊓ Subgroup.normalizer (((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup _) : Set (H ⧸ primeComplementCore (G := H) p)) ≤
      Subgroup.normalizer ((d1MapPCore p M H ⊓
        ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) : Subgroup _) :
          Set (H ⧸ primeComplementCore (G := H) p)))
    (hTab : ∀ a ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K,
      ∀ b ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K, a * b = b * a) :
    d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨T₁, hT₁, -⟩ := hd.exists_sylow
  have hdata : SmallRankOneData p K T₁ := by
    rcases hLA with h | ⟨rfl, h⟩
    · exact smallRankOneData_of_isSmallLinTwo hd.cfg.red.ne_two h T₁
    · exact smallRankOneData_of_altSix h T₁
  set V := d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)
    with hVdef
  have hVle : V ≤ (T₁ : Subgroup K).map K.subtype := hT₁ ▸ inf_le_right
  have hVK : V ≤ K := hVle.trans (Subgroup.map_subtype_le _)
  have hVmap : (V.subgroupOf K).map K.subtype = V := Subgroup.map_subgroupOf_eq_of_le hVK
  have hV'T : V.subgroupOf K ≤ T₁ := by
    intro v hv
    obtain ⟨t, ht, htv⟩ := hVle (Subgroup.mem_subgroupOf.mp hv)
    rwa [← Subtype.ext htv]
  have hV'1 : V.subgroupOf K ≠ ⊥ := by
    intro hbot
    apply hVT
    rw [← hVmap, hbot, Subgroup.map_bot]
  have hNV' : Subgroup.normalizer ((T₁ : Subgroup K) : Set K) ≤
      Subgroup.normalizer ((V.subgroupOf K : Subgroup K) : Set K) := fun n hn =>
    Subgroup.le_normalizer_comap K.subtype ((hT₁ ▸ hNV) (coe_mem_normalizer_map hn))
  have hTcen : centerOf (T₁ : Subgroup K) = T₁ := by
    refine le_antisymm inf_le_left fun a ha => Subgroup.mem_inf.mpr ⟨ha, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hmb : (b : H ⧸ primeComplementCore (G := H) p) ∈
        (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K := hT₁ ▸ ⟨b, hb, rfl⟩
    have hma : (a : H ⧸ primeComplementCore (G := H) p) ∈
        (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K := hT₁ ▸ ⟨a, ha, rfl⟩
    exact Subtype.ext (hTab _ hmb _ hma)
  have hV'eq : V.subgroupOf K = T₁ := by
    rcases hdata.invariant _ hV'T hV'1 hNV' with h | ⟨h, -⟩
    · exact h
    · rw [h, hTcen]
  rw [← hT₁, ← hVmap, hV'eq]

theorem pair_liftX_le (h3 : D1PhaseThree p P M H R) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hd : D1OneSmallData p P M H R Rbar K)
    (hVT : d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) :
    d1LiftX p H R K ≤ pCorePreimage p M := by
  have hp := hd.cfg.red.prime
  have hRp : IsPGroup p (R.subgroupOf H) := hd.cfg.ext.isPGroup.comap_subtype
  have hO := primeComplementCore_coprime (G := H) p
  set mk := QuotientGroup.mk' (primeComplementCore (G := H) p) with hmk
  set Y := pCorePreimage p M with hYdef
  set Q := pCoreOf 2 M with hQdef
  have hYeq : (R ⊓ Y) ⊔ Q = Y := h3.inf_sup_twoCore_eq h84 hD2
  have hYM : Y ≤ M := pCorePreimage_le p M
  rintro _ ⟨x, ⟨hxR, hxK⟩, rfl⟩
  have hxT : mk x ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :=
    ⟨hd.cfg.rbar ▸ ⟨x, hxR, rfl⟩, hxK⟩
  rw [← hVT] at hxT
  obtain ⟨y, hyY, hyx⟩ := hxT.1
  have hyY' : (y : G) ∈ (((R ⊓ Y) ⊔ Q : Subgroup G) : Set G) := by
    rw [SetLike.mem_coe, hYeq]
    exact hyY
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (R ⊓ Y) Q
    ((inf_le_right.trans hYM).trans (localGroup_le_normalizer_pCoreOf 2 M))] at hyY'
  obtain ⟨r, hr, q, hq, hrq⟩ := hyY'
  have hrH : r ∈ H := hd.cfg.ext.le_H hr.1
  have hqH : q ∈ H := h3.twoCore_M_le_glbPrimeCore.trans (glbPrimeCore_le p H) hq
  have hq1 : mk ⟨q, hqH⟩ = 1 := by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', ← glbPrimeCore_subgroupOf]
    exact Subgroup.mem_subgroupOf.mpr (h3.twoCore_M_le_glbPrimeCore hq)
  have hyrq : y = ⟨r, hrH⟩ * ⟨q, hqH⟩ := Subtype.ext hrq.symm
  have hrx : mk ⟨r, hrH⟩ = mk x := by
    rw [← hyx, hyrq, map_mul, hq1, mul_one]
  have h5 := eq_of_mk_eq_of_isPGroup hp _ hO hRp (Subgroup.mem_subgroupOf.mpr hr.1) hxR hrx
  rw [← h5]
  exact hr.2

theorem pair_inf_pCorePreimage (h3 : D1PhaseThree p P M H R) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hd : D1OneSmallData p P M H R Rbar K) (hWK : d1MapPCore p M H ≤ K)
    (hVT : d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) :
    R ⊓ pCorePreimage p M = d1LiftX p H R K := by
  refine le_antisymm ?_ (le_inf (d1LiftX_le p H R K) (pair_liftX_le h3 h84 hD2 hd hVT))
  rintro r ⟨hrR, hrY⟩
  have hrH : r ∈ H := hd.cfg.ext.le_H hrR
  exact ⟨⟨r, hrH⟩, ⟨Subgroup.mem_subgroupOf.mpr hrR, hWK ⟨⟨r, hrH⟩, hrY, rfl⟩⟩, rfl⟩

theorem pair_pCorePreimage_facts (hFi : KFactSPLNotFi22) (hUP : KFactUPrimeSmall)
    (hSTO : KFactSmallThreeOrders) (hKU2 : KFactUnitarySylowStructure)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hLA : IsSmallLinTwo p K ∨ (p = 3 ∧ IsAltTwoP 3 K)) (hSP : D1CzSP p z)
    (hVK : d1MapPCore p M H ⊓ K ≠ ⊥)
    (hVC : d1MapPCore p M H ⊓
      Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) = ⊥)
    (hN : ∀ (P' : Sylow p G) (Pbar : Sylow p (D1CzQuot p z)) (KC : Subgroup (D1CzQuot p z)),
      D1ReducedCentralizer p P' M z Pbar KC → R ≤ (P' : Subgroup G) → (P' : Subgroup G) ≤ M →
      Nat.card ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC : Subgroup _) = p ^ 6 ∧
      ((d1LiftX p H R K).subgroupOf (Subgroup.centralizer ({z} : Set G))).map
          (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p)) =
        centerOf ((Pbar : Subgroup (D1CzQuot p z)) ⊓ KC)) :
    d1LiftX p H R K ≤ pCorePreimage p M ∧
      d1LiftX p H R K ⊔ pCoreOf 2 M = pCorePreimage p M := by
  obtain ⟨h3, -, hWK, -, hXab⟩ := hd.splPair_facts hFi hUP hSTO hKU2 h84 hD2 hz hLA hSP hVK hVC hN
  obtain ⟨hVT, hNV⟩ := hd.inf_ne_bot_and_normalizer_le h3 h84 hD2 hVK
  have hTab := hd.inf_comm_of_liftX_comm hXab
  have hVeq := pair_inf_eq hd hLA hVT hNV hTab
  refine ⟨pair_liftX_le h3 h84 hD2 hd hVeq, ?_⟩
  rw [← pair_inf_pCorePreimage h3 h84 hD2 hd hWK hVeq]
  exact h3.inf_sup_twoCore_eq h84 hD2

end CFSG.AGLEmbedding
