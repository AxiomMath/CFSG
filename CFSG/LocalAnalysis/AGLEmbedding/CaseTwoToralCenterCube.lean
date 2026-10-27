module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoToralCenterDefs
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoHexGroup
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFGroup
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPOdd
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReducedBAux
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoThreeA6Out
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoToralCenterClass
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoToralCenterOrbit
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalCount
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeDiag
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
import CFSG.Assembly.ComponentTypeDefs
import CFSG.Assembly.RankThreeEvenDefs
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G}

theorem D1PhaseThree.false_of_center_cube (h : D1PhaseThree 3 P M H R)
    (hBF : CitedBlockToralThreeCenter) (hBF2 : CitedBlockToralThreeCenterFix)
    (h85 : Asc81bEightFive) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hcyc : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ barM M (H ⊓ M) → ⁅V, V⁆ = V →
      ∀ Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Q ≤ V → IsPGroup 3 Q → IsCyclic Q)
    {z : G} (hzM : z ∈ M) (hz3 : z ^ 3 = 1) (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hin : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∈
        barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hrk : ∀ E : Subgroup G, E ≤ Subgroup.centralizer ({z} : Set G) → IsElemAbelian 3 E →
      Nat.card E ≤ 3 ^ 3)
    (hP4 : 4 ≤ Open.pRank 3 (P : Subgroup G))
    (hno6 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      Nat.card (Subgroup.center ↥(barM M L)) = 3 →
      ¬ Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)))
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) {ζ : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hζA : ζ ∈ barM M L)
    (hζC : ζ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1)
    (hVC : (∃ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅V, V⁆ = V ∧
        V ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
        V ≤ Subgroup.normalizer (barM M (pCoreOf 2 H) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∈ V) ∨
      ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ blockPL M (pCoreOf 2 H) L → ⁅V, V⁆ = V →
        Nat.Coprime 3 (Nat.card V))
    {R' : Subgroup G} (hR'P : R' ≤ P) (hR'z : R' ≤ Subgroup.centralizer ({z} : Set G))
    (hR'S : R' ≤ Subgroup.normalizer (pCoreOf 2 H : Set G))
    (hSyl : ∀ T : Subgroup G, T ≤ Subgroup.centralizer ({z} : Set G) → IsPGroup 3 T →
      Nat.card T ≤ Nat.card R')
    {w : G} (hwP : w ∈ (P : Subgroup G)) (hwo : orderOf w = 3) (hwz : Commute w z)
    (hwPc : ∀ g ∈ (P : Subgroup G), Commute w g)
    (hΩP : ∀ g ∈ (P : Subgroup G), (∀ h ∈ (P : Subgroup G), Commute g h) → g ^ 3 = 1 →
      g ∈ Subgroup.zpowers w)
    (hΩR : ∀ g ∈ R', (∀ h ∈ R', Commute g h) → g ^ 3 = 1 →
      g ∈ Subgroup.zpowers w ⊔ Subgroup.zpowers z)
    (hcube : ∃ y ∈ R', y ^ 3 = z) : False := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hPM : (P : Subgroup G) ≤ M := h.toD1Escape.sylow_le
  set zb := mk ⟨z, hzM⟩ with hzb
  have hz : IsPGroup 3 (Subgroup.zpowers z) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hz3)
  set A₀ := barM M L with hA₀
  set Cn := Subgroup.centralizer (A₀ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hCn
  have hnC : zb ∉ Cn := h.not_mem_centralizer_block hp hp2 hzM hz hCz hL
  obtain ⟨hZζ, -, -⟩ := D1PhaseThree.bf_center h hBF h85 h93 hD2 hcyc hzM hz3 hCz hL
    (hin L hL) (fun hh => hno6 L hL hh.1 hh.2) hζA hζC hζ3 hζ1
  set Pb := barM M (P : Subgroup G) with hPb
  have hmemPb : ∀ g (hg : g ∈ (P : Subgroup G)), mk ⟨g, hPM hg⟩ ∈ Pb := fun g hg =>
    ⟨⟨g, hPM hg⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  have hPbmem : ∀ x ∈ Pb, ∃ g, ∃ hg : g ∈ (P : Subgroup G), mk ⟨g, hPM hg⟩ = x := by
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨m, Subgroup.mem_subgroupOf.mp hm, rfl⟩
  have hinj : ∀ x y (hx : x ∈ (P : Subgroup G)) (hy : y ∈ (P : Subgroup G)),
      mk ⟨x, hPM hx⟩ = mk ⟨y, hPM hy⟩ → x = y := fun x y hx hy hxy =>
    eq_of_mk_eq_of_three P.isPGroup' hPM hx hy hxy
  have hmkmul : ∀ x y (hx : x ∈ M) (hy : y ∈ M),
      mk ⟨x * y, M.mul_mem hx hy⟩ = mk ⟨x, hx⟩ * mk ⟨y, hy⟩ := fun x y hx hy => by
    rw [← map_mul]; rfl
  have hPb3 : IsPGroup 3 Pb := (P.isPGroup'.comap_subtype (K := M)).map _
  have hpe : ∀ x ∈ Pb, ∃ k : ℕ, x ^ 3 ^ k = 1 := fun x hx => by
    obtain ⟨k, hk⟩ := hPb3 ⟨x, hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hPN : ∀ g ∈ (P : Subgroup G), g ∈ Subgroup.normalizer (L : Set G) := fun g hg =>
    D1PhaseThree.mem_normalizer_of_center h hBF h85 h93 hD2 hcyc hzM hz3 hCz hin hrk hno6 hL
      hζA hζC hζ3 hζ1 (hPM hg) (P.isPGroup'.to_le ((Subgroup.zpowers_le).mpr hg))
  have hPbN : Pb ≤ Subgroup.normalizer (A₀ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := hPbmem x hx
    exact mem_normalizer_barM (hPM hg) (hPN g hg)
  set Pbs : Sylow 3 (↥M ⧸ CFSG.pCore 2 ↥M) :=
    (P.subtype hPM).mapSurjective (QuotientGroup.mk'_surjective _) with hPbsdef
  have hPbs : (Pbs : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) = Pb := by
    rw [hPbsdef, Sylow.coe_mapSurjective, Sylow.coe_subtype]
    rfl
  have hζo : orderOf ζ = 3 := orderOf_eq_prime hζ3 hζ1
  have hPζ : ∀ g ∈ Pb, Commute g ζ := by
    intro g hg
    have hgN := hPbN hg
    have hgζ : g * ζ * g⁻¹ ∈ Subgroup.zpowers ζ := by
      refine hZζ _ ((Subgroup.mem_normalizer_iff.mp hgN ζ).mp hζA)
        ((Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer hgN) ζ).mp hζC) ?_
      rw [conj_pow, hζ3, mul_one, mul_inv_cancel]
    obtain ⟨k, hk⟩ := hpe g hg
    exact commute_of_mem_normalizer_zpowers_of_pow_prime_pow hp hζo
      (mem_normalizer_zpowers_of_mem_zpowers hgζ) hk
  have hζPb : ζ ∈ Pb := by
    have hζN : Subgroup.zpowers ζ ≤ Subgroup.normalizer (Pb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.mpr fun g hg => (hPζ g hg).eq)
    have hV := IsPGroup.to_sup_of_normal_left' hPb3
      (isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hζ3)) hζN
    have hmax := Pbs.is_maximal' (hPbs ▸ hV) (by rw [hPbs]; exact le_sup_left)
    rw [hPbs] at hmax
    exact hmax ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers ζ)
  set wb := mk ⟨w, hPM hwP⟩ with hwb
  have hζw : ζ ∈ Subgroup.zpowers wb := by
    obtain ⟨g, hg, hgζ⟩ := hPbmem ζ hζPb
    have hgc : ∀ h' ∈ (P : Subgroup G), Commute g h' := by
      intro h' hh'
      apply hinj _ _ (P.mul_mem hg hh') (P.mul_mem hh' hg)
      rw [hmkmul _ _ (hPM hg) (hPM hh'), hmkmul _ _ (hPM hh') (hPM hg), hgζ]
      exact (hPζ _ (hmemPb h' hh')).eq.symm
    have hg3 : g ^ 3 = 1 := by
      apply hinj _ _ (P.pow_mem hg 3) P.one_mem
      rw [show (⟨g ^ 3, hPM (P.pow_mem hg 3)⟩ : M) = ⟨g, hPM hg⟩ ^ 3 from rfl, map_pow, hgζ, hζ3]
      exact (map_one mk).symm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hΩP g hg hgc hg3)
    have : (⟨g, hPM hg⟩ : M) = ⟨w, hPM hwP⟩ ^ k := Subtype.ext (by simp [hk])
    rw [← hgζ, this, map_zpow]
    exact Subgroup.zpow_mem_zpowers _ k
  have hwo' : orderOf wb = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · have h1 : (⟨w, hPM hwP⟩ : M) ^ 3 = 1 := Subtype.ext (by
        simp [← hwo, pow_orderOf_eq_one])
      rw [hwb, ← map_pow, h1, map_one]
    · intro h1
      have := hinj w 1 hwP P.one_mem (by rw [← hwb, h1]; exact (map_one mk).symm)
      rw [this, orderOf_one] at hwo
      norm_num at hwo
  have hζeq : Subgroup.zpowers ζ = Subgroup.zpowers wb := Subgroup.eq_of_le_of_card_ge
    (Subgroup.zpowers_le.mpr hζw) (by rw [Nat.card_zpowers, Nat.card_zpowers, hζo, hwo'])
  have hwbZ : wb ∈ Subgroup.zpowers ζ := hζeq ▸ Subgroup.mem_zpowers wb
  have hwbA : wb ∈ A₀ := (Subgroup.zpowers_le.mpr hζA) hwbZ
  have hwbC : wb ∈ Cn := (Subgroup.zpowers_le.mpr hζC) hwbZ
  have hR'M : R' ≤ M := hR'P.trans hPM
  have hR'3 : IsPGroup 3 R' := P.isPGroup'.to_le hR'P
  set Xb := barM M R' with hXb
  have hXb3 : IsPGroup 3 Xb := (hR'3.comap_subtype (K := M)).map _
  have hXbPb : Xb ≤ Pb := barM_mono hR'P
  have hmemX : ∀ r (hr : r ∈ R'), mk ⟨r, hR'M hr⟩ ∈ Xb := fun r hr =>
    ⟨⟨r, hR'M hr⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
  have hXbmem : ∀ x ∈ Xb, ∃ r, ∃ hr : r ∈ R', mk ⟨r, hR'M hr⟩ = x := by
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨m, Subgroup.mem_subgroupOf.mp hm, rfl⟩
  have hXbS : Xb ≤ Subgroup.normalizer (barM M (pCoreOf 2 H) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := hXbmem x hx
    exact mem_normalizer_barM (hR'M hr) (hR'S hr)
  have hXbz : Xb ≤ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := hXbmem x hx
    have hrz := Subgroup.mem_centralizer_singleton_iff.mp (hR'z hr)
    rw [Subgroup.mem_centralizer_singleton_iff, hzb, ← hmkmul _ _ hzM (hR'M hr),
      ← hmkmul _ _ (hR'M hr) hzM]
    congr 1
    exact Subtype.ext hrz
  have hXbcard : Nat.card Xb = Nat.card R' := card_barM_of_isPGroup hp hp2 hR'M hR'3
  have hmaxX : ∀ Y : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsPGroup 3 Y →
      Y ≤ Subgroup.normalizer (A₀ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      Y ≤ Subgroup.normalizer (barM M (pCoreOf 2 H) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      Y ≤ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      Nat.card Y ≤ Nat.card Xb := by
    intro Y hY3 _ _ hYz
    rw [hXbcard]
    exact card_le_of_le_centralizer_barM_pgroup hzM hz3 hSyl hYz hY3
  have hzb3 : zb ^ 3 = 1 := by
    have h1 : (⟨z, hzM⟩ : M) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
    rw [hzb, ← map_pow, h1, map_one]
  have hKeq := h.toD1Escape.inf_eq_inf_normalizer_twoCore
  have hcycL : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ blockPL M (pCoreOf 2 H) L →
      ⁅V, V⁆ = V → ∀ Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Q ≤ V → IsPGroup 3 Q →
        IsCyclic Q := by
    intro V hV hVp
    refine hcyc V (hV.trans (barM_mono ?_)) hVp
    rw [hKeq]
    exact le_inf (inf_le_right.trans hL.le) inf_le_left
  obtain ⟨he, hf⟩ := hBF2 G M (pCoreOf 2 H) L h.isKGroup.1 h.asc81bHyp hL (h.nineThree h93 hL)
    (h.nineThree_not_one h85 hD2 hL).1 (h.not_isSylowTwoOf_inf h85 hD2 hL) hcycL
    (fun hh => hno6 L hL hh.1 hh.2) ζ hζA hζC hζ3 hζ1 zb (hin L hL) hzb3 hnC
    (fun l hl hl' => h.fixed_le_barM_normalizer_inf hp hp2 hzM hz hCz l hl hl') hVC
  obtain ⟨r, hrA, -, hrc, hrn⟩ := exists_rep_of_mem_sup (hin L hL) hzb3 hnC
  obtain ⟨hr3, hrfix⟩ := he r hrA hrc
  have hXbN : Xb ≤ Subgroup.normalizer (A₀ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := hXbPb.trans hPbN
  have hX3e : ∀ x ∈ Xb, ∃ k : ℕ, x ^ 3 ^ k = 1 := fun x hx => by
    obtain ⟨k, hk⟩ := hXb3 ⟨x, hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hrX : ∀ x ∈ Xb, x * r = r * x := fun x hx =>
    hrfix x (hXbN hx) (hXbS hx) (Subgroup.mem_centralizer_singleton_iff.mp (hXbz hx))
      (hX3e x hx)
  have hrz : r ∈ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    d1_mem_centralizer_of_rep hrA hrc
  have hrN : Subgroup.zpowers r ≤ Subgroup.normalizer (Xb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun x hx => hrX x hx)
  have hXr3 : IsPGroup 3 (Xb ⊔ Subgroup.zpowers r : Subgroup _) :=
    IsPGroup.to_sup_of_normal_left' hXb3 (isPGroup_zpowers_of_pow_eq_one (k := 1)
      (by simpa using hr3)) hrN
  have hXrz : Xb ⊔ Subgroup.zpowers r ≤
      Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    sup_le hXbz ((Subgroup.zpowers_le).mpr hrz)
  have hXrc : Nat.card (Xb ⊔ Subgroup.zpowers r : Subgroup _) ≤ Nat.card Xb := by
    rw [hXbcard]
    exact card_le_of_le_centralizer_barM_pgroup hzM hz3 hSyl hXrz hXr3
  have hXreq : Xb = Xb ⊔ Subgroup.zpowers r := Subgroup.eq_of_le_of_card_ge le_sup_left hXrc
  have hrXb : r ∈ Xb := hXreq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers r)
  obtain ⟨r₀, hr₀R, rfl⟩ := hXbmem _ hrXb
  have hr₀c : ∀ s ∈ R', Commute r₀ s := by
    intro s hs
    apply hinj _ _ (P.mul_mem (hR'P hr₀R) (hR'P hs)) (P.mul_mem (hR'P hs) (hR'P hr₀R))
    rw [hmkmul _ _ (hR'M hr₀R) (hR'M hs), hmkmul _ _ (hR'M hs) (hR'M hr₀R)]
    exact (hrX _ (hmemX s hs)).symm
  have hr₀3 : r₀ ^ 3 = 1 := by
    apply hinj _ _ (P.pow_mem (hR'P hr₀R) 3) P.one_mem
    rw [show (⟨r₀ ^ 3, hPM (P.pow_mem (hR'P hr₀R) 3)⟩ : M) = ⟨r₀, hR'M hr₀R⟩ ^ 3 from rfl,
      map_pow, hr3]
    exact (map_one mk).symm
  obtain ⟨u, hu, v, hv, huv⟩ := (mem_zpowers_sup_zpowers_iff hwz).mp (hΩR r₀ hr₀R hr₀c hr₀3)
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  have himg : mk ⟨r₀, hR'M hr₀R⟩ = wb ^ i * zb ^ j := by
    have e1 : (⟨r₀, hR'M hr₀R⟩ : M) = ⟨w, hPM hwP⟩ ^ i * ⟨z, hzM⟩ ^ j :=
      Subtype.ext (by simp [← huv])
    rw [e1, map_mul, map_zpow, map_zpow]
  have hzjA : zb ^ j ∈ A₀ := by
    have h1 : (wb ^ i)⁻¹ * mk ⟨r₀, hR'M hr₀R⟩ ∈ A₀ :=
      A₀.mul_mem (A₀.inv_mem (A₀.zpow_mem hwbA i)) hrA
    rwa [himg, ← mul_assoc, inv_mul_cancel, one_mul] at h1
  have hzo : orderOf zb = 3 := orderOf_eq_prime hzb3 (fun h1 => hnC (h1 ▸ Cn.one_mem))
  by_cases hzj : zb ^ j = 1
  · apply hrn
    rw [himg, hzj, mul_one]
    exact Cn.zpow_mem hwbC i
  have hzjo : orderOf (zb ^ j) = 3 := by
    refine orderOf_eq_prime ?_ hzj
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzb3, one_zpow]
  have heq : Subgroup.zpowers (zb ^ j) = Subgroup.zpowers zb :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (Subgroup.zpow_mem_zpowers zb j))
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hzo, hzjo])
  have hzbA : zb ∈ A₀ :=
    (Subgroup.zpowers_le.mpr hzjA) (heq ▸ Subgroup.mem_zpowers zb : zb ∈ Subgroup.zpowers (zb ^ j))
  rcases hf hzbA with hexp | hcen
  · obtain ⟨y, hyR, hy3⟩ := hcube
    have h1 := hexp _ (hXbN (hmemX y hyR)) (hXbS (hmemX y hyR))
      (Subgroup.mem_centralizer_singleton_iff.mp (hXbz (hmemX y hyR))) (hX3e _ (hmemX y hyR))
    apply hnC
    have h2 : mk ⟨y, hR'M hyR⟩ ^ 3 = zb := by
      rw [hzb, ← map_pow]
      congr 1
      exact Subtype.ext (by simpa using hy3)
    rwa [h2] at h1
  · have hmaxP : ∀ Z : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsPGroup 3 Z →
        Z ≤ Subgroup.normalizer (A₀ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
        Z ≤ Subgroup.normalizer (barM M (pCoreOf 2 H) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
        Z ≤ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
        Nat.card Z ≤ Nat.card Xb := hmaxX
    have hall : ∀ g ∈ (P : Subgroup G), g * z * g⁻¹ * z⁻¹ ∈ Subgroup.zpowers w := by
      intro g hg
      have hgN := hPbN (hmemPb g hg)
      set gb := mk ⟨g, hPM hg⟩ with hgb
      have hC := hcen Pb Xb hPb3 hPbN hXbPb hXbS hXbz hmaxP gb (hmemPb g hg)
      have hA : gb * zb * gb⁻¹ * zb⁻¹ ∈ A₀ :=
        A₀.mul_mem ((Subgroup.mem_normalizer_iff.mp hgN zb).mp hzbA) (A₀.inv_mem hzbA)
      have hcz : Commute (gb * zb * gb⁻¹ * zb⁻¹) zb :=
        (Subgroup.mem_centralizer_iff.mp hC zb hzbA).symm
      have h3 : (gb * zb * gb⁻¹ * zb⁻¹) ^ 3 = 1 := by
        have e1 : gb * zb * gb⁻¹ = (gb * zb * gb⁻¹ * zb⁻¹) * zb := by group
        have e2 : (gb * zb * gb⁻¹) ^ 3 = 1 := by
          rw [conj_pow, hzb3, mul_one, mul_inv_cancel]
        rw [e1, hcz.mul_pow, hzb3, mul_one] at e2
        exact e2
      have hmem : gb * zb * gb⁻¹ * zb⁻¹ ∈ Subgroup.zpowers wb :=
        hζeq ▸ hZζ _ hA hC h3
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hzP' : z ∈ (P : Subgroup G) := hR'P (hcube.choose_spec.2 ▸
        R'.pow_mem hcube.choose_spec.1 3)
      have hc : g * z * g⁻¹ * z⁻¹ ∈ (P : Subgroup G) :=
        P.mul_mem (P.mul_mem (P.mul_mem hg hzP') (P.inv_mem hg)) (P.inv_mem hzP')
      have hwk : w ^ k ∈ (P : Subgroup G) := P.zpow_mem hwP k
      have heq2 : g * z * g⁻¹ * z⁻¹ = w ^ k := by
        apply hinj _ _ hc hwk
        have e3 : mk ⟨g * z * g⁻¹ * z⁻¹, hPM hc⟩ = gb * zb * gb⁻¹ * zb⁻¹ := by
          rw [hgb, hzb, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
          rfl
        have e4 : mk ⟨w ^ k, hPM hwk⟩ = wb ^ k := by
          rw [hwb, ← map_zpow]
          rfl
        rw [e3, e4, hk]
      rw [heq2]
      exact Subgroup.zpow_mem_zpowers w k
    obtain ⟨g, hg, hgz⟩ := d1_exists_conj_not_mem_zpowers hz3 hwo hwPc hrk hP4
    exact hgz (hall g hg)

end CFSG.AGLEmbedding
