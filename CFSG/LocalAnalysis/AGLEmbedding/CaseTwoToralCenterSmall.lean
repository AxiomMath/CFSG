module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoToralCenterDefs
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFGroup
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPOdd
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReducedBAux
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoThreeA6Out
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoToralCenterClass
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoToralCenterOrbit
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeDiag
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
import CFSG.Assembly.ComponentTypeDefs
import CFSG.Assembly.RankThreeEvenDefs
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G}

theorem D1PhaseThree.false_of_center_small (h : D1PhaseThree 3 P M H R)
    (hBF : CitedBlockToralThreeCenter) (h85 : Asc81bEightFive) (h93 : Asc81bNineThree)
    (hD2 : D1NoXBlock)
    (hcyc : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ barM M (H ⊓ M) → ⁅V, V⁆ = V →
      ∀ Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Q ≤ V → IsPGroup 3 Q → IsCyclic Q)
    {z : G} (hzM : z ∈ M) (hz3 : z ^ 3 = 1) (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hin : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∈
        barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hrk : ∀ E : Subgroup G, E ≤ Subgroup.centralizer ({z} : Set G) → IsElemAbelian 3 E →
      Nat.card E ≤ 3 ^ 3)
    (hno6 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      Nat.card (Subgroup.center ↥(barM M L)) = 3 →
      ¬ Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)))
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) {ζ : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hζA : ζ ∈ barM M L)
    (hζC : ζ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1)
    {R' : Subgroup G} (hR'P : R' ≤ P) (hR'z : R' ≤ Subgroup.centralizer ({z} : Set G))
    (hR'S : R' ≤ Subgroup.normalizer (pCoreOf 2 H : Set G))
    (hSyl : ∀ T : Subgroup G, T ≤ Subgroup.centralizer ({z} : Set G) → IsPGroup 3 T →
      Nat.card T ≤ Nat.card R')
    {w : G} (hwP : w ∈ (P : Subgroup G)) (hwo : orderOf w = 3) (hwz : Commute w z)
    (hΩP : ∀ g ∈ (P : Subgroup G), (∀ h ∈ (P : Subgroup G), Commute g h) → g ^ 3 = 1 →
      g ∈ Subgroup.zpowers w)
    (hΩR : ∀ g ∈ R', (∀ h ∈ R', Commute g h) → g ^ 3 = 1 →
      g ∈ Subgroup.zpowers w ⊔ Subgroup.zpowers z)
    (hR81 : Nat.card R' ≤ 3 ^ 4) {a b : G} (ha : a ∈ R') (hb : b ∈ R') (hab : a * b ≠ b * a) :
    False := by
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
  obtain ⟨hZζ, -, hXf⟩ := D1PhaseThree.bf_center h hBF h85 h93 hD2 hcyc hzM hz3 hCz hL
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
  obtain ⟨hXC, hXe⟩ := hXf Xb hXb3 (hXbPb.trans hPbN) hXbS hXbz (hXbcard ▸ hR81) hmaxX
  have hab' : mk ⟨a, hR'M ha⟩ * mk ⟨b, hR'M hb⟩ ≠ mk ⟨b, hR'M hb⟩ * mk ⟨a, hR'M ha⟩ := by
    intro he
    apply hab
    apply hinj _ _ (P.mul_mem (hR'P ha) (hR'P hb)) (P.mul_mem (hR'P hb) (hR'P ha))
    rw [hmkmul _ _ (hR'M ha) (hR'M hb), hmkmul _ _ (hR'M hb) (hR'M ha)]
    exact he
  obtain ⟨e, heX, he1, he3, hecent⟩ :=
    exists_mem_commutator_center hXb3 (hmemX a ha) (hmemX b hb) hab'
  have hcomm_le : ⁅Xb, Xb⁆ ≤ Xb := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [commutatorElement_def]
    exact Xb.mul_mem (Xb.mul_mem (Xb.mul_mem hg₁ hg₂) (Xb.inv_mem hg₁)) (Xb.inv_mem hg₂)
  obtain ⟨e₀, he₀R, rfl⟩ := hXbmem e (hcomm_le heX)
  have he₀c : ∀ r ∈ R', Commute e₀ r := by
    intro r hr
    apply hinj _ _ (P.mul_mem (hR'P he₀R) (hR'P hr)) (P.mul_mem (hR'P hr) (hR'P he₀R))
    rw [hmkmul _ _ (hR'M he₀R) (hR'M hr), hmkmul _ _ (hR'M hr) (hR'M he₀R)]
    exact (hecent _ (hmemX r hr)).eq
  have he₀3 : e₀ ^ 3 = 1 := by
    apply hinj _ _ (P.pow_mem (hR'P he₀R) 3) P.one_mem
    rw [show (⟨e₀ ^ 3, hPM (P.pow_mem (hR'P he₀R) 3)⟩ : M) = ⟨e₀, hR'M he₀R⟩ ^ 3 from rfl,
      map_pow, he3]
    exact (map_one mk).symm
  obtain ⟨u, hu, v, hv, huv⟩ := (mem_zpowers_sup_zpowers_iff hwz).mp (hΩR e₀ he₀R he₀c he₀3)
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  have hzbj : zb ^ j ∈ Cn := by
    have himg : mk ⟨e₀, hR'M he₀R⟩ = wb ^ i * zb ^ j := by
      have e1 : (⟨e₀, hR'M he₀R⟩ : M) = ⟨w, hPM hwP⟩ ^ i * ⟨z, hzM⟩ ^ j :=
        Subtype.ext (by simp [← huv])
      rw [e1, map_mul, map_zpow, map_zpow]
    have h1 : wb ^ i * zb ^ j ∈ Cn := himg ▸ hXC heX
    have h2 : (wb ^ i)⁻¹ ∈ Cn := Cn.inv_mem (Cn.zpow_mem hwbC i)
    have h3 := Cn.mul_mem h2 h1
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at h3
  have hzb3 : zb ^ 3 = 1 := by
    have h1 : (⟨z, hzM⟩ : M) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
    rw [hzb, ← map_pow, h1, map_one]
  by_cases hzj : zb ^ j = 1
  · apply he1
    have himg : mk ⟨e₀, hR'M he₀R⟩ = wb ^ i := by
      have e1 : (⟨e₀, hR'M he₀R⟩ : M) = ⟨w, hPM hwP⟩ ^ i * ⟨z, hzM⟩ ^ j :=
        Subtype.ext (by simp [← huv])
      rw [e1, map_mul, map_zpow, map_zpow, ← hzb, hzj, mul_one]
    refine hXe _ heX ?_ he3
    rw [himg]
    exact A₀.zpow_mem hwbA i
  · apply hnC
    have hzo : orderOf zb = 3 := orderOf_eq_prime hzb3 (fun h1 => hnC (h1 ▸ Cn.one_mem))
    have hzjo : orderOf (zb ^ j) = 3 := by
      refine orderOf_eq_prime ?_ hzj
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzb3, one_zpow]
    have heq : Subgroup.zpowers (zb ^ j) = Subgroup.zpowers zb :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (Subgroup.zpow_mem_zpowers zb j))
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hzo, hzjo])
    have hzmem : zb ∈ Subgroup.zpowers (zb ^ j) := heq ▸ Subgroup.mem_zpowers zb
    exact (Subgroup.zpowers_le.mpr hzbj) hzmem

end CFSG.AGLEmbedding
