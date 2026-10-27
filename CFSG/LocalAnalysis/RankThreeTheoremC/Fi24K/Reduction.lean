module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoInf
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.AGLEmbedding.RankTools
public import CFSG.LocalAnalysis.SectionRank.TwoGenerators

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem pRank_zpowers_eq_one {p : ℕ} [Fact p.Prime] {Y : Type*} [Group Y] [Finite Y]
    {x : Y} (hx : orderOf x = p) : CFSG.Open.pRank p (Subgroup.zpowers x) = 1 := by
  have hp : p.Prime := Fact.out
  have h1 : 1 ≤ CFSG.Open.pRank p (Subgroup.zpowers x) := by
    refine CFSG.SectionRank.le_pRank hp.one_lt le_rfl
      (CFSG.Open.isElemAbelian_zpowers (by rw [← hx]; exact pow_orderOf_eq_one x)) ?_
    rw [Nat.card_zpowers, hx, pow_one]
  exact le_antisymm (CFSG.SectionRank.pRank_le_one_of_isCyclic hp inferInstance) h1

theorem sylow_le_inf_sup_inf_centralizer_of_not_dvd {p : ℕ} [Fact p.Prime] {Y : Type}
    [Group Y] [Finite Y] {K : Subgroup Y} [K.Normal] (R : Sylow p Y)
    (hZ : K ⊓ centralizer (K : Set Y) = ⊥) (hout : ¬ p ∣ Nat.card (Outer K)) :
    (R : Subgroup Y) ≤ ((R : Subgroup Y) ⊓ K) ⊔
      ((R : Subgroup Y) ⊓ centralizer (K : Set Y)) := by
  have hp : p.Prime := Fact.out
  intro r hr
  obtain ⟨n, hn⟩ := R.isPGroup' ⟨r, hr⟩
  have hrn : r ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hkey : ∃ k ∈ K, k⁻¹ * r ∈ centralizer (K : Set Y) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.exists_inv_mul_mem_centralizer_of_not_dvd
      hout hrn
  obtain ⟨k, hkK, hc⟩ := hkey
  set c := k⁻¹ * r with hcdef
  have hrkc : r = k * c := by rw [hcdef, mul_inv_cancel_left]
  have hkc : Commute k c := mem_centralizer_iff.mp hc k hkK
  have hkn : k ^ p ^ n = 1 := by
    have h1 : (k * c) ^ p ^ n = k ^ p ^ n * c ^ p ^ n := hkc.mul_pow _
    rw [← hrkc, hrn] at h1
    have hmem : k ^ p ^ n ∈ K ⊓ centralizer (K : Set Y) := by
      refine mem_inf.mpr ⟨pow_mem hkK _, ?_⟩
      rw [eq_inv_of_mul_eq_one_left h1.symm]
      exact (centralizer (K : Set Y)).inv_mem ((centralizer (K : Set Y)).pow_mem hc _)
    rw [hZ] at hmem
    exact hmem
  have hcT : ∀ t ∈ K, c * t = t * c := fun t ht => (mem_centralizer_iff.mp hc t ht).symm
  have hconj : ∀ t ∈ K, k * t * k⁻¹ = r * t * r⁻¹ := fun t ht => by
    rw [hrkc]
    calc k * t * k⁻¹ = k * (t * c) * c⁻¹ * k⁻¹ := by group
      _ = k * (c * t) * c⁻¹ * k⁻¹ := by rw [hcT t ht]
      _ = k * c * t * (k * c)⁻¹ := by group
  have hkN : k ∈ normalizer (((R : Subgroup Y) ⊓ K : Subgroup Y) : Set Y) := by
    rw [mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      obtain ⟨htR, htK⟩ := mem_inf.mp ht
      rw [hconj t htK]
      exact mem_inf.mpr ⟨R.toSubgroup.mul_mem (R.toSubgroup.mul_mem hr htR)
        (R.toSubgroup.inv_mem hr), ‹K.Normal›.conj_mem t htK r⟩
    · intro ht
      obtain ⟨htR, htK⟩ := mem_inf.mp ht
      have htK' : t ∈ K := by
        have h := ‹K.Normal›.conj_mem _ htK k⁻¹
        rwa [show k⁻¹ * (k * t * k⁻¹) * k⁻¹⁻¹ = t by group] at h
      rw [hconj t htK'] at htR
      refine mem_inf.mpr ⟨?_, htK'⟩
      have h := R.toSubgroup.mul_mem (R.toSubgroup.mul_mem (R.toSubgroup.inv_mem hr) htR) hr
      rwa [show r⁻¹ * (r * t * r⁻¹) * r = t by group] at h
  have hkT : k ∈ (R : Subgroup Y) ⊓ K := by
    obtain ⟨T', hT'⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R K
    have hT'eq : (T' : Subgroup ↥K) = ((R : Subgroup Y) ⊓ K).subgroupOf K :=
      Subgroup.map_injective K.subtype_injective (by
        rw [hT', Subgroup.map_subgroupOf_eq_of_le inf_le_right])
    have hkN' : (⟨k, hkK⟩ : ↥K) ∈ normalizer ((T' : Subgroup ↥K) : Set ↥K) := by
      rw [hT'eq, ← Subgroup.subgroupOf_normalizer_eq (H := (R : Subgroup Y) ⊓ K) inf_le_right]
      exact Subgroup.mem_subgroupOf.mpr hkN
    have hkp : IsPGroup p (Subgroup.zpowers (⟨k, hkK⟩ : ↥K)) := by
      have hkndvd : orderOf (⟨k, hkK⟩ : ↥K) ∣ p ^ n := by
        rw [← Subgroup.orderOf_coe]
        exact orderOf_dvd_of_pow_eq_one hkn
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hkndvd
      exact IsPGroup.iff_card.mpr ⟨j, by rw [Nat.card_zpowers, hj]⟩
    have hsup : IsPGroup p
        ((Subgroup.zpowers (⟨k, hkK⟩ : ↥K) ⊔ (T' : Subgroup ↥K) : Subgroup ↥K)) :=
      IsPGroup.to_sup_of_normal_right' hkp T'.isPGroup' (Subgroup.zpowers_le.mpr hkN')
    have heq : (Subgroup.zpowers (⟨k, hkK⟩ : ↥K) ⊔ (T' : Subgroup ↥K) : Subgroup ↥K) =
        (T' : Subgroup ↥K) :=
      T'.is_maximal' hsup le_sup_right
    have hmem : (⟨k, hkK⟩ : ↥K) ∈ (T' : Subgroup ↥K) := by
      rw [← heq]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    have hkmap : k ∈ (T' : Subgroup ↥K).map K.subtype := Subgroup.mem_map_of_mem K.subtype hmem
    rwa [hT'] at hkmap
  have hcR : c ∈ (R : Subgroup Y) :=
    R.toSubgroup.mul_mem (R.toSubgroup.inv_mem hkT.1) hr
  rw [hrkc]
  exact mul_mem (mem_sup_left hkT) (mem_sup_right (mem_inf.mpr ⟨hcR, hc⟩))

theorem exists_plane_normalizer_inf_le {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Y : Type} [Group Y]
    [Finite Y] {K Y₀ E : Subgroup Y} (R : Sylow p Y) [K.Normal]
    (hER : E ≤ R) (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 2)
    (hcore : (if 3 ≤ pRank p (R : Subgroup Y) then GLBWeakCore p (R : Subgroup Y)
      else GLBCore p 1 E) ≤ Y₀)
    (hZ : K ⊓ centralizer (K : Set Y) = ⊥) (hout : ¬ p ∣ Nat.card (Outer K))
    (hT : Nat.card ((R : Subgroup Y) ⊓ K : Subgroup Y) = p ^ 3)
    (hTnc : ∃ x ∈ (R : Subgroup Y) ⊓ K, ∃ y ∈ (R : Subgroup Y) ⊓ K, x * y ≠ y * x) :
    ∃ E' : Subgroup Y, E' ≤ (R : Subgroup Y) ⊓ K ∧ Nat.card E' = p ^ 2 ∧
      ∀ t ∈ E', t ≠ 1 → normalizer ((zpowers t : Subgroup Y) : Set Y) ⊓ K ≤ Y₀ := by
  classical
  have hp : p.Prime := Fact.out
  have hTnotcomm : ¬ IsMulCommutative ↥((R : Subgroup Y) ⊓ K) := by
    intro hcomm
    letI : IsMulCommutative ↥((R : Subgroup Y) ⊓ K) := hcomm
    obtain ⟨x, hx, y, hy, hxy⟩ := hTnc
    exact hxy (congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥((R : Subgroup Y) ⊓ K))
      (⟨y, hy⟩ : ↥((R : Subgroup Y) ⊓ K))))
  have hTnotcyc : ¬ IsCyclic ↥((R : Subgroup Y) ⊓ K) := by
    intro hcyc
    letI : IsCyclic ↥((R : Subgroup Y) ⊓ K) := hcyc
    exact hTnotcomm IsCyclic.isMulCommutative
  have hTrank : CFSG.Open.pRank p ((R : Subgroup Y) ⊓ K) ≤ 2 := by
    refine CFSG.SectionRank.pRank_le hp.one_lt ?_
    intro F hFT hFea
    by_contra hcon
    push Not at hcon
    have hFdvd : Nat.card F ∣ p ^ 3 := by
      have h := Subgroup.card_dvd_of_le hFT
      rwa [hT] at h
    obtain ⟨j, hj3, hj⟩ := (Nat.dvd_prime_pow hp).mp hFdvd
    rw [hj] at hcon
    have h2j : 2 < j := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hcon
    have hjeq : j = 3 := by omega
    have hFeq : F = (R : Subgroup Y) ⊓ K := by
      refine Subgroup.eq_of_le_of_card_ge hFT ?_
      rw [hT, hj, hjeq]
    exact hTnotcomm (hFeq ▸ hFea.1)
  have hTp : IsPGroup p ↥((R : Subgroup Y) ⊓ K) :=
    R.isPGroup'.to_le (inf_le_left : (R : Subgroup Y) ⊓ K ≤ (R : Subgroup Y))
  obtain ⟨E₀, hE₀T, hE₀ea, hE₀card⟩ :=
    CFSG.Quasithin.A1c.exists_isElemAbelian_card_sq hp2 hTp hTnotcyc
  have hE₀rank : CFSG.Open.pRank p E₀ = 2 := by
    have h1 : 2 ≤ CFSG.Open.pRank p E₀ := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hE₀ea hE₀card
    have h2 : CFSG.Open.pRank p E₀ ≤ 2 :=
      (CFSG.SectionRank.pRank_mono hp.one_lt hE₀T).trans hTrank
    omega
  have hRdec : (R : Subgroup Y) ≤ ((R : Subgroup Y) ⊓ K) ⊔
      ((R : Subgroup Y) ⊓ centralizer (K : Set Y)) :=
    sylow_le_inf_sup_inf_centralizer_of_not_dvd R hZ hout
  have exists_d : ((R : Subgroup Y) ⊓ centralizer (K : Set Y)) ≠ ⊥ →
      ∃ d ∈ ((R : Subgroup Y) ⊓ centralizer (K : Set Y)), orderOf d = p := by
    intro hDne
    have hDp : IsPGroup p ↥((R : Subgroup Y) ⊓ centralizer (K : Set Y)) :=
      R.isPGroup'.to_le
        (inf_le_left : (R : Subgroup Y) ⊓ centralizer (K : Set Y) ≤ (R : Subgroup Y))
    have hcardne : Nat.card ↥((R : Subgroup Y) ⊓ centralizer (K : Set Y)) ≠ 1 :=
      fun h => hDne (Subgroup.eq_bot_of_card_eq _ h)
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hDp
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hcardne (by rw [hm, pow_zero])
    have hdvd : p ∣ Nat.card ↥((R : Subgroup Y) ⊓ centralizer (K : Set Y)) := by
      rw [hm]
      exact dvd_pow_self p hm0
    haveI : Fintype ↥((R : Subgroup Y) ⊓ centralizer (K : Set Y)) := Fintype.ofFinite _
    have hdvd' : p ∣ Fintype.card ↥((R : Subgroup Y) ⊓ centralizer (K : Set Y)) := by
      rwa [Nat.card_eq_fintype_card] at hdvd
    obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card p hdvd'
    exact ⟨(y : Y), y.2, by rw [Subgroup.orderOf_coe]; exact hyord⟩
  by_cases h3 : 3 ≤ CFSG.Open.pRank p (R : Subgroup Y)
  ·
    have h3c : 3 ≤ pRank p (R : Subgroup Y) := by
      rwa [CFSG.SectionRank.pRank_coe_eq_openPRank p (R : Subgroup Y)]
    rw [if_pos h3c] at hcore
    have hDne : ((R : Subgroup Y) ⊓ centralizer (K : Set Y)) ≠ ⊥ := by
      intro hDbot
      have hRT : (R : Subgroup Y) ≤ (R : Subgroup Y) ⊓ K := by
        have h0 := hRdec
        rw [hDbot] at h0
        simpa using h0
      have hpr : CFSG.Open.pRank p (R : Subgroup Y) =
          CFSG.Open.pRank p ((R : Subgroup Y) ⊓ K) :=
        congrArg (CFSG.Open.pRank p)
          (le_antisymm hRT (inf_le_left : (R : Subgroup Y) ⊓ K ≤ (R : Subgroup Y)))
      omega
    obtain ⟨d, hdD, hdord⟩ := exists_d hDne
    obtain ⟨hdR, hdC⟩ := mem_inf.mp hdD
    have hdcent : ∀ y ∈ K, Commute y d := fun y hy => mem_centralizer_iff.mp hdC y hy
    have hdX : Subgroup.zpowers d ≤ centralizer (K : Set Y) := zpowers_le.mpr hdC
    refine ⟨E₀, hE₀T, hE₀card, ?_⟩
    intro t htE ht1
    have htT : t ∈ (R : Subgroup Y) ⊓ K := hE₀T htE
    have htK : t ∈ K := (mem_inf.mp htT).2
    have htR : t ∈ (R : Subgroup Y) := (mem_inf.mp htT).1
    have htp : t ^ p = 1 := hE₀ea.2 t htE
    have htord : orderOf t = p := by
      rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one htp) with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) ht1
      · exact h
    have hdisj : Subgroup.zpowers t ⊓ Subgroup.zpowers d = ⊥ := by
      refine le_antisymm ?_ bot_le
      intro z hz
      obtain ⟨hzt, hzd⟩ := mem_inf.mp hz
      have hzbot : z ∈ K ⊓ centralizer (K : Set Y) :=
        mem_inf.mpr ⟨zpowers_le.mpr htK hzt, hdX hzd⟩
      rwa [hZ] at hzbot
    have hcomm : ∀ a ∈ Subgroup.zpowers t, ∀ b ∈ Subgroup.zpowers d, a * b = b * a := by
      intro a ha b hb
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (((hdcent t htK).zpow_left i).zpow_right j).eq
    have hXrank : 2 ≤ CFSG.Open.pRank p (Subgroup.zpowers t ⊔ Subgroup.zpowers d) := by
      have h := pRank_add_le_pRank_sup_of_coprime hp hcomm (by
        rw [hdisj, Subgroup.card_bot]; exact Nat.coprime_one_right p)
      rw [pRank_zpowers_eq_one htord, pRank_zpowers_eq_one hdord] at h
      omega
    have hcomm2 : ∀ a ∈ E₀, ∀ b ∈ Subgroup.zpowers d, a * b = b * a := by
      intro a ha b hb
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact ((hdcent a ((mem_inf.mp (hE₀T ha)).2)).zpow_right j).eq
    have hE₀cent : E₀ ≤ centralizer
        ((Subgroup.zpowers t ⊔ Subgroup.zpowers d : Subgroup Y) : Set Y) := by
      have hdea : IsElemAbelian p (Subgroup.zpowers d) :=
        CFSG.Open.isElemAbelian_zpowers (by rw [← hdord]; exact pow_orderOf_eq_one d)
      have hea : IsElemAbelian p (E₀ ⊔ Subgroup.zpowers d) :=
        CFSG.Open.IsElemAbelian.sup_of_commute hE₀ea hdea hcomm2
      refine (le_sup_left : E₀ ≤ E₀ ⊔ Subgroup.zpowers d).trans ?_
      refine (Subgroup.le_centralizer_iff_isMulCommutative.mpr hea.1).trans ?_
      exact Subgroup.centralizer_le fun x hx =>
        sup_le ((Subgroup.zpowers_le.mpr htE).trans le_sup_left) le_sup_right hx
    have hdisj2 : E₀ ⊓ Subgroup.zpowers d = ⊥ := by
      refine le_antisymm ?_ bot_le
      intro z hz
      obtain ⟨hzE, hzd⟩ := mem_inf.mp hz
      have hzbot : z ∈ K ⊓ centralizer (K : Set Y) :=
        mem_inf.mpr ⟨(mem_inf.mp (hE₀T hzE)).2, hdX hzd⟩
      rwa [hZ] at hzbot
    have hE₀R : E₀ ≤ (R : Subgroup Y) := hE₀T.trans inf_le_left
    have hXR : (Subgroup.zpowers t ⊔ Subgroup.zpowers d : Subgroup Y) ≤ (R : Subgroup Y) :=
      sup_le (zpowers_le.mpr htR) (zpowers_le.mpr hdR)
    have hX3 : 3 ≤ CFSG.Open.pRank p ((Subgroup.zpowers t ⊔ Subgroup.zpowers d) ⊔
        ((R : Subgroup Y) ⊓ centralizer
          ((Subgroup.zpowers t ⊔ Subgroup.zpowers d : Subgroup Y) : Set Y))) := by
      have h := pRank_add_le_pRank_sup_of_coprime hp hcomm2 (by
        rw [hdisj2, Subgroup.card_bot]; exact Nat.coprime_one_right p)
      rw [pRank_zpowers_eq_one hdord, hE₀rank] at h
      have hle : E₀ ⊔ Subgroup.zpowers d ≤ (Subgroup.zpowers t ⊔ Subgroup.zpowers d) ⊔
          ((R : Subgroup Y) ⊓ centralizer
            ((Subgroup.zpowers t ⊔ Subgroup.zpowers d : Subgroup Y) : Set Y)) := by
        refine sup_le ?_ ?_
        · exact (le_inf hE₀R hE₀cent).trans le_sup_right
        · exact le_sup_right.trans le_sup_left
      exact (by omega : 3 ≤ CFSG.Open.pRank p (E₀ ⊔ Subgroup.zpowers d)).trans
        (CFSG.SectionRank.pRank_mono hp.one_lt hle)
    have hXcore : normalizer ((Subgroup.zpowers t ⊔ Subgroup.zpowers d : Subgroup Y) : Set Y) ≤
        GLBWeakCore p (R : Subgroup Y) :=
      le_sSup ⟨_, hXR, hXrank, hX3, rfl⟩
    intro x hx
    obtain ⟨hxN, hxK⟩ := mem_inf.mp hx
    have hxNd : x ∈ normalizer (Subgroup.zpowers d : Set Y) :=
      Subgroup.centralizer_le_normalizer _ (by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
        exact ((Commute.symm (hdcent x hxK)).zpow_left i).eq)
    have hxNX : x ∈ normalizer
        ((Subgroup.zpowers t ⊔ Subgroup.zpowers d : Subgroup Y) : Set Y) :=
      Subgroup.inf_normalizer_le_normalizer_sup
        (Subgroup.zpowers t) (Subgroup.zpowers d) ⟨hxN, hxNd⟩
    exact hcore (hXcore hxNX)
  ·
    have h3c : ¬ 3 ≤ pRank p (R : Subgroup Y) := by
      rwa [CFSG.SectionRank.pRank_coe_eq_openPRank p (R : Subgroup Y)]
    rw [if_neg h3c] at hcore
    have hDbot : ((R : Subgroup Y) ⊓ centralizer (K : Set Y)) = ⊥ := by
      by_contra hDne
      obtain ⟨d, hdD, hdord⟩ := exists_d hDne
      obtain ⟨hdR, hdC⟩ := mem_inf.mp hdD
      have hdcent : ∀ y ∈ K, Commute y d := fun y hy => mem_centralizer_iff.mp hdC y hy
      have hdX : Subgroup.zpowers d ≤ centralizer (K : Set Y) := zpowers_le.mpr hdC
      have hdisj2 : E₀ ⊓ Subgroup.zpowers d = ⊥ := by
        refine le_antisymm ?_ bot_le
        intro z hz
        obtain ⟨hzE, hzd⟩ := mem_inf.mp hz
        have hzbot : z ∈ K ⊓ centralizer (K : Set Y) :=
          mem_inf.mpr ⟨(mem_inf.mp (hE₀T hzE)).2, hdX hzd⟩
        rwa [hZ] at hzbot
      have hcomm2 : ∀ a ∈ E₀, ∀ b ∈ Subgroup.zpowers d, a * b = b * a := by
        intro a ha b hb
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        exact ((hdcent a ((mem_inf.mp (hE₀T ha)).2)).zpow_right j).eq
      have h := pRank_add_le_pRank_sup_of_coprime hp hcomm2 (by
        rw [hdisj2, Subgroup.card_bot]; exact Nat.coprime_one_right p)
      rw [pRank_zpowers_eq_one hdord, hE₀rank] at h
      have hle : E₀ ⊔ Subgroup.zpowers d ≤ (R : Subgroup Y) :=
        sup_le (hE₀T.trans inf_le_left) (zpowers_le.mpr hdR)
      have h3' : 3 ≤ CFSG.Open.pRank p (R : Subgroup Y) :=
        (by omega : 3 ≤ CFSG.Open.pRank p (E₀ ⊔ Subgroup.zpowers d)).trans
          (CFSG.SectionRank.pRank_mono hp.one_lt hle)
      exact h3 h3'
    have hRK : (R : Subgroup Y) ≤ K := by
      have h0 : (R : Subgroup Y) ≤ (R : Subgroup Y) ⊓ K := by
        have h := hRdec
        rw [hDbot] at h
        simpa using h
      exact h0.trans inf_le_right
    refine ⟨E, le_inf hER (hER.trans hRK), hEc, ?_⟩
    intro t htE ht1
    have htp : t ^ p = 1 := hE.2 t htE
    have htord : orderOf t = p := by
      rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one htp) with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) ht1
      · exact h
    have hone : 1 ≤ CFSG.Open.pRank p (Subgroup.zpowers t) := by
      rw [pRank_zpowers_eq_one htord]
    have hN : normalizer (Subgroup.zpowers t : Set Y) ≤ GLBCore p 1 E :=
      le_sSup ⟨Subgroup.zpowers t, zpowers_le.mpr htE, hone, rfl⟩
    exact inf_le_left.trans (hN.trans hcore)

end CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K
