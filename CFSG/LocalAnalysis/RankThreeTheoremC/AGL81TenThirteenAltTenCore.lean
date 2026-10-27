module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenAltTenRho
public import CFSG.Open.GLBDefs
public import CFSG.Foundations.Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenAltTenSylow
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenAltTenK
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenTenClaimOf

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.AltTen

open CFSG.Open Subgroup Equiv Equiv.Perm

theorem pow_five_eq_one_of_pow_25 {σ : Perm (Fin 10)} (h : σ ^ 25 = 1) : σ ^ 5 = 1 := by
  have hall : ∀ n ∈ σ.cycleType, n ∣ 5 := by
    intro n hn
    have h1 := two_le_of_mem_cycleType hn
    have h2 : n ∣ 25 := (dvd_of_mem_cycleType hn).trans (orderOf_dvd_of_pow_eq_one h)
    have h3 : n ≤ 10 := (le_card_support_of_mem_cycleType hn).trans
      (by simpa using Finset.card_le_univ σ.support)
    have h4 : n ∈ Nat.divisors 25 := Nat.mem_divisors.mpr ⟨h2, by norm_num⟩
    have h5 : Nat.divisors 25 = {1, 5, 25} := by decide
    rw [h5] at h4
    simp only [Finset.mem_insert, Finset.mem_singleton] at h4
    rcases h4 with rfl | rfl | rfl <;> omega
  have hord : orderOf σ ∣ 5 := by
    rw [← lcm_cycleType]
    exact Multiset.lcm_dvd.mpr hall
  exact orderOf_dvd_iff_pow_eq_one.mp hord

private theorem relIndex_dvd_index_of_normal_K {H : Type*} [Group H] [Finite H] (S K : Subgroup H)
    [K.Normal] : S.relIndex K ∣ S.index := by
  have h1 : S.relIndex K * K.index = (S ⊓ K).index := by
    have h := Subgroup.relIndex_inf_mul_relIndex S K ⊤
    rwa [inf_top_eq, Subgroup.relIndex_top_right, Subgroup.relIndex_top_right] at h
  have h2 : (S ⊓ K).relIndex S * S.index = (S ⊓ K).index :=
    Subgroup.relIndex_mul_index inf_le_left
  have h3 : (S ⊓ K).relIndex S = K.relIndex (S ⊔ K) := by
    rw [Subgroup.relIndex_sup_right, inf_comm, Subgroup.inf_relIndex_right]
  obtain ⟨m, hm⟩ := Subgroup.relIndex_dvd_index_of_le (le_sup_right : K ≤ S ⊔ K)
  have hpos : 0 < K.relIndex (S ⊔ K) := by
    apply Nat.pos_of_ne_zero
    intro h0
    rw [h0, zero_mul] at hm
    exact Subgroup.index_ne_zero_of_finite hm
  refine ⟨m, ?_⟩
  rw [hm, ← h2, h3] at h1
  have h4 : K.relIndex (S ⊔ K) * (S.relIndex K * m) = K.relIndex (S ⊔ K) * S.index := by
    rw [← h1]
    ring
  exact (Nat.eq_of_mul_eq_mul_left hpos h4).symm

private theorem elemAbelian_zpowers_five {G : Type*} [Group G] {s : G} (hs : orderOf s = 5) :
    IsElemAbelian 5 (zpowers s) ∧ Nat.card (zpowers s) = 5 ^ 1 := by
  have hcomm : IsMulCommutative (zpowers s) := ⟨⟨fun a b => by
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp a.2
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj]
    exact (Commute.zpow_zpow_self s i j).eq⟩⟩
  have hexp : ∀ x ∈ zpowers s, x ^ 5 = 1 := by
    intro x hx
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hs, pow_orderOf_eq_one,
      one_zpow]
  exact ⟨⟨hcomm, hexp⟩, by rw [Nat.card_zpowers, hs, pow_one]⟩

variable {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} [K.Normal]

theorem core_le_of_altTen (eK : ↥K ≃* alternatingGroup (Fin 10)) {Y₀ : Subgroup Y}
    (hcent : centralizer (K : Set Y) ≤ Y₀) (R : Sylow 5 Y) {E : Subgroup Y}
    (hER : E ≤ R) (hE : IsElemAbelian 5 E) (hEc : Nat.card E = 5 ^ 2)
    (hcore : (if 3 ≤ CFSG.pRank 5 ↥(R : Subgroup Y) then GLBWeakCore 5 (R : Subgroup Y)
      else GLBCore 5 1 E) ≤ Y₀) :
    ∃ T : Sylow 5 ↥K, normalizer ((T : Subgroup K) : Set K) ≤ Y₀.subgroupOf K ∧
      ∀ s ∈ (T : Subgroup K), s ≠ 1 → ∀ k : ↥K, Commute k s → (k : Y) ∈ Y₀ := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5 : 1 < 5 := by norm_num
  have hTp : IsPGroup 5 ((R : Subgroup Y).subgroupOf K) := R.isPGroup'.comap_subtype
  have hTi : ¬ 5 ∣ ((R : Subgroup Y).subgroupOf K).index := by
    intro hdvd
    have h : 5 ∣ (R : Subgroup Y).relIndex K := hdvd
    exact R.not_dvd_index (dvd_trans h (relIndex_dvd_index_of_normal_K (R : Subgroup Y) K))
  set T : Sylow 5 ↥K := hTp.toSylow hTi with hT
  have hTcoe : (T : Subgroup K) = (R : Subgroup Y).subgroupOf K := IsPGroup.toSylow_coe _ _
  set TY : Subgroup Y := (T : Subgroup K).map K.subtype with hTY
  have hTYeq : TY = (R : Subgroup Y) ⊓ K := by
    rw [hTY, hTcoe, Subgroup.subgroupOf_map_subtype]
  have hTYR : TY ≤ R := hTYeq ▸ inf_le_left
  have hTYK : TY ≤ K := hTYeq ▸ inf_le_right
  have hTcard : Nat.card (T : Subgroup K) = 25 := by
    have hes : Function.Surjective eK.toMonoidHom := eK.surjective
    have := card_sylow_five (T.mapSurjective hes)
    rwa [Sylow.coe_mapSurjective, Subgroup.card_map_of_injective eK.injective] at this
  have hTYcard : Nat.card TY = 5 ^ 2 := by
    rw [hTY, Subgroup.card_map_of_injective K.subtype_injective, hTcard]
    norm_num
  have hTYab : IsElemAbelian 5 TY := by
    refine ⟨⟨⟨IsPGroup.commutative_of_card_eq_prime_sq hTYcard⟩⟩, fun x hx => ?_⟩
    have hx25 : x ^ 25 = 1 := by
      have h1 := orderOf_dvd_natCard (⟨x, hx⟩ : TY)
      rw [hTYcard] at h1
      have h2 : (⟨x, hx⟩ : TY) ^ 25 = 1 := orderOf_dvd_iff_pow_eq_one.mp h1
      simpa using congrArg Subtype.val h2
    have hxK : x ∈ K := hTYK hx
    have h1 : ((eK ⟨x, hxK⟩ : alternatingGroup (Fin 10)) : Perm (Fin 10)) ^ 25 = 1 := by
      rw [← SubgroupClass.coe_pow, ← map_pow]
      have : (⟨x, hxK⟩ : ↥K) ^ 25 = 1 := Subtype.ext (by simpa using hx25)
      rw [this, map_one]
      rfl
    have h2 := pow_five_eq_one_of_pow_25 h1
    rw [← SubgroupClass.coe_pow, ← map_pow] at h2
    have h3 : eK (⟨x, hxK⟩ ^ 5) = eK 1 := by
      rw [map_one]
      exact Subtype.ext h2
    have h4 := congrArg Subtype.val (eK.injective h3)
    simpa using h4
  have hrankT : 2 ≤ Open.pRank 5 TY := CFSG.SectionRank.le_pRank h5 le_rfl hTYab hTYcard
  have hKC : ∀ y ∈ K, y ∈ centralizer (K : Set Y) → y = 1 := by
    intro y hy hyC
    have h1 : rho eK ((⟨y, hy⟩ : ↥K) : Y) = 1 := (rho_eq_one_iff eK _).2 hyC
    rw [rho_coe] at h1
    have h2 : eK ⟨y, hy⟩ = eK 1 := by
      rw [map_one]
      exact Subtype.ext h1
    exact congrArg Subtype.val (eK.injective h2)
  have hRT_of : (∀ z ∈ (R : Subgroup Y), z ∈ centralizer (K : Set Y) → z = 1) →
      (R : Subgroup Y) = TY := by
    intro hRC
    have hinj : Function.Injective ((rho eK).comp (R : Subgroup Y).subtype) := by
      rw [injective_iff_map_eq_one]
      intro r hr
      exact Subtype.ext (hRC r r.2 ((rho_eq_one_iff eK r).1 hr))
    set P : Subgroup (alternatingGroup (Fin 10)) :=
      ((R : Subgroup Y).map (rho eK)).comap (alternatingGroup (Fin 10)).subtype with hP
    have hPmap : P.map (alternatingGroup (Fin 10)).subtype = (R : Subgroup Y).map (rho eK) := by
      rw [hP, Subgroup.map_comap_eq, inf_eq_right]
      rintro _ ⟨r, hr, rfl⟩
      refine ⟨⟨rho eK r, rho_mem_alt_of_odd eK ?_⟩, rfl⟩
      obtain ⟨n, hn⟩ := (R.isPGroup' ⟨r, hr⟩)
      have : orderOf r ∣ 5 ^ n := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hn)
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp this
      rw [hj]
      exact Odd.pow (by decide)
    have hPp : IsPGroup 5 P := by
      intro σ
      obtain ⟨r, hr, hrσ⟩ := (show (σ : Perm (Fin 10)) ∈ (R : Subgroup Y).map (rho eK) from
        hPmap ▸ ⟨σ, σ.2, rfl⟩)
      obtain ⟨n, hn⟩ := R.isPGroup' ⟨r, hr⟩
      refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← hrσ, ← map_pow]
      have : r ^ 5 ^ n = 1 := by simpa using congrArg Subtype.val hn
      rw [this, map_one]
    obtain ⟨Q, hPQ⟩ := hPp.exists_le_sylow
    have hPcard : Nat.card P ≤ 25 := by
      rw [← card_sylow_five Q]
      exact Subgroup.card_le_of_le hPQ
    have hRcard : Nat.card (R : Subgroup Y) ≤ 25 := by
      have h1 : Nat.card ((R : Subgroup Y).map (rho eK)) = Nat.card (R : Subgroup Y) := by
        rw [show (R : Subgroup Y).map (rho eK) =
          ((rho eK).comp (R : Subgroup Y).subtype).range by
            rw [MonoidHom.range_comp, Subgroup.range_subtype]]
        exact Nat.card_range_of_injective hinj
      rw [← h1, ← hPmap, Subgroup.card_map_of_injective (alternatingGroup (Fin 10)).subtype_injective]
      exact hPcard
    exact (Subgroup.eq_of_le_of_card_ge hTYR (by rw [hTYcard]; exact hRcard)).symm
  have hz_of : (R : Subgroup Y) ≠ TY → ∃ z ∈ (R : Subgroup Y),
      z ∈ centralizer (K : Set Y) ∧ orderOf z = 5 := by
    intro hne
    have h1 : ∃ z ∈ (R : Subgroup Y), z ∈ centralizer (K : Set Y) ∧ z ≠ 1 := by
      by_contra h
      push Not at h
      exact hne (hRT_of h)
    obtain ⟨z₀, hz₀R, hz₀C, hz₀1⟩ := h1
    set D := (R : Subgroup Y) ⊓ centralizer (K : Set Y) with hD
    have hDp : IsPGroup 5 D := R.isPGroup'.to_le inf_le_left
    have h5D : 5 ∣ Nat.card D := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hDp
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hk
        have hbot := Subgroup.eq_bot_of_card_eq D hk
        have : z₀ ∈ D := ⟨hz₀R, hz₀C⟩
        rw [hbot, mem_bot] at this
        exact hz₀1 this
      rw [hk]
      exact dvd_pow_self 5 hk0
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := D) 5 h5D
    exact ⟨z, z.2.1, z.2.2, by rw [Subgroup.orderOf_coe]; exact hz⟩
  have hE125 : ∀ z ∈ (R : Subgroup Y), z ∈ centralizer (K : Set Y) → orderOf z = 5 →
      IsElemAbelian 5 (TY ⊔ zpowers z) ∧ Nat.card (TY ⊔ zpowers z : Subgroup Y) = 5 ^ 3 := by
    intro z hzR hzC hz5
    obtain ⟨hZab, hZc⟩ := elemAbelian_zpowers_five hz5
    have hc : ∀ a ∈ TY, ∀ c ∈ zpowers z, a * c = c * a := by
      intro a ha c hc
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hc
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.zpow_mem _ hzC i)) a (hTYK ha)
    have hinf : TY ⊓ zpowers z = ⊥ := by
      rw [eq_bot_iff]
      rintro y ⟨hy1, hy2⟩
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy2
      exact hKC _ (hTYK hy1) (Subgroup.zpow_mem _ hzC i)
    obtain ⟨hab, hcard⟩ := TenTenClaim.elemAbelian_sup_card hTYab hZab hc hinf
    refine ⟨hab, ?_⟩
    rw [hcard, hTYcard, hZc]
    norm_num
  have hcase : (3 ≤ CFSG.pRank 5 ↥(R : Subgroup Y) ∧ GLBWeakCore 5 (R : Subgroup Y) ≤ Y₀ ∧
      ∃ z ∈ (R : Subgroup Y), z ∈ centralizer (K : Set Y) ∧ orderOf z = 5) ∨
      (GLBCore 5 1 E ≤ Y₀ ∧ E = TY) := by
    by_cases h3 : 3 ≤ CFSG.pRank 5 ↥(R : Subgroup Y)
    · rw [if_pos h3] at hcore
      have hne : (R : Subgroup Y) ≠ TY := by
        intro h
        rw [CFSG.SectionRank.pRank_coe_eq_openPRank, h] at h3
        have := CFSG.SectionRank.pRank_le h5 (H := TY) (k := 2) (fun F hF _ => by
          rw [← hTYcard]
          exact Subgroup.card_le_of_le hF)
        omega
      exact Or.inl ⟨h3, hcore, hz_of hne⟩
    · rw [if_neg h3] at hcore
      have hRT : (R : Subgroup Y) = TY := by
        by_contra hne
        obtain ⟨z, hzR, hzC, hz5⟩ := hz_of hne
        obtain ⟨hab, hcard⟩ := hE125 z hzR hzC hz5
        apply h3
        rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
        refine CFSG.SectionRank.le_pRank h5 (sup_le hTYR ?_) hab hcard
        rw [zpowers_le]
        exact hzR
      exact Or.inr ⟨hcore, Subgroup.eq_of_le_of_card_ge (hER.trans hRT.le)
        (by rw [hTYcard, hEc])⟩
  have hzTY : ∀ z, z ∈ centralizer (K : Set Y) → z ∈ centralizer (TY : Set Y) := fun z hzC =>
    Subgroup.mem_centralizer_iff.mpr fun a ha => (Subgroup.mem_centralizer_iff.mp hzC) a (hTYK ha)
  have hNY : normalizer (TY : Set Y) ≤ Y₀ := by
    rcases hcase with ⟨-, hcore, z, hzR, hzC, hz5⟩ | ⟨hcore, hET⟩
    · obtain ⟨hab, hcard⟩ := hE125 z hzR hzC hz5
      unfold GLBWeakCore rankThreeAschCore at hcore
      refine le_trans (le_sSup ?_) hcore
      refine ⟨TY, hTYR, hrankT, ?_, rfl⟩
      refine CFSG.SectionRank.le_pRank h5 (E := TY ⊔ zpowers z) (sup_le le_sup_left ?_) hab hcard
      rw [zpowers_le]
      exact Subgroup.mem_sup_right ⟨hzR, hzTY z hzC⟩
    · unfold GLBCore at hcore
      refine le_trans (le_sSup ?_) hcore
      refine ⟨E, le_rfl, ?_, by rw [hET]⟩
      exact (CFSG.SectionRank.le_pRank h5 le_rfl hE hEc).trans' (by norm_num)
  have hTsub : TY.subgroupOf K = (T : Subgroup K) := by
    rw [hTY]
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  refine ⟨T, ?_, ?_⟩
  · intro k hk
    rw [← hTsub, ← Subgroup.subgroupOf_normalizer_eq hTYK] at hk
    rw [mem_subgroupOf] at hk ⊢
    exact hNY hk
  · intro s hsT hs1 k hks
    have hsY : (s : Y) ∈ TY := ⟨s, hsT, rfl⟩
    have hs1Y : (s : Y) ≠ 1 := fun h => hs1 (Subtype.ext h)
    have hs5 : orderOf (s : Y) = 5 := orderOf_eq_prime (hTYab.2 _ hsY) hs1Y
    obtain ⟨hSab, hSc⟩ := elemAbelian_zpowers_five hs5
    have hks' : (k : Y) * s = s * k := congrArg Subtype.val hks.eq
    have hnorm : ∀ X : Subgroup Y, X ≤ centralizer ({(k : Y)} : Set Y) →
        (k : Y) ∈ normalizer (X : Set Y) := by
      intro X hX
      rw [mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        have hc : h * k = k * h := Subgroup.mem_centralizer_singleton_iff.mp (hX hh)
        have : (k : Y) * h * (k : Y)⁻¹ = h := by
          rw [← hc]
          group
        rw [this]
        exact hh
      · intro hh
        have hc := Subgroup.mem_centralizer_singleton_iff.mp (hX hh)
        have h1 : (k : Y) * h = (k : Y) * ((k : Y) * h * (k : Y)⁻¹) := by
          rw [← hc]
          group
        rw [mul_left_cancel h1]
        exact hh
    have hsk : zpowers (s : Y) ≤ centralizer ({(k : Y)} : Set Y) := by
      rw [zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact hks'.symm
    rcases hcase with ⟨-, hcore, z, hzR, hzC, hz5⟩ | ⟨hcore, hET⟩
    ·
      obtain ⟨hZab, hZc⟩ := elemAbelian_zpowers_five hz5
      have hc : ∀ a ∈ zpowers (s : Y), ∀ c ∈ zpowers z, a * c = c * a := by
        intro a ha c hc
        obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
        obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hc
        exact (Subgroup.mem_centralizer_iff.mp (Subgroup.zpow_mem _ hzC j)) _
          (Subgroup.zpow_mem _ s.2 i)
      have hinf : zpowers (s : Y) ⊓ zpowers z = ⊥ := by
        rw [eq_bot_iff]
        rintro y ⟨hy1, hy2⟩
        obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy1
        obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hy2
        refine hKC _ (Subgroup.zpow_mem _ s.2 i) ?_
        rw [← hj]
        exact Subgroup.zpow_mem _ hzC j
      obtain ⟨hXab, hXc⟩ := TenTenClaim.elemAbelian_sup_card hSab hZab hc hinf
      have hXR : zpowers (s : Y) ⊔ zpowers z ≤ R :=
        sup_le (zpowers_le.mpr (hTYR hsY)) (zpowers_le.mpr hzR)
      have h2 : 2 ≤ Open.pRank 5 (zpowers (s : Y) ⊔ zpowers z) :=
        CFSG.SectionRank.le_pRank h5 le_rfl hXab (by rw [hXc, hSc, hZc]; norm_num)
      have hTYC : TY ≤ centralizer ((zpowers (s : Y) ⊔ zpowers z : Subgroup Y) : Set Y) := by
        rw [Subgroup.le_centralizer_iff]
        refine sup_le ?_ ?_
        · rw [zpowers_le]
          exact Subgroup.mem_centralizer_iff.mpr fun a ha =>
            congrArg Subtype.val (hTYab.1.is_comm.comm (⟨a, ha⟩ : TY) ⟨s, hsY⟩)
        · rw [zpowers_le]
          exact hzTY z hzC
      have h3 : 3 ≤ Open.pRank 5 ((zpowers (s : Y) ⊔ zpowers z) ⊔
          ((R : Subgroup Y) ⊓ centralizer ((zpowers (s : Y) ⊔ zpowers z : Subgroup Y) : Set Y))) := by
        obtain ⟨hab, hcard⟩ := hE125 z hzR hzC hz5
        refine CFSG.SectionRank.le_pRank h5 (sup_le ?_ ?_) hab hcard
        · exact le_sup_of_le_right (le_inf hTYR hTYC)
        · exact le_sup_of_le_left le_sup_right
      unfold GLBWeakCore rankThreeAschCore at hcore
      have hN : normalizer ((zpowers (s : Y) ⊔ zpowers z : Subgroup Y) : Set Y) ≤ Y₀ := by
        refine le_trans (le_sSup ?_) hcore
        exact ⟨_, hXR, h2, h3, rfl⟩
      exact hN (hnorm _ (sup_le hsk (by
        rw [zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact ((Subgroup.mem_centralizer_iff.mp hzC) k k.2).symm)))
    ·
      have hQE : zpowers (s : Y) ≤ E := by
        rw [zpowers_le, hET]
        exact hsY
      have h1 : 1 ≤ Open.pRank 5 (zpowers (s : Y)) := CFSG.SectionRank.le_pRank h5 le_rfl hSab hSc
      unfold GLBCore at hcore
      have hN : normalizer ((zpowers (s : Y) : Subgroup Y) : Set Y) ≤ Y₀ := by
        refine le_trans (le_sSup ?_) hcore
        exact ⟨_, hQE, h1, rfl⟩
      exact hN (hnorm _ hsk)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.AltTen
