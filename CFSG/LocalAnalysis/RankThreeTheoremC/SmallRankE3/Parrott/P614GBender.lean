module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614GBasic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614G

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {M B H S K : Subgroup G} {z : G}

theorem card_le_of_le_pre (c : Ctx M B H S K z) {U : Subgroup (Kbar K)} {Q : Subgroup G}
    (hQ : Q ≤ pre K U) (hQ3 : IsPGroup 3 Q) : Nat.card Q ≤ Nat.card U := by
  have hQK : Q ≤ K := hQ.trans (pre_le K U)
  let f : Q → U := fun q => ⟨QuotientGroup.mk ⟨q, hQK q.2⟩, (mem_pre (hQK q.2)).1 (hQ q.2)⟩
  refine Nat.card_le_card_of_injective f fun q₁ q₂ h => ?_
  have h1 : (QuotientGroup.mk ⟨q₁, hQK q₁.2⟩ : Kbar K) = QuotientGroup.mk ⟨q₂, hQK q₂.2⟩ :=
    congrArg Subtype.val h
  have hO := (c.mk_eq_mk_iff _ _).1 h1
  have hQm : (q₁ : G)⁻¹ * q₂ ∈ Q := Q.mul_mem (Q.inv_mem q₁.2) q₂.2
  obtain ⟨a, ha⟩ := c.isPGroup_core ⟨_, hO⟩
  obtain ⟨b, hb⟩ := hQ3 ⟨_, hQm⟩
  have ha' : ((q₁ : G)⁻¹ * q₂) ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hb' : ((q₁ : G)⁻¹ * q₂) ^ 3 ^ b = 1 := by simpa using congrArg Subtype.val hb
  have hco : Nat.Coprime (2 ^ a) (3 ^ b) := Nat.Coprime.pow a b (by norm_num)
  have h1' : orderOf ((q₁ : G)⁻¹ * q₂) = 1 :=
    Nat.eq_one_of_dvd_coprimes hco (orderOf_dvd_of_pow_eq_one ha') (orderOf_dvd_of_pow_eq_one hb')
  rw [orderOf_eq_one_iff, inv_mul_eq_one] at h1'
  exact Subtype.ext h1'

theorem isSylowOf_zpowers (c : Ctx M B H S K z) :
    CFSG.ABGLocalTools.IsSylowOf 3 (zpowers z) (pre K (zpowers c.zbar)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Y := pre K (zpowers c.zbar) with hY
  have hzY : z ∈ Y := (mem_pre c.z_mem_K).2 (mem_zpowers _)
  have hZY : zpowers z ≤ Y := zpowers_le.mpr hzY
  have hZ3 : IsPGroup 3 (zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, c.z_order, pow_one])
  obtain ⟨Q₀, hQ₀⟩ := (hZ3.comap_subtype (K := Y)).exists_le_sylow
  have hQY : (Q₀ : Subgroup ↥Y).map Y.subtype ≤ Y := map_subtype_le _
  have hZQ : zpowers z ≤ (Q₀ : Subgroup ↥Y).map Y.subtype := by
    intro g hg
    exact ⟨⟨g, hZY hg⟩, hQ₀ hg, rfl⟩
  have hcard : Nat.card ((Q₀ : Subgroup ↥Y).map Y.subtype) ≤ Nat.card (zpowers z) := by
    have h1 := c.card_le_of_le_pre hQY (Q₀.isPGroup'.map Y.subtype)
    have h2 : Nat.card (zpowers c.zbar) = Nat.card (zpowers z) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, c.orderOf_zbar, c.z_order]
    exact h1.trans h2.le
  exact ⟨Q₀, (Subgroup.eq_of_le_of_card_ge hZQ hcard).symm⟩

theorem pre_zbar_le (c : Ctx M B H S K z) : pre K (zpowers c.zbar) ≤ M := by
  intro g hg
  have hgK := pre_le K _ hg
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp ((mem_pre hgK).1 hg)
  have hj' : (QuotientGroup.mk (⟨z, c.z_mem_K⟩ ^ j) : Kbar K) = QuotientGroup.mk ⟨g, hgK⟩ := by
    rw [QuotientGroup.mk_zpow]
    exact hj
  have h1 := (c.mk_eq_mk_iff _ _).1 hj'
  have e : g = z ^ j * ((z ^ j)⁻¹ * g) := by group
  rw [e]
  refine M.mul_mem (M.zpow_mem c.z_mem_M j) (c.core_le_M ?_)
  simpa using h1

theorem normalizer_zbar_le (c : Ctx M B H S K z) :
    normalizer ((zpowers c.zbar : Subgroup (Kbar K)) : Set (Kbar K)) ≤ kbarM K M := by
  intro q hq
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  have hkH : (k : G) ∈ H := c.K_le k.2
  have hpres : ∀ (n : G) (hn : n ∈ K), (QuotientGroup.mk ⟨n, hn⟩ : Kbar K) ∈
      normalizer ((zpowers c.zbar : Subgroup (Kbar K)) : Set (Kbar K)) →
      ∀ u ∈ zpowers c.zbar, c.rho ⟨n, c.K_le hn⟩ u ∈ zpowers c.zbar := by
    intro n hn hnN u hu
    rw [c.rho_of_mem_K hn, MulAut.conj_apply]
    exact (mem_normalizer_iff.mp hnN u).1 hu
  have hkY : (k : G) ∈ normalizer ((pre K (zpowers c.zbar) : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro g
    refine ⟨fun hg => c.conj_mem_pre hkH (hpres k k.2 hq) hg, fun hg => ?_⟩
    have hk' : (k : G)⁻¹ ∈ K := K.inv_mem k.2
    have hq' : (QuotientGroup.mk ⟨(k : G)⁻¹, hk'⟩ : Kbar K) ∈
        normalizer ((zpowers c.zbar : Subgroup (Kbar K)) : Set (Kbar K)) := by
      have : (QuotientGroup.mk ⟨(k : G)⁻¹, hk'⟩ : Kbar K) = (QuotientGroup.mk k)⁻¹ := rfl
      rw [this]
      exact inv_mem hq
    have := c.conj_mem_pre (H.inv_mem hkH) (hpres _ hk' hq') hg
    simpa [mul_assoc] using this
  have hle := le_sup_normalizer_of_isSylowOf (zpowers_le.mpr hkY) c.isSylowOf_zpowers
  have hkM : (k : G) ∈ M := sup_le c.pre_zbar_le c.NZ_le (hle (mem_zpowers _))
  exact mk_mem_kbarM k.2 hkM

@[expose] noncomputable def rbar (K S : Subgroup G) : Subgroup (Kbar K) :=
  (S.subgroupOf K).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))

theorem mk_mem_rbar {K S : Subgroup G} {k : G} (hk : k ∈ K) (hkS : k ∈ S) :
    (QuotientGroup.mk ⟨k, hk⟩ : Kbar K) ∈ rbar K S :=
  ⟨⟨k, hk⟩, mem_subgroupOf.mpr hkS, rfl⟩

theorem isPGroup_rbar (c : Ctx M B H S K z) : IsPGroup 2 (rbar K S) :=
  (c.isPGroup_S.comap_subtype (K := K)).map _

theorem rbar_le_kbarM (c : Ctx M B H S K z) : rbar K S ≤ kbarM K M := by
  rintro _ ⟨k, hk, rfl⟩
  show _ ∈ (M.subgroupOf K).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))
  exact mem_map_of_mem _ (mem_subgroupOf.mpr (c.S_le_M (mem_subgroupOf.mp hk)))

theorem rho_mem_rbar (c : Ctx M B H S K z) {n : G} (hn : n ∈ H)
    (hnS : n ∈ normalizer (S : Set G)) {u : Kbar K} (hu : u ∈ rbar K S) :
    c.rho ⟨n, hn⟩ u ∈ rbar K S := by
  obtain ⟨k, hk, rfl⟩ := hu
  rw [QuotientGroup.mk'_apply, c.rho_mk]
  exact mk_mem_rbar _ ((mem_normalizer_iff.mp hnS _).1 (mem_subgroupOf.mp hk))

theorem rbar_ne_bot (c : Ctx M B H S K z) (hR : pCoreOf 2 H < kRad H S K) :
    rbar K S ≠ ⊥ := by
  obtain ⟨r, hrR, hrO⟩ := SetLike.exists_of_lt hR
  obtain ⟨hrS, hrKO⟩ := mem_inf.mp hrR
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right K (pCoreOf 2 H)
    (c.K_le.trans c.H_le_normalizer_core)] at hrKO
  obtain ⟨k, hk, o, ho, rfl⟩ := Set.mem_mul.1 hrKO
  have hkS : k ∈ S := by simpa using S.mul_mem hrS (S.inv_mem (c.core_le ho))
  intro hbot
  have h1 : (QuotientGroup.mk ⟨k, hk⟩ : Kbar K) ∈ rbar K S := mk_mem_rbar hk hkS
  rw [hbot, mem_bot] at h1
  exact hrO (mul_mem ((c.mk_eq_one_iff _).1 h1) ho)

theorem false_of_bender (c : Ctx M B H S K z) (hTI : KFactBenderTI) (hGen : KFactBenderGen)
    (hR : pCoreOf 2 H < kRad H S K) (hBen : CFSG.Open.fusionIsBenderGroup (Kbar K)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hRT⟩ := c.isPGroup_rbar.exists_le_sylow
  have hinv : ∀ (n : G) (hn : n ∈ H), n ∈ normalizer (S : Set G) →
      ∀ u ∈ (T : Subgroup (Kbar K)), c.rho ⟨n, hn⟩ u ∈ (T : Subgroup (Kbar K)) := by
    intro n hn hnS u hu
    have hsurj : Function.Surjective (c.rho ⟨n, hn⟩).toMonoidHom := (c.rho ⟨n, hn⟩).surjective
    have hT' := hTI (Kbar K) hBen T (T.mapSurjective hsurj) (by
      intro hbot
      apply c.rbar_ne_bot hR
      rw [eq_bot_iff]
      intro r hr
      rw [← hbot]
      refine mem_inf.mpr ⟨hRT hr, ?_⟩
      rw [Sylow.coe_mapSurjective]
      refine ⟨(c.rho ⟨n, hn⟩).symm r, hRT ?_, (c.rho ⟨n, hn⟩).apply_symm_apply r⟩
      have hn' : n⁻¹ ∈ normalizer (S : Set G) := inv_mem hnS
      have h1 := c.rho_mem_rbar (H.inv_mem hn) hn' hr
      have e : (c.rho ⟨n, hn⟩).symm r = c.rho ⟨n⁻¹, H.inv_mem hn⟩ r := by
        rw [show (⟨n⁻¹, H.inv_mem hn⟩ : ↥H) = (⟨n, hn⟩ : ↥H)⁻¹ from rfl, map_inv]
        rfl
      rw [e]
      exact h1)
    have : (T : Subgroup (Kbar K)) = (T : Subgroup (Kbar K)).map (c.rho ⟨n, hn⟩).toMonoidHom := by
      rw [← Sylow.coe_mapSurjective hsurj, ← hT']
    rw [this]
    exact mem_map_of_mem _ hu
  have hpre := c.pre_le_S (U := (T : Subgroup (Kbar K))) T.isPGroup'
    (fun s hs => hinv s (c.S_le hs) (le_normalizer hs))
    (fun b hb => hinv b (c.B_le hb) (c.B_le_normalizer_S hb))
  have hTR : (T : Subgroup (Kbar K)) ≤ rbar K S := by
    intro t ht
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective t
    exact mk_mem_rbar k.2 (hpre ((mem_pre k.2).2 ht))
  have hZT : zpowers c.zbar ≤ normalizer ((T : Subgroup (Kbar K)) : Set (Kbar K)) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro t
    have hzS : z ∈ normalizer (S : Set G) := c.B_le_normalizer_S c.z_mem_B
    have key : ∀ (n : G) (hn : n ∈ K), n ∈ normalizer (S : Set G) → ∀ u ∈ (T : Subgroup (Kbar K)),
        (QuotientGroup.mk ⟨n, hn⟩ : Kbar K) * u * (QuotientGroup.mk ⟨n, hn⟩)⁻¹ ∈
          (T : Subgroup (Kbar K)) := by
      intro n hn hnS u hu
      have h1 := c.rho_mem_rbar (c.K_le hn) hnS (hTR hu)
      rw [c.rho_of_mem_K hn, MulAut.conj_apply] at h1
      exact hRT h1
    refine ⟨fun ht => key z c.z_mem_K hzS t ht, fun ht => ?_⟩
    have h1 := key z⁻¹ (K.inv_mem c.z_mem_K) (inv_mem hzS) _ ht
    have e : (QuotientGroup.mk ⟨z⁻¹, K.inv_mem c.z_mem_K⟩ : Kbar K) = c.zbar⁻¹ := rfl
    rw [e] at h1
    simpa [mul_assoc] using h1
  have hsyl : CFSG.ABGLocalTools.IsSylowOf 2 (T : Subgroup (Kbar K)) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, T.isPGroup', ?_⟩
    rw [relIndex_top_right]
    exact T.not_dvd_index
  have hcard : Nat.card (zpowers c.zbar) = 3 := by rw [Nat.card_zpowers, c.orderOf_zbar]
  have hgen := hGen (Kbar K) hBen T (zpowers c.zbar) hsyl hZT (by rw [hcard]; exact Nat.prime_three)
    (by rw [hcard]; decide)
  refine c.kbarM_ne_top (eq_top_iff.mpr ?_)
  rw [← hgen]
  exact sup_le c.normalizer_zbar_le (hTR.trans c.rbar_le_kbarM)

end Ctx

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614G
