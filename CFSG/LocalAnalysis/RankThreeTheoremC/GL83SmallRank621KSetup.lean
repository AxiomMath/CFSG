module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank621Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank620CampParab
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank620Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627L32Data

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family

variable {G : Type} [Group G] [Finite G] {M B H S K : Subgroup G} {z b : G} {f : ↥K →* GL32}

private theorem Data620.ks_X_le_H (h : Data620 M B H S K z b f) : K ⊔ pCoreOf 2 H ≤ H :=
  sup_le h.K_le (CFSG.LieType.BorelTits.pCoreOf_le 2 H)

private theorem Data620.ks_H_le_normalizer_X (h : Data620 M B H S K z b f) :
    H ≤ normalizer ((K ⊔ pCoreOf 2 H : Subgroup G) : Set G) :=
  fun _ hg => Subgroup.inf_normalizer_le_normalizer_sup K (pCoreOf 2 H)
    ⟨h.K_normal hg, h.eq_normalizer.le hg⟩

private theorem Data620.ks_X_le_normalizer (h : Data620 M B H S K z b f) :
    K ⊔ pCoreOf 2 H ≤ normalizer (pCoreOf 2 H : Set G) :=
  h.ks_X_le_H.trans h.eq_normalizer.le

private theorem Data620.ks_isPGroup_core (h : Data620 M B H S K z b f) :
    IsPGroup 2 (pCoreOf 2 H) :=
  h.maxInv.1.2.1.to_le h.core_le

private theorem Data620.ks_pCoreOf_X (h : Data620 M B H S K z b f) :
    pCoreOf 2 (K ⊔ pCoreOf 2 H) = pCoreOf 2 H := by
  refine le_antisymm ?_ ?_
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans h.ks_X_le_H)
      (h.ks_H_le_normalizer_X.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right
      h.ks_X_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)

omit [Finite G] in
private theorem ks_relIndex_eq {Y T N A : Subgroup G} (hTY : T ≤ Y) (hNA : N ≤ A)
    (hAY : A ≤ Y) (hYN : Y ≤ normalizer (N : Set G)) (hY : Y ≤ T ⊔ N) :
    A.relIndex T = A.relIndex Y := by
  have hNY : N ≤ Y := hNA.trans hAY
  have : (N.subgroupOf Y).Normal := (normal_subgroupOf_iff_le_normalizer hNY).2 hYN
  let π : ↥Y →* ↥Y ⧸ N.subgroupOf Y := QuotientGroup.mk' (N.subgroupOf Y)
  let ψ : ↥T →* ↥Y ⧸ N.subgroupOf Y := π.comp (inclusion hTY)
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have hy : (y : G) ∈ T ⊔ N := hY y.2
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right T N (hTY.trans hYN)] at hy
    obtain ⟨t, ht, n, hn, hty⟩ := Set.mem_mul.1 hy
    refine ⟨⟨t, ht⟩, ?_⟩
    change ((⟨t, hTY ht⟩ : ↥Y) : ↥Y ⧸ N.subgroupOf Y) = y
    rw [QuotientGroup.eq, mem_subgroupOf]
    simpa [← hty] using hn
  have hker : π.ker ≤ A.subgroupOf Y := by
    rw [QuotientGroup.ker_mk']
    exact subgroupOf_mono Y hNA
  have h1 : ((A.subgroupOf Y).map π).index = (A.subgroupOf Y).index :=
    index_map_eq _ (QuotientGroup.mk'_surjective _) hker
  have h2 : (((A.subgroupOf Y).map π).comap ψ).index = ((A.subgroupOf Y).map π).index :=
    index_comap_of_surjective _ hψ
  have h3 : ((A.subgroupOf Y).map π).comap ψ = A.subgroupOf T := by
    change ((A.subgroupOf Y).map π).comap (π.comp (inclusion hTY)) = _
    rw [← comap_comap, comap_map_eq, sup_of_le_left hker]
    ext t
    simp [mem_subgroupOf]
  change (A.subgroupOf T).index = (A.subgroupOf Y).index
  rw [← h3, h2, h1]

private theorem Data620.ks_ker (h : Data620 M B H S K z b f) :
    f.ker = (pCoreOf 2 H).subgroupOf K := by
  ext k
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  exact h.f_ker k

private theorem Data620.ks_relIndex_K (h : Data620 M B H S K z b f) :
    (pCoreOf 2 H).relIndex K = 168 := by
  rw [relIndex, ← h.ks_ker, index_ker, MonoidHom.range_eq_top.2 h.f_surj, card_top]
  exact L32Insp.card_GL

private theorem Data620.ks_relIndex_X (h : Data620 M B H S K z b f) :
    (pCoreOf 2 H).relIndex (K ⊔ pCoreOf 2 H) = 168 := by
  rw [← ks_relIndex_eq le_sup_left le_rfl le_sup_right h.ks_X_le_normalizer le_rfl]
  exact h.ks_relIndex_K

private theorem Data620.ks_card_X (h : Data620 M B H S K z b f) :
    Nat.card (K ⊔ pCoreOf 2 H : Subgroup G) = Nat.card (pCoreOf 2 H : Subgroup G) * 168 := by
  rw [← relIndex_bot_left, ← relIndex_mul_relIndex ⊥ (pCoreOf 2 H) (K ⊔ pCoreOf 2 H) bot_le
    le_sup_right, h.ks_relIndex_X, relIndex_bot_left]

private theorem Data620.ks_card_zpowers (h : Data620 M B H S K z b f) :
    Nat.card (zpowers z) = 3 := by
  rw [Nat.card_zpowers, h.z_order]

private theorem Data620.ks_isPGroup_zpowers (h : Data620 M B H S K z b f) :
    IsPGroup 3 (zpowers z) :=
  IsPGroup.of_card (n := 1) (by rw [h.ks_card_zpowers]; norm_num)

private theorem Data620.ks_z_mem (h : Data620 M B H S K z b f) :
    z ∈ (K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G) :=
  ⟨mem_sup_left h.z_mem_K, h.maxInv.1.2.2 h.z_mem_B⟩

private theorem ks_arith {a c i : ℕ} (h7 : a * 7 = 2 ^ c * 168) (h3 : 3 * i = a) : ¬ 3 ∣ i := by
  have hi : i = 2 ^ c * 8 := by
    generalize 2 ^ c = t at h7
    omega
  rw [hi]
  intro hd
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 hd with hd | hd
  · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
    omega
  · omega

private theorem Data620.ks_not_dvd_index (h : Data620 M B H S K z b f) :
    ¬ 3 ∣ ((zpowers z).subgroupOf ((K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G))).index := by
  obtain ⟨c, hc⟩ := IsPGroup.iff_card.1 h.ks_isPGroup_core
  have hzP : zpowers z ≤ (K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G) :=
    zpowers_le.2 h.ks_z_mem
  have h7 : ((K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G)).relIndex (K ⊔ pCoreOf 2 H) = 7 :=
    h.index_normalizer_eq_seven
  have hP : Nat.card ((K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G) : Subgroup G) * 7 =
      2 ^ c * 168 := by
    have := relIndex_mul_relIndex ⊥ ((K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G))
      (K ⊔ pCoreOf 2 H) bot_le inf_le_left
    rw [relIndex_bot_left, relIndex_bot_left, h7, h.ks_card_X, hc] at this
    exact this
  have hD : 3 * (zpowers z).relIndex ((K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G)) =
      Nat.card ((K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G) : Subgroup G) := by
    have := relIndex_mul_relIndex ⊥ (zpowers z) ((K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G))
      bot_le hzP
    rwa [relIndex_bot_left, relIndex_bot_left, h.ks_card_zpowers] at this
  exact ks_arith hP hD

private theorem Data620.ks_exists_ne_one (h : Data620 M B H S K z b f) :
    ∃ o ∈ pCoreOf 2 H, o ≠ 1 := by
  by_contra hcon'
  have hcon : ∀ o ∈ pCoreOf 2 H, o = 1 := fun o ho => by_contra fun ho1 => hcon' ⟨o, ho, ho1⟩
  refine h.K_not_le fun k hk => ?_
  have hkC : k ∈ centralizer (pCoreOf 2 H : Set G) := by
    rw [mem_centralizer_iff]
    intro o ho
    rw [hcon o ho]
    simp
  have hk1 : k = 1 := hcon k (h.charTwo H h.twoLocal ⟨h.K_le hk, hkC⟩)
  rw [hk1]
  exact M.one_mem

private theorem Data620.ks_exists_noncomm (h : Data620 M B H S K z b f) :
    ∃ x ∈ K ⊔ pCoreOf 2 H, b * x ≠ x * b := by
  obtain ⟨o, ho, ho1⟩ := h.ks_exists_ne_one
  exact ⟨o, mem_sup_right ho, fun hbo => ho1 (h.b_fpf o ho hbo)⟩

private theorem Data620.ks_b_pow (h : Data620 M B H S K z b f) : b ^ 3 = 1 := by
  rw [← h.b_order]
  exact pow_orderOf_eq_one b

private theorem Data620.ks_B_le (h : Data620 M B H S K z b f) :
    B ≤ K ⊔ pCoreOf 2 H ⊔ zpowers b := by
  rw [h.B_eq]
  exact sup_le (le_sup_of_le_left (zpowers_le.2 (mem_sup_left h.z_mem_K))) le_sup_right

private theorem Data620.ks_isPGroup_B (h : Data620 M B H S K z b f) : IsPGroup 3 B :=
  IsPGroup.of_card (n := 2) (by rw [h.B_card]; norm_num)

private theorem Data620.ks_zpowers_le (h : Data620 M B H S K z b f) : zpowers z ≤ B :=
  zpowers_le.2 h.z_mem_B

private theorem Data620.ks_not_dvd_index_B (h : Data620 M B H S K z b f) :
    ¬ 3 ∣ (B.subgroupOf (K ⊔ pCoreOf 2 H ⊔ zpowers b)).index := by
  have hXb : K ⊔ pCoreOf 2 H ⊔ zpowers b ≤ H :=
    sup_le h.ks_X_le_H (zpowers_le.2 (h.B_le h.b_mem))
  intro hd
  apply h.B_sylow
  rw [← relIndex_mul_relIndex B (K ⊔ pCoreOf 2 H ⊔ zpowers b) H h.ks_B_le hXb]
  exact Dvd.dvd.mul_right hd _

private theorem Data620.ks_key (hK : KFactLemma2813) (h : Data620 M B H S K z b f)
    {R : Subgroup G} (hSR : S ≤ R) (hRX : R ≤ K ⊔ pCoreOf 2 H) (hR2 : IsPGroup 2 R)
    (hRi : ¬ 2 ∣ (R.subgroupOf (K ⊔ pCoreOf 2 H)).index) :
    Nat.card ↥⁅omegaCenter S, zpowers z⁆ ≤ 16 ∧
      ((K ⊔ pCoreOf 2 H) ⊓ centralizer ((omegaCenter R : Subgroup G) : Set G) ≠
          (K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G) →
        ¬ K ⊔ pCoreOf 2 H ≤ centralizer ((omegaCenter R : Subgroup G) : Set G) →
        ∀ v ∈ omegaCenter S, v * z = z * v → ∀ x ∈ K ⊔ pCoreOf 2 H, v * x = x * v) ∧
      (K ⊔ pCoreOf 2 H ≤ centralizer ((omegaCenter R : Subgroup G) : Set G) →
        ∀ v ∈ omegaCenter S, v * z = z * v → ∀ y ∈ B, ∀ x ∈ K ⊔ pCoreOf 2 H,
          (v * y * v⁻¹ * y⁻¹) * x = x * (v * y * v⁻¹ * y⁻¹)) := by
  have h0 := h.ks_pCoreOf_X
  have h1 : (K ⊔ pCoreOf 2 H) ⊓ centralizer (pCoreOf 2 (K ⊔ pCoreOf 2 H) : Set G) ≤
      pCoreOf 2 (K ⊔ pCoreOf 2 H) := by
    rw [h0]
    exact (inf_le_inf_right _ h.ks_X_le_H).trans (h.charTwo H h.twoLocal)
  have h2 : K ⊔ pCoreOf 2 H = K ⊔ pCoreOf 2 (K ⊔ pCoreOf 2 H) := by rw [h0]
  have h3 : ∃ f' : ↥K →* GL32, Function.Surjective f' ∧
      ∀ k : ↥K, f' k = 1 ↔ (k : G) ∈ pCoreOf 2 (K ⊔ pCoreOf 2 H) :=
    ⟨f, h.f_surj, fun k => by rw [h0]; exact h.f_ker k⟩
  have h5 : R ≤ (K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G) :=
    le_inf hRX (h.le_normalizer_of_sylow hSR hRX hR2 hRi)
  have hV : normalizer ((omegaCenter S : Subgroup G) : Set G) ≤ M :=
    h.char_le _ (omegaCenter_le S) (omegaCenter_ne_bot h.maxInv.1.2.1 h.S_ne_bot)
      (omegaCenter_characteristic S)
  have h7 : ∀ Q₀ : Subgroup G,
      Q₀ ≤ pCoreOf 2 ((K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G)) → Q₀ ≠ ⊥ →
      (Q₀.subgroupOf (pCoreOf 2 ((K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G)))).Characteristic →
      ¬ K ⊔ pCoreOf 2 H ≤
        ((K ⊔ pCoreOf 2 H) ⊓ centralizer ((omegaCenter
          (pCoreOf 2 ((K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G))) : Subgroup G) : Set G)) ⊔
        ((K ⊔ pCoreOf 2 H) ⊓ normalizer (Q₀ : Set G)) := by
    intro Q₀ hQS hQ hchar hX
    rw [h.pCoreOf_normalizer_eq] at hQS hchar hX
    have hQM : normalizer (Q₀ : Set G) ≤ M := h.char_le Q₀ hQS hQ hchar
    have hCV : (K ⊔ pCoreOf 2 H) ⊓ centralizer ((omegaCenter S : Subgroup G) : Set G) ≤ M :=
      inf_le_right.trans ((centralizer_le_normalizer _).trans hV)
    have hNQ : (K ⊔ pCoreOf 2 H) ⊓ normalizer (Q₀ : Set G) ≤ M := inf_le_right.trans hQM
    exact h.K_not_le fun k hk => sup_le hCV hNQ (hX (mem_sup_left hk))
  have key := hK G (K ⊔ pCoreOf 2 H) K R ((K ⊔ pCoreOf 2 H) ⊓ normalizer (S : Set G)) b h1
    le_sup_left (h.ks_X_le_H.trans h.K_normal) h.K_perfect h2 h3 hRX hR2 hRi h5 inf_le_left
    h.index_normalizer_eq_seven h7 (zpowers z) (zpowers_le.2 h.ks_z_mem)
    h.ks_isPGroup_zpowers h.ks_not_dvd_index
  rw [h.pCoreOf_normalizer_eq, h0] at key
  obtain ⟨k1, k2, k3⟩ := key
  refine ⟨k1, fun hne hn v hv hvz x hx => k2 hne hn v hv (fun d hd => ?_) x hx, ?_⟩
  · obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hd
    exact ((show Commute v z from hvz).zpow_right n).eq
  · intro hXc v hv hvz y hy x hx
    refine k3 hXc (h.ks_H_le_normalizer_X (h.B_le h.b_mem)) h.ks_b_pow h.b_cent
      h.ks_exists_noncomm B h.ks_B_le h.ks_isPGroup_B h.ks_zpowers_le h.ks_not_dvd_index_B v hv
      (fun d hd => ?_) y hy x hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hd
    exact ((show Commute v z from hvz).zpow_right n).eq

private theorem Data620.ks_comm (h : Data620 M B H S K z b f) : z * b = b * z := by
  have := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := B)
    (by rw [h.B_card]; norm_num)
  exact congrArg Subtype.val
    (this.is_comm.comm (⟨z, h.z_mem_B⟩ : B) (⟨b, h.b_mem⟩ : B))

private theorem Data620.ks_omegaCenter_le_core (h : Data620 M B H S K z b f) :
    omegaCenter S ≤ pCoreOf 2 H := by
  intro v hv
  obtain ⟨hvS, hvC, -⟩ := mem_omegaCenter.1 hv
  have hvO : v ∈ centralizer (pCoreOf 2 H : Set G) :=
    mem_centralizer_iff.2 fun o ho => (hvC o (h.core_le ho)).symm
  exact h.charTwo H h.twoLocal ⟨h.maxInv.1.1 hvS, hvO⟩

private theorem Data620.ks_conj_mem (h : Data620 M B H S K z b f) {a : G}
    (ha : a ∈ omegaCenter S ⊓ centralizer ({z} : Set G)) :
    b * a * b⁻¹ ∈ omegaCenter S ⊓ centralizer ({z} : Set G) := by
  obtain ⟨haV, haz⟩ := Subgroup.mem_inf.1 ha
  rw [mem_centralizer_singleton_iff] at haz
  refine Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 (normalizer_le_normalizer_omegaCenter S
    (h.maxInv.1.2.2 h.b_mem)) a).1 haV, mem_centralizer_singleton_iff.2 ?_⟩
  have hbz : b⁻¹ * z * b = z := by
    rw [mul_assoc, h.ks_comm]
    group
  calc b * a * b⁻¹ * z = b * a * (b⁻¹ * z * b) * b⁻¹ := by group
    _ = b * (a * z) * b⁻¹ := by rw [hbz]; group
    _ = b * (z * a) * b⁻¹ := by rw [haz]
    _ = (b * z) * a * b⁻¹ := by group
    _ = (z * b) * a * b⁻¹ := by rw [h.ks_comm]
    _ = z * (b * a * b⁻¹) := by group

private theorem Data620.ks_exists_commutator (h : Data620 M B H S K z b f) {v : G}
    (hv : v ∈ omegaCenter S ⊓ centralizer ({z} : Set G)) :
    ∃ x ∈ omegaCenter S ⊓ centralizer ({z} : Set G), v = x⁻¹ * (b * x * b⁻¹) := by
  set A : Subgroup G := omegaCenter S ⊓ centralizer ({z} : Set G)
  let e : ↥A → ↥A := fun x =>
    ⟨(x : G)⁻¹ * (b * x * b⁻¹), A.mul_mem (A.inv_mem x.2) (h.ks_conj_mem x.2)⟩
  have he : Function.Injective e := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    have hxy' : x⁻¹ * (b * x * b⁻¹) = y⁻¹ * (b * y * b⁻¹) := congrArg Subtype.val hxy
    have hu : y * x⁻¹ ∈ A := A.mul_mem hy (A.inv_mem hx)
    have e1 : b * y * b⁻¹ = y * x⁻¹ * (b * x * b⁻¹) := by
      calc b * y * b⁻¹ = y * (y⁻¹ * (b * y * b⁻¹)) := by group
        _ = y * (x⁻¹ * (b * x * b⁻¹)) := by rw [← hxy']
        _ = y * x⁻¹ * (b * x * b⁻¹) := by group
    have hcomm : b * (y * x⁻¹) = (y * x⁻¹) * b := by
      calc b * (y * x⁻¹) = (b * y * b⁻¹) * (b * x⁻¹) := by group
        _ = y * x⁻¹ * (b * x * b⁻¹) * (b * x⁻¹) := by rw [e1]
        _ = (y * x⁻¹) * b := by group
    have h1 := h.b_fpf _ (h.ks_omegaCenter_le_core (Subgroup.mem_inf.1 hu).1) hcomm
    exact Subtype.ext (mul_inv_eq_one.1 h1).symm
  obtain ⟨x, hx⟩ := Finite.injective_iff_surjective.1 he ⟨v, hv⟩
  exact ⟨x, x.2, (congrArg Subtype.val hx).symm⟩

private theorem Data620.ks_central_of_commutators (h : Data620 M B H S K z b f)
    (hc : ∀ v ∈ omegaCenter S, v * z = z * v → ∀ x ∈ K ⊔ pCoreOf 2 H,
      (v * b * v⁻¹ * b⁻¹) * x = x * (v * b * v⁻¹ * b⁻¹)) :
    ∀ v ∈ omegaCenter S, v * z = z * v → ∀ x ∈ K ⊔ pCoreOf 2 H, v * x = x * v := by
  intro v hv hvz x hx
  obtain ⟨w, hw, rfl⟩ := h.ks_exists_commutator
    (show v ∈ omegaCenter S ⊓ centralizer ({z} : Set G) from
      Subgroup.mem_inf.2 ⟨hv, mem_centralizer_singleton_iff.2 hvz⟩)
  obtain ⟨hwV, hwz⟩ := Subgroup.mem_inf.1 ((omegaCenter S ⊓ centralizer ({z} : Set G)).inv_mem hw)
  have e : w⁻¹ * b * w⁻¹⁻¹ * b⁻¹ = w⁻¹ * (b * w * b⁻¹) := by group
  rw [← e]
  exact hc w⁻¹ hwV (mem_centralizer_singleton_iff.1 hwz) x hx

theorem Data620.k2813_conclusion (hK : KFactLemma2813) (h : Data620 M B H S K z b f)
    {R : Subgroup G} (hSR : S ≤ R) (hRX : R ≤ K ⊔ pCoreOf 2 H) (hR2 : IsPGroup 2 R)
    (hRi : ¬ 2 ∣ (R.subgroupOf (K ⊔ pCoreOf 2 H)).index)
    (hfail : ¬ ((K ⊔ pCoreOf 2 H) ⊓ centralizer ((omegaCenter R : Subgroup G) : Set G) ≤
      normalizer (S : Set G))) :
    Nat.card ↥⁅omegaCenter S, zpowers z⁆ ≤ 16 ∧
      ∀ v ∈ omegaCenter S, v * z = z * v → ∀ y ∈ K ⊔ pCoreOf 2 H, v * y = y * v := by
  obtain ⟨k1, k2, k3⟩ := h.ks_key hK hSR hRX hR2 hRi
  refine ⟨k1, ?_⟩
  by_cases hXc : K ⊔ pCoreOf 2 H ≤ centralizer ((omegaCenter R : Subgroup G) : Set G)
  · exact h.ks_central_of_commutators fun v hv hvz x hx => k3 hXc v hv hvz b h.b_mem x hx
  · exact fun v hv hvz x hx => k2 (fun heq => hfail (heq.le.trans inf_le_right)) hXc v hv hvz x hx

end CFSG.LocalAnalysis.RankThreeTheoremC
