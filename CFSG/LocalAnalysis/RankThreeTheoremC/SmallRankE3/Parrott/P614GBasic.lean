module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank619Group
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Lines
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614G

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

variable {G : Type} [Group G] [Finite G]

structure Ctx (M B H S K : Subgroup G) (z : G) : Prop where
  charTwo : H ⊓ centralizer (pCoreOf 2 H : Set G) ≤ pCoreOf 2 H
  eq_normalizer : H = normalizer (pCoreOf 2 H : Set G)
  H_ne_top : H ≠ ⊤
  kGroup : ∀ X : Subgroup G, X ≤ H → CFSG.Open.IsKGroup ↥X
  B_le : B ≤ H
  B_three : IsPGroup 3 B
  maxInv : IsMaxTwoInvariantIn B H S
  core_le : pCoreOf 2 H ≤ S
  S_ne_bot : S ≠ ⊥
  S_le_M : S ≤ M
  norm_le : ∀ S₀ : Subgroup G, pCoreOf 2 H < S₀ → S₀ ≤ S → S ⊔ B ≤ normalizer (S₀ : Set G) →
    normalizer (S₀ : Set G) ≤ M
  char_le : ∀ S₀ : Subgroup G, S₀ ≤ S → S₀ ≠ ⊥ → (S₀.subgroupOf S).Characteristic →
    normalizer (S₀ : Set G) ≤ M
  core_eq : rankThreePrimeCore 3 H = pCoreOf 2 H
  comp : PComp 3 M H K z
  NZ_le : normalizer ((zpowers z : Subgroup G) : Set G) ≤ M
  z_mem_B : z ∈ B
  z_order : orderOf z = 3
  chevAlt : ChevTwoOrAlt (Kbar K)

theorem Ctx.of_hyp {P : Sylow 3 G} {M : Subgroup G} {x z : G} {H S K : Subgroup G}
    (hyp : Hyp P M x z H S) (st : Stage618 M H K z) :
    Ctx M (zpowers x ⊔ zpowers z) H S K z := by
  have hpair := hyp.optimal.ext.pair
  have hpl := SmallRankPlane.of_situation hyp.setting hyp.situation hyp.point hyp.central
  have hBP : zpowers x ⊔ zpowers z ≤ (P : Subgroup G) := hpl.isIsolatedPlane.1
  have hzo : orderOf z = 3 := orderOf_eq_prime hyp.central.pow_eq_one hyp.central.ne_one
  have hO2 : IsPGroup 2 (pCoreOf 2 H) := pCoreOf_isPGroup 2 H
  have hHtop : H ≠ ⊤ := by
    intro hH
    have hsimple : IsSimpleGroup G := hyp.setting.simple
    have hn : (pCoreOf 2 H).Normal := by
      rw [← normalizer_eq_top_iff, ← top_le_iff, ← hH]
      exact hyp.optimal.eq_normalizer.le
    rcases hn.eq_bot_or_eq_top with h | h
    · exact twoLocal_pCoreOf_ne_bot H hpair.isTwoLocal h
    · obtain ⟨k, hk⟩ := hO2 ⟨z, h ▸ mem_top z⟩
      have h1 : z ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [hzo] at h2
      exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h2)) (by norm_num)
  exact
    { charTwo := hyp.setting.charTwo H hpair.isTwoLocal
      eq_normalizer := hyp.optimal.eq_normalizer
      H_ne_top := hHtop
      kGroup := fun X hX => CFSG.AGLEmbedding.isKGroup_of_catalogSimpleSections
        (CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hyp.setting.kProper X
          fun h => hHtop (top_le_iff.mp (h ▸ hX)))
      B_le := hpair.le
      B_three := P.isPGroup'.to_le hBP
      maxInv := hyp.optimal.maxInv
      core_le := hyp.optimal.core_le
      S_ne_bot := hpair.ne_bot
      S_le_M := hpair.isMax.1.1.trans inf_le_right
      norm_le := hyp.optimal.norm_le
      char_le := hyp.optimal.char_le
      core_eq := st.core_eq
      comp := st.comp
      NZ_le := normalizer_zpowers_le_of_largeObstruction_empty hyp.setting
        hyp.situation.mem_sigmaA hyp.situation.isCoreMaxLocal
        hyp.situation.largeObstruction_empty hyp.central.mem hyp.central.centralizes
        hyp.central.ne_one hyp.central.pow_eq_one
      z_mem_B := mem_sup_right (mem_zpowers z)
      z_order := hzo
      chevAlt := st.chevAlt }

namespace Ctx

variable {M B H S K : Subgroup G} {z : G}

theorem S_le (c : Ctx M B H S K z) : S ≤ H := c.maxInv.1.1

theorem isPGroup_S (c : Ctx M B H S K z) : IsPGroup 2 S := c.maxInv.1.2.1

theorem B_le_normalizer_S (c : Ctx M B H S K z) : B ≤ normalizer (S : Set G) := c.maxInv.1.2.2

theorem isPGroup_core (c : Ctx M B H S K z) : IsPGroup 2 (pCoreOf 2 H) := pCoreOf_isPGroup 2 H

theorem core_le_M (c : Ctx M B H S K z) : pCoreOf 2 H ≤ M := c.core_le.trans c.S_le_M

theorem K_le (c : Ctx M B H S K z) : K ≤ H := c.comp.le

theorem K_not_le (c : Ctx M B H S K z) : ¬ K ≤ M := c.comp.not_le

theorem core_conj_iff (c : Ctx M B H S K z) {n : G} (hn : n ∈ H) {x : G} :
    x ∈ pCoreOf 2 H ↔ n * x * n⁻¹ ∈ pCoreOf 2 H :=
  mem_normalizer_iff.1 (c.eq_normalizer.le hn) x

theorem core_conj_mem (c : Ctx M B H S K z) {n : G} (hn : n ∈ H) {x : G}
    (hx : x ∈ pCoreOf 2 H) : n * x * n⁻¹ ∈ pCoreOf 2 H := (c.core_conj_iff hn).1 hx

theorem K_conj_mem (c : Ctx M B H S K z) {n : G} (hn : n ∈ H) {k : G} (hk : k ∈ K) :
    n * k * n⁻¹ ∈ K :=
  (mem_normalizer_iff.1 (c.comp.normal hn) k).1 hk

theorem H_le_normalizer_core (c : Ctx M B H S K z) : H ≤ normalizer (pCoreOf 2 H : Set G) :=
  c.eq_normalizer.le

theorem z_mem_K (c : Ctx M B H S K z) : z ∈ K := c.comp.mem (mem_zpowers z)

theorem z_mem_H (c : Ctx M B H S K z) : z ∈ H := c.K_le c.z_mem_K

theorem z_mem_M (c : Ctx M B H S K z) : z ∈ M := c.NZ_le (le_normalizer (mem_zpowers z))

theorem not_mem_core_of_orderOf (c : Ctx M B H S K z) {y : G} (hy : orderOf y = 3) :
    y ∉ pCoreOf 2 H := by
  intro hyO
  obtain ⟨k, hk⟩ := c.isPGroup_core ⟨y, hyO⟩
  have h1 : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [hy] at h2
  exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow h2)) (by norm_num)

theorem z_not_mem_core (c : Ctx M B H S K z) : z ∉ pCoreOf 2 H :=
  c.not_mem_core_of_orderOf c.z_order

theorem K_lt (c : Ctx M B H S K z) : K ⊓ pCoreOf 2 H < K := by
  have h := c.comp.lt
  rwa [c.core_eq] at h

theorem K_maximal (c : Ctx M B H S K z) (N : Subgroup G) (hNK : N ≤ K)
    (hN : (N.subgroupOf K).Normal) (hle : K ⊓ pCoreOf 2 H ≤ N) :
    N = K ⊓ pCoreOf 2 H ∨ N = K := by
  have h := c.comp.maximal N hNK hN (by rwa [c.core_eq])
  rwa [c.core_eq] at h

theorem le_core_of_coprime (c : Ctx M B H S K z) {N : Subgroup G} (hNH : N ≤ H)
    (hN : (N.subgroupOf H).Normal) (hc : Nat.Coprime 3 (Nat.card N)) : N ≤ pCoreOf 2 H := by
  rw [← c.core_eq]
  exact le_sSup ⟨hNH, hN, hc⟩

theorem pPrimeCore_eq (c : Ctx M B H S K z) :
    CFSG.pPrimeCore 3 ↥K = (pCoreOf 2 H).subgroupOf K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply le_antisymm
  · set N : Subgroup G := (CFSG.pPrimeCore 3 ↥K).map K.subtype with hN
    have hNK : N ≤ K := map_subtype_le _
    have key : ∀ n : G, n ∈ normalizer (K : Set G) → ∀ g ∈ N, n * g * n⁻¹ ∈ N := by
      intro n hn g hg
      obtain ⟨k, hk, rfl⟩ := hg
      have hφ := (Subgroup.characteristic_iff_map_eq.mp
        (CFSG.pPrimeCore_characteristic (p := 3) (G := ↥K))) (K.normalizerMonoidHom ⟨n, hn⟩)
      refine ⟨K.normalizerMonoidHom ⟨n, hn⟩ k, ?_, ?_⟩
      · rw [← hφ]
        exact mem_map_of_mem _ hk
      · simp [Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hNH : H ≤ normalizer (N : Set G) := by
      intro h hh
      rw [mem_normalizer_iff]
      intro g
      refine ⟨key h (c.comp.normal hh) g, fun hg => ?_⟩
      have := key h⁻¹ (c.comp.normal (H.inv_mem hh)) _ hg
      simpa [mul_assoc] using this
    have hcop : Nat.Coprime 3 (Nat.card N) := by
      rw [hN, card_map_of_injective K.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    have hle := c.le_core_of_coprime (hNK.trans c.K_le)
      ((normal_subgroupOf_iff_le_normalizer (hNK.trans c.K_le)).mpr hNH) hcop
    intro k hk
    exact mem_subgroupOf.mpr (hle ⟨k, hk, rfl⟩)
  · have hnorm : ((pCoreOf 2 H).subgroupOf K).Normal :=
      ⟨fun n hn g => mem_subgroupOf.mpr (by
        simpa using c.core_conj_mem (c.K_le g.2) (mem_subgroupOf.mp hn))⟩
    have hcop : Nat.Coprime 3 (Nat.card ((pCoreOf 2 H).subgroupOf K)) := by
      have h2 : IsPGroup 2 ((pCoreOf 2 H).subgroupOf K) := c.isPGroup_core.comap_subtype
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
      rw [hn]
      exact Nat.Coprime.pow_right n (by norm_num)
    unfold CFSG.pPrimeCore
    exact le_sSup ⟨hnorm, hcop⟩

theorem mk_eq_one_iff (c : Ctx M B H S K z) (k : ↥K) :
    (QuotientGroup.mk k : Kbar K) = 1 ↔ (k : G) ∈ pCoreOf 2 H := by
  rw [QuotientGroup.eq_one_iff, c.pPrimeCore_eq, mem_subgroupOf]

theorem mk_eq_mk_iff (c : Ctx M B H S K z) (k k' : ↥K) :
    (QuotientGroup.mk k : Kbar K) = QuotientGroup.mk k' ↔ (k : G)⁻¹ * k' ∈ pCoreOf 2 H := by
  rw [QuotientGroup.eq, c.pPrimeCore_eq, mem_subgroupOf]
  simp

noncomputable abbrev zbar (c : Ctx M B H S K z) : Kbar K :=
  QuotientGroup.mk ⟨z, c.z_mem_K⟩

theorem orderOf_zbar (c : Ctx M B H S K z) : orderOf c.zbar = 3 := by
  have h3 : z ^ 3 = 1 := by rw [← c.z_order]; exact pow_orderOf_eq_one z
  refine orderOf_eq_prime ?_ ?_
  · have h3' : (⟨z, c.z_mem_K⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using h3)
    rw [zbar, ← QuotientGroup.mk_pow, h3', QuotientGroup.mk_one]
  · intro h
    exact c.z_not_mem_core ((c.mk_eq_one_iff _).1 h)

theorem isSimpleGroup (c : Ctx M B H S K z) : IsSimpleGroup (Kbar K) := by
  have hnt : Nontrivial (Kbar K) := by
    refine ⟨⟨c.zbar, 1, fun h => ?_⟩⟩
    have := c.orderOf_zbar
    rw [h, orderOf_one] at this
    omega
  refine ⟨fun N hN => ?_⟩
  have hN'K : (N.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))).map K.subtype ≤ K :=
    map_subtype_le _
  have hsub : ((N.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))).map K.subtype).subgroupOf K =
      N.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)) :=
    comap_map_eq_self_of_injective K.subtype_injective _
  have hnorm : (((N.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))).map
      K.subtype).subgroupOf K).Normal := by
    rw [hsub]
    exact hN.comap _
  have hle : K ⊓ pCoreOf 2 H ≤ (N.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))).map
      K.subtype := by
    rintro g ⟨hgK, hgO⟩
    refine mem_map.mpr ⟨⟨g, hgK⟩, ?_, rfl⟩
    rw [mem_comap, QuotientGroup.mk'_apply, (c.mk_eq_one_iff _).2 hgO]
    exact N.one_mem
  rcases c.K_maximal _ hN'K hnorm hle with h | h
  · left
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    have hk : (k : G) ∈ (N.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))).map K.subtype :=
      ⟨k, hq, rfl⟩
    have hk' : (k : G) ∈ K ⊓ pCoreOf 2 H := h ▸ hk
    exact (mem_bot).mpr ((c.mk_eq_one_iff k).2 hk'.2)
  · right
    rw [eq_top_iff]
    intro q _
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    have hk : (k : G) ∈ (N.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))).map K.subtype := by
      rw [h]
      exact k.2
    obtain ⟨k', hk', hkk'⟩ := hk
    rw [← Subtype.ext hkk']
    exact hk'

theorem exists_ne_comm (c : Ctx M B H S K z) : ∃ a b : Kbar K, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hcomm : ⁅K, K⁆ ≤ pCoreOf 2 H := by
    rw [commutator_le]
    intro g hg g' hg'
    have h1 := hcon (QuotientGroup.mk ⟨g, hg⟩) (QuotientGroup.mk ⟨g', hg'⟩)
    have h2 : (QuotientGroup.mk ((⟨g, hg⟩ : ↥K) * ⟨g', hg'⟩ * (⟨g, hg⟩ : ↥K)⁻¹ *
        (⟨g', hg'⟩ : ↥K)⁻¹) : Kbar K) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, QuotientGroup.mk_inv, h1]
      group
    rw [commutatorElement_def]
    simpa using (c.mk_eq_one_iff _).1 h2
  have hKO : K ≤ pCoreOf 2 H := c.comp.perfect ▸ hcomm
  exact (lt_irrefl K) (lt_of_le_of_lt (le_inf le_rfl hKO) c.K_lt)

theorem center_eq_bot (c : Ctx M B H S K z) : Subgroup.center (Kbar K) = ⊥ := by
  have := c.isSimpleGroup
  rcases (Subgroup.center (Kbar K)).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := c.exists_ne_comm
    exact hab (Subgroup.mem_center_iff.mp (h ▸ mem_top b) a)

theorem exists_rho (c : Ctx M B H S K z) : ∃ Φ : ↥H →* MulAut (Kbar K), ∀ (n : ↥H) (k k' : ↥K),
    (k' : G) = (n : G) * (k : G) * (n : G)⁻¹ →
      Φ n (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) k) =
        QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) k' :=
  exists_inducedHom K H (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))
    (QuotientGroup.mk'_surjective _) c.comp.normal fun n hn k k' hk' => by
      simp only [QuotientGroup.mk'_apply]
      rw [c.mk_eq_one_iff, c.mk_eq_one_iff, hk']
      exact c.core_conj_iff hn

@[expose] noncomputable def rho (c : Ctx M B H S K z) : ↥H →* MulAut (Kbar K) := c.exists_rho.choose

theorem rho_mk (c : Ctx M B H S K z) {n : G} (hn : n ∈ H) (k : ↥K) :
    c.rho ⟨n, hn⟩ (QuotientGroup.mk k : Kbar K) =
      QuotientGroup.mk (⟨n * k * n⁻¹, c.K_conj_mem hn k.2⟩ : ↥K) :=
  c.exists_rho.choose_spec ⟨n, hn⟩ k _ rfl

theorem rho_of_mem_K (c : Ctx M B H S K z) {k : G} (hk : k ∈ K) :
    c.rho ⟨k, c.K_le hk⟩ = MulAut.conj (QuotientGroup.mk ⟨k, hk⟩ : Kbar K) := by
  ext q
  obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective q
  rw [c.rho_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  rfl

theorem rho_eq_one_iff (c : Ctx M B H S K z) {n : G} (hn : n ∈ H) :
    c.rho ⟨n, hn⟩ = 1 ↔ ∀ k ∈ K, n * k * n⁻¹ * k⁻¹ ∈ pCoreOf 2 H := by
  constructor
  · intro h k hk
    have h1 := c.rho_mk hn ⟨k, hk⟩
    rw [h, MulAut.one_apply, eq_comm, c.mk_eq_mk_iff] at h1
    have h1' : (n * k * n⁻¹)⁻¹ * k ∈ pCoreOf 2 H := h1
    have e : n * k * n⁻¹ * k⁻¹ = k * ((n * k * n⁻¹)⁻¹ * k)⁻¹ * k⁻¹ := by group
    rw [e]
    exact c.core_conj_mem (c.K_le hk) (inv_mem h1')
  · intro h
    ext q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    rw [c.rho_mk, MulAut.one_apply, c.mk_eq_mk_iff]
    have e : (n * (k : G) * n⁻¹)⁻¹ * k = (k : G)⁻¹ * (n * k * n⁻¹ * (k : G)⁻¹)⁻¹ * k := by group
    rw [e]
    simpa using c.core_conj_mem (c.K_le (K.inv_mem k.2)) (inv_mem (h k k.2))

theorem rho_eq_one_of_mem_core (c : Ctx M B H S K z) {o : G} (ho : o ∈ pCoreOf 2 H) :
    c.rho ⟨o, c.S_le (c.core_le ho)⟩ = 1 := by
  refine (c.rho_eq_one_iff _).2 fun k hk => ?_
  have e : o * k * o⁻¹ * k⁻¹ = o * (k * o⁻¹ * k⁻¹) := by group
  rw [e]
  exact mul_mem ho (c.core_conj_mem (c.K_le hk) (inv_mem ho))

theorem mem_core_of_mem_K (c : Ctx M B H S K z) {k : G} (hk : k ∈ K)
    (h : c.rho ⟨k, c.K_le hk⟩ = 1) : k ∈ pCoreOf 2 H := by
  rw [c.rho_of_mem_K hk] at h
  set y : Kbar K := QuotientGroup.mk ⟨k, hk⟩ with hy
  have hc : y ∈ Subgroup.center (Kbar K) := by
    rw [Subgroup.mem_center_iff]
    intro q
    have := congrArg (fun φ : MulAut (Kbar K) => φ q) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc q * y = (y * q * y⁻¹) * y := by rw [this]
      _ = y * q := by group
  rw [c.center_eq_bot, mem_bot] at hc
  exact (c.mk_eq_one_iff _).1 hc

omit [Finite G] in
theorem pow_mem_of_pow_eq_one {N T : Subgroup G} (hT : T ≤ normalizer (N : Set G))
    {n t : G} (hn : n ∈ N) (ht : t ∈ T) {m : ℕ} (htm : t ^ m = 1) : (n * t) ^ m ∈ N := by
  have key : ∀ j : ℕ, ∃ n' ∈ N, (n * t) ^ j = n' * t ^ j := by
    intro j
    induction j with
    | zero => exact ⟨1, N.one_mem, by simp⟩
    | succ j ih =>
      obtain ⟨n', hn', e⟩ := ih
      refine ⟨n' * (t ^ j * n * (t ^ j)⁻¹), N.mul_mem hn' ?_, ?_⟩
      · exact le_normalizer_iff.1 hT _ (T.pow_mem ht j) n hn
      · rw [pow_succ, e]
        group
  obtain ⟨n', hn', e⟩ := key m
  rw [e, htm, mul_one]
  exact hn'

theorem exists_mul_KS (c : Ctx M B H S K z) {y : G} (hy : y ∈ K ⊔ S) :
    ∃ k ∈ K, ∃ s ∈ S, y = k * s := by
  rw [← SetLike.mem_coe,
    coe_mul_of_right_le_normalizer_left K S (c.S_le.trans c.comp.normal)] at hy
  obtain ⟨k, hk, s, hs, rfl⟩ := Set.mem_mul.1 hy
  exact ⟨k, hk, s, hs, rfl⟩

@[expose] noncomputable def centK (c : Ctx M B H S K z) : Subgroup G := c.rho.ker.map H.subtype

theorem mem_centK (c : Ctx M B H S K z) {y : G} :
    y ∈ c.centK ↔ ∃ hy : y ∈ H, c.rho ⟨y, hy⟩ = 1 := by
  constructor
  · rintro ⟨y', hy', rfl⟩
    exact ⟨y'.2, hy'⟩
  · rintro ⟨hy, h⟩
    exact ⟨⟨y, hy⟩, h, rfl⟩

theorem H_le_normalizer_centK (c : Ctx M B H S K z) : H ≤ normalizer (c.centK : Set G) := by
  rw [le_normalizer_iff]
  intro g hg y hy
  obtain ⟨hyH, h⟩ := c.mem_centK.1 hy
  refine c.mem_centK.2 ⟨H.mul_mem (H.mul_mem hg hyH) (H.inv_mem hg), ?_⟩
  have e : (⟨g * y * g⁻¹, H.mul_mem (H.mul_mem hg hyH) (H.inv_mem hg)⟩ : ↥H) =
      ⟨g, hg⟩ * ⟨y, hyH⟩ * (⟨g, hg⟩ : ↥H)⁻¹ := rfl
  rw [e, map_mul, map_mul, h, mul_one, map_inv, mul_inv_cancel]

@[expose] noncomputable def dSub (c : Ctx M B H S K z) : Subgroup G := c.centK ⊓ (K ⊔ S)

theorem isPGroup_dSub (c : Ctx M B H S K z) : IsPGroup 2 c.dSub := by
  rintro ⟨d, hdC, hdKS⟩
  obtain ⟨k, hk, s, hs, rfl⟩ := c.exists_mul_KS hdKS
  obtain ⟨m, hm⟩ := c.isPGroup_S ⟨s, hs⟩
  have hs' : s ^ 2 ^ m = 1 := congrArg Subtype.val hm
  have h1 : (k * s) ^ 2 ^ m ∈ K :=
    pow_mem_of_pow_eq_one (c.S_le.trans c.comp.normal) hk hs hs'
  have h2 : (k * s) ^ 2 ^ m ∈ c.centK := c.centK.pow_mem hdC _
  obtain ⟨hH, h3⟩ := c.mem_centK.1 h2
  obtain ⟨r, hr⟩ := c.isPGroup_core ⟨_, c.mem_core_of_mem_K h1 h3⟩
  have hr' : ((k * s) ^ 2 ^ m) ^ 2 ^ r = 1 := congrArg Subtype.val hr
  refine ⟨m + r, Subtype.ext ?_⟩
  show (k * s) ^ 2 ^ (m + r) = 1
  rw [pow_add, pow_mul]
  exact hr'

theorem core_le_dSub (c : Ctx M B H S K z) : pCoreOf 2 H ≤ c.dSub :=
  fun o ho => ⟨c.mem_centK.2 ⟨_, c.rho_eq_one_of_mem_core ho⟩, mem_sup_right (c.core_le ho)⟩

theorem mem_normalizer_dSub (c : Ctx M B H S K z) {g : G} (hg : g ∈ H)
    (hg' : g ∈ normalizer ((K ⊔ S : Subgroup G) : Set G)) :
    g ∈ normalizer (c.dSub : Set G) :=
  inf_normalizer_le_normalizer_inf ⟨c.H_le_normalizer_centK hg, hg'⟩

theorem S_le_normalizer_dSub (c : Ctx M B H S K z) : S ≤ normalizer (c.dSub : Set G) :=
  fun _ hs => c.mem_normalizer_dSub (c.S_le hs) ((K ⊔ S).le_normalizer (mem_sup_right hs))

theorem K_le_normalizer_dSub (c : Ctx M B H S K z) : K ≤ normalizer (c.dSub : Set G) :=
  fun _ hk => c.mem_normalizer_dSub (c.K_le hk) ((K ⊔ S).le_normalizer (mem_sup_left hk))

theorem B_le_normalizer_dSub (c : Ctx M B H S K z) : B ≤ normalizer (c.dSub : Set G) :=
  fun _ hb => c.mem_normalizer_dSub (c.B_le hb)
    (inf_normalizer_le_normalizer_sup K S ⟨c.comp.normal (c.B_le hb), c.B_le_normalizer_S hb⟩)

theorem dSub_le_S (c : Ctx M B H S K z) : c.dSub ≤ S := by
  have hjoin : IsTwoInvariantIn B H (c.dSub ⊔ S) :=
    ⟨sup_le (inf_le_left.trans (map_subtype_le _)) c.S_le,
      c.isPGroup_dSub.to_sup_of_normal_left' c.isPGroup_S c.S_le_normalizer_dSub,
      fun b hb => inf_normalizer_le_normalizer_sup _ _
        ⟨c.B_le_normalizer_dSub hb, c.B_le_normalizer_S hb⟩⟩
  exact le_sup_left.trans (c.maxInv.2 _ hjoin le_sup_right).le

theorem dSub_le_core (c : Ctx M B H S K z) : c.dSub ≤ pCoreOf 2 H := by
  by_contra hne
  have hlt : pCoreOf 2 H < c.dSub := lt_of_le_of_ne c.core_le_dSub fun e => hne e.ge
  exact c.K_not_le (c.K_le_normalizer_dSub.trans
    (c.norm_le _ hlt c.dSub_le_S (sup_le c.S_le_normalizer_dSub c.B_le_normalizer_dSub)))

theorem mem_core_of_trivial (c : Ctx M B H S K z) {y : G} (hyH : y ∈ H)
    (hy : c.rho ⟨y, hyH⟩ = 1) (hyKS : y ∈ K ⊔ S) : y ∈ pCoreOf 2 H :=
  c.dSub_le_core ⟨c.mem_centK.2 ⟨hyH, hy⟩, hyKS⟩

theorem mem_sup_of_inner (c : Ctx M B H S K z) {s : G} (hs : s ∈ S)
    (h : c.rho ⟨s, c.S_le hs⟩ ∈ (MulAut.conj : Kbar K →* MulAut (Kbar K)).range) :
    s ∈ K ⊔ pCoreOf 2 H := by
  obtain ⟨q, hq⟩ := h
  obtain ⟨k₀, rfl⟩ := QuotientGroup.mk_surjective q
  have hk₀H : (k₀ : G)⁻¹ ∈ H := H.inv_mem (c.K_le k₀.2)
  have hyH : (k₀ : G)⁻¹ * s ∈ H := H.mul_mem hk₀H (c.S_le hs)
  have hy : c.rho ⟨(k₀ : G)⁻¹ * s, hyH⟩ = 1 := by
    have e : (⟨(k₀ : G)⁻¹ * s, hyH⟩ : ↥H) =
        (⟨(k₀ : G), c.K_le k₀.2⟩ : ↥H)⁻¹ * ⟨s, c.S_le hs⟩ := rfl
    rw [e, map_mul, map_inv, ← hq, c.rho_of_mem_K k₀.2]
    exact inv_mul_cancel _
  have hyKS : (k₀ : G)⁻¹ * s ∈ K ⊔ S := mul_mem (mem_sup_left (inv_mem k₀.2)) (mem_sup_right hs)
  have e : s = (k₀ : G) * ((k₀ : G)⁻¹ * s) := by group
  rw [e]
  exact mul_mem (mem_sup_left k₀.2) (mem_sup_right (c.mem_core_of_trivial hyH hy hyKS))

omit [Finite G] in
theorem le_normalizer_of_conj {X Y : Subgroup G} (h : ∀ x ∈ X, ∀ y ∈ Y, x * y * x⁻¹ ∈ Y) :
    X ≤ normalizer (Y : Set G) := by
  intro x hx
  rw [mem_normalizer_iff]
  intro y
  refine ⟨h x hx y, fun hy => ?_⟩
  have h1 := h x⁻¹ (X.inv_mem hx) _ hy
  rwa [show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y by group] at h1

@[expose] noncomputable def pre (K : Subgroup G) (U : Subgroup (Kbar K)) : Subgroup G :=
  (U.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))).map K.subtype

theorem pre_le (K : Subgroup G) (U : Subgroup (Kbar K)) : pre K U ≤ K := map_subtype_le _

theorem mem_pre {K : Subgroup G} {U : Subgroup (Kbar K)} {g : G} (hg : g ∈ K) :
    g ∈ pre K U ↔ (QuotientGroup.mk ⟨g, hg⟩ : Kbar K) ∈ U := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact hk
  · intro h
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem isPGroup_pre (c : Ctx M B H S K z) {U : Subgroup (Kbar K)} (hU : IsPGroup 2 U) :
    IsPGroup 2 (pre K U) := by
  rintro ⟨g, hg⟩
  have hgK := pre_le K U hg
  obtain ⟨a, ha⟩ := hU ⟨_, (mem_pre hgK).1 hg⟩
  have ha' : (QuotientGroup.mk (⟨g, hgK⟩ ^ 2 ^ a) : Kbar K) = 1 := by
    rw [QuotientGroup.mk_pow]
    exact congrArg Subtype.val ha
  obtain ⟨b, hb⟩ := c.isPGroup_core ⟨_, (c.mk_eq_one_iff _).1 ha'⟩
  have hb' : (g ^ 2 ^ a) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
  refine ⟨a + b, Subtype.ext ?_⟩
  show g ^ 2 ^ (a + b) = 1
  rw [pow_add, pow_mul]
  exact hb'

theorem conj_mem_pre (c : Ctx M B H S K z) {U : Subgroup (Kbar K)} {n : G} (hn : n ∈ H)
    (hnU : ∀ u ∈ U, c.rho ⟨n, hn⟩ u ∈ U) {g : G} (hg : g ∈ pre K U) :
    n * g * n⁻¹ ∈ pre K U := by
  have hgK := pre_le K U hg
  refine (mem_pre (c.K_conj_mem hn hgK)).2 ?_
  rw [← c.rho_mk hn ⟨g, hgK⟩]
  exact hnU _ ((mem_pre hgK).1 hg)

theorem pre_le_S (c : Ctx M B H S K z) {U : Subgroup (Kbar K)} (hU : IsPGroup 2 U)
    (hSU : ∀ s (hs : s ∈ S), ∀ u ∈ U, c.rho ⟨s, c.S_le hs⟩ u ∈ U)
    (hBU : ∀ b (hb : b ∈ B), ∀ u ∈ U, c.rho ⟨b, c.B_le hb⟩ u ∈ U) : pre K U ≤ S := by
  have hSQ : S ≤ normalizer (pre K U : Set G) :=
    le_normalizer_of_conj fun s hs _ hg => c.conj_mem_pre (c.S_le hs) (hSU s hs) hg
  have hBQ : B ≤ normalizer (pre K U : Set G) :=
    le_normalizer_of_conj fun b hb _ hg => c.conj_mem_pre (c.B_le hb) (hBU b hb) hg
  have hjoin : IsTwoInvariantIn B H (pre K U ⊔ S) :=
    ⟨sup_le ((pre_le K U).trans c.K_le) c.S_le,
      (c.isPGroup_pre hU).to_sup_of_normal_left' c.isPGroup_S hSQ,
      fun b hb => inf_normalizer_le_normalizer_sup _ _ ⟨hBQ hb, c.B_le_normalizer_S hb⟩⟩
  exact le_sup_left.trans (c.maxInv.2 _ hjoin le_sup_right).le

theorem false_of_cover (c : Ctx M B H S K z)
    (h : ∀ q : Kbar K, ∃ m : ↥K, (m : G) ∈ M ∧ (QuotientGroup.mk m : Kbar K) = q) : False := by
  apply c.K_not_le
  intro k hk
  obtain ⟨m, hm, hq⟩ := h (QuotientGroup.mk ⟨k, hk⟩)
  have h1 := (c.mk_eq_mk_iff _ _).1 hq
  have e : k = (m : G) * ((m : G)⁻¹ * k) := by group
  rw [e]
  exact M.mul_mem hm (c.core_le_M h1)

@[expose] noncomputable def kbarM (K M : Subgroup G) : Subgroup (Kbar K) :=
  (M.subgroupOf K).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))

theorem mk_mem_kbarM {K M : Subgroup G} {k : G} (hk : k ∈ K) (hkM : k ∈ M) :
    (QuotientGroup.mk ⟨k, hk⟩ : Kbar K) ∈ kbarM K M :=
  ⟨⟨k, hk⟩, mem_subgroupOf.mpr hkM, rfl⟩

theorem kbarM_ne_top (c : Ctx M B H S K z) : kbarM K M ≠ ⊤ := by
  intro h
  refine c.false_of_cover fun q => ?_
  obtain ⟨m, hm, rfl⟩ : q ∈ kbarM K M := h ▸ mem_top q
  exact ⟨m, mem_subgroupOf.mp hm, rfl⟩

end Ctx

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614G
