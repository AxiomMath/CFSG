module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiStartBasic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiCoordsModel
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiStageZero
public import CFSG.LocalAnalysis.SeitzReduction.RankOneStart
public import CFSG.LocalAnalysis.SeitzReduction.RankOneKernel
public import CFSG.GH74.Uniqueness.Bender.SuzukiAut

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.Blueprint CFSG.GH74.Uniqueness.Bender

variable {G : Type*} [Group G]

@[expose] def szT₁ (L T : Subgroup G) : Subgroup G := T ⊓ L

@[expose] def szA (L T : Subgroup G) (t : G) : Subgroup G := szA₁ (szT₁ L T) ⊔ zpowers t

theorem szT₁_le_left (L T : Subgroup G) : szT₁ L T ≤ T := inf_le_left

theorem szT₁_le_right (L T : Subgroup G) : szT₁ L T ≤ L := inf_le_right

theorem szA₁_le_szA (L T : Subgroup G) (t : G) : szA₁ (szT₁ L T) ≤ szA L T t := le_sup_left

theorem mem_szA_right (L T : Subgroup G) (t : G) : t ∈ szA L T t :=
  mem_sup_right (mem_zpowers t)

theorem exists_benderType_of_lieModel_twistedB2 {X : Type} [Group X] {f : ℕ}
    (h : LieModel X .twistedB2 0 2 f) : ∃ a : ℕ, 1 ≤ a ∧ f = 2 * a + 1 ∧ BenderType X f 2 1 := by
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := suzukiModel_of_lieModel_twistedB2 h
  exact ⟨a, ha, rfl, BenderType.suzuki a ha (e.trans ((MulEquiv.subgroupCongr
    (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
    ((CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hK).trans
      (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))))⟩

structure SzStart (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G)
    (T : Subgroup G) : Prop where
  setting : SeitzSetting G L
  model : LieModel L .twistedB2 0 2 f
  inv : orderOf t = 2
  mem : t ∈ centralizer (L : Set G)
  le : T ≤ centralizer ({t} : Set G)
  sylow : ∃ P : Sylow 2 (centralizer ({t} : Set G)),
    (P : Subgroup _) = T.subgroupOf (centralizer ({t} : Set G))

namespace SzStart

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem card_sylow
    (h : SzStart G L f t T) : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2 :=
  rankOneKernel G L h.setting (Or.inr (Or.inr ⟨f, h.model⟩))

theorem sq_eq_one (h : SzStart G L f t T) : t ^ 2 = 1 := by
  rw [← h.inv]
  exact pow_orderOf_eq_one t

theorem mem_centralizer_szT₁ (h : SzStart G L f t T) : t ∈ centralizer (szT₁ L T : Set G) :=
  centralizer_le (szT₁_le_right L T) h.mem

theorem isPGroup (h : SzStart G L f t T) : IsPGroup 2 T := by
  obtain ⟨P, hP⟩ := h.sylow
  have hP' := P.isPGroup'
  rw [hP] at hP'
  exact hP'.of_equiv (subgroupOfEquivOfLe h.le)

theorem eq_sup_of_card_sylow (h : SzStart G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    T = szT₁ L T ⊔ zpowers t ∧ szT₁ L T ⊓ zpowers t = ⊥ ∧
      ∃ P : Sylow 2 L, (P : Subgroup L) = (szT₁ L T).subgroupOf L := by
  have hst := h.setting.standardSetting
  obtain ⟨-, htT, -, -, ⟨U, hU⟩, -, hUt, -, hinner⟩ :=
    sylow_centralizer_start_of_card_sylow_eq_two hst.standard h.setting.center_eq_bot hS2 h.mem
      h.inv (hst.core t h.inv) h.le h.sylow
  have hHN := (CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
    hst.standard h.mem h.inv).1
  have hOut := odd_card_outer_of_lieModel_twistedB2 h.model
  refine ⟨le_antisymm (fun x hx => ?_) (sup_le (szT₁_le_left L T) (zpowers_le.mpr htT)), hUt,
    ⟨U, by rw [hU, szT₁, inf_subgroupOf_right]⟩⟩
  obtain ⟨k, hk⟩ := h.isPGroup ⟨x, hx⟩
  have hxk : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨l, hl, hlx⟩ :=
    exists_inv_mul_mem_centralizer_of_odd_card_outer hOut (hHN (h.le hx)) hxk
  refine hinner x hx l hl fun y hy => ?_
  have e := mem_centralizer_iff.mp hlx y hy
  calc x * y * x⁻¹ = l * (l⁻¹ * x * y) * x⁻¹ := by group
    _ = l * (y * (l⁻¹ * x)) * x⁻¹ := by rw [e]
    _ = l * y * l⁻¹ := by group

theorem centralizer_szA_le_of_card_sylow (h : SzStart G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    centralizer (szA L T t : Set G) ≤ szT₁ L T ⊔ zpowers t := by
  have hst := h.setting.standardSetting
  obtain ⟨-, -, Q, hQ⟩ := h.eq_sup_of_card_sylow hS2
  obtain ⟨-, -, -, hB⟩ := exists_benderType_of_lieModel_twistedB2 h.model
  have hHN := (CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
    hst.standard h.mem h.inv).1
  intro x hx
  have hxt : x ∈ centralizer ({t} : Set G) :=
    centralizer_le (Set.singleton_subset_iff.mpr (mem_szA_right L T t)) hx
  have hxA₁ : ∀ b ∈ szA₁ (szT₁ L T), b * x = x * b := fun b hb =>
    mem_centralizer_iff.mp hx b (szA₁_le_szA L T t hb)
  have hmemQ : ∀ y : L, y ∈ (Q : Subgroup L) ↔ (y : G) ∈ szT₁ L T := fun y => by
    rw [hQ, mem_subgroupOf]
  set σ := L.normalizerMonoidHom ⟨x, hHN hxt⟩ with hσ
  have hσz : ∀ z ∈ rootCenter (Q : Subgroup L), σ z = z := by
    intro z hz
    obtain ⟨hzQ, hzC⟩ := mem_inf.mp hz
    have hzA : (z : G) ∈ szA₁ (szT₁ L T) := by
      refine mem_szA₁.mpr ⟨(hmemQ z).mp hzQ, mem_centralizer_iff.mpr fun y hy => ?_⟩
      have hyQ : (⟨y, szT₁_le_right L T hy⟩ : L) ∈ (Q : Subgroup L) := (hmemQ _).mpr hy
      exact congrArg Subtype.val (mem_centralizer_iff.mp hzC _ hyQ)
    apply Subtype.ext
    rw [hσ, normalizerMonoidHom_apply_apply_coe]
    show x * (z : G) * x⁻¹ = z
    rw [← hxA₁ _ hzA, mul_inv_cancel_right]
  obtain ⟨r, hrQ, hσr⟩ := hB.exists_eq_conj_of_centralizes_center_suzuki Q σ hσz
  have hrT₁ : (r : G) ∈ szT₁ L T := (hmemQ r).mp hrQ
  have hconj : ∀ y ∈ L, x * y * x⁻¹ = r * y * (r : G)⁻¹ := by
    intro y hy
    have e := congrArg (fun φ : MulAut L => ((φ ⟨y, hy⟩ : L) : G)) hσr
    simpa [hσ, normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply] using e
  have hrx : (r : G)⁻¹ * x ∈ zpowers t := by
    rw [← inf_centralizer_eq_zpowers_of_card_sylow_eq_two hst.standard hS2 h.mem h.inv
      (hst.core t h.inv)]
    refine mem_inf.mpr ⟨mem_centralizer_iff.mpr fun y hy => ?_,
      mul_mem (inv_mem (h.le (szT₁_le_left L T hrT₁))) hxt⟩
    calc y * ((r : G)⁻¹ * x) = (r : G)⁻¹ * (r * y * (r : G)⁻¹) * x := by group
      _ = (r : G)⁻¹ * (x * y * x⁻¹) * x := by rw [hconj y hy]
      _ = (r : G)⁻¹ * x * y := by group
  have e : x = r * ((r : G)⁻¹ * x) := by group
  rw [e]
  exact mul_mem_sup hrT₁ hrx

theorem facts_of_card_sylow (h : SzStart G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    T = szT₁ L T ⊔ zpowers t ∧ szT₁ L T ⊓ zpowers t = ⊥ ∧
    Nat.card T = 2 * 2 ^ f * 2 ^ f ∧ Nat.card (szA₁ (szT₁ L T)) = 2 ^ f ∧
    szA₁ (szT₁ L T) = ⁅T, T⁆ ∧ T ⊓ centralizer (T : Set G) = szA L T t ∧
    (∀ x ∈ T, x ^ 2 = 1 → x ∈ szA L T t) ∧ centralizer (szA L T t : Set G) = T ∧
    (∀ g : G, g⁻¹ * t * g ∉ szA₁ (szT₁ L T)) ∧
    ∀ g : G, g⁻¹ * t * g ∈ szA L T t →
      ∃ n ∈ normalizer (szA L T t : Set G), n⁻¹ * t * n = g⁻¹ * t * g := by
  obtain ⟨hTeq, hdisj, hT₁syl⟩ := h.eq_sup_of_card_sylow hS2
  have hcentA := h.centralizer_szA_le_of_card_sylow hS2
  have htC₁ := h.mem_centralizer_szT₁
  obtain ⟨-, a, ha, K, _, _, hfa, hK₀, ⟨e⟩⟩ := suzukiModel_of_lieModel_twistedB2 h.model
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK₀, hfa]
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK
  have hKf : Fintype.card K = 2 ^ (2 * a + 1) := by rw [← Nat.card_eq_fintype_card, hK]
  obtain ⟨u, v, κ, hc⟩ := exists_szRootCoords_of_sylow ha hK e (szT₁_le_right L T) hT₁syl
    (one_mem L) (one_mem _)
  have hcomm : szA₁ (szT₁ L T) = ⁅T, T⁆ := by
    have key := hc.szA₁_eq_commutator ha hKf htC₁
    rwa [← hTeq] at key
  have hZT : T ⊓ centralizer (T : Set G) = szA L T t := by
    have key := SzRootCoords.inf_centralizer_sup_eq (T₁ := szT₁ L T) htC₁
    rwa [← hTeq] at key
  have hinv : ∀ x ∈ T, x ^ 2 = 1 → x ∈ szA L T t := fun x hx hx2 =>
    hc.mem_of_sq_eq_one ha hKf htC₁ h.sq_eq_one (by rwa [← hTeq]) hx2
  have hAZ : szA L T t ≤ T ⊓ centralizer (T : Set G) := hZT.ge
  have hTs : ∀ s ∈ szA L T t, T ≤ centralizer ({s} : Set G) := fun s hs y hy =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (mem_inf.mp (hAZ hs)).2 y hy)
  refine ⟨hTeq, hdisj, ?_, ?_, hcomm, hZT, hinv, ?_, ?_, ?_⟩
  · have hcard := card_sup_zpowers_of_disjoint htC₁ h.inv hdisj
    rw [← hTeq, hc.card_eq, hK₀] at hcard
    rw [hcard]
    ring
  · rw [hc.card_szA₁ ha hKf, hK₀]
  · refine le_antisymm (fun x hx => ?_) ?_
    · rw [hTeq]
      exact hcentA hx
    · rw [le_centralizer_iff]
      exact hAZ.trans inf_le_right
  · intro g hg
    obtain ⟨n, hn, hnt⟩ := exists_mem_normalizer_inv_mul_mul_eq h.le h.sylow
      (hTs _ (szA₁_le_szA L T t hg))
    rw [hcomm] at hg
    have h1 := conj_mem_commutator_of_mem_normalizer hn hg
    rw [← hnt, show n * (n⁻¹ * t * n) * n⁻¹ = t by group, ← hcomm] at h1
    have ht1 : t ∈ szT₁ L T ⊓ zpowers t := mem_inf.mpr ⟨szA₁_le _ h1, mem_zpowers t⟩
    rw [hdisj, mem_bot] at ht1
    have h2 := h.inv
    rw [ht1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  · intro g hg
    obtain ⟨n, hn, hnt⟩ := exists_mem_normalizer_inv_mul_mul_eq h.le h.sylow (hTs _ hg)
    refine ⟨n, ?_, hnt⟩
    rw [← hZT]
    exact normalizer_le_normalizer_inf_centralizer T hn

theorem facts (h : SzStart G L f t T) :
    T = szT₁ L T ⊔ zpowers t ∧ szT₁ L T ⊓ zpowers t = ⊥ ∧
    Nat.card T = 2 * 2 ^ f * 2 ^ f ∧ Nat.card (szA₁ (szT₁ L T)) = 2 ^ f ∧
    szA₁ (szT₁ L T) = ⁅T, T⁆ ∧ T ⊓ centralizer (T : Set G) = szA L T t ∧
    (∀ x ∈ T, x ^ 2 = 1 → x ∈ szA L T t) ∧ centralizer (szA L T t : Set G) = T ∧
    (∀ g : G, g⁻¹ * t * g ∉ szA₁ (szT₁ L T)) ∧
    ∀ g : G, g⁻¹ * t * g ∈ szA L T t →
      ∃ n ∈ normalizer (szA L T t : Set G), n⁻¹ * t * n = g⁻¹ * t * g :=
  h.facts_of_card_sylow h.card_sylow

theorem exists_torusCoords_of_card_sylow (h : SzStart G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    ∃ a : ℕ, 1 ≤ a ∧ f = 2 * a + 1 ∧ ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2),
      Fintype.card K = 2 ^ f ∧ ∃ (d : G) (u v : G → K) (κ : K), d ∈ L ∧
        d ∈ normalizer (szT₁ L T : Set G) ∧ SzRootCoords (szT₁ L T) a d u v κ ∧
        (∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w) ∧
        ∀ w : K, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w := by
  classical
  obtain ⟨-, -, hT₁syl⟩ := h.eq_sup_of_card_sylow hS2
  obtain ⟨-, a, ha, K, _, _, hfa, hK₀, ⟨e⟩⟩ := suzukiModel_of_lieModel_twistedB2 h.model
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK₀, hfa]
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK
  obtain ⟨e', he'⟩ := exists_mulEquiv_szModelU_eq hK e (szT₁_le_right L T) hT₁syl
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hgen : ∀ w : K, w ≠ 0 → ∃ m : ℕ, (g : K) ^ m = w := by
    intro w hw
    obtain ⟨m, hm⟩ := mem_powers_iff_mem_zpowers.mpr (hg (Units.mk0 w hw))
    have hm' : g ^ m = Units.mk0 w hw := hm
    exact ⟨m, by rw [← Units.val_pow_eq_pow_val, hm', Units.val_mk0]⟩
  obtain ⟨u, v, hc⟩ := exists_szRootCoords hK e' 0 0 g
  rw [he'] at hc
  refine ⟨a, ha, hfa, K, inferInstance, inferInstance, inferInstance,
    by rw [← Nat.card_eq_fintype_card, hK₀], _, u, v, (g : K), SetLike.coe_mem _,
    mem_normalizer_of_forall_inv_mul_mul_mem hc.conj_mem, hc, hgen,
    pow_theta_succ_generator_of_generator ha hK hgen⟩

theorem szA_facts_of_card_sylow (h : SzStart G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    Nat.card (szA L T t) = 2 * 2 ^ f ∧ (∀ x ∈ szA L T t, x ^ 2 = 1) ∧
      ∀ x ∈ szA L T t, ∀ y ∈ szA L T t, x * y = y * x := by
  obtain ⟨-, hdisj, -⟩ := h.eq_sup_of_card_sylow hS2
  obtain ⟨-, -, -, -, -, hZT, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨a, ha, hfa, K, _, _, _, hK, d, u, v, κ, -, -, hc, -, -⟩ :=
    h.exists_torusCoords_of_card_sylow hS2
  have hKa : Fintype.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  refine ⟨?_, fun x hx => hc.sq_eq_one_of_mem_szA₁_sup ha hKa h.mem_centralizer_szT₁
    h.sq_eq_one hx, fun x hx y hy => ?_⟩
  · rw [szA, card_szA₁_sup h.mem_centralizer_szT₁ h.inv hdisj, hc.card_szA₁ ha hKa,
      Nat.card_eq_fintype_card, hK, mul_comm]
  · rw [← hZT] at hx hy
    exact (mem_centralizer_iff.mp (mem_inf.mp hx).2 y (mem_inf.mp hy).1).symm

end SzStart

end CFSG.SeitzReduction.RankOne
