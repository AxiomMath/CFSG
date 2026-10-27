module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.Model
public import CFSG.LieType.Ree.LargeReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionKernel
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup CFSG.Open
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff isSylowOf_of_card)
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)
open scoped commutatorElement

structure Setup (G : Type) [Group G] [Finite G]
    where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  L : Subgroup G
  std : standardComponentIsStandard L
  core : ∀ x : G, orderOf x = 2 → standardComponentOddCore (centralizer ({x} : Set G)) = ⊥
  cyc : ∀ S : Sylow 2 (centralizer (L : Set G)), IsCyclic (S : Subgroup (centralizer (L : Set G)))
  K : Type
  [fld : Field K]
  [fin : Finite K]
  [chr : CharP K F4.prime]
  a : ℕ
  one_le_a : 1 ≤ a
  card_K : Nat.card K = 2 ^ (2 * a + 1)
  ι : F4.reeGamma K a ≃* L
  t : G
  ht : orderOf t = 2
  htL : t ∈ centralizer (L : Set G)

attribute [instance] Setup.fld Setup.fin Setup.chr

namespace Setup

variable {G : Type} [Group G] [Finite G]
  (h : Setup G)

abbrev C : Subgroup G := centralizer ({h.t} : Set G)

@[expose] def emb : F4.reeGamma h.K h.a →* G := h.L.subtype.comp h.ι.toMonoidHom

@[expose] def pull (M : Subgroup (ModGL F4.tag h.K)) : Subgroup G :=
  (M.subgroupOf (F4.reeGamma h.K h.a)).map h.emb

open Classical in
@[expose] def elt (g : ModGL F4.tag h.K) : G :=
  if hg : g ∈ F4.reeGamma h.K h.a then h.emb ⟨g, hg⟩ else 1

@[expose] def P : Subgroup G := h.pull (F4.reeFixedPosUnipotent h.K h.a)

@[expose] def V (i : Idx) : Subgroup G := h.pull (rootV h.K h.a i)

@[expose] def H : Subgroup G := h.pull (torusH h.K h.a)

@[expose] def Ht (i : Idx) : Subgroup G := h.pull (torusHi h.K h.a i)

@[expose] def N (i : Idx) : Subgroup G := h.pull (leviN h.K h.a i)

@[expose] def R : Subgroup G := h.pull (radR h.K h.a)

@[expose] def S : Subgroup G := h.pull (radS h.K h.a)

@[expose] def R₁ : Subgroup G := h.pull (R1 h.K h.a)

@[expose] def S₁ : Subgroup G := h.pull (S1 h.K h.a)

@[expose] def S₂ : Subgroup G := h.pull (S2 h.K h.a)

@[expose] def S₃ : Subgroup G := h.pull (S3 h.K h.a)

@[expose] def S₄ : Subgroup G := h.pull (S4 h.K h.a)

@[expose] def J : Subgroup G := h.C ⊓ normalizer (h.R : Set G)

@[expose] def Kp : Subgroup G := h.C ⊓ normalizer (h.S : Set G)

@[expose] def e : G := h.elt (invE h.K h.a)

@[expose] def f : G := h.elt (invF h.K h.a)

@[expose] def r : G := h.emb ⟨weylR h.K, weylR_mem_reeGamma⟩

@[expose] def s : G := h.emb ⟨weylS h.K, weylS_mem_reeGamma⟩

@[expose] def Tsyl : Subgroup G := centralizer (h.L : Set G) ⊓ h.C

theorem emb_apply (g : F4.reeGamma h.K h.a) : h.emb g = (h.ι g : G) := rfl

theorem emb_injective : Function.Injective h.emb :=
  Subtype.val_injective.comp h.ι.injective

theorem emb_mem (g : F4.reeGamma h.K h.a) : h.emb g ∈ h.L := (h.ι g).2

theorem emb_symm (l : h.L) : h.emb (h.ι.symm l) = l := by
  rw [emb_apply, MulEquiv.apply_symm_apply]

theorem range_emb : h.emb.range = h.L := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact h.emb_mem g
  · intro hx
    exact ⟨h.ι.symm ⟨x, hx⟩, h.emb_symm ⟨x, hx⟩⟩

theorem mem_pull {M : Subgroup (ModGL F4.tag h.K)} {x : G} :
    x ∈ h.pull M ↔ ∃ g : F4.reeGamma h.K h.a, (g : ModGL F4.tag h.K) ∈ M ∧ h.emb g = x := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩

theorem emb_mem_pull {M : Subgroup (ModGL F4.tag h.K)} {g : F4.reeGamma h.K h.a} :
    h.emb g ∈ h.pull M ↔ (g : ModGL F4.tag h.K) ∈ M := by
  rw [mem_pull]
  constructor
  · rintro ⟨g', hg', e⟩
    rwa [← h.emb_injective e]
  · intro hg
    exact ⟨g, hg, rfl⟩

theorem pull_le_L (M : Subgroup (ModGL F4.tag h.K)) : h.pull M ≤ h.L := by
  rintro _ ⟨g, -, rfl⟩
  exact h.emb_mem g

theorem pull_mono {M M' : Subgroup (ModGL F4.tag h.K)} (hM : M ≤ M') : h.pull M ≤ h.pull M' := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := h.mem_pull.1 hx
  exact h.mem_pull.2 ⟨g, hM hg, rfl⟩

theorem pull_inf (M M' : Subgroup (ModGL F4.tag h.K)) :
    h.pull (M ⊓ M') = h.pull M ⊓ h.pull M' := by
  refine le_antisymm (le_inf (h.pull_mono inf_le_left) (h.pull_mono inf_le_right)) ?_
  rintro x ⟨hx, hx'⟩
  obtain ⟨g, hg, rfl⟩ := h.mem_pull.1 hx
  exact h.mem_pull.2 ⟨g, ⟨hg, h.emb_mem_pull.1 hx'⟩, rfl⟩

theorem pull_reeGamma : h.pull (F4.reeGamma h.K h.a) = h.L := by
  rw [pull, subgroupOf_self, ← MonoidHom.range_eq_map, range_emb]

theorem card_pull {M : Subgroup (ModGL F4.tag h.K)} (hM : M ≤ F4.reeGamma h.K h.a) :
    Nat.card (h.pull M) = Nat.card M := by
  rw [pull, card_map_of_injective h.emb_injective]
  exact Nat.card_congr (subgroupOfEquivOfLe hM).toEquiv

theorem elt_of_mem {g : ModGL F4.tag h.K} (hg : g ∈ F4.reeGamma h.K h.a) :
    h.elt g = h.emb ⟨g, hg⟩ :=
  dite_eq_left hg

theorem elt_mem_pull {M : Subgroup (ModGL F4.tag h.K)} {g : ModGL F4.tag h.K}
    (hg : g ∈ F4.reeGamma h.K h.a) : h.elt g ∈ h.pull M ↔ g ∈ M := by
  rw [h.elt_of_mem hg, emb_mem_pull]

theorem elt_mem {g : ModGL F4.tag h.K} (hg : g ∈ F4.reeGamma h.K h.a) : h.elt g ∈ h.L := by
  rw [h.elt_of_mem hg]
  exact h.emb_mem _

theorem pull_map_conj (M : Subgroup (ModGL F4.tag h.K)) {g : ModGL F4.tag h.K}
    (hg : g ∈ F4.reeGamma h.K h.a) :
    h.pull (M.map (MulAut.conj g).toMonoidHom) =
      (h.pull M).map (MulAut.conj (h.elt g)).toMonoidHom := by
  rw [h.elt_of_mem hg]
  ext x
  constructor
  · intro hx
    obtain ⟨y, ⟨m, hm, hmy⟩, rfl⟩ := h.mem_pull.1 hx
    have hmΓ : m ∈ F4.reeGamma h.K h.a := by
      have : m = g⁻¹ * (y : ModGL F4.tag h.K) * g := by
        rw [← hmy, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [this]
      exact mul_mem (mul_mem (inv_mem hg) y.2) hg
    refine ⟨h.emb ⟨m, hmΓ⟩, h.emb_mem_pull.2 hm, ?_⟩
    have hy : y = ⟨g, hg⟩ * ⟨m, hmΓ⟩ * (⟨g, hg⟩ : F4.reeGamma h.K h.a)⁻¹ :=
      Subtype.ext (by rw [← hmy]; rfl)
    rw [hy, map_mul, map_mul, map_inv]
    rfl
  · rintro ⟨_, hz, rfl⟩
    obtain ⟨m, hm, rfl⟩ := h.mem_pull.1 hz
    refine h.mem_pull.2 ⟨⟨g, hg⟩ * m * (⟨g, hg⟩ : F4.reeGamma h.K h.a)⁻¹, ⟨m, hm, rfl⟩, ?_⟩
    rw [map_mul, map_mul, map_inv]
    rfl

theorem pull_bot : h.pull ⊥ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨g, hg, rfl⟩ := h.mem_pull.1 hx
  have hg1 : g = 1 := Subtype.ext ((mem_bot).1 hg)
  rw [hg1, map_one]
  exact one_mem _

theorem pull_sup {M M' : Subgroup (ModGL F4.tag h.K)} (hM : M ≤ F4.reeGamma h.K h.a)
    (hM' : M' ≤ F4.reeGamma h.K h.a) : h.pull (M ⊔ M') = h.pull M ⊔ h.pull M' := by
  rw [pull, subgroupOf_sup hM hM', Subgroup.map_sup]
  rfl

theorem pull_le_normalizer {M M' : Subgroup (ModGL F4.tag h.K)}
    (hM : M ≤ normalizer (M' : Set (ModGL F4.tag h.K))) :
    h.pull M ≤ normalizer (h.pull M' : Set G) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := h.mem_pull.1 hx
  have hyN := hM hy
  rw [mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    obtain ⟨w, hw, rfl⟩ := h.mem_pull.1 hz
    rw [← map_inv, ← map_mul, ← map_mul, emb_mem_pull]
    exact (mem_normalizer_iff.1 hyN w).1 hw
  · intro hz
    obtain ⟨w, hw, hwz⟩ := h.mem_pull.1 hz
    have hz' : z = h.emb (y⁻¹ * w * y) := by
      rw [map_mul, map_mul, map_inv, hwz]
      group
    rw [hz', emb_mem_pull]
    have h1 := (mem_normalizer_iff.1 (inv_mem hyN) w).1 hw
    rwa [inv_inv] at h1

theorem pull_normalizer {M : Subgroup (ModGL F4.tag h.K)} (hM : M ≤ F4.reeGamma h.K h.a) :
    h.pull (normalizer (M : Set (ModGL F4.tag h.K))) = h.L ⊓ normalizer (h.pull M : Set G) := by
  refine le_antisymm (le_inf (h.pull_le_L _) (h.pull_le_normalizer le_rfl)) ?_
  rintro x ⟨hxL, hxN⟩
  rw [← h.range_emb] at hxL
  obtain ⟨y, rfl⟩ := hxL
  refine h.emb_mem_pull.2 (mem_normalizer_iff.2 fun w => ?_)
  constructor
  · intro hw
    have hwΓ := hM hw
    have h1 := (mem_normalizer_iff.1 hxN (h.emb ⟨w, hwΓ⟩)).1 (h.emb_mem_pull.2 hw)
    rw [← map_inv, ← map_mul, ← map_mul, emb_mem_pull] at h1
    exact h1
  · intro hw
    have hwΓ : w ∈ F4.reeGamma h.K h.a := by
      have := mul_mem (mul_mem (inv_mem y.2) (hM hw)) y.2
      rwa [show (y : ModGL F4.tag h.K)⁻¹ *
        ((y : ModGL F4.tag h.K) * w * (y : ModGL F4.tag h.K)⁻¹) * y = w by group] at this
    have h1 : h.emb (y * ⟨w, hwΓ⟩ * y⁻¹) ∈ h.pull M := h.emb_mem_pull.2 hw
    rw [map_mul, map_mul, map_inv] at h1
    have h2 := (mem_normalizer_iff.1 hxN (h.emb ⟨w, hwΓ⟩)).2 h1
    exact h.emb_mem_pull.1 h2

theorem pull_centralizer {g : ModGL F4.tag h.K} (hg : g ∈ F4.reeGamma h.K h.a) :
    h.pull (centralizer ({g} : Set (ModGL F4.tag h.K))) =
      h.L ⊓ centralizer ({h.elt g} : Set G) := by
  rw [h.elt_of_mem hg]
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := h.mem_pull.1 hx
    refine ⟨h.emb_mem y, mem_centralizer_singleton_iff.2 ?_⟩
    have hyg : y * ⟨g, hg⟩ = ⟨g, hg⟩ * y :=
      Subtype.ext (mem_centralizer_singleton_iff.1 hy)
    rw [← map_mul, ← map_mul, hyg]
  · rintro ⟨hxL, hxg⟩
    rw [← h.range_emb] at hxL
    obtain ⟨y, rfl⟩ := hxL
    refine h.emb_mem_pull.2 (mem_centralizer_singleton_iff.2 ?_)
    have h1 := mem_centralizer_singleton_iff.1 hxg
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (h.emb_injective h1)

theorem t_ne_one : h.t ≠ 1 := fun h1 => by
  have := h.ht
  rw [h1, orderOf_one] at this
  exact absurd this (by norm_num)

theorem t_mul_t : h.t * h.t = 1 := by
  rw [← sq, ← h.ht, pow_orderOf_eq_one]

theorem t_inv : h.t⁻¹ = h.t :=
  inv_eq_of_mul_eq_one_right h.t_mul_t

theorem t_mem_C : h.t ∈ h.C :=
  mem_centralizer_singleton_iff.2 rfl

theorem card_zpowers_t : Nat.card (zpowers h.t) = 2 := by
  rw [Nat.card_zpowers, h.ht]

theorem isPGroup_zpowers_t : IsPGroup 2 (zpowers h.t) :=
  IsPGroup.of_card (n := 1) (by rw [h.card_zpowers_t, pow_one])

include h in
theorem center_G_eq_bot : center G = ⊥ := by
  have := h.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with hc | hc
  · exact hc
  · exfalso
    obtain ⟨a, b, hab⟩ := h.nonab
    exact hab (mem_center_iff.1 (hc ▸ mem_top a : a ∈ center G) b).symm

theorem center_eq_bot : center h.L = ⊥ := by
  have hZ := large_Ree_fixed_group_center_trivial h.a h.K h.card_K
  refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
  have hz' : h.ι.symm z ∈ center (F4.reeGamma h.K h.a) := by
    rw [mem_center_iff] at hz ⊢
    intro y
    apply h.ι.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hz (h.ι y)
  rw [hZ, mem_bot] at hz'
  simpa using congrArg h.ι hz'

theorem inf_centralizer_eq_bot :
    h.L ⊓ centralizer (h.L : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxL, hxC⟩
  have hx : (⟨x, hxL⟩ : h.L) ∈ center h.L :=
    mem_center_iff.2 fun y => Subtype.ext (mem_centralizer_iff.1 hxC y y.2)
  rw [h.center_eq_bot, mem_bot] at hx
  exact mem_bot.2 (congrArg Subtype.val hx)

theorem t_not_mem_L : h.t ∉ h.L := fun htL => by
  have : h.t ∈ h.L ⊓ centralizer (h.L : Set G) := ⟨htL, h.htL⟩
  rw [h.inf_centralizer_eq_bot, mem_bot] at this
  exact h.t_ne_one this

theorem finite_reeGamma : Finite (F4.reeGamma h.K h.a) :=
  Finite.of_equiv _ h.ι.symm.toEquiv

theorem isSylowOf_P : IsSylowOf 2 h.P h.L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact F4.prime.Prime := ⟨Nat.prime_two⟩
  have := h.finite_reeGamma
  have hp : IsPGroup 2 ((F4.reeFixedPosUnipotent h.K h.a).subgroupOf (F4.reeGamma h.K h.a)) :=
    isPGroup_reeFixedPosUnipotent_subgroupOf
  have hi : ¬ 2 ∣ ((F4.reeFixedPosUnipotent h.K h.a).subgroupOf (F4.reeGamma h.K h.a)).index :=
    not_dvd_index_reeFixedPosUnipotent
  have h1 : Nat.card ((F4.reeFixedPosUnipotent h.K h.a).subgroupOf (F4.reeGamma h.K h.a)) =
      2 ^ (Nat.card (F4.reeGamma h.K h.a)).factorization 2 :=
    Sylow.card_eq_multiplicity (hp.toSylow hi)
  have h2 : Nat.card h.L = Nat.card (F4.reeGamma h.K h.a) := (Nat.card_congr h.ι.toEquiv).symm
  refine isSylowOf_of_card (h.pull_le_L _) ?_
  rw [h2, ← h1]
  exact card_map_of_injective h.emb_injective

theorem P_le_L : h.P ≤ h.L := h.pull_le_L _

theorem isPGroup_P : IsPGroup 2 h.P := h.isSylowOf_P.isPGroup

theorem V_le_P (i : Idx) : h.V i ≤ h.P :=
  h.pull_mono (rootV_le_sylowP h.card_K i)

theorem card_V (i : Idx) :
    Nat.card (h.V i) = (2 ^ (2 * h.a + 1)) ^ (if i.isSz then 2 else 1) := by
  rw [V, h.card_pull (rootV_le_reeGamma h.card_K i), card_rootV h.card_K i]

theorem isPGroup_V (i : Idx) : IsPGroup 2 (h.V i) :=
  h.isPGroup_P.to_le (h.V_le_P i)

theorem V_center_le (i : Idx) : h.V i.center ≤ h.V i :=
  h.pull_mono (rootV_center_le h.card_K i).1

theorem R_le_P_and_S_le_P : h.R ≤ h.P ∧ h.S ≤ h.P :=
  ⟨h.pull_mono (rootJoin_le_sylowP h.card_K _), h.pull_mono (rootJoin_le_sylowP h.card_K _)⟩

theorem S₁_le_S₂_le_S₃_le_S₄_le_S :
    h.S₁ ≤ h.S₂ ∧ h.S₂ ≤ h.S₃ ∧ h.S₃ ≤ h.S₄ ∧ h.S₄ ≤ h.S ∧ h.R₁ ≤ h.R ∧ h.S₂ ≤ h.R₁ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := S1_le_S2_le_S3_le_S4_le_radS (a := h.a) h.card_K
  exact ⟨h.pull_mono h1, h.pull_mono h2, h.pull_mono h3, h.pull_mono h4, h.pull_mono h5,
    h.pull_mono h6⟩

theorem card_R_S :
    (Nat.card h.R = (2 ^ (2 * h.a + 1)) ^ 10 ∧ h.P ≤ normalizer (h.R : Set G)) ∧
      (Nat.card h.S = (2 ^ (2 * h.a + 1)) ^ 11 ∧ h.P ≤ normalizer (h.S : Set G)) ∧
      (Nat.card h.R₁ = (2 ^ (2 * h.a + 1)) ^ 5 ∧ h.P ≤ normalizer (h.R₁ : Set G)) ∧
      (Nat.card h.S₁ = (2 ^ (2 * h.a + 1)) ^ 2 ∧ h.P ≤ normalizer (h.S₁ : Set G)) ∧
      (Nat.card h.S₂ = (2 ^ (2 * h.a + 1)) ^ 3 ∧ h.P ≤ normalizer (h.S₂ : Set G)) ∧
      (Nat.card h.S₃ = (2 ^ (2 * h.a + 1)) ^ 5 ∧ h.P ≤ normalizer (h.S₃ : Set G)) ∧
      (Nat.card h.S₄ = (2 ^ (2 * h.a + 1)) ^ 9 ∧ h.P ≤ normalizer (h.S₄ : Set G)) := by
  have key : ∀ {M : Subgroup (ModGL F4.tag h.K)} {n : ℕ}, M ≤ F4.reeGamma h.K h.a →
      Nat.card M = (2 ^ (2 * h.a + 1)) ^ n →
      F4.reeFixedPosUnipotent h.K h.a ≤ normalizer (M : Set (ModGL F4.tag h.K)) →
      Nat.card (h.pull M) = (2 ^ (2 * h.a + 1)) ^ n ∧ h.P ≤ normalizer (h.pull M : Set G) :=
    fun hM hc hN => ⟨by rw [h.card_pull hM, hc], h.pull_le_normalizer hN⟩
  obtain ⟨hR, -, hRc, hRN⟩ := radR_spec (a := h.a) h.card_K
  obtain ⟨hS, -, hSc, hSN⟩ := radS_spec (a := h.a) h.card_K
  obtain ⟨hR1, -, hR1c, hR1N⟩ := R1_spec (a := h.a) h.card_K
  obtain ⟨hS1, -, hS1c, hS1N⟩ := S1_spec (a := h.a) h.card_K
  obtain ⟨hS2, -, hS2c, hS2N⟩ := S2_spec (a := h.a) h.card_K
  obtain ⟨hS3, -, hS3c, hS3N⟩ := S3_spec (a := h.a) h.card_K
  obtain ⟨hS4, -, hS4c, hS4N⟩ := S4_spec (a := h.a) h.card_K
  exact ⟨key (hR.le.trans inf_le_right) hRc hRN, key (hS.le.trans inf_le_right) hSc hSN,
    key (hR1.le.trans inf_le_right) hR1c hR1N, key (hS1.le.trans inf_le_right) hS1c hS1N,
    key (hS2.le.trans inf_le_right) hS2c hS2N, key (hS3.le.trans inf_le_right) hS3c hS3N,
    key (hS4.le.trans inf_le_right) hS4c hS4N⟩

theorem card_H : Nat.card h.H = (2 ^ (2 * h.a + 1) - 1) ^ 2 := by
  rw [H, h.card_pull (torusH_le_reeGamma h.card_K), card_torusH h.card_K]

theorem Ht_le_H (i : Idx) : h.Ht i ≤ h.H := h.pull_mono (torusHi_le_torusH i)

theorem H_le_normalizer_P : h.H ≤ normalizer (h.P : Set G) :=
  h.pull_le_normalizer (torusH_le_normalizer_sylowP h.card_K)

theorem nonempty_N_equiv_suzuki {i : Idx} (hi : i.isLin = false) :
    Nonempty (h.N i ≃* CFSG.Blueprint.suzukiGroup h.a h.K) := by
  obtain ⟨e⟩ := nonempty_leviN_equiv_suzuki h.one_le_a h.card_K hi
  exact ⟨(((leviN h.K h.a i).subgroupOfEquivOfLe (leviN_le_reeGamma h.card_K i)).symm.trans
    (((leviN h.K h.a i).subgroupOf (F4.reeGamma h.K h.a)).equivMapOfInjective h.emb
      h.emb_injective)).symm.trans e⟩

theorem V_le_N (i : Idx) :
    h.V i ≤ h.N i :=
  h.pull_mono (rootV_le_leviN h.card_K i)

theorem r_mem_N_s_mem_N : h.r ∈ h.N .i1 ∧ h.s ∈ h.N .i3 :=
  ⟨h.emb_mem_pull.2 weylR_mem_leviN, h.emb_mem_pull.2 weylS_mem_leviN⟩

theorem r_mul_self_s_mul_self : h.r * h.r = 1 ∧ h.s * h.s = 1 := by
  refine ⟨?_, ?_⟩
  · rw [r, ← map_mul]
    have : (⟨weylR h.K, weylR_mem_reeGamma⟩ * ⟨weylR h.K, weylR_mem_reeGamma⟩ :
        F4.reeGamma h.K h.a) = 1 := Subtype.ext weylR_mul_self
    rw [this, map_one]
  · rw [s, ← map_mul]
    have : (⟨weylS h.K, weylS_mem_reeGamma⟩ * ⟨weylS h.K, weylS_mem_reeGamma⟩ :
        F4.reeGamma h.K h.a) = 1 := Subtype.ext weylS_mul_self
    rw [this, map_one]

theorem e_eq_f_eq :
    h.e = h.emb ⟨invE h.K h.a, rootV_le_reeGamma h.card_K _ (invE_invF_mem h.card_K).1⟩ ∧
      h.f = h.emb ⟨invF h.K h.a, rootV_le_reeGamma h.card_K _ (invE_invF_mem h.card_K).2.1⟩ :=
  ⟨h.elt_of_mem _, h.elt_of_mem _⟩

theorem e_f_mem_orderOf :
    h.e ∈ h.V .i12 ∧ h.f ∈ h.V .i10 ∧ orderOf h.e = 2 ∧ orderOf h.f = 2 := by
  obtain ⟨he, hf⟩ := h.e_eq_f_eq
  obtain ⟨he12, hf10, -, -, hoe, hof⟩ := invE_invF_mem (a := h.a) h.card_K
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [he]
    exact h.emb_mem_pull.2 he12
  · rw [hf]
    exact h.emb_mem_pull.2 hf10
  · rw [he, orderOf_injective _ h.emb_injective, orderOf_mk, hoe]
  · rw [hf, orderOf_injective _ h.emb_injective, orderOf_mk, hof]

theorem commute_e {u : G}
    (hu : u ∈ h.P) : u * h.e = h.e * u := by
  obtain ⟨y, hy, rfl⟩ := h.mem_pull.1 hu
  rw [h.e_eq_f_eq.1, ← map_mul, ← map_mul]
  refine congrArg h.emb (Subtype.ext ?_)
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact commute_invE h.one_le_a h.card_K hy

theorem centralizer_e_f :
    h.L ⊓ centralizer ({h.e} : Set G) = h.R ⊔ h.N .i1 ∧ h.R ⊓ h.N .i1 = ⊥ ∧
      h.L ⊓ centralizer ({h.f} : Set G) = h.S₄ ⊔ h.N .i3 ∧ h.S₄ ⊓ h.N .i3 = ⊥ ∧
      ∀ g ∈ h.L, g * h.e * g⁻¹ ≠ h.f := by
  obtain ⟨hz, hzR, ht, htR, hconj⟩ := reeGamma_inf_centralizer_invE_invF h.one_le_a h.card_K
  have hE : invE h.K h.a ∈ F4.reeGamma h.K h.a :=
    rootV_le_reeGamma h.card_K _ (invE_invF_mem h.card_K).1
  have hF : invF h.K h.a ∈ F4.reeGamma h.K h.a :=
    rootV_le_reeGamma h.card_K _ (invE_invF_mem h.card_K).2.1
  have hRΓ : radR h.K h.a ≤ F4.reeGamma h.K h.a :=
    (rootJoin_le_sylowP h.card_K _).trans inf_le_right
  have hS4Γ : S4 h.K h.a ≤ F4.reeGamma h.K h.a :=
    (rootJoin_le_sylowP h.card_K _).trans inf_le_right
  have hcent : ∀ {g : ModGL F4.tag h.K}, g ∈ F4.reeGamma h.K h.a →
      h.pull (F4.reeGamma h.K h.a ⊓ centralizer ({g} : Set (ModGL F4.tag h.K))) =
        h.L ⊓ centralizer ({h.elt g} : Set G) := by
    intro g hg
    rw [h.pull_inf, h.pull_reeGamma, h.pull_centralizer hg, ← inf_assoc, inf_idem]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [e, ← hcent hE, hz, h.pull_sup hRΓ (leviN_le_reeGamma h.card_K _)]
    rfl
  · rw [R, N, ← h.pull_inf, hzR, h.pull_bot]
  · rw [f, ← hcent hF, ht, h.pull_sup hS4Γ (leviN_le_reeGamma h.card_K _)]
    rfl
  · rw [S₄, N, ← h.pull_inf, htR, h.pull_bot]
  · intro g hg hgef
    rw [← h.range_emb] at hg
    obtain ⟨y, rfl⟩ := hg
    obtain ⟨he, hf⟩ := h.e_eq_f_eq
    rw [he, hf, ← map_inv, ← map_mul, ← map_mul] at hgef
    have h1 := congrArg Subtype.val (h.emb_injective hgef)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    exact hconj y y.2 h1

theorem normality :
    h.C ≤ normalizer (h.L : Set G) ∧ h.L ≤ h.C ∧ (h.L.subgroupOf h.C).Normal ∧
      CFSG.Assembly.IsComponentOf h.L h.C ∧
      ((centralizer (h.L : Set G) ⊓ h.C).subgroupOf h.C).Normal :=
  CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality h.std h.htL h.ht

theorem centralizer_le_normalizer : h.C ≤ normalizer (h.L : Set G) := h.normality.1

theorem L_le_C : h.L ≤ h.C := h.normality.2.1

theorem normal_subgroupOf : (h.L.subgroupOf h.C).Normal := h.normality.2.2.1

instance normal_L_subgroupOf_C : (h.L.subgroupOf h.C).Normal := h.normal_subgroupOf

instance normal_kernel_subgroupOf_C :
    ((centralizer (h.L : Set G) ⊓ h.C).subgroupOf h.C).Normal :=
  h.normality.2.2.2.2

theorem P_le_C : h.P ≤ h.C := h.P_le_L.trans h.L_le_C

theorem conj_mem_L {x : G} (hx : x ∈ h.C) {l : G} (hl : l ∈ h.L) : x * l * x⁻¹ ∈ h.L :=
  (mem_normalizer_iff.1 (h.centralizer_le_normalizer hx) l).1 hl

theorem kernel :
    IsCyclic (centralizer (h.L : Set G) ⊓ h.C : Subgroup G) ∧
      IsPGroup 2 (centralizer (h.L : Set G) ⊓ h.C : Subgroup G) ∧
      (∀ x ∈ centralizer (h.L : Set G) ⊓ h.C, orderOf x = 2 → x = h.t) ∧
      ((centralizer (h.L : Set G) ⊓ h.C).subgroupOf h.C).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set tc : centralizer (h.L : Set G) := ⟨h.t, h.htL⟩ with htc
  have htc2 : orderOf tc = 2 := by rw [← orderOf_coe]; exact h.ht
  have hz : IsPGroup 2 (zpowers tc) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htc2, pow_one])
  obtain ⟨S, hSt⟩ := hz.exists_le_sylow
  have htS : tc ∈ S := hSt (mem_zpowers _)
  have hSc := h.cyc S
  obtain ⟨-, huniq, -, -, -, -, hR, hRn, -⟩ :=
    CFSG.ComponentClassification.StandardRecognition.standard_cyclic_local_centralizer_kernel
      h.std S hSc htS htc2 (h.core h.t h.ht)
  have hR' : centralizer (h.L : Set G) ⊓ h.C =
      (S : Subgroup (centralizer (h.L : Set G))).map (centralizer (h.L : Set G)).subtype := hR
  rw [hR']
  refine ⟨isCyclic_of_surjective _ (MonoidHom.subgroupMap_surjective _ _),
    S.isPGroup'.map _, ?_, hRn⟩
  rintro _ ⟨y, hy, rfl⟩ hy2
  rw [Subgroup.subtype_apply, orderOf_coe] at hy2
  exact congrArg Subtype.val (huniq y hy hy2)

theorem isCyclic_kernel : IsCyclic (centralizer (h.L : Set G) ⊓ h.C : Subgroup G) :=
  h.kernel.1

theorem isPGroup_kernel : IsPGroup 2 (centralizer (h.L : Set G) ⊓ h.C : Subgroup G) :=
  h.kernel.2.1

theorem eq_t_of_mem_kernel {x : G} (hx : x ∈ centralizer (h.L : Set G) ⊓ h.C)
    (hx2 : orderOf x = 2) : x = h.t :=
  h.kernel.2.2.1 x hx hx2

theorem t_mem_kernel : h.t ∈ centralizer (h.L : Set G) ⊓ h.C :=
  ⟨h.htL, h.t_mem_C⟩

theorem kernel_comm {c d : G} (hc : c ∈ centralizer (h.L : Set G) ⊓ h.C)
    (hd : d ∈ centralizer (h.L : Set G) ⊓ h.C) : c * d = d * c := by
  have := h.isCyclic_kernel
  exact congrArg Subtype.val (mul_comm' (⟨c, hc⟩ :
    (centralizer (h.L : Set G) ⊓ h.C : Subgroup G)) ⟨d, hd⟩)

theorem isCyclic_Tsyl : IsCyclic h.Tsyl := h.isCyclic_kernel

theorem t_mem_Tsyl : h.t ∈ h.Tsyl := h.t_mem_kernel

theorem Tsyl_eq_zpowers (hT : Nat.card h.Tsyl = 2) : h.Tsyl = zpowers h.t :=
  (Subgroup.eq_of_le_of_card_ge ((zpowers_le).2 h.t_mem_Tsyl)
    (by rw [hT, h.card_zpowers_t])).symm

@[expose] def act : h.C →* MulAut (F4.reeGamma h.K h.a) :=
  (MulAut.congr h.ι.symm).toMonoidHom.comp
    (h.L.normalizerMonoidHom.comp (inclusion h.centralizer_le_normalizer))

theorem emb_act_apply (x : h.C) (g : F4.reeGamma h.K h.a) :
    h.emb (h.act x g) = x * h.emb g * (x : G)⁻¹ := by
  simp only [act, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
    MulEquiv.trans_apply, MulEquiv.symm_symm, emb_symm, normalizerMonoidHom_apply_apply_coe,
    coe_inclusion]
  rfl

theorem act_eq_one_iff (x : h.C) : h.act x = 1 ↔ (x : G) ∈ centralizer (h.L : Set G) := by
  constructor
  · intro h1
    rw [mem_centralizer_iff]
    intro l hl
    have h2 := h.emb_act_apply x (h.ι.symm ⟨l, hl⟩)
    rw [h1, MulAut.one_apply, h.emb_symm] at h2
    calc l * x = x * l * (x : G)⁻¹ * x := by rw [← h2]
      _ = x * l := by group
  · intro hx
    refine MulEquiv.ext fun g => h.emb_injective ?_
    rw [emb_act_apply, MulAut.one_apply, ← mem_centralizer_iff.1 hx _ (h.emb_mem g),
      mul_inv_cancel_right]

theorem ker_act : h.act.ker = (centralizer (h.L : Set G) ⊓ h.C).subgroupOf h.C := by
  ext x
  rw [MonoidHom.mem_ker, act_eq_one_iff, inf_subgroupOf_right, mem_subgroupOf]

theorem act_emb (g : F4.reeGamma h.K h.a) :
    h.act ⟨h.emb g, h.L_le_C (h.emb_mem g)⟩ = MulAut.conj g := by
  refine MulEquiv.ext fun y => h.emb_injective ?_
  rw [emb_act_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem act_of_mem {l : G} (hl : l ∈ h.L) :
    h.act ⟨l, h.L_le_C hl⟩ = MulAut.conj (h.ι.symm ⟨l, hl⟩) := by
  refine MulEquiv.ext fun y => h.emb_injective ?_
  rw [emb_act_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, h.emb_symm]

theorem card_ringEquiv_and_isCyclic :
    Nat.card (h.K ≃+* h.K) = 2 * h.a + 1 ∧ IsCyclic (h.K ≃+* h.K) := by
  obtain ⟨σ, -, -, hσ, hcard, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega : 1 ≤ 2 * h.a + 1) h.card_K
  exact ⟨hcard, isCyclic_iff_exists_zpowers_eq_top.mpr ⟨σ, hσ⟩⟩

theorem card_ringEquiv : Nat.card (h.K ≃+* h.K) = 2 * h.a + 1 :=
  h.card_ringEquiv_and_isCyclic.1

@[expose] def autEquiv :
    F4.reeGamma h.K h.a ⋊[F4.reeGammaFieldAutHom h.K h.a] (h.K ≃+* h.K) ≃*
      MulAut (F4.reeGamma h.K h.a) :=
  Classical.choose
    (large_Ree_full_inner_field_automorphism_normal_form h.a h.one_le_a h.K h.card_K).2.2.1

theorem autEquiv_apply (x : F4.reeGamma h.K h.a)
    (β : h.K ≃+* h.K) :
    h.autEquiv ⟨x, β⟩ = MulAut.conj x * F4.reeGammaFieldAut h.K h.a β :=
  Classical.choose_spec
    (large_Ree_full_inner_field_automorphism_normal_form h.a h.one_le_a h.K h.card_K).2.2.1 x β

theorem autEquiv_inl (x : F4.reeGamma h.K h.a) :
    h.autEquiv (SemidirectProduct.inl x) = MulAut.conj x := by
  change h.autEquiv ⟨x, 1⟩ = _
  rw [autEquiv_apply, ← reeGammaFieldAutHom_apply, map_one, mul_one]

@[expose] def actSemi :
    h.C →* F4.reeGamma h.K h.a ⋊[F4.reeGammaFieldAutHom h.K h.a] (h.K ≃+* h.K) :=
  h.autEquiv.symm.toMonoidHom.comp h.act

theorem autEquiv_actSemi (x : h.C) :
    h.autEquiv (h.actSemi x) = h.act x :=
  h.autEquiv.apply_symm_apply _

theorem ker_actSemi :
    h.actSemi.ker = (centralizer (h.L : Set G) ⊓ h.C).subgroupOf h.C := by
  rw [← h.ker_act]
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← h.autEquiv_actSemi, MulEquiv.map_eq_one_iff]

theorem actSemi_of_mem {l : G} (hl : l ∈ h.L) :
    h.actSemi ⟨l, h.L_le_C hl⟩ = SemidirectProduct.inl (h.ι.symm ⟨l, hl⟩) := by
  apply h.autEquiv.injective
  rw [autEquiv_actSemi, autEquiv_inl, act_of_mem]

@[expose] def fieldFactor : h.C →* (h.K ≃+* h.K) :=
  SemidirectProduct.rightHom.comp h.actSemi

theorem act_eq_conj_mul (x : h.C) :
    h.act x = MulAut.conj (h.actSemi x).left * F4.reeGammaFieldAut h.K h.a (h.fieldFactor x) := by
  rw [← h.autEquiv_actSemi x, ← autEquiv_apply]
  rfl

theorem fieldFactor_eq_one_iff (x : h.C) :
    h.fieldFactor x = 1 ↔ ∃ l ∈ h.L, ∃ c ∈ centralizer (h.L : Set G) ⊓ h.C, (x : G) = l * c := by
  constructor
  · intro hx
    set y := (h.actSemi x).left
    have hxy : h.act x = h.act ⟨h.emb y, h.L_le_C (h.emb_mem y)⟩ := by
      rw [act_eq_conj_mul, hx, ← reeGammaFieldAutHom_apply, map_one, mul_one, act_emb]
    set l : h.C := ⟨h.emb y, h.L_le_C (h.emb_mem y)⟩
    have hc : h.act (l⁻¹ * x) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
    refine ⟨h.emb y, h.emb_mem y, ((l⁻¹ * x : h.C) : G), ⟨(h.act_eq_one_iff _).1 hc,
      (l⁻¹ * x).2⟩, ?_⟩
    change (x : G) = h.emb y * ((h.emb y)⁻¹ * x)
    group
  · rintro ⟨l, hl, c, hc, hx⟩
    have hxc : x = ⟨l, h.L_le_C hl⟩ * ⟨c, hc.2⟩ := Subtype.ext hx
    have hc1 : h.actSemi ⟨c, hc.2⟩ = 1 := by
      rw [← MonoidHom.mem_ker, ker_actSemi, mem_subgroupOf]
      exact hc
    rw [fieldFactor, MonoidHom.comp_apply, hxc, map_mul, hc1, mul_one, h.actSemi_of_mem hl,
      SemidirectProduct.rightHom_inl]

theorem ker_fieldFactor :
    h.fieldFactor.ker = (h.L ⊔ (centralizer (h.L : Set G) ⊓ h.C)).subgroupOf h.C := by
  ext x
  rw [MonoidHom.mem_ker, fieldFactor_eq_one_iff, mem_subgroupOf]
  constructor
  · rintro ⟨l, hl, c, hc, hx⟩
    rw [hx]
    exact mul_mem (mem_sup_left hl) (mem_sup_right hc)
  · intro hx
    have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute h.L
      (centralizer (h.L : Set G) ⊓ h.C) fun l hl c hc => mem_centralizer_iff.1 hc.1 l hl).2
    have hx' : (x : G) ∈ ((h.L ⊔ (centralizer (h.L : Set G) ⊓ h.C) : Subgroup G) : Set G) := hx
    rw [hset] at hx'
    obtain ⟨l, hl, c, hc, hlc⟩ := hx'
    exact ⟨l, hl, c, hc, hlc.symm⟩

theorem card_range_fieldFactor_dvd :
    Nat.card h.fieldFactor.range ∣ 2 * h.a + 1 :=
  h.card_ringEquiv ▸ Subgroup.card_subgroup_dvd_card _

theorem relIndex_eq_card_range_fieldFactor :
    (h.L ⊔ (centralizer (h.L : Set G) ⊓ h.C)).relIndex h.C = Nat.card h.fieldFactor.range := by
  rw [relIndex, ← ker_fieldFactor, index_ker]

theorem odd_relIndex :
    Odd ((h.L ⊔ (centralizer (h.L : Set G) ⊓ h.C)).relIndex h.C) := by
  rw [relIndex_eq_card_range_fieldFactor]
  exact Odd.of_dvd_nat (odd_two_mul_add_one _) h.card_range_fieldFactor_dvd

theorem fieldFactor_eq_one_of_pow_eq_one {x : h.C} {k : ℕ}
    (hx : x ^ 2 ^ k = 1) : h.fieldFactor x = 1 := by
  have h1 : orderOf (h.fieldFactor x) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hx, map_one])
  have h2 : orderOf (h.fieldFactor x) ∣ 2 * h.a + 1 := h.card_ringEquiv ▸ orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) (2 * h.a + 1) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 (odd_two_mul_add_one _))
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem le_sup_of_isPGroup {X : Subgroup G} (hXC : X ≤ h.C)
    (hX : IsPGroup 2 X) : X ≤ h.L ⊔ (centralizer (h.L : Set G) ⊓ h.C) := by
  intro x hx
  obtain ⟨k, hk⟩ := hX ⟨x, hx⟩
  have hk' : (⟨x, hXC hx⟩ : h.C) ^ 2 ^ k = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val hk)
  obtain ⟨l, hl, c, hc, hlc⟩ := (h.fieldFactor_eq_one_iff _).1
    (h.fieldFactor_eq_one_of_pow_eq_one hk')
  change x = l * c at hlc
  rw [hlc]
  exact mul_mem (mem_sup_left hl) (mem_sup_right hc)

theorem involution_mem {x : G} (hx : x ∈ h.C) (hx2 : x ^ 2 = 1) :
    x ∈ h.L ∨ h.t * x ∈ h.L := by
  have hk : (⟨x, hx⟩ : h.C) ^ 2 ^ 1 = 1 :=
    Subtype.ext (by rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]; exact hx2)
  obtain ⟨l, hl, c, hc, hxlc⟩ :=
    (h.fieldFactor_eq_one_iff _).1 (h.fieldFactor_eq_one_of_pow_eq_one hk)
  change x = l * c at hxlc
  have hcomm : l * c = c * l := mem_centralizer_iff.1 hc.1 l hl
  have h1 : l ^ 2 * c ^ 2 = 1 := by
    rw [← hx2, hxlc]
    calc l ^ 2 * c ^ 2 = l * (l * c) * c := by simp only [sq, mul_assoc]
      _ = l * (c * l) * c := by rw [hcomm]
      _ = (l * c) ^ 2 := by simp only [sq, mul_assoc]
  have hl2 : l ^ 2 = 1 := by
    have hls : l ^ 2 = (c ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hmem : l ^ 2 ∈ h.L ⊓ centralizer (h.L : Set G) :=
      mem_inf.2 ⟨pow_mem hl 2, hls ▸ inv_mem (pow_mem hc.1 2)⟩
    rw [h.inf_centralizer_eq_bot, mem_bot] at hmem
    exact hmem
  have hc2 : c ^ 2 = 1 := by rwa [hl2, one_mul] at h1
  by_cases hc1 : c = 1
  · left
    rw [hxlc, hc1, mul_one]
    exact hl
  · right
    have hct : c = h.t := h.eq_t_of_mem_kernel hc (orderOf_eq_prime hc2 hc1)
    have htl : h.t * l = l * h.t := (mem_centralizer_iff.1 h.htL l hl).symm
    rw [hxlc, hct, ← mul_assoc, htl, mul_assoc, h.t_mul_t, mul_one]
    exact hl

theorem centralizer_structure :
    IsPGroup 2 (centralizer (h.L : Set G) ⊓ h.C : Subgroup G) ∧
      IsCyclic (centralizer (h.L : Set G) ⊓ h.C : Subgroup G) ∧
      Odd ((h.L ⊔ (centralizer (h.L : Set G) ⊓ h.C)).relIndex h.C) ∧
      IsSylowOf 2 (h.P ⊔ (centralizer (h.L : Set G) ⊓ h.C)) h.C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨h.isPGroup_kernel, h.isCyclic_kernel, h.odd_relIndex, ?_⟩
  set T := centralizer (h.L : Set G) ⊓ h.C with hT
  have hTL : ∀ x ∈ h.L, ∀ y ∈ T, x * y = y * x := fun x hx y hy =>
    mem_centralizer_iff.1 hy.1 x hx
  have hLT : h.L ⊓ T = ⊥ :=
    le_bot_iff.1 ((inf_le_inf_left _ inf_le_left).trans h.inf_centralizer_eq_bot.le)
  have hPT : h.P ⊓ T = ⊥ := le_bot_iff.1 ((inf_le_inf_right _ h.P_le_L).trans hLT.le)
  have hcardLT : Nat.card (h.L ⊔ T : Subgroup G) = Nat.card h.L * Nat.card T := by
    have := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute h.L T hTL).1
    rwa [hLT, Subgroup.card_bot, mul_one] at this
  have hcardPT : Nat.card (h.P ⊔ T : Subgroup G) = Nat.card h.P * Nat.card T := by
    have := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute h.P T fun x hx y hy =>
      hTL x (h.P_le_L hx) y hy).1
    rwa [hPT, Subgroup.card_bot, mul_one] at this
  have hPL := h.isSylowOf_P
  have hPTle : h.P ⊔ T ≤ h.L ⊔ T := sup_le_sup_right h.P_le_L _
  have hLTC : h.L ⊔ T ≤ h.C := sup_le h.L_le_C inf_le_right
  have hTN : T ≤ normalizer (h.P : Set G) := fun y hy =>
    Subgroup.centralizer_le_normalizer _ (centralizer_le (fun x hx => h.P_le_L hx) hy.1)
  rw [isSylowOf_iff]
  refine ⟨hPTle.trans hLTC, hPL.isPGroup.to_sup_of_normal_left' h.isPGroup_kernel hTN, ?_⟩
  rw [← relIndex_mul_relIndex _ _ _ hPTle hLTC]
  have hrel : (h.P ⊔ T).relIndex (h.L ⊔ T) = h.P.relIndex h.L := by
    have e1 := relIndex_mul_card (h.P ⊔ T) (h.L ⊔ T)
    rw [inf_of_le_left hPTle, hcardPT, hcardLT] at e1
    have e2 := relIndex_mul_card h.P h.L
    rw [inf_of_le_left h.P_le_L] at e2
    have hpos : 0 < Nat.card h.P * Nat.card T := Nat.mul_pos Nat.card_pos Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [e1, ← e2, mul_assoc]
  rw [hrel]
  intro hdvd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hdvd with h1 | h1
  · exact (isSylowOf_iff.1 hPL).2.2 h1
  · exact (Nat.not_even_iff_odd.2 h.odd_relIndex) (even_iff_two_dvd.2 h1)

theorem isSylowOf_P_sup_Tsyl : IsSylowOf 2 (h.P ⊔ h.Tsyl) h.C :=
  h.centralizer_structure.2.2.2

theorem P_sup_Tsyl_le_J_Kp :
    h.P ⊔ h.Tsyl ≤ h.J ∧ h.P ⊔ h.Tsyl ≤ h.Kp := by
  obtain ⟨⟨-, hPR⟩, ⟨-, hPS⟩, -⟩ := h.card_R_S
  have hT : ∀ {M : Subgroup G}, M ≤ h.L → h.Tsyl ≤ normalizer (M : Set G) := fun hM y hy =>
    Subgroup.centralizer_le_normalizer _ (centralizer_le (fun x hx => hM hx) hy.1)
  have hC : h.P ⊔ h.Tsyl ≤ h.C := sup_le h.P_le_C inf_le_right
  exact ⟨le_inf hC (sup_le hPR (hT (h.pull_le_L _))),
    le_inf hC (sup_le hPS (hT (h.pull_le_L _)))⟩

end Setup

section Existence

theorem exists_setup_of_involution {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {L : Subgroup G}
    (hL : standardComponentIsStandard L)
    (hcore : ∀ x : G, orderOf x = 2 → standardComponentOddCore (centralizer ({x} : Set G)) = ⊥)
    (S : Sylow 2 (centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (centralizer (L : Set G)))) {f : ℕ}
    (hm : LieModel L .twistedF4 0 2 f) {t : G} (htL : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) :
    ∃ h : Setup G, h.L = L ∧ h.t = t ∧ 2 * h.a + 1 = f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hree : ReeTitsModel L .twistedF4 2 f := by
    rcases hm with ⟨hcl, -⟩ | ⟨-, hce, -⟩ | ⟨-, -, hree⟩ | ⟨-, hsz, -⟩
    · exact absurd hcl (by decide)
    · exact absurd hce (by decide)
    · exact hree
    · exact absurd hsz (by decide)
  obtain ⟨-, -, -, -, ⟨a, ha, hfa⟩, hiso⟩ := large_Ree_model_Schreier L 2 f hree
  obtain ⟨-, a', hfa', K, _, _, hK, ⟨e₀⟩⟩ := hree
  have haa : a' = a := by omega
  subst haa
  have : Fintype K := Fintype.ofFinite K
  have : CharP K F4.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨E⟩ := hiso a' K hfa hK ⟨e₀⟩
  have hK' : Nat.card K = 2 ^ (2 * a' + 1) := by rw [hK, hfa]
  have hcyc : ∀ S' : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S' : Subgroup (centralizer (L : Set G))) := by
    intro S'
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (centralizer (L : Set G)) S S'
    rw [Sylow.coe_subgroup_smul]
    exact isCyclic_of_surjective ((MulAut.conj g).toMonoidHom.subgroupMap
      (S : Subgroup (centralizer (L : Set G)))) (MonoidHom.subgroupMap_surjective _ _)
  exact ⟨⟨‹IsSimpleGroup G›, hnonab, L, hL, hcore, hcyc, K, a', ha, hK', E.symm, t, ht, htL⟩,
    rfl, rfl, hfa.symm⟩

theorem exists_setup {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {L : Subgroup G}
    (hL : standardComponentIsStandard L)
    (hcore : ∀ x : G, orderOf x = 2 → standardComponentOddCore (centralizer ({x} : Set G)) = ⊥)
    (S : Sylow 2 (centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (centralizer (L : Set G)))) {f : ℕ}
    (hm : LieModel L .twistedF4 0 2 f) :
    ∃ h : Setup G, h.L = L ∧ 2 * h.a + 1 = f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := centralizer (L : Set G)) 2
    (even_iff_two_dvd.1 hL.2.1)
  obtain ⟨h, hL', -, hf⟩ := exists_setup_of_involution hnonab hL hcore S hS hm t.2
    (by rw [Subgroup.orderOf_coe]; exact ht)
  exact ⟨h, hL', hf⟩

end Existence

end CFSG.LocalAnalysis.EvenBN.TwoF4
