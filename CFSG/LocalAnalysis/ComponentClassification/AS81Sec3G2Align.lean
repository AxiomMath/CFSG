module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3G2Para
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2LeviCent
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.ComponentClassification.AS81.G2

open Subgroup CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ABGLocalTools

variable {K : Type} [Field K] [CharP K 2]

local notation "X" => pinnedX Tag.G2 K

variable (K) in
@[expose] def g2LongPos :
    Subgroup (ModGL .G2 K) where
  carrier := {g | ∃ B E F : K, g = g2N 0 B 0 0 E F}
  mul_mem' := by
    rintro _ _ ⟨B, E, F, rfl⟩ ⟨B', E', F', rfl⟩
    refine ⟨B + B', E + E', F + F' + B' * E, ?_⟩
    rw [mul_g2N, g2N_mul_r, g2N_mul_a, g2N_mul_u, g2N_mul_v, g2N_mul_b, g2N_mul_c]
    exact g2N_eq_g2N (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)
  one_mem' := ⟨0, 0, 0, g2N_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨B, E, F, rfl⟩
    refine ⟨B, E, F + B * E, ?_⟩
    rw [inv_eq_iff_mul_eq_one, mul_g2N, g2N_mul_r, g2N_mul_a, g2N_mul_u, g2N_mul_v, g2N_mul_b,
      g2N_mul_c, ← g2N_zero]
    exact g2N_eq_g2N (by ring) (by char2_ring) (by ring) (by ring) (by char2_ring)
      (by char2_ring)

variable (K) in
@[expose] def g2ACGroup :
    Subgroup (ModGL .G2 K) where
  carrier := {g | ∃ B F : K, g = g2N 0 B 0 0 0 F}
  mul_mem' := by
    rintro _ _ ⟨B, F, rfl⟩ ⟨B', F', rfl⟩
    refine ⟨B + B', F + F', ?_⟩
    rw [mul_g2N, g2N_mul_r, g2N_mul_a, g2N_mul_u, g2N_mul_v, g2N_mul_b, g2N_mul_c]
    exact g2N_eq_g2N (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)
  one_mem' := ⟨0, 0, g2N_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨B, F, rfl⟩
    refine ⟨B, F, ?_⟩
    rw [inv_eq_iff_mul_eq_one, mul_g2N, g2N_mul_r, g2N_mul_a, g2N_mul_u, g2N_mul_v, g2N_mul_b,
      g2N_mul_c, ← g2N_zero]
    exact g2N_eq_g2N (by ring) (by char2_ring) (by ring) (by ring) (by ring) (by char2_ring)

theorem g2ACGroup_le_g2LongPos :
    g2ACGroup K ≤ g2LongPos K := by
  rintro _ ⟨B, F, rfl⟩
  exact ⟨B, 0, F, rfl⟩

theorem card_g2ACGroup
    [Finite K] : Nat.card (g2ACGroup K) = Nat.card K * Nat.card K := by
  rw [← Nat.card_prod]
  refine (Nat.card_eq_of_bijective (fun p : K × K => (⟨g2N 0 p.1 0 0 0 p.2, ⟨p.1, p.2, rfl⟩⟩ :
    g2ACGroup K)) ⟨fun p p' h => ?_, fun g => ?_⟩).symm
  · simp only at h
    obtain ⟨-, h1, -, -, -, h2⟩ := g2N_injective (Subtype.mk.inj h)
    exact Prod.ext h1 h2
  · obtain ⟨B, F, hg⟩ := g.2
    exact ⟨(B, F), Subtype.ext hg.symm⟩

theorem card_g2LongPos
    [Finite K] : Nat.card (g2LongPos K) = Nat.card K ^ 3 := by
  have e : Nat.card (K × K × K) = Nat.card K ^ 3 := by
    simp only [Nat.card_prod]
    ring
  rw [← e]
  refine (Nat.card_eq_of_bijective (fun p : K × K × K =>
    (⟨g2N 0 p.1 0 0 p.2.1 p.2.2, ⟨p.1, p.2.1, p.2.2, rfl⟩⟩ : g2LongPos K))
    ⟨fun p p' h => ?_, fun g => ?_⟩).symm
  · simp only at h
    obtain ⟨-, h1, -, -, h2, h3⟩ := g2N_injective (Subtype.mk.inj h)
    exact Prod.ext h1 (Prod.ext h2 h3)
  · obtain ⟨B, E, F, hg⟩ := g.2
    exact ⟨(B, E, F), Subtype.ext hg.symm⟩

theorem g2N_long_sq
    (B E F : K) : g2N 0 B 0 0 E F * g2N 0 B 0 0 E F = g2N 0 0 0 0 0 (B * E) := by
  rw [g2N_mul_self]
  exact g2N_eq_g2N rfl rfl (by ring) (by ring) (by ring) (by ring)

theorem eq_or_eq_of_elem
    [Finite K] {W : Subgroup (ModGL .G2 K)} (hWU : W ≤ g2LongPos K) (hW : IsElemAbelian 2 W)
    (hcard : Nat.card W = Nat.card K * Nat.card K) : W = g2BCGroup K ∨ W = g2ACGroup K := by
  have hBE : ∀ {B E F : K}, g2N 0 B 0 0 E F ∈ W → B * E = 0 := by
    intro B E F hw
    have h1 := hW.2 _ hw
    rw [sq, g2N_long_sq, ← g2N_zero] at h1
    exact (g2N_injective h1).2.2.2.2.2
  by_cases hB : ∀ w ∈ W, w ∈ g2BCGroup K
  · left
    exact eq_of_le_of_card_ge hB (by rw [card_g2BCGroup, hcard])
  · right
    push Not at hB
    obtain ⟨w₁, hw₁, hw₁B⟩ := hB
    obtain ⟨B₁, E₁, F₁, rfl⟩ := hWU hw₁
    have hB₁ : B₁ ≠ 0 := by
      rintro rfl
      exact hw₁B ⟨E₁, F₁, rfl⟩
    have hE₁ : E₁ = 0 := by
      have := hBE hw₁
      exact (mul_eq_zero.mp this).resolve_left hB₁
    subst hE₁
    refine eq_of_le_of_card_ge (fun w hw => ?_) (by rw [card_g2ACGroup, hcard])
    obtain ⟨B, E, F, rfl⟩ := hWU hw
    by_cases hE : E = 0
    · subst hE
      exact ⟨B, F, rfl⟩
    · exfalso
      have hB0 : B = 0 := (mul_eq_zero.mp (hBE hw)).resolve_right hE
      subst hB0
      have e : g2N (0 : K) B₁ 0 0 0 F₁ * g2N 0 0 0 0 E F = g2N 0 B₁ 0 0 E (F₁ + F) := by
        rw [mul_g2N, g2N_mul_r, g2N_mul_a, g2N_mul_u, g2N_mul_v, g2N_mul_b, g2N_mul_c]
        exact g2N_eq_g2N (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)
      have hmem := mul_mem hw₁ hw
      rw [e] at hmem
      exact mul_ne_zero hB₁ hE (hBE hmem)

theorem weylElt_r_conj_bc
    (y z : K) : weylElt .G2 K g2ir 1 * g2N 0 0 0 0 y z * (weylElt .G2 K g2ir 1)⁻¹ =
      g2N 0 y 0 0 0 z := by
  have e1 : g2N (0 : K) 0 0 0 y z = X g2b y * X g2c z := by
    simp only [g2N, pinnedX_zero, one_mul]
  have e2 : g2N (0 : K) y 0 0 0 z = X g2a y * X g2c z := by
    simp only [g2N, pinnedX_zero, one_mul, mul_one]
  rw [e1, e2, show weylElt .G2 K g2ir 1 * (X g2b y * X g2c z) * (weylElt .G2 K g2ir 1)⁻¹ =
    (weylElt .G2 K g2ir 1 * X g2b y * (weylElt .G2 K g2ir 1)⁻¹) *
      (weylElt .G2 K g2ir 1 * X g2c z * (weylElt .G2 K g2ir 1)⁻¹) by group,
    weylElt_conj g2ir isRoot_g2b, weylElt_conj g2ir isRoot_g2c, reflect_r_b, reflect_r_c]

theorem weylElt_r_conj_ac
    (y z : K) : weylElt .G2 K g2ir 1 * g2N 0 y 0 0 0 z * (weylElt .G2 K g2ir 1)⁻¹ =
      g2N 0 0 0 0 y z := by
  have e1 : g2N (0 : K) 0 0 0 y z = X g2b y * X g2c z := by
    simp only [g2N, pinnedX_zero, one_mul]
  have e2 : g2N (0 : K) y 0 0 0 z = X g2a y * X g2c z := by
    simp only [g2N, pinnedX_zero, one_mul, mul_one]
  rw [e1, e2, show weylElt .G2 K g2ir 1 * (X g2a y * X g2c z) * (weylElt .G2 K g2ir 1)⁻¹ =
    (weylElt .G2 K g2ir 1 * X g2a y * (weylElt .G2 K g2ir 1)⁻¹) *
      (weylElt .G2 K g2ir 1 * X g2c z * (weylElt .G2 K g2ir 1)⁻¹) by group,
    weylElt_conj g2ir isRoot_g2a, weylElt_conj g2ir isRoot_g2c, reflect_r_a, reflect_r_c]

theorem map_weylElt_r_g2BCGroup :
    (g2BCGroup K).map (MulAut.conj (weylElt .G2 K g2ir 1)).toMonoidHom = g2ACGroup K := by
  ext g
  constructor
  · rintro ⟨_, ⟨y, z, rfl⟩, rfl⟩
    show weylElt .G2 K g2ir 1 * g2N 0 0 0 0 y z * (weylElt .G2 K g2ir 1)⁻¹ ∈ g2ACGroup K
    rw [weylElt_r_conj_bc]
    exact ⟨y, z, rfl⟩
  · rintro ⟨y, z, rfl⟩
    refine ⟨g2N 0 0 0 0 y z, ⟨y, z, rfl⟩, ?_⟩
    show weylElt .G2 K g2ir 1 * g2N 0 0 0 0 y z * (weylElt .G2 K g2ir 1)⁻¹ = g2N 0 y 0 0 0 z
    exact weylElt_r_conj_bc y z

theorem mem_normalizer_closure {G : Type*} [Group G] {T : Set G} {g : G}
    (h₁ : ∀ t ∈ T, g * t * g⁻¹ ∈ closure T) (h₂ : ∀ t ∈ T, g⁻¹ * t * g ∈ closure T) :
    g ∈ normalizer (closure T : Set G) := by
  have key : ∀ k : G, (∀ t ∈ T, k * t * k⁻¹ ∈ closure T) →
      ∀ w ∈ closure T, k * w * k⁻¹ ∈ closure T := by
    intro k hk w hw
    have hle : closure T ≤ (closure T).comap (MulAut.conj k).toMonoidHom :=
      (closure_le _).2 fun t ht => hk t ht
    exact hle hw
  refine mem_normalizer_of_conj (key g h₁) (fun w hw => ?_)
  have := key g⁻¹ (fun t ht => by rw [inv_inv]; exact h₂ t ht) w hw
  rwa [inv_inv] at this

theorem weylElt_r_mem_normalizer_g2LongA2 :
    weylElt .G2 K g2ir 1 ∈ normalizer (g2LongA2 K : Set (ModGL .G2 K)) := by
  have hinv : (weylElt .G2 K g2ir 1)⁻¹ = weylElt .G2 K g2ir 1 := weylElt_inv g2ir
  have key : ∀ t ∈ (Set.range (pinnedX .G2 K g2a) ∪ Set.range (pinnedX .G2 K (-g2a)) ∪
      Set.range (pinnedX .G2 K g2b) ∪ Set.range (pinnedX .G2 K (-g2b)) ∪
      Set.range (pinnedX .G2 K g2c) ∪ Set.range (pinnedX .G2 K (-g2c))),
      weylElt .G2 K g2ir 1 * t * (weylElt .G2 K g2ir 1)⁻¹ ∈ g2LongA2 K := by
    rintro _ (((((⟨x, rfl⟩ | ⟨x, rfl⟩) | ⟨x, rfl⟩) | ⟨x, rfl⟩) | ⟨x, rfl⟩) | ⟨x, rfl⟩)
    · rw [weylElt_conj g2ir isRoot_g2a, reflect_r_a]
      exact pinnedX_b_mem_g2LongA2 x
    · rw [weylElt_conj g2ir (IsRoot.neg isRoot_g2a),
        show reflect .G2 g2ir (-g2a) = -g2b from List.ofFn_injective (by decide +kernel)]
      exact pinnedX_nb_mem_g2LongA2 x
    · rw [weylElt_conj g2ir isRoot_g2b, reflect_r_b]
      exact pinnedX_a_mem_g2LongA2 x
    · rw [weylElt_conj g2ir (IsRoot.neg isRoot_g2b),
        show reflect .G2 g2ir (-g2b) = -g2a from List.ofFn_injective (by decide +kernel)]
      exact pinnedX_na_mem_g2LongA2 x
    · rw [weylElt_conj g2ir isRoot_g2c, reflect_r_c]
      exact pinnedX_c_mem_g2LongA2 x
    · rw [weylElt_conj g2ir (IsRoot.neg isRoot_g2c),
        show reflect .G2 g2ir (-g2c) = -g2c from List.ofFn_injective (by decide +kernel)]
      exact pinnedX_nc_mem_g2LongA2 x
  exact mem_normalizer_closure key (fun t ht => by
    have := key t ht
    rw [hinv] at this ⊢
    exact this)

theorem weylElt_r_mem_normalizer_g2TorusR :
    weylElt .G2 K g2ir 1 ∈ normalizer (g2TorusR K : Set (ModGL .G2 K)) := by
  have hinv : (weylElt .G2 K g2ir 1)⁻¹ = weylElt .G2 K g2ir 1 := weylElt_inv g2ir
  have key : ∀ h ∈ g2TorusR K,
      weylElt .G2 K g2ir 1 * h * (weylElt .G2 K g2ir 1)⁻¹ ∈ g2TorusR K := by
    rintro _ ⟨t, rfl⟩
    exact ⟨t⁻¹, (weylElt_mul_torusElt_mul_inv g2ir t).symm⟩
  exact mem_normalizer_of_conj key (fun h hh => by
    have := key h hh
    rw [hinv] at this ⊢
    exact this)

theorem map_weylElt_r_g2ACGroup :
    (g2ACGroup K).map (MulAut.conj (weylElt .G2 K g2ir 1)).toMonoidHom = g2BCGroup K := by
  ext g
  constructor
  · rintro ⟨_, ⟨y, z, rfl⟩, rfl⟩
    show weylElt .G2 K g2ir 1 * g2N 0 y 0 0 0 z * (weylElt .G2 K g2ir 1)⁻¹ ∈ g2BCGroup K
    rw [weylElt_r_conj_ac]
    exact ⟨y, z, rfl⟩
  · rintro ⟨y, z, rfl⟩
    refine ⟨g2N 0 y 0 0 0 z, ⟨y, z, rfl⟩, ?_⟩
    show weylElt .G2 K g2ir 1 * g2N 0 y 0 0 0 z * (weylElt .G2 K g2ir 1)⁻¹ = g2N 0 0 0 0 y z
    exact weylElt_r_conj_ac y z

theorem g2LongPos_le_g2LongA2 :
    g2LongPos K ≤ g2LongA2 K := by
  rintro _ ⟨B, E, F, rfl⟩
  have e : g2N (0 : K) B 0 0 E F = X g2a B * X g2b E * X g2c F := by
    simp only [g2N, pinnedX_zero, one_mul, mul_one]
  rw [e]
  exact mul_mem (mul_mem (pinnedX_a_mem_g2LongA2 B) (pinnedX_b_mem_g2LongA2 E))
    (pinnedX_c_mem_g2LongA2 F)

omit [CharP K 2] in
theorem g2LongA2_le_centralizer_g2TorusR
    [Finite K] (hK : Nat.card K = 4) :
    g2LongA2 K ≤ centralizer (g2TorusR K : Set (ModGL .G2 K)) := by
  intro l hl
  rw [mem_centralizer_iff]
  rintro _ ⟨t, rfl⟩
  have h := g2LongA2_le_centralizer_torusElt (pow_three_eq_one_of_card hK t) hl
  exact (mem_centralizer_singleton_iff.mp h).symm

theorem isElemAbelian_map_of {H H' : Type*} [Group H] [Group H'] (f : H →* H')
    {W : Subgroup H} (hW : IsElemAbelian 2 W) : IsElemAbelian 2 (W.map f) :=
  CFSG.Open.IsElemAbelian.map hW _

theorem map_conj_mul {G : Type*} [Group G] (W : Subgroup G) (a b : G) :
    W.map (MulAut.conj (a * b)).toMonoidHom =
      (W.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem exists_align
    [Finite K] (hK : Nat.card K = 4) {S W₁ W₂ : Subgroup (ModGL .G2 K)}
    (hS : IsSylowOf 2 S (g2LongA2 K)) (hS64 : Nat.card S = 64) (hW₁S : W₁ ≤ S) (hW₂S : W₂ ≤ S)
    (hW₁ : IsElemAbelian 2 W₁) (hW₂ : IsElemAbelian 2 W₂) (h₁ : Nat.card W₁ = 16)
    (h₂ : Nat.card W₂ = 16) (hne : W₁ ≠ W₂) :
    ∃ c ∈ adjointGroup .G2 K, c ∈ normalizer (g2LongA2 K : Set (ModGL .G2 K)) ∧
      c ∈ normalizer (g2TorusR K : Set (ModGL .G2 K)) ∧
      W₁.map (MulAut.conj c).toMonoidHom = g2BCGroup K ∧
      W₂.map (MulAut.conj c).toMonoidHom = g2ACGroup K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : Nat.card K * Nat.card K = 16 := by rw [hK]
  have hU : IsSylowOf 2 (g2LongPos K) (g2LongA2 K) := by
    refine isSylowOf_of_card g2LongPos_le_g2LongA2 ?_
    rw [← hS.card_eq, hS64, card_g2LongPos, hK]
    norm_num
  obtain ⟨k, hkL, hk⟩ := hS.exists_mem_conj hU
  have hkS : ∀ {W : Subgroup (ModGL .G2 K)}, W ≤ S →
      W.map (MulAut.conj k).toMonoidHom ≤ g2LongPos K := by
    rintro W hWS _ ⟨w, hw, rfl⟩
    refine (hk _).mpr ?_
    show k⁻¹ * (k * w * k⁻¹) * k ∈ S
    rw [show k⁻¹ * (k * w * k⁻¹) * k = w by group]
    exact hWS hw
  have hcard : ∀ {W : Subgroup (ModGL .G2 K)}, Nat.card W = 16 →
      Nat.card (W.map (MulAut.conj k).toMonoidHom) = Nat.card K * Nat.card K := by
    intro W hW
    rw [card_map_of_injective (MulAut.conj k).injective, hW, hq]
  have hinj : W₁.map (MulAut.conj k).toMonoidHom ≠ W₂.map (MulAut.conj k).toMonoidHom :=
    fun h => hne (map_injective (MulAut.conj k).injective h)
  have hkC : k ∈ adjointGroup .G2 K := g2LongA2_le_adjointGroup hkL
  have hkN : k ∈ normalizer (g2LongA2 K : Set (ModGL .G2 K)) := le_normalizer hkL
  have hkH : k ∈ normalizer (g2TorusR K : Set (ModGL .G2 K)) :=
    centralizer_le_normalizer _ (g2LongA2_le_centralizer_g2TorusR hK hkL)
  have hnC : weylElt .G2 K g2ir 1 ∈ adjointGroup .G2 K :=
    g2RankOne_le_adjointGroup g2ir (weylElt_mem_g2RankOne g2ir 1)
  rcases eq_or_eq_of_elem (hkS hW₁S) (isElemAbelian_map_of _ hW₁) (hcard h₁) with e₁ | e₁ <;>
    rcases eq_or_eq_of_elem (hkS hW₂S) (isElemAbelian_map_of _ hW₂) (hcard h₂) with e₂ | e₂
  · exact absurd (e₁.trans e₂.symm) hinj
  · exact ⟨k, hkC, hkN, hkH, e₁, e₂⟩
  · refine ⟨weylElt .G2 K g2ir 1 * k, mul_mem hnC hkC,
      mul_mem weylElt_r_mem_normalizer_g2LongA2 hkN,
      mul_mem weylElt_r_mem_normalizer_g2TorusR hkH, ?_, ?_⟩
    · rw [map_conj_mul, e₁, map_weylElt_r_g2ACGroup]
    · rw [map_conj_mul, e₂, map_weylElt_r_g2BCGroup]
  · exact absurd (e₁.trans e₂.symm) hinj

end CFSG.ComponentClassification.AS81.G2
