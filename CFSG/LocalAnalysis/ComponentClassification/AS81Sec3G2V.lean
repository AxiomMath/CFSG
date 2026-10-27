module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3G2Align
public import CFSG.Sporadic.Recognition.LyonsAS44Quat

public section

namespace CFSG.ComponentClassification.AS81.G2

open Subgroup CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ABGLocalTools

variable {K : Type} [Field K] [CharP K 2]

local notation "X" => pinnedX Tag.G2 K

omit [CharP K 2] in
theorem pow_four_eq_self [Finite K] (hK : Nat.card K = 4) (c : K) : c ^ 4 = c := by
  have := Fintype.ofFinite K
  have h := FiniteField.pow_card c
  rwa [← Nat.card_eq_fintype_card, hK] at h

omit [CharP K 2] in
theorem pow_three_eq_one_of_ne [Finite K] (hK : Nat.card K = 4) {c : K} (hc : c ≠ 0) :
    c ^ 3 = 1 := by
  have h := pow_four_eq_self hK c
  have h' : c * (c ^ 3 - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h0 | h1
  · exact absurd h0 hc
  · exact sub_eq_zero.mp h1

omit [CharP K 2] in
theorem sq_add_self_add_one_of_ne [Finite K] (hK : Nat.card K = 4) {ω : K} (h0 : ω ≠ 0)
    (h1 : ω ≠ 1) : ω ^ 2 + ω + 1 = 0 := by
  have h3 := pow_three_eq_one_of_ne hK h0
  have h' : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.mp h' with h | h
  · exact absurd (sub_eq_zero.mp h) h1
  · exact h

omit [CharP K 2] in
theorem exists_ne_zero_ne_one [Finite K] (hK : Nat.card K = 4) : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 := by
  classical
  by_contra h
  have := Fintype.ofFinite K
  have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun ω _ => by
    by_cases h0 : ω = 0
    · simp [h0]
    · have h1 : ω = 1 := by
        by_contra h1
        exact h ⟨ω, h0, h1⟩
      simp [h1]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK] at h1
  have h2 := Finset.card_le_two (a := (0 : K)) (b := 1)
  omega

theorem g2N_uv_mul
    (C D E F C' D' E' F' : K) :
    g2N 0 0 C D E F * g2N 0 0 C' D' E' F' =
      g2N 0 0 (C + C') (D + D') (E + E') (F + F' + C' * D) := by
  rw [g2N_zero_mul_g2N_zero]
  exact g2N_eq_g2N rfl (by ring) rfl rfl rfl (by ring)

theorem g2N_uv_inv
    (C D E F : K) : (g2N 0 0 C D E F)⁻¹ = g2N 0 0 C D E (F + C * D) := by
  rw [g2N_zero_inv]
  exact g2N_eq_g2N rfl rfl rfl rfl rfl (by ring)

variable (K) in
@[expose] def g2V0 :
    Subgroup (ModGL .G2 K) where
  carrier := {g | ∃ C D E F : K, g = g2N 0 0 C D E F}
  mul_mem' := by
    rintro _ _ ⟨C, D, E, F, rfl⟩ ⟨C', D', E', F', rfl⟩
    exact ⟨_, _, _, _, g2N_uv_mul C D E F C' D' E' F'⟩
  one_mem' := ⟨0, 0, 0, 0, g2N_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨C, D, E, F, rfl⟩
    exact ⟨_, _, _, _, g2N_uv_inv C D E F⟩

variable (K) in
@[expose] def g2V :
    Subgroup (ModGL .G2 K) where
  carrier := {g | ∃ C D F : K, g = g2N 0 0 C D 0 F}
  mul_mem' := by
    rintro _ _ ⟨C, D, F, rfl⟩ ⟨C', D', F', rfl⟩
    exact ⟨_, _, _, (g2N_uv_mul C D 0 F C' D' 0 F').trans (by rw [add_zero])⟩
  one_mem' := ⟨0, 0, 0, g2N_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨C, D, F, rfl⟩
    exact ⟨_, _, _, g2N_uv_inv C D 0 F⟩

theorem g2V0_le_g2ShortParabolicRadical :
    g2V0 K ≤ g2ShortParabolicRadical K := by
  rintro _ ⟨C, D, E, F, rfl⟩
  exact g2N_mem_g2ShortParabolicRadical 0 C D E F

theorem g2V_le_g2V0 :
    g2V K ≤ g2V0 K := by
  rintro _ ⟨C, D, F, rfl⟩
  exact ⟨C, D, 0, F, rfl⟩

omit [CharP K 2] in
theorem torus_r_conj_g2N_uv
    (t : Kˣ) (C D E F : K) :
    torusElt .G2 K g2ir t * g2N 0 0 C D E F * (torusElt .G2 K g2ir t)⁻¹ =
      g2N 0 0 (((t ^ (-1 : ℤ) : Kˣ) : K) * C) (((t ^ (1 : ℤ) : Kˣ) : K) * D)
        (((t ^ (3 : ℤ) : Kˣ) : K) * E) F := by
  have e : ∀ a b : ModGL .G2 K, torusElt .G2 K g2ir t * (a * b) * (torusElt .G2 K g2ir t)⁻¹ =
      (torusElt .G2 K g2ir t * a * (torusElt .G2 K g2ir t)⁻¹) *
        (torusElt .G2 K g2ir t * b * (torusElt .G2 K g2ir t)⁻¹) := fun a b => by group
  simp only [g2N, pinnedX_zero, one_mul, e]
  rw [torus_r_conj t isRoot_g2u (-1) (by decide), torus_r_conj t isRoot_g2v 1 (by decide),
    torus_r_conj t isRoot_g2b 3 (by decide), torus_r_conj t isRoot_g2c 0 (by decide), zpow_zero,
    Units.val_one, one_mul]

omit [CharP K 2] in
theorem torus_r_conj_g2N_uv'
    [Finite K] (hK : Nat.card K = 4) (t : Kˣ) (C D E F : K) :
    torusElt .G2 K g2ir t * g2N 0 0 C D E F * (torusElt .G2 K g2ir t)⁻¹ =
      g2N 0 0 ((t : K) ^ 2 * C) ((t : K) * D) E F := by
  have ht3 : t ^ 3 = 1 := pow_three_eq_one_of_card hK t
  have h1 : t ^ (-1 : ℤ) = t ^ 2 := by
    rw [zpow_neg_one]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact ht3)
  have h3 : t ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, ht3]
  rw [torus_r_conj_g2N_uv, h1, h3, zpow_one, Units.val_one, one_mul, Units.val_pow_eq_pow_val]

theorem coord_eq_of_mul_inv_mem_g2BCGroup
    {A B C D E F A' B' C' D' E' F' : K}
    (h : g2N A B C D E F * (g2N A' B' C' D' E' F')⁻¹ ∈ g2BCGroup K) :
    A = A' ∧ B = B' ∧ C = C' ∧ D = D' := by
  have hN := borelGroup_le_normalizer_g2BCGroup (g2N_mem_borelGroup A' B' C' D' E' F')
  have h' := (mem_normalizer_iff.mp (inv_mem hN) _).mp h
  rw [show (g2N A' B' C' D' E' F')⁻¹ * (g2N A B C D E F * (g2N A' B' C' D' E' F')⁻¹) *
    (g2N A' B' C' D' E' F')⁻¹⁻¹ = (g2N A' B' C' D' E' F')⁻¹ * g2N A B C D E F by group] at h'
  obtain ⟨y, z, hyz⟩ := h'
  have e : g2N A B C D E F = g2N A' B' C' D' (E' + y) (F' + z) := by
    rw [← mul_inv_cancel_left (g2N A' B' C' D' E' F') (g2N A B C D E F), hyz, mul_g2N, g2N_mul_r,
      g2N_mul_a, g2N_mul_u, g2N_mul_v, g2N_mul_b, g2N_mul_c]
    exact g2N_eq_g2N (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)
  obtain ⟨h1, h2, h3, h4, -, -⟩ := g2N_injective e
  exact ⟨h1, h2, h3, h4⟩

theorem commutator_mem_g2BCGroup_of_mem_g2V0
    {d g : ModGL .G2 K} (hd : d ∈ g2V0 K) (hg : g ∈ g2LongPos K) :
    d * g * d⁻¹ * g⁻¹ ∈ g2BCGroup K := by
  obtain ⟨C, D, E, F, rfl⟩ := hd
  obtain ⟨B, E', F', rfl⟩ := hg
  rw [show g2N 0 0 C D E F * g2N 0 B 0 0 E' F' * (g2N 0 0 C D E F)⁻¹ * (g2N 0 B 0 0 E' F')⁻¹ =
    (g2N 0 0 C D E F * g2N 0 B 0 0 E' F') * (g2N 0 B 0 0 E' F' * g2N 0 0 C D E F)⁻¹ by group,
    g2N_zero_mul_g2N_zero, g2N_zero_mul_g2N_zero, g2N_zero_inv, g2N_zero_mul_g2N_zero]
  exact ⟨_, _, g2N_eq_g2N rfl (by char2_ring) (by char2_ring) (by char2_ring) rfl rfl⟩

theorem mem_g2V0_of_commutator_mem
    {d g : ModGL .G2 K} (hd : d ∈ g2ShortParabolicRadical K) (hg : g ∈ g2LongPos K)
    (hgZ : g ∉ g2BCGroup K) (h : d * g * d⁻¹ * g⁻¹ ∈ g2BCGroup K) : d ∈ g2V0 K := by
  obtain ⟨A, C, D, E, F, rfl⟩ := hd
  obtain ⟨B, E', F', rfl⟩ := hg
  have hB : B ≠ 0 := by
    rintro rfl
    exact hgZ ⟨E', F', rfl⟩
  have e1 : g2N A 0 C D E F * g2N 0 B 0 0 E' F' = g2N A B C D (E + E') (F + B * E + F') := by
    rw [mul_g2N, g2N_mul_r, g2N_mul_a, g2N_mul_u, g2N_mul_v, g2N_mul_b, g2N_mul_c]
    exact g2N_eq_g2N (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)
  have e2 : g2N 0 B 0 0 E' F' * g2N A 0 C D E F = g2N A B (B * A + C) (B * A ^ 2 + D)
      (E' + B * A ^ 3 + E) (F' + B ^ 2 * A ^ 3 + C * (B * A ^ 2) + F) := by
    rw [mul_g2N, g2N_mul_r, g2N_mul_a, g2N_mul_u, g2N_mul_v, g2N_mul_b, g2N_mul_c]
    exact g2N_eq_g2N (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)
  rw [show g2N A 0 C D E F * g2N 0 B 0 0 E' F' * (g2N A 0 C D E F)⁻¹ * (g2N 0 B 0 0 E' F')⁻¹ =
    (g2N A 0 C D E F * g2N 0 B 0 0 E' F') * (g2N 0 B 0 0 E' F' * g2N A 0 C D E F)⁻¹ by group,
    e1, e2] at h
  obtain ⟨-, -, hC, -⟩ := coord_eq_of_mul_inv_mem_g2BCGroup h
  have hA : A = 0 := by
    have h0 : B * A = 0 := by linear_combination -hC
    rcases mul_eq_zero.mp h0 with h0 | h0
    · exact absurd h0 hB
    · exact h0
  subst hA
  exact ⟨C, D, E, F, rfl⟩

theorem commutator_g2V0_g2TorusR
    [Finite K] (hK : Nat.card K = 4) : ⁅g2V0 K, g2TorusR K⁆ = g2V K := by
  apply le_antisymm
  · rw [commutator_le]
    rintro _ ⟨C, D, E, F, rfl⟩ _ ⟨t, rfl⟩
    change g2N 0 0 C D E F * torusElt .G2 K g2ir t * (g2N 0 0 C D E F)⁻¹ *
      (torusElt .G2 K g2ir t)⁻¹ ∈ g2V K
    rw [show g2N 0 0 C D E F * torusElt .G2 K g2ir t * (g2N 0 0 C D E F)⁻¹ *
      (torusElt .G2 K g2ir t)⁻¹ = g2N 0 0 C D E F * (torusElt .G2 K g2ir t * g2N 0 0 C D E F *
        (torusElt .G2 K g2ir t)⁻¹)⁻¹ by group, torus_r_conj_g2N_uv' hK, g2N_uv_inv, g2N_uv_mul]
    exact ⟨_, _, _, g2N_eq_g2N rfl rfl rfl rfl (by char2_ring) rfl⟩
  · obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one hK
    have hω := sq_add_self_add_one_of_ne hK hω0 hω1
    have hω4 := pow_four_eq_self hK ω
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    set t : Kˣ := Units.mk0 ω hω0 with ht
    have hmem : ∀ v ∈ g2V0 K, v * torusElt .G2 K g2ir t * v⁻¹ * (torusElt .G2 K g2ir t)⁻¹ ∈
        ⁅g2V0 K, g2TorusR K⁆ := fun v hv => commutator_mem_commutator hv ⟨t, rfl⟩
    have key : ∀ v : ModGL .G2 K, v * torusElt .G2 K g2ir t * v⁻¹ * (torusElt .G2 K g2ir t)⁻¹ =
        v * (torusElt .G2 K g2ir t * v * (torusElt .G2 K g2ir t)⁻¹)⁻¹ := fun v => by group
    have hu : ∀ C : K, g2N 0 0 C 0 0 0 ∈ ⁅g2V0 K, g2TorusR K⁆ := by
      intro C
      have h := hmem _ ⟨ω ^ 2 * C, 0, 0, 0, rfl⟩
      rwa [key, torus_r_conj_g2N_uv' hK, g2N_uv_inv, g2N_uv_mul, Units.val_mk0,
        show g2N 0 0 (ω ^ 2 * C + ω ^ 2 * (ω ^ 2 * C)) (0 + ω * 0) (0 + 0)
          (0 + (0 + ω ^ 2 * (ω ^ 2 * C) * (ω * 0)) + ω ^ 2 * (ω ^ 2 * C) * 0) =
            g2N 0 0 C 0 0 0 from g2N_eq_g2N rfl rfl
          (by linear_combination (norm := char2_ring) C * hω + C * hω4) (by ring) (by ring)
          (by ring)] at h
    have hv : ∀ D : K, g2N 0 0 0 D 0 0 ∈ ⁅g2V0 K, g2TorusR K⁆ := by
      intro D
      have h := hmem _ ⟨0, ω * D, 0, 0, rfl⟩
      rwa [key, torus_r_conj_g2N_uv' hK, g2N_uv_inv, g2N_uv_mul, Units.val_mk0,
        show g2N 0 0 (0 + ω ^ 2 * 0) (ω * D + ω * (ω * D)) (0 + 0)
          (0 + (0 + ω ^ 2 * 0 * (ω * (ω * D))) + ω ^ 2 * 0 * (ω * D)) =
            g2N 0 0 0 D 0 0 from g2N_eq_g2N rfl rfl (by ring)
          (by linear_combination (norm := char2_ring) D * hω) (by ring) (by ring)] at h
    have hc : ∀ F : K, g2N 0 0 0 0 0 F ∈ ⁅g2V0 K, g2TorusR K⁆ := by
      intro F
      have h := mul_mem (mul_mem (mul_mem (hu F) (hv 1)) (inv_mem (hu F))) (inv_mem (hv 1))
      rwa [g2N_uv_inv, g2N_uv_inv, g2N_uv_mul, g2N_uv_mul, g2N_uv_mul,
        show g2N 0 0 (F + 0 + F + 0) (0 + 1 + 0 + 1) (0 + 0 + 0 + 0)
          (0 + 0 + 0 * 0 + (0 + F * 0) + F * (0 + 1) + (0 + 0 * 1) + 0 * (0 + 1 + 0)) =
            g2N 0 0 0 0 0 F from g2N_eq_g2N rfl rfl (by char2_ring) (by char2_ring) (by ring)
          (by char2_ring)] at h
    rintro _ ⟨C, D, F, rfl⟩
    have h := mul_mem (mul_mem (hu C) (hv D)) (hc F)
    rwa [g2N_uv_mul, g2N_uv_mul, show g2N 0 0 (C + 0 + 0) (0 + D + 0) (0 + 0 + 0)
      (0 + 0 + 0 * 0 + F + 0 * (0 + D)) = g2N 0 0 C D 0 F from g2N_eq_g2N rfl rfl (by ring)
        (by ring) (by ring) (by ring)] at h

theorem eq_g2N_c_of_mem_g2LongPos
    {g : ModGL .G2 K} (hg : g ∈ g2LongPos K)
    (ha : g * g2N 0 1 0 0 0 0 = g2N 0 1 0 0 0 0 * g)
    (hb : g * g2N 0 0 0 0 1 0 = g2N 0 0 0 0 1 0 * g) : ∃ l : K, g = g2N 0 0 0 0 0 l := by
  obtain ⟨B, E, F, rfl⟩ := hg
  rw [g2N_zero_mul_g2N_zero, g2N_zero_mul_g2N_zero] at ha hb
  obtain ⟨-, -, -, -, -, hE⟩ := g2N_injective ha
  obtain ⟨-, -, -, -, -, hB⟩ := g2N_injective hb
  have hE' : E = 0 := by linear_combination hE
  have hB' : B = 0 := by linear_combination -hB
  subst hE' hB'
  exact ⟨F, rfl⟩

variable (K) in
@[expose] def g2Q0
    (l : K) : Subgroup (ModGL .G2 K) where
  carrier := {g | ∃ C F : K, C ^ 4 = C ∧ F ^ 2 + l * F + l ^ 2 * C ^ 3 = 0 ∧
    g = g2N 0 0 C (l * C ^ 2) 0 F}
  mul_mem' := by
    rintro _ _ ⟨C, F, hC, hF, rfl⟩ ⟨C', F', hC', hF', rfl⟩
    refine ⟨C + C', F + F' + C' * (l * C ^ 2), ?_, ?_, ?_⟩
    · linear_combination (norm := char2_ring) hC + hC'
    · linear_combination (norm := char2_ring) hF + hF' + l ^ 2 * C' ^ 2 * hC
    · rw [g2N_uv_mul]
      exact g2N_eq_g2N rfl rfl rfl (by char2_ring) (by ring) rfl
  one_mem' := ⟨0, 0, by ring, by ring, by rw [show l * (0 : K) ^ 2 = 0 by ring, g2N_zero]⟩
  inv_mem' := by
    rintro _ ⟨C, F, hC, hF, rfl⟩
    refine ⟨C, F + C * (l * C ^ 2), hC, ?_, g2N_uv_inv _ _ _ _⟩
    linear_combination (norm := char2_ring) hF + l ^ 2 * C ^ 2 * hC

theorem g2Q0_le_g2V
    (l : K) : g2Q0 K l ≤ g2V K := by
  rintro _ ⟨C, F, -, -, rfl⟩
  exact ⟨C, l * C ^ 2, F, rfl⟩

theorem roots_g2Q0 {l c f r : K} (hr : r ^ 2 + l * r = l ^ 2 * c ^ 3) :
    f ^ 2 + l * f + l ^ 2 * c ^ 3 = 0 ↔ f = r ∨ f = r + l := by
  have e : f ^ 2 + l * f + l ^ 2 * c ^ 3 = (f - r) * (f - (r + l)) := by
    linear_combination (norm := char2_ring) -hr
  rw [e, mul_eq_zero, sub_eq_zero, sub_eq_zero]

theorem exists_root_g2Q0 [Finite K] (hK : Nat.card K = 4) {l ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    (c : K) : ∃ r : K, r ^ 2 + l * r = l ^ 2 * c ^ 3 := by
  by_cases hc : c = 0
  · exact ⟨0, by rw [hc]; ring⟩
  · refine ⟨l * ω, ?_⟩
    rw [pow_three_eq_one_of_ne hK hc]
    linear_combination (norm := char2_ring) l ^ 2 * hω

theorem card_g2Q0
    [Finite K] (hK : Nat.card K = 4) {l : K} (hl : l ≠ 0) : Nat.card (g2Q0 K l) = 8 := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one hK
  have hω := sq_add_self_add_one_of_ne hK hω0 hω1
  let P : K → K → Prop := fun c f => f ^ 2 + l * f + l ^ 2 * c ^ 3 = 0
  have e : {p : K × K // P p.1 p.2} ≃ g2Q0 K l := Equiv.ofBijective
    (fun p => ⟨g2N 0 0 p.1.1 (l * p.1.1 ^ 2) 0 p.1.2,
      ⟨p.1.1, p.1.2, pow_four_eq_self hK _, p.2, rfl⟩⟩)
    ⟨fun p p' h => by
      obtain ⟨-, -, h1, -, -, h2⟩ := g2N_injective (Subtype.mk.inj h)
      exact Subtype.ext (Prod.ext h1 h2),
    fun g => by
      obtain ⟨C, F, -, hF, hg⟩ := g.2
      exact ⟨⟨(C, F), hF⟩, Subtype.ext hg.symm⟩⟩
  rw [← Nat.card_congr e, Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype P), Nat.card_sigma]
  have hfib : ∀ c : K, Nat.card {f : K // P c f} = 2 := by
    intro c
    obtain ⟨r, hr⟩ := exists_root_g2Q0 hK hω c
    have e : {f : K // P c f} ≃ ↥({r, r + l} : Set K) := Equiv.subtypeEquivRight fun f => by
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact roots_g2Q0 hr
    rw [Nat.card_congr e, Nat.card_coe_set_eq, Set.ncard_pair]
    intro h
    exact hl (by linear_combination -h)
  simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, hK]

theorem g2N_c_mem_g2Q0
    (l : K) : g2N 0 0 0 0 0 l ∈ g2Q0 K l :=
  ⟨0, l, by ring, by char2_ring, g2N_eq_g2N rfl rfl rfl (by ring) rfl rfl⟩

theorem g2N_c_comm
    (l C D E F : K) : g2N 0 0 C D E F * g2N 0 0 0 0 0 l = g2N 0 0 0 0 0 l * g2N 0 0 C D E F := by
  rw [g2N_uv_mul, g2N_uv_mul]
  exact g2N_eq_g2N (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)

theorem centerIn_g2Q0
    [Finite K] (hK : Nat.card K = 4) {l : K} (hl : l ≠ 0) :
    CFSG.centerIn (g2Q0 K l) = zpowers (g2N 0 0 0 0 0 l) := by
  obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one hK
  have hω := sq_add_self_add_one_of_ne hK hω0 hω1
  have hω3 := pow_three_eq_one_of_ne hK hω0
  apply le_antisymm
  · rintro _ ⟨⟨C, F, -, hF, rfl⟩, hc⟩
    have hC : C = 0 := by
      by_contra hC
      have hC3 := pow_three_eq_one_of_ne hK hC
      have hmem : g2N 0 0 (ω * C) (l * (ω * C) ^ 2) 0 (l * ω) ∈ g2Q0 K l :=
        ⟨ω * C, l * ω, pow_four_eq_self hK _, by
          linear_combination (norm := ring_nf) l ^ 2 * hω + l ^ 2 * ω ^ 3 * hC3 +
            l ^ 2 * hω3, rfl⟩
      have h := mem_centralizer_iff.mp hc _ hmem
      rw [g2N_uv_mul, g2N_uv_mul] at h
      obtain ⟨-, -, -, -, -, hF'⟩ := g2N_injective h
      have h1 : l * ω * (ω - 1) = 0 := by
        linear_combination (norm := char2_ring) hF' - l * ω * hC3 + l * ω ^ 2 * hC3
      rcases mul_eq_zero.mp h1 with h1 | h1
      · rcases mul_eq_zero.mp h1 with h1 | h1
        · exact hl h1
        · exact hω0 h1
      · exact hω1 (sub_eq_zero.mp h1)
    subst hC
    have hF' : F * (F + l) = 0 := by linear_combination (norm := ring_nf) hF
    rw [show l * (0 : K) ^ 2 = 0 by ring]
    rcases mul_eq_zero.mp hF' with h0 | h0
    · rw [h0, g2N_zero]
      exact one_mem _
    · rw [show F = l by linear_combination (norm := char2_ring) h0]
      exact mem_zpowers _
  · rw [zpowers_le]
    refine ⟨g2N_c_mem_g2Q0 l, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨C, F, -, -, rfl⟩
    exact g2N_c_comm l C (l * C ^ 2) 0 F

theorem g2Q0_quaternion
    [Finite K] (hK : Nat.card K = 4) {l : K} (hl : l ≠ 0) :
    Nonempty (↥(g2Q0 K l) ≃* QuaternionGroup 2) := by
  obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one hK
  have hω := sq_add_self_add_one_of_ne hK hω0 hω1
  have hω3 := pow_three_eq_one_of_ne hK hω0
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  let x : ↥(g2Q0 K l) := ⟨g2N 0 0 1 l 0 (l * ω), 1, l * ω, by ring, by
    linear_combination (norm := ring_nf) l ^ 2 * hω, g2N_eq_g2N rfl rfl rfl (by ring) rfl rfl⟩
  let y : ↥(g2Q0 K l) := ⟨g2N 0 0 ω (l * ω ^ 2) 0 (l * ω), ω, l * ω, pow_four_eq_self hK ω, by
    linear_combination (norm := ring_nf) l ^ 2 * hω + l ^ 2 * hω3, rfl⟩
  have hx2 : ((x ^ 2 : ↥(g2Q0 K l)) : ModGL .G2 K) = g2N 0 0 0 0 0 l := by
    rw [sq, Subgroup.coe_mul, g2N_uv_mul]
    exact g2N_eq_g2N rfl rfl (by char2_ring) (by char2_ring) (by ring) (by char2_ring)
  refine CFSG.Sporadic.Recognition.LyonsSims.nonempty_mulEquiv_quaternionGroup_two
    (card_g2Q0 hK hl) x y ?_ ?_ ?_ ?_
  · refine Subtype.ext ?_
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq (x ^ 2), Subgroup.coe_mul, hx2, g2N_uv_mul,
      Subgroup.coe_one, ← g2N_zero]
    exact g2N_eq_g2N rfl rfl (by ring) (by ring) (by ring) (by char2_ring)
  · intro h
    have h' := congrArg Subtype.val h
    rw [hx2, Subgroup.coe_one, ← g2N_zero] at h'
    obtain ⟨-, -, -, -, -, h'⟩ := g2N_injective h'
    exact hl h'
  · refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv,
      mul_inv_eq_iff_eq_mul, g2N_uv_inv, g2N_uv_mul, g2N_uv_mul]
    exact g2N_eq_g2N rfl rfl (by ring) (by ring) (by ring)
      (by linear_combination (norm := char2_ring) l * hω)
  · refine Subtype.ext ?_
    rw [hx2, sq, Subgroup.coe_mul, g2N_uv_mul]
    exact g2N_eq_g2N rfl rfl (by char2_ring) (by char2_ring) (by ring)
      (by linear_combination (norm := char2_ring) l * hω3)

theorem torus_r_conj_mem_g2Q0
    [Finite K] (hK : Nat.card K = 4) (l : K) (t : Kˣ) {g : ModGL .G2 K} (hg : g ∈ g2Q0 K l) :
    torusElt .G2 K g2ir t * g * (torusElt .G2 K g2ir t)⁻¹ ∈ g2Q0 K l := by
  obtain ⟨C, F, -, hF, rfl⟩ := hg
  have ht3 : (t : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, pow_three_eq_one_of_card hK t, Units.val_one]
  rw [torus_r_conj_g2N_uv' hK]
  refine ⟨(t : K) ^ 2 * C, F, pow_four_eq_self hK _, ?_, ?_⟩
  · linear_combination (norm := ring_nf) hF + l ^ 2 * C ^ 3 * ((t : K) ^ 3 + 1) * ht3
  · exact g2N_eq_g2N rfl rfl rfl
      (by linear_combination (norm := ring_nf) -l * C ^ 2 * (t : K) * ht3) rfl rfl

theorem torusElt_mem_normalizer_g2Q0
    [Finite K] (hK : Nat.card K = 4) (l : K) (t : Kˣ) :
    torusElt .G2 K g2ir t ∈ normalizer (g2Q0 K l : Set (ModGL .G2 K)) := by
  have hinv : (torusElt .G2 K g2ir t)⁻¹ = torusElt .G2 K g2ir t⁻¹ :=
    (map_inv (torusEltHom .G2 K g2ir) t).symm
  refine mem_normalizer_of_conj (fun w hw => torus_r_conj_mem_g2Q0 hK l t hw) (fun w hw => ?_)
  have h := torus_r_conj_mem_g2Q0 hK l t⁻¹ hw
  rwa [← hinv, inv_inv] at h

theorem eq_g2Q0
    [Finite K] (hK : Nat.card K = 4) {l : K} (hl : l ≠ 0) {t : Kˣ} (ht : t ≠ 1)
    {Y : Subgroup (ModGL .G2 K)} (hYV : Y ≤ g2V K)
    (hN : torusElt .G2 K g2ir t ∈ normalizer (Y : Set (ModGL .G2 K))) (h8 : Nat.card Y = 8)
    (hinv : ∀ y ∈ Y, y * y = 1 → y = 1 ∨ y = g2N 0 0 0 0 0 l) : Y = g2Q0 K l := by
  have hσ0 : (t : K) ≠ 0 := t.ne_zero
  have hσ1 : (t : K) ≠ 1 := fun h => ht (Units.ext h)
  have hσ := sq_add_self_add_one_of_ne hK hσ0 hσ1
  have hσ3 := pow_three_eq_one_of_ne hK hσ0
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hc : ∀ G : K, g2N 0 0 0 0 0 G ∈ Y → G = 0 ∨ G = l := by
    intro G hG
    have hsq : g2N 0 0 0 0 0 G * g2N 0 0 0 0 0 G = 1 := by
      rw [g2N_uv_mul, ← g2N_zero]
      exact g2N_eq_g2N rfl rfl (by ring) (by ring) (by ring) (by char2_ring)
    rcases hinv _ hG hsq with h | h
    · rw [← g2N_zero] at h
      exact Or.inl (g2N_injective h).2.2.2.2.2
    · exact Or.inr (g2N_injective h).2.2.2.2.2
  refine Subgroup.eq_of_le_of_card_ge (fun y hy => ?_) (by rw [card_g2Q0 hK hl, h8])
  obtain ⟨C, D, F, rfl⟩ := hYV hy
  have hyy : g2N 0 0 C D 0 F * g2N 0 0 C D 0 F = g2N 0 0 0 0 0 (C * D) := by
    rw [g2N_uv_mul]
    exact g2N_eq_g2N rfl rfl (by char2_ring) (by char2_ring) (by ring) (by char2_ring)
  have hCD := hc (C * D) (hyy ▸ mul_mem hy hy)
  rcases hCD with hCD | hCD
  ·
    have h1 : g2N 0 0 C D 0 F * g2N 0 0 C D 0 F = 1 := by
      rw [hyy, hCD, g2N_zero]
    rcases hinv _ hy h1 with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact g2N_c_mem_g2Q0 l
  ·
    have hC : C ≠ 0 := by
      rintro rfl
      exact hl (by rw [← hCD]; ring)
    have hC3 := pow_three_eq_one_of_ne hK hC
    have hD : D = l * C ^ 2 := by linear_combination (norm := ring_nf) C ^ 2 * hCD - D * hC3
    have hy₁ := (mem_normalizer_iff.mp hN _).mp hy
    have hy₂ := (mem_normalizer_iff.mp hN _).mp hy₁
    rw [torus_r_conj_g2N_uv' hK] at hy₁
    rw [torus_r_conj_g2N_uv' hK, torus_r_conj_g2N_uv' hK] at hy₂
    have hw := mul_mem hy (inv_mem (mul_mem hy₁ hy₂))
    rw [g2N_uv_mul, g2N_uv_inv, g2N_uv_mul,
      show g2N 0 0 (C + ((t : K) ^ 2 * C + (t : K) ^ 2 * ((t : K) ^ 2 * C)))
        (D + ((t : K) * D + (t : K) * ((t : K) * D))) (0 + (0 + 0))
        (F + (F + F + (t : K) ^ 2 * ((t : K) ^ 2 * C) * ((t : K) * D) +
          ((t : K) ^ 2 * C + (t : K) ^ 2 * ((t : K) ^ 2 * C)) *
            ((t : K) * D + (t : K) * ((t : K) * D))) +
          ((t : K) ^ 2 * C + (t : K) ^ 2 * ((t : K) ^ 2 * C)) * D) =
        g2N 0 0 0 0 0 (F + (t : K) ^ 2 * l) from g2N_eq_g2N rfl rfl
        (by linear_combination (norm := char2_ring) C * hσ + C * (t : K) * hσ3)
        (by linear_combination (norm := char2_ring) D * hσ) (by ring) (by
          linear_combination (norm := char2_ring) (t : K) ^ 2 * hCD + C * D * (t : K) ^ 3 * hσ3)]
      at hw
    have hF : F = (t : K) ^ 2 * l ∨ F = (t : K) * l := by
      rcases hc _ hw with h | h
      · exact Or.inl (by linear_combination (norm := char2_ring) h)
      · exact Or.inr (by linear_combination (norm := char2_ring) h + l * hσ)
    refine ⟨C, F, pow_four_eq_self hK C, ?_, by rw [hD]⟩
    rcases hF with rfl | rfl
    · linear_combination (norm := char2_ring) l ^ 2 * hσ + l ^ 2 * hC3 + l ^ 2 * (t : K) * hσ3
    · linear_combination (norm := char2_ring) l ^ 2 * hσ + l ^ 2 * hC3

end CFSG.ComponentClassification.AS81.G2
