module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenShortCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Radical
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Core

public section

namespace CFSG.ComponentClassification.AS81.G2

open Subgroup CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open scoped Pointwise

variable {K : Type} [Field K] [CharP K 2]

local notation "X" => pinnedX Tag.G2 K

theorem g2BCGroup_le_borelGroup :
    g2BCGroup K ≤ borelGroup .G2 K := by
  rintro _ ⟨y, z, rfl⟩
  exact g2N_mem_borelGroup _ _ _ _ _ _

theorem eq_b_or_c_of_pinnedX_mem
    {γ : Fin Tag.G2.rank → ℤ} (hγ : IsRoot .G2 γ) (h : X γ 1 ∈ g2BCGroup K) :
    γ = g2b ∨ γ = g2c := by
  have hB := g2BCGroup_le_borelGroup h
  obtain ⟨y, z, hyz⟩ := h
  have h10 : (1 : K) ≠ 0 := one_ne_zero
  have hneg : ∀ {δ : Fin Tag.G2.rank → ℤ}, (δ = g2r ∨ δ = g2a ∨ δ = g2u ∨ δ = g2v ∨
      δ = g2b ∨ δ = g2c) → X (-δ) 1 ∈ borelGroup .G2 K → False := fun hδ hδB =>
    h10 (pinnedX_injective .G2 K _ ((eq_one_of_mem_borel_of_mem_neg hδB
      (pinnedX_neg_mem_negUnipotent hδ 1)).trans (pinnedX_zero .G2 K _).symm))
  rcases g2_root_cases hγ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  · rw [pinnedX_r_eq_g2N] at hyz
    exact absurd (g2N_injective hyz).1 h10
  · rw [pinnedX_a_eq_g2N] at hyz
    exact absurd (g2N_injective hyz).2.1 h10
  · rw [pinnedX_u_eq_g2N] at hyz
    exact absurd (g2N_injective hyz).2.2.1 h10
  · rw [pinnedX_v_eq_g2N] at hyz
    exact absurd (g2N_injective hyz).2.2.2.1 h10
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact (hneg (Or.inl rfl) hB).elim
  · exact (hneg (Or.inr (Or.inl rfl)) hB).elim
  · exact (hneg (Or.inr (Or.inr (Or.inl rfl))) hB).elim
  · exact (hneg (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hB).elim
  · exact (hneg (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hB).elim
  · exact (hneg (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) hB).elim

theorem weyl_eq_of_bc
    {w : WeylGroup .G2} (hb : w • g2b = g2b ∨ w • g2b = g2c)
    (hc : w • g2c = g2b ∨ w • g2c = g2c) : w = 1 ∨ w = simple .G2 g2ia := by
  rcases g2_weyl_cases w with ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ |
    ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ <;>
    rw [smul_g2b, ha, hr] at hb <;> rw [smul_g2c, ha, hr] at hc
  · exact Or.inl (eq_one_of_smul ha hr)
  · exact Or.inr (eq_simple_a_of_smul ha hr)
  all_goals exfalso; revert hb hc; decide

theorem mem_normalizer_of_conj {G : Type*} [Group G] {S : Subgroup G} {g : G}
    (h₁ : ∀ w ∈ S, g * w * g⁻¹ ∈ S) (h₂ : ∀ w ∈ S, g⁻¹ * w * g ∈ S) :
    g ∈ normalizer (S : Set G) := by
  rw [mem_normalizer_iff]
  intro w
  refine ⟨h₁ w, fun hw => ?_⟩
  have := h₂ _ hw
  rwa [show g⁻¹ * (g * w * g⁻¹) * g = w by group] at this

theorem pinnedX_b_mem_g2BCGroup
    (y : K) : X g2b y ∈ g2BCGroup K :=
  ⟨y, 0, pinnedX_b_eq_g2N y⟩

theorem pinnedX_c_mem_g2BCGroup
    (z : K) : X g2c z ∈ g2BCGroup K :=
  ⟨0, z, pinnedX_c_eq_g2N z⟩

theorem conj_mem_g2BCGroup_of_pos
    {γ : Fin Tag.G2.rank → ℤ}
    (hγ : γ = g2r ∨ γ = g2a ∨ γ = g2u ∨ γ = g2v ∨ γ = g2b ∨ γ = g2c) (s : K) {w : ModGL .G2 K}
    (hw : w ∈ g2BCGroup K) : X γ s * w * X γ s ∈ g2BCGroup K := by
  obtain ⟨y, z, rfl⟩ := hw
  rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [conj_r]
    exact ⟨_, _, g2N_eq_g2N rfl rfl (by ring) (by ring) (by ring) (by ring)⟩
  · rw [conj_a]
    exact ⟨_, _, g2N_eq_g2N rfl rfl (by ring) (by ring) (by ring) rfl⟩
  · rw [conj_u]
    exact ⟨_, _, g2N_eq_g2N rfl rfl rfl rfl (by ring) (by ring)⟩
  · rw [conj_v]
    exact ⟨_, _, g2N_eq_g2N rfl rfl rfl rfl (by ring) (by ring)⟩
  · rw [conj_b]
    exact ⟨_, _, g2N_eq_g2N rfl rfl rfl rfl rfl (by ring)⟩
  · rw [conj_c]
    exact ⟨_, _, rfl⟩

theorem pinnedX_mem_normalizer_g2BCGroup
    {γ : Fin Tag.G2.rank → ℤ}
    (hγ : γ = g2r ∨ γ = g2a ∨ γ = g2u ∨ γ = g2v ∨ γ = g2b ∨ γ = g2c) (s : K) :
    X γ s ∈ normalizer (g2BCGroup K : Set (ModGL .G2 K)) := by
  refine mem_normalizer_of_conj (fun w hw => ?_) (fun w hw => ?_)
  · rw [pinnedX_inv_eq]
    exact conj_mem_g2BCGroup_of_pos hγ s hw
  · rw [pinnedX_inv_eq]
    exact conj_mem_g2BCGroup_of_pos hγ s hw

theorem posUnipotent_le_normalizer_g2BCGroup :
    posUnipotent .G2 K ≤ normalizer (g2BCGroup K : Set (ModGL .G2 K)) := by
  intro u hu
  obtain ⟨A, B, C, D, E, F, rfl⟩ := exists_g2N_of_mem_posUnipotent hu
  have h := fun {γ : Fin Tag.G2.rank → ℤ}
    (hγ : γ = g2r ∨ γ = g2a ∨ γ = g2u ∨ γ = g2v ∨ γ = g2b ∨ γ = g2c) (s : K) =>
    pinnedX_mem_normalizer_g2BCGroup (K := K) hγ s
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (h (Or.inl rfl) A) (h (Or.inr (Or.inl rfl)) B))
    (h (Or.inr (Or.inr (Or.inl rfl))) C)) (h (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) D))
    (h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) E))
    (h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) F)

theorem torusGroup_le_normalizer_g2BCGroup :
    torusGroup .G2 K ≤ normalizer (g2BCGroup K : Set (ModGL .G2 K)) := by
  have key : ∀ h ∈ torusGroup .G2 K, ∀ w ∈ g2BCGroup K, h * w * h⁻¹ ∈ g2BCGroup K := by
    rintro h hh _ ⟨y, z, rfl⟩
    obtain ⟨cb, hcb⟩ := exists_torus_scale hh isRoot_g2b
    obtain ⟨cc, hcc⟩ := exists_torus_scale hh isRoot_g2c
    have e : g2N (0 : K) 0 0 0 y z = X g2b y * X g2c z := by
      simp only [g2N, pinnedX_zero, one_mul]
    rw [e, show h * (X g2b y * X g2c z) * h⁻¹ = (h * X g2b y * h⁻¹) * (h * X g2c z * h⁻¹) by
      group, hcb, hcc]
    exact mul_mem (pinnedX_b_mem_g2BCGroup _) (pinnedX_c_mem_g2BCGroup _)
  intro h hh
  refine mem_normalizer_of_conj (key h hh) (fun w hw => ?_)
  have := key h⁻¹ (inv_mem hh) w hw
  rwa [inv_inv] at this

theorem borelGroup_le_normalizer_g2BCGroup :
    borelGroup .G2 K ≤ normalizer (g2BCGroup K : Set (ModGL .G2 K)) := by
  intro b hb
  obtain ⟨h, hh, u, hu, rfl⟩ := exists_torus_mul_of_mem_borel hb
  exact mul_mem (torusGroup_le_normalizer_g2BCGroup hh) (posUnipotent_le_normalizer_g2BCGroup hu)

omit [CharP K 2] in
theorem g2TorusR_le_torusGroup :
    g2TorusR K ≤ torusGroup .G2 K := by
  rintro _ ⟨t, rfl⟩
  exact torusElt_mem_torusGroup g2ir t

theorem exists_mem_mul_of_mem_normalizer
    {g : ModGL .G2 K} (hg : g ∈ adjointGroup .G2 K)
    (hgN : g ∈ normalizer (g2BCGroup K : Set (ModGL .G2 K))) :
    ∃ q ∈ g2ShortParabolicRadical K, ∃ l ∈ g2RankOne K g2ia, ∃ h ∈ g2TorusR K,
      g = q * l * h := by
  obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl⟩ := exists_bruhat hg
  set n := canonicalRep (coxeterSystem .G2) K w with hn
  have hBN := borelGroup_le_normalizer_g2BCGroup (K := K)
  have hnN : n ∈ normalizer (g2BCGroup K : Set (ModGL .G2 K)) := by
    have e : n = b₁⁻¹ * (b₁ * n * b₂) * b₂⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (hBN hb₁)) hgN) (inv_mem (hBN hb₂))
  have hw : ∀ {γ : Fin Tag.G2.rank → ℤ}, IsRoot .G2 γ → X γ 1 ∈ g2BCGroup K →
      w • γ = g2b ∨ w • γ = g2c := fun {γ} hγ hX => by
    refine eq_b_or_c_of_pinnedX_mem (K := K) (IsRoot.smul hγ w) ?_
    rw [← canonicalRep_conj w hγ 1, ← hn]
    exact (mem_normalizer_iff.mp hnN _).mp hX
  have hnL : n ∈ g2RankOne K g2ia := by
    rcases weyl_eq_of_bc (hw isRoot_g2b (pinnedX_b_mem_g2BCGroup 1))
      (hw isRoot_g2c (pinnedX_c_mem_g2BCGroup 1)) with rfl | rfl
    · rw [hn, canonicalRep_one]
      exact one_mem _
    · rw [hn, canonicalRep_simple]
      exact weylElt_mem_g2RankOne g2ia 1
  obtain ⟨h₁, hh₁, u₁, hu₁, rfl⟩ := exists_torus_mul_of_mem_borel hb₁
  obtain ⟨h₂, hh₂, u₂, hu₂, rfl⟩ := exists_torus_mul_of_mem_borel hb₂
  obtain ⟨q₁, hq₁, s₁, rfl⟩ := exists_mul_pinnedX_a_of_mem_posUnipotent hu₁
  obtain ⟨s₂, q₂, hq₂, rfl⟩ := exists_pinnedX_a_mul_of_mem_posUnipotent hu₂
  obtain ⟨t₁, t₂, rfl⟩ := exists_eq_torusElt_mul hh₁
  obtain ⟨t₁', t₂', rfl⟩ := exists_eq_torusElt_mul hh₂
  set da := torusElt .G2 K g2ia t₁
  set dr := torusElt .G2 K g2ir t₂
  set da' := torusElt .G2 K g2ia t₁'
  set dr' := torusElt .G2 K g2ir t₂'
  have haL : ∀ s : K, X g2a s ∈ g2RankOne K g2ia := fun s => by
    rw [← xUnit_g2ia]
    exact xUnit_mem_g2RankOne g2ia s
  have hdrT : dr ∈ torusGroup .G2 K := torusElt_mem_torusGroup g2ir t₂
  have hdrrT : dr * dr' ∈ torusGroup .G2 K :=
    mul_mem hdrT (torusElt_mem_torusGroup g2ir t₂')
  have hdaL : da ∈ g2RankOne K g2ia := torusElt_mem_g2RankOne g2ia t₁
  have hda'L : da' ∈ g2RankOne K g2ia := torusElt_mem_g2RankOne g2ia t₁'
  set p₁ := da * (dr * q₁ * dr⁻¹) * da⁻¹ with hp₁
  have hp₁Q : p₁ ∈ g2ShortParabolicRadical K :=
    conj_mem_g2ShortParabolicRadical hdaL (torus_r_conj_mem_g2ShortParabolicRadical t₂ hq₁)
  set l := da * (dr * (X g2a s₁ * n * da') * dr⁻¹) *
    ((dr * dr') * X g2a s₂ * (dr * dr')⁻¹) with hl
  have hlL : l ∈ g2RankOne K g2ia :=
    mul_mem (mul_mem hdaL (torus_conj_mem_g2RankOne_a hdrT (mul_mem (mul_mem (haL s₁) hnL)
      hda'L))) (torus_conj_mem_g2RankOne_a hdrrT (haL s₂))
  have hdd : dr * dr' = torusElt .G2 K g2ir (t₂ * t₂') := (torusElt_mul g2ir t₂ t₂').symm
  set p₂ := (dr * dr') * q₂ * (dr * dr')⁻¹ with hp₂
  have hp₂Q : p₂ ∈ g2ShortParabolicRadical K := by
    rw [hp₂, hdd]
    exact torus_r_conj_mem_g2ShortParabolicRadical _ hq₂
  refine ⟨p₁ * (l * p₂ * l⁻¹), mul_mem hp₁Q (conj_mem_g2ShortParabolicRadical hlL hp₂Q), l, hlL,
    dr * dr', ⟨t₂ * t₂', hdd.symm⟩, ?_⟩
  rw [hp₁, hl, hp₂]
  group

omit [CharP K 2] in
theorem borelGroup_le_adjointGroup₀ :
    borelGroup .G2 K ≤ adjointGroup .G2 K :=
  ((triangular_borel_structure.{0, 0} .G2 K).2.2.2.2.2.2.2.2.2.2.2 K).1

theorem g2ShortParabolicRadical_le_adjointGroup :
    g2ShortParabolicRadical K ≤ adjointGroup .G2 K := by
  rintro _ ⟨A, C, D, E, F, rfl⟩
  exact borelGroup_le_adjointGroup₀ (g2N_mem_borelGroup _ _ _ _ _ _)

omit [CharP K 2] in
theorem g2TorusR_le_adjointGroup :
    g2TorusR K ≤ adjointGroup .G2 K :=
  (g2TorusR_le_torusGroup.trans le_sup_left).trans borelGroup_le_adjointGroup₀

theorem g2ShortParabolicRadical_le_centralizer :
    g2ShortParabolicRadical K ≤ centralizer (g2BCGroup K : Set (ModGL .G2 K)) := by
  rintro _ ⟨A, C, D, E, F, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨y, z, rfl⟩
  rw [mul_g2N, mul_g2N, g2N_mul_r, g2N_mul_a, g2N_mul_u, g2N_mul_v, g2N_mul_b, g2N_mul_c,
    g2N_mul_r, g2N_mul_a, g2N_mul_u, g2N_mul_v, g2N_mul_b, g2N_mul_c]
  exact g2N_eq_g2N (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)

theorem g2RankOne_a_le_normalizer :
    g2RankOne K g2ia ≤ normalizer (g2BCGroup K : Set (ModGL .G2 K)) := by
  have key : ∀ l ∈ g2RankOne K g2ia, ∀ w ∈ g2BCGroup K, l * w * l⁻¹ ∈ g2BCGroup K := by
    rintro l hl _ ⟨y, z, rfl⟩
    obtain ⟨T, hT⟩ := exists_actsOnShort hl
    have h := hT.2.2 ![y, z]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
    rw [h]
    exact ⟨_, _, rfl⟩
  intro l hl
  refine mem_normalizer_of_conj (key l hl) (fun w hw => ?_)
  have := key l⁻¹ (inv_mem hl) w hw
  rwa [inv_inv] at this

variable (K) in
@[expose] noncomputable def g2Para :
    Subgroup (ModGL .G2 K) :=
  g2ShortParabolicRadical K ⊔ g2RankOne K g2ia ⊔ g2TorusR K

theorem adjointGroup_inf_normalizer_eq :
    adjointGroup .G2 K ⊓ normalizer (g2BCGroup K : Set (ModGL .G2 K)) = g2Para K := by
  apply le_antisymm
  · rintro g ⟨hg, hgN⟩
    obtain ⟨q, hq, l, hl, h, hh, rfl⟩ := exists_mem_mul_of_mem_normalizer hg hgN
    exact mul_mem (mul_mem (mem_sup_left (mem_sup_left hq)) (mem_sup_left (mem_sup_right hl)))
      (mem_sup_right hh)
  · refine sup_le (sup_le (le_inf g2ShortParabolicRadical_le_adjointGroup
      (g2ShortParabolicRadical_le_centralizer.trans (centralizer_le_normalizer _)))
      (le_inf (g2RankOne_le_adjointGroup g2ia) g2RankOne_a_le_normalizer))
      (le_inf g2TorusR_le_adjointGroup
        (g2TorusR_le_torusGroup.trans torusGroup_le_normalizer_g2BCGroup))

theorem g2ShortParabolicRadical_isPGroup :
    IsPGroup 2 (g2ShortParabolicRadical K) := by
  rintro ⟨_, ⟨A, C, D, E, F, rfl⟩⟩
  refine ⟨2, Subtype.ext ?_⟩
  show g2N A 0 C D E F ^ 2 ^ 2 = 1
  have h2 : g2N A 0 C D E F ^ 2 = g2N 0 0 0 0 (A ^ 2 * C + A * D) (A * C ^ 2 + C * D) := by
    rw [sq, g2N_mul_self]
    exact g2N_eq_g2N rfl rfl (by ring) (by ring) (by ring) (by ring)
  rw [show (2 : ℕ) ^ 2 = 2 * 2 from rfl, pow_mul, h2, sq, g2N_zero_mul_g2N_zero, ← g2N_zero]
  exact g2N_eq_g2N (by ring) (by ring) (by ring) (by ring) (by char2_ring) (by char2_ring)

theorem g2Para_le_normalizer :
    g2Para K ≤ normalizer (g2ShortParabolicRadical K : Set (ModGL .G2 K)) := by
  have hL : g2RankOne K g2ia ≤ normalizer (g2ShortParabolicRadical K : Set (ModGL .G2 K)) :=
    fun l hl => mem_normalizer_of_conj (fun q hq => conj_mem_g2ShortParabolicRadical hl hq)
      (fun q hq => by
        have := conj_mem_g2ShortParabolicRadical (inv_mem hl) hq
        rwa [inv_inv] at this)
  have hH : g2TorusR K ≤ normalizer (g2ShortParabolicRadical K : Set (ModGL .G2 K)) := by
    rintro _ ⟨t, rfl⟩
    refine mem_normalizer_of_conj (fun q hq => torus_r_conj_mem_g2ShortParabolicRadical t hq)
      (fun q hq => ?_)
    have h := torus_r_conj_mem_g2ShortParabolicRadical t⁻¹ hq
    have e : torusElt .G2 K g2ir t⁻¹ = (torusEltHom .G2 K g2ir t)⁻¹ := by
      rw [← map_inv]
      rfl
    rwa [e, inv_inv] at h
  exact sup_le (sup_le le_normalizer hL) hH

theorem pow_three_eq_one_of_card {L : Type} [Field L] [Finite L] (hL : Nat.card L = 4)
    (t : Lˣ) : t ^ 3 = 1 := by
  have h : Nat.card Lˣ = 3 := by rw [Nat.card_units, hL]
  rw [← h]
  exact pow_card_eq_one'

omit [CharP K 2] in
theorem g2TorusR_le_centralizer_g2RankOne
    [Finite K] (hK : Nat.card K = 4) :
    g2TorusR K ≤ centralizer (g2RankOne K g2ia : Set (ModGL .G2 K)) := by
  rintro _ ⟨t, rfl⟩
  have ht : t ^ (3 : ℤ) = 1 := by exact_mod_cast pow_three_eq_one_of_card hK t
  have hc : ∀ x ∈ g2RankOne K g2ia,
      torusElt .G2 K g2ir t * x * (torusElt .G2 K g2ir t)⁻¹ = x := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with ⟨s, rfl⟩ | ⟨s, rfl⟩
      · rw [xUnit_g2ia, torus_r_conj t isRoot_g2a (-3) (by decide) s, zpow_neg, ht, inv_one,
          Units.val_one, one_mul]
      · rw [yUnit_g2ia, torus_r_conj t isRoot_g2na 3 (by decide) s, ht, Units.val_one, one_mul]
    | one => group
    | mul x y _ _ hx hy =>
      rw [show torusElt .G2 K g2ir t * (x * y) * (torusElt .G2 K g2ir t)⁻¹ =
        (torusElt .G2 K g2ir t * x * (torusElt .G2 K g2ir t)⁻¹) *
          (torusElt .G2 K g2ir t * y * (torusElt .G2 K g2ir t)⁻¹) by group, hx, hy]
    | inv x _ hx =>
      rw [show torusElt .G2 K g2ir t * x⁻¹ * (torusElt .G2 K g2ir t)⁻¹ =
        (torusElt .G2 K g2ir t * x * (torusElt .G2 K g2ir t)⁻¹)⁻¹ by group, hx]
  rw [mem_centralizer_iff]
  intro x hx
  show x * torusElt .G2 K g2ir t = torusElt .G2 K g2ir t * x
  have := hc x hx
  calc x * torusElt .G2 K g2ir t = torusElt .G2 K g2ir t * x * (torusElt .G2 K g2ir t)⁻¹ *
        torusElt .G2 K g2ir t := by rw [this]
    _ = torusElt .G2 K g2ir t * x := by group

theorem g2TorusR_le_centralizer_g2BCGroup
    [Finite K] (hK : Nat.card K = 4) :
    g2TorusR K ≤ centralizer (g2BCGroup K : Set (ModGL .G2 K)) := by
  rintro _ ⟨t, rfl⟩
  have ht : t ^ (3 : ℤ) = 1 := by exact_mod_cast pow_three_eq_one_of_card hK t
  rw [mem_centralizer_iff]
  rintro _ ⟨y, z, rfl⟩
  show g2N 0 0 0 0 y z * torusElt .G2 K g2ir t = torusElt .G2 K g2ir t * g2N 0 0 0 0 y z
  have e : g2N (0 : K) 0 0 0 y z = X g2b y * X g2c z := by
    simp only [g2N, pinnedX_zero, one_mul]
  have h1 : torusElt .G2 K g2ir t * (X g2b y * X g2c z) * (torusElt .G2 K g2ir t)⁻¹ =
      X g2b y * X g2c z := by
    rw [show torusElt .G2 K g2ir t * (X g2b y * X g2c z) * (torusElt .G2 K g2ir t)⁻¹ =
      (torusElt .G2 K g2ir t * X g2b y * (torusElt .G2 K g2ir t)⁻¹) *
        (torusElt .G2 K g2ir t * X g2c z * (torusElt .G2 K g2ir t)⁻¹) by group,
      torus_r_conj t isRoot_g2b 3 (by decide) y, torus_r_conj t isRoot_g2c 0 (by decide) z, ht,
      zpow_zero, Units.val_one, one_mul, one_mul]
  rw [e]
  calc X g2b y * X g2c z * torusElt .G2 K g2ir t = torusElt .G2 K g2ir t *
        (X g2b y * X g2c z) * (torusElt .G2 K g2ir t)⁻¹ * torusElt .G2 K g2ir t := by rw [h1]
    _ = _ := by group

theorem eq_one_of_mem_g2RankOne_of_centralizes
    [Finite K] {l : ModGL .G2 K} (hl : l ∈ g2RankOne K g2ia)
    (hc : l ∈ centralizer (g2BCGroup K : Set (ModGL .G2 K))) : l = 1 := by
  have hspec := shAction_spec ⟨l, hl⟩
  have hid : ActsOnShort l LinearMap.id := by
    refine ⟨hspec.1, hspec.2.1, fun y => ?_⟩
    have h := mem_centralizer_iff.mp hc _ ⟨y 0, y 1, rfl⟩
    rw [LinearMap.id_apply, ← h, mul_inv_cancel_right]
  have h1 : shActionHom ⟨l, hl⟩ = 1 := Units.ext (hspec.unique hid)
  have h2 := shActionHom_injective (h1.trans (map_one _).symm)
  exact congrArg Subtype.val h2

theorem not_isPGroup_of_isPerfect {H : Type*} [Group H] [Finite H] [Nontrivial H] {p : ℕ}
    [Fact p.Prime] (hperf : Group.IsPerfect H) : ¬ IsPGroup p H := by
  intro hp
  have : Group.IsNilpotent H := hp.isNilpotent
  obtain ⟨n, hn⟩ := (inferInstance : Group.IsSolvable H).solvable
  have htop : ∀ k, derivedSeries H k = ⊤ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [derivedSeries_succ, ih, ← _root_.commutator_def, (Group.isPerfect_def).1 hperf]
  rw [htop] at hn
  exact (top_ne_bot (α := Subgroup H)) hn

theorem mem_of_pow_eq_one_of_mem_sup {G : Type*} [Group G] [Finite G] {D H : Subgroup G}
    (hHD : H ≤ normalizer (D : Set G)) {w : G} (hw : w ∈ D ⊔ H) {n m : ℕ} (hn : w ^ n = 1)
    (hm : ∀ h ∈ H, h ^ m = 1) (hcop : n.Coprime m) : w ∈ D := by
  have hw' : w ∈ (D : Set G) * (H : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left D H hHD]
    exact hw
  obtain ⟨d, hd, h, hh, rfl⟩ := hw'
  have key : ∀ k : ℕ, (d * h) ^ k * (h ^ k)⁻¹ ∈ D := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : (d * h) ^ (k + 1) * (h ^ (k + 1))⁻¹ =
          ((d * h) ^ k * (h ^ k)⁻¹) * (h ^ k * d * (h ^ k)⁻¹) := by
        rw [pow_succ, pow_succ]
        group
      rw [e]
      refine D.mul_mem ih ?_
      exact (mem_normalizer_iff.mp (pow_mem (hHD hh) k) d).mp hd
  have h1 := key n
  rw [hn, one_mul] at h1
  have hhn : h ^ n ∈ D := by simpa using D.inv_mem h1
  have hcop' : (orderOf h).Coprime n :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one (hm h hh)) hcop.symm
  have hz : zpowers (h ^ n) = zpowers h := by
    refine eq_of_le_of_card_ge (zpowers_le.mpr (pow_mem (mem_zpowers h) _)) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hcop'.orderOf_pow]
  have hhD : h ∈ D := zpowers_le.mpr hhn (hz ▸ mem_zpowers h)
  exact D.mul_mem hd hhD

theorem le_of_isPGroup_of_isSimpleGroup {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {P N L W : Subgroup G} (hNP : N ≤ P) (hPN : P ≤ normalizer (N : Set G))
    (hLP : L ≤ P) (hsup : N ⊔ L = P) (hinf : N ⊓ L = ⊥) [IsSimpleGroup ↥L]
    (hL : ¬ IsPGroup p ↥L) (hWP : W ≤ P) (hPW : P ≤ normalizer (W : Set G))
    (hW : IsPGroup p W) : W ≤ N := by
  set N' := N.subgroupOf P with hN'
  have hN'n : N'.Normal := (normal_subgroupOf_iff_le_normalizer hNP).mpr hPN
  set π := QuotientGroup.mk' N'
  set L' := L.subgroupOf P
  have hLL : L' ≃* ↥L := subgroupOfEquivOfLe hLP
  have hπinj : Function.Injective (π.comp L'.subtype) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨l, hl⟩ h1
    have h2 : (l : ↥P) ∈ N' := by
      rw [← QuotientGroup.ker_mk' N']
      exact h1
    have h3 : (l : G) ∈ N ⊓ L := ⟨h2, hl⟩
    rw [hinf, mem_bot] at h3
    exact Subtype.ext (Subtype.ext h3)
  have hπsurj : Function.Surjective (π.comp L'.subtype) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N' y
    have hg : (g : G) ∈ (N : Set G) * (L : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left N L (hLP.trans hPN), hsup]
      exact g.2
    obtain ⟨n, hn, l, hl, hnl⟩ := hg
    refine ⟨⟨⟨l, hLP hl⟩, hl⟩, ?_⟩
    show π ⟨l, hLP hl⟩ = π g
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    show (⟨l, hLP hl⟩ : ↥P)⁻¹ * g ∈ N'
    rw [mem_subgroupOf]
    have e : ((⟨l, hLP hl⟩ : ↥P)⁻¹ * g : ↥P).val = l⁻¹ * n * l := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, ← hnl]
      group
    rw [e]
    have := (mem_normalizer_iff.mp (hPN (hLP (inv_mem hl))) n).mp hn
    rwa [inv_inv] at this
  let e : ↥L' ≃* (↥P ⧸ N') := MulEquiv.ofBijective (π.comp L'.subtype) ⟨hπinj, hπsurj⟩
  have hsimple : IsSimpleGroup (↥P ⧸ N') := (hLL.symm.trans e).symm.isSimpleGroup
  set W' := W.subgroupOf P
  have hW'n : W'.Normal := (normal_subgroupOf_iff_le_normalizer hWP).mpr hPW
  have hW' : IsPGroup p W' := hW.comap_subtype
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N'
  have himn : (W'.map π).Normal := hW'n.map π hπs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (W'.map π) with hbot | htop
  · intro w hw
    have h1 : (⟨w, hWP hw⟩ : ↥P) ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      have h2 : π ⟨w, hWP hw⟩ ∈ W'.map π := ⟨_, hw, rfl⟩
      rw [hbot, mem_bot] at h2
      exact h2
    rw [QuotientGroup.ker_mk'] at h1
    exact h1
  · exfalso
    apply hL
    have hq : IsPGroup p (↥P ⧸ N') := by
      intro y
      have hy : y ∈ W'.map π := by rw [htop]; exact mem_top y
      obtain ⟨w, hw, rfl⟩ := hy
      obtain ⟨k, hk⟩ := hW' ⟨w, hw⟩
      exact ⟨k, by rw [← map_pow]; exact (congrArg (fun t : ↥W' => π t) hk).trans (map_one π)⟩
    exact hq.of_equiv (hLL.symm.trans e).symm

theorem mem_normalizer_centralizer_of_mem_normalizer {G : Type*} [Group G] {S : Subgroup G}
    {g : G} (hg : g ∈ normalizer (S : Set G)) :
    g ∈ normalizer (centralizer (S : Set G) : Set G) := by
  have key : ∀ g ∈ normalizer (S : Set G), ∀ c ∈ centralizer (S : Set G),
      g * c * g⁻¹ ∈ centralizer (S : Set G) := by
    intro g hg c hc
    rw [mem_centralizer_iff]
    intro s hs
    have hs' : g⁻¹ * s * g ∈ S := by
      have := (mem_normalizer_iff.mp (inv_mem hg) s).mp hs
      rwa [inv_inv] at this
    have h1 := mem_centralizer_iff.mp hc _ hs'
    calc s * (g * c * g⁻¹) = g * ((g⁻¹ * s * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * s * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * s := by group
  refine mem_normalizer_of_conj (key g hg) (fun c hc => ?_)
  have := key g⁻¹ (inv_mem hg) c hc
  rwa [inv_inv] at this

theorem g2Para_le_normalizer_g2BCGroup :
    g2Para K ≤ normalizer (g2BCGroup K : Set (ModGL .G2 K)) := by
  rw [← adjointGroup_inf_normalizer_eq]
  exact inf_le_right

theorem g2Para_inf_centralizer_le
    [Finite K] (hK : Nat.card K = 4) :
    g2Para K ⊓ centralizer (g2BCGroup K : Set (ModGL .G2 K)) ≤
      g2ShortParabolicRadical K ⊔ g2TorusR K := by
  rintro g ⟨hgP, hgC⟩
  rw [← adjointGroup_inf_normalizer_eq] at hgP
  obtain ⟨q, hq, l, hl, h, hh, rfl⟩ := exists_mem_mul_of_mem_normalizer hgP.1 hgP.2
  have hqC := g2ShortParabolicRadical_le_centralizer hq
  have hhC := g2TorusR_le_centralizer_g2BCGroup hK hh
  have hlC : l ∈ centralizer (g2BCGroup K : Set (ModGL .G2 K)) := by
    have e : l = q⁻¹ * (q * l * h) * h⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hqC) hgC) (inv_mem hhC)
  rw [eq_one_of_mem_g2RankOne_of_centralizes hl hlC, mul_one]
  exact mul_mem (mem_sup_left hq) (mem_sup_right hh)

theorem pCoreOf_g2Para
    [Finite K] (hK : Nat.card K = 4) :
    pCoreOf 2 (g2Para K) = g2ShortParabolicRadical K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD₀P : g2ShortParabolicRadical K ≤ g2Para K := le_sup_left.trans le_sup_left
  have hLP : g2RankOne K g2ia ≤ g2Para K := le_sup_right.trans le_sup_left
  have hHP : g2TorusR K ≤ g2Para K := le_sup_right
  refine le_antisymm ?_ (LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hD₀P
    g2Para_le_normalizer g2ShortParabolicRadical_isPGroup)
  set P := g2Para K
  set N := P ⊓ centralizer (g2BCGroup K : Set (ModGL .G2 K)) with hN
  obtain ⟨hperf, hsimple, hnt⟩ := g2RankOne_isPerfect_isSimpleGroup (K := K) (by omega)
  have hPN : P ≤ normalizer (N : Set (ModGL .G2 K)) := by
    intro g hg
    have h1 : g ∈ normalizer (P : Set (ModGL .G2 K)) := le_normalizer hg
    have h2 := mem_normalizer_centralizer_of_mem_normalizer (g2Para_le_normalizer_g2BCGroup hg)
    refine mem_normalizer_of_conj (fun c hc => ⟨?_, ?_⟩) (fun c hc => ⟨?_, ?_⟩)
    · exact (mem_normalizer_iff.mp h1 c).mp hc.1
    · exact (mem_normalizer_iff.mp h2 c).mp hc.2
    · have := (mem_normalizer_iff.mp (inv_mem h1) c).mp hc.1
      rwa [inv_inv] at this
    · have := (mem_normalizer_iff.mp (inv_mem h2) c).mp hc.2
      rwa [inv_inv] at this
  have hsup : N ⊔ g2RankOne K g2ia = P := by
    refine le_antisymm (sup_le inf_le_left hLP) (sup_le (sup_le ?_ le_sup_right) ?_)
    · exact le_sup_of_le_left (le_inf hD₀P g2ShortParabolicRadical_le_centralizer)
    · exact le_sup_of_le_left (le_inf hHP (g2TorusR_le_centralizer_g2BCGroup hK))
  have hinf : N ⊓ g2RankOne K g2ia = ⊥ := by
    rw [eq_bot_iff]
    rintro l ⟨⟨-, hlC⟩, hl⟩
    exact eq_one_of_mem_g2RankOne_of_centralizes hl hlC
  have hL : ¬ IsPGroup 2 ↥(g2RankOne K g2ia) := not_isPGroup_of_isPerfect hperf
  have h1 : pCoreOf 2 P ≤ N := le_of_isPGroup_of_isSimpleGroup inf_le_left hPN hLP hsup hinf hL
    (LieType.BorelTits.pCoreOf_le 2 P) (LieType.BorelTits.le_normalizer_pCoreOf 2 P)
    (LieType.BorelTits.pCoreOf_isPGroup 2 P)
  intro w hw
  obtain ⟨k, hk⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 P ⟨w, hw⟩
  have hk' : w ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hH3 : ∀ h ∈ g2TorusR K, h ^ 3 = 1 := by
    rintro _ ⟨t, rfl⟩
    rw [← map_pow, pow_three_eq_one_of_card hK t, map_one]
  exact mem_of_pow_eq_one_of_mem_sup (hHP.trans g2Para_le_normalizer)
    (g2Para_inf_centralizer_le hK (h1 hw)) hk' hH3 (Nat.Coprime.pow_left k (by decide))

omit [CharP K 2] in
theorem g2N_eq_mul_g2BC
    (A C D E F : K) : g2N A 0 C D E F = g2N A 0 C D 0 0 * g2N 0 0 0 0 E F := by
  simp only [g2N, pinnedX_zero, mul_one, one_mul, mul_assoc]

theorem g2BCGroup_le_g2ShortParabolicRadical :
    g2BCGroup K ≤ g2ShortParabolicRadical K := by
  rintro _ ⟨y, z, rfl⟩
  exact g2N_mem_g2ShortParabolicRadical 0 0 0 y z

theorem mul_inv_mem_g2BCGroup
    (A C D E F E' F' : K) :
    g2N A 0 C D E F * (g2N A 0 C D E' F')⁻¹ ∈ g2BCGroup K := by
  rw [g2N_eq_mul_g2BC A C D E F, g2N_eq_mul_g2BC A C D E' F']
  have hz : g2N (0 : K) 0 0 0 E F * (g2N (0 : K) 0 0 0 E' F')⁻¹ ∈ g2BCGroup K :=
    mul_mem ⟨E, F, rfl⟩ (inv_mem ⟨E', F', rfl⟩)
  have hp := g2ShortParabolicRadical_le_centralizer (K := K)
    (g2N_mem_g2ShortParabolicRadical A C D 0 0)
  rw [show g2N A 0 C D 0 0 * g2N 0 0 0 0 E F * (g2N A 0 C D 0 0 * g2N 0 0 0 0 E' F')⁻¹ =
    g2N A 0 C D 0 0 * (g2N 0 0 0 0 E F * (g2N 0 0 0 0 E' F')⁻¹) * (g2N A 0 C D 0 0)⁻¹ by
    group, (mem_centralizer_iff.mp hp _ hz).symm, mul_inv_cancel_right]
  exact hz

theorem centerIn_g2ShortParabolicRadical :
    centerIn (g2ShortParabolicRadical K) = g2BCGroup K := by
  apply le_antisymm
  · rintro _ ⟨⟨A, C, D, E, F, rfl⟩, hc⟩
    have hv := mem_centralizer_iff.mp hc (X g2v 1) (by
      rw [pinnedX_v_eq_g2N]; exact g2N_mem_g2ShortParabolicRadical 0 0 1 0 0)
    have hu := mem_centralizer_iff.mp hc (X g2u 1) (by
      rw [pinnedX_u_eq_g2N]; exact g2N_mem_g2ShortParabolicRadical 0 1 0 0 0)
    have hv' : X g2v 1 * g2N A 0 C D E F * X g2v 1 = g2N A 0 C D E F := by
      rw [hv, mul_assoc, pinnedX_mul_self, mul_one]
    rw [conj_v] at hv'
    obtain ⟨-, -, -, -, h1, h2⟩ := g2N_injective hv'
    have hA : A = 0 := by linear_combination h1
    have hC : C = 0 := by linear_combination h2
    subst hA hC
    have hu' : X g2u 1 * g2N 0 0 0 D E F * X g2u 1 = g2N 0 0 0 D E F := by
      rw [hu, mul_assoc, pinnedX_mul_self, mul_one]
    rw [conj_u] at hu'
    obtain ⟨-, -, -, -, -, h3⟩ := g2N_injective hu'
    have hD : D = 0 := by linear_combination h3
    subst hD
    exact ⟨E, F, rfl⟩
  · intro z hz
    refine ⟨g2BCGroup_le_g2ShortParabolicRadical hz, mem_centralizer_iff.mpr fun q hq => ?_⟩
    exact (mem_centralizer_iff.mp (g2ShortParabolicRadical_le_centralizer hq) z hz).symm

theorem g2ShortParabolicRadical_elem
    {d d' : ModGL .G2 K} (hd : d ∈ g2ShortParabolicRadical K)
    (hd' : d' ∈ g2ShortParabolicRadical K) :
    d * d ∈ g2BCGroup K ∧ d * d' * d⁻¹ * d'⁻¹ ∈ g2BCGroup K := by
  obtain ⟨A, C, D, E, F, rfl⟩ := hd
  obtain ⟨A', C', D', E', F', rfl⟩ := hd'
  refine ⟨?_, ?_⟩
  · rw [g2N_mul_self]
    exact ⟨_, _, g2N_eq_g2N rfl rfl (by ring) (by ring) rfl rfl⟩
  · have e1 : g2N A 0 C D E F * g2N A' 0 C' D' E' F' =
        g2N (A + A') 0 (C + C') (D + D') (E + C * A' ^ 2 + D * A' + E')
          (F + C ^ 2 * A' + C' * D + F') := by
      rw [mul_g2N, g2N_mul_r, g2N_mul_a, g2N_mul_u, g2N_mul_v, g2N_mul_b, g2N_mul_c]
      exact g2N_eq_g2N rfl (by ring) (by ring) (by ring) (by ring) (by ring)
    have e2 : g2N A' 0 C' D' E' F' * g2N A 0 C D E F =
        g2N (A + A') 0 (C + C') (D + D') (E' + C' * A ^ 2 + D' * A + E)
          (F' + C' ^ 2 * A + C * D' + F) := by
      rw [mul_g2N, g2N_mul_r, g2N_mul_a, g2N_mul_u, g2N_mul_v, g2N_mul_b, g2N_mul_c]
      exact g2N_eq_g2N (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)
    rw [show g2N A 0 C D E F * g2N A' 0 C' D' E' F' * (g2N A 0 C D E F)⁻¹ *
        (g2N A' 0 C' D' E' F')⁻¹ = (g2N A 0 C D E F * g2N A' 0 C' D' E' F') *
          (g2N A' 0 C' D' E' F' * g2N A 0 C D E F)⁻¹ by group, e1, e2]
    exact mul_inv_mem_g2BCGroup _ _ _ _ _ _ _

theorem card_g2ShortParabolicRadical
    [Finite K] : Nat.card (g2ShortParabolicRadical K) = Nat.card K ^ 5 := by
  have e : Nat.card (K × K × K × K × K) = Nat.card K ^ 5 := by
    simp only [Nat.card_prod]
    ring
  rw [← e]
  refine (Nat.card_eq_of_bijective (fun p : K × K × K × K × K =>
    (⟨g2N p.1 0 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2,
      g2N_mem_g2ShortParabolicRadical _ _ _ _ _⟩ : g2ShortParabolicRadical K))
    ⟨fun p p' h => ?_, fun g => ?_⟩).symm
  · simp only at h
    obtain ⟨h1, -, h3, h4, h5, h6⟩ := g2N_injective (Subtype.mk.inj h)
    exact Prod.ext h1 (Prod.ext h3 (Prod.ext h4 (Prod.ext h5 h6)))
  · obtain ⟨A, C, D, E, F, hg⟩ := g.2
    exact ⟨(A, C, D, E, F), Subtype.ext hg.symm⟩

theorem relIndex_g2BCGroup
    [Finite K] : (g2BCGroup K).relIndex (g2ShortParabolicRadical K) = Nat.card K ^ 3 := by
  have h := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup (ModGL .G2 K)) (g2BCGroup K)
    (g2ShortParabolicRadical K) bot_le g2BCGroup_le_g2ShortParabolicRadical
  rw [relIndex_bot_left, relIndex_bot_left, card_g2BCGroup, card_g2ShortParabolicRadical] at h
  have hK : 0 < Nat.card K := Nat.card_pos
  have : Nat.card K ^ 5 = (Nat.card K * Nat.card K) * Nat.card K ^ 3 := by ring
  rw [this] at h
  exact Nat.eq_of_mul_eq_mul_left (by positivity) h

theorem coord_eq_of_mul_inv_mem
    {A C D E F A' C' D' E' F' : K}
    (h : g2N A 0 C D E F * (g2N A' 0 C' D' E' F')⁻¹ ∈ g2BCGroup K) :
    A = A' ∧ C = C' ∧ D = D' := by
  obtain ⟨y, z, hyz⟩ := h
  have e1 : g2N A 0 C D E F = g2N 0 0 0 0 y z * g2N A' 0 C' D' E' F' := by
    rw [← hyz, inv_mul_cancel_right]
  have e2 : g2N 0 0 0 0 y z * g2N A' 0 C' D' E' F' = g2N A' 0 C' D' E' F' * g2N 0 0 0 0 y z :=
    mem_centralizer_iff.mp (g2ShortParabolicRadical_le_centralizer
      (g2N_mem_g2ShortParabolicRadical A' C' D' E' F')) _ ⟨y, z, rfl⟩
  have e3 : g2N A' 0 C' D' E' F' * g2N 0 0 0 0 y z = g2N A' 0 C' D' (E' + y) (F' + z) := by
    rw [mul_g2N, g2N_mul_r, g2N_mul_a, g2N_mul_u, g2N_mul_v, g2N_mul_b, g2N_mul_c]
    exact g2N_eq_g2N (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)
  obtain ⟨h1, -, h3, h4, -, -⟩ := g2N_injective (e1.trans (e2.trans e3))
  exact ⟨h1, h3, h4⟩

theorem center_eq_bot_of_isPerfect {H : Type*} [Group H] [IsSimpleGroup H]
    (hperf : Group.IsPerfect H) : center H = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center H) with h | h
  · exact h
  · exfalso
    have hc : commutator H = ⊥ := by
      rw [_root_.commutator_def, commutator_eq_bot_iff_le_centralizer]
      intro a _
      rw [mem_centralizer_iff]
      intro b _
      have : b ∈ center H := by rw [h]; exact mem_top b
      exact (mem_center_iff.mp this a).symm
    rw [(Group.isPerfect_def).1 hperf] at hc
    exact (top_ne_bot (α := Subgroup H)) hc

theorem center_mod_g2BCGroup
    [Finite K] (hK : Nat.card K = 4) {d : ModGL .G2 K}
    (hd : d ∈ g2ShortParabolicRadical K ⊔ g2RankOne K g2ia) :
    (∀ j ∈ g2ShortParabolicRadical K ⊔ g2RankOne K g2ia, d * j * d⁻¹ * j⁻¹ ∈ g2BCGroup K) ↔
      d ∈ rootSubgroup .G2 K g2v ⊔ g2BCGroup K := by
  have hLD : g2RankOne K g2ia ≤ normalizer (g2ShortParabolicRadical K : Set (ModGL .G2 K)) :=
    (le_sup_right.trans le_sup_left).trans g2Para_le_normalizer
  have hDL : ∀ {q l : ModGL .G2 K}, q ∈ g2ShortParabolicRadical K → l ∈ g2RankOne K g2ia →
      q = l → l = 1 := fun {q l} hq hl hql =>
    eq_one_of_mem_g2RankOne_of_centralizes hl (hql ▸ g2ShortParabolicRadical_le_centralizer hq)
  have hmul : ∀ {g : ModGL .G2 K}, g ∈ g2ShortParabolicRadical K ⊔ g2RankOne K g2ia →
      ∃ q ∈ g2ShortParabolicRadical K, ∃ l ∈ g2RankOne K g2ia, g = q * l := fun {g} hg => by
    have hg' : g ∈ (g2ShortParabolicRadical K : Set (ModGL .G2 K)) *
        (g2RankOne K g2ia : Set (ModGL .G2 K)) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ hLD]
      exact hg
    obtain ⟨q, hq, l, hl, rfl⟩ := hg'
    exact ⟨q, hq, l, hl, rfl⟩
  have hvZ : ∀ {s : K}, X g2v s ∈ g2ShortParabolicRadical K := fun {s} => by
    rw [pinnedX_v_eq_g2N]
    exact g2N_mem_g2ShortParabolicRadical 0 0 s 0 0
  constructor
  · intro hc
    obtain ⟨q, hq, l, hl, rfl⟩ := hmul hd
    obtain ⟨hperf, hsimple, -⟩ := g2RankOne_isPerfect_isSimpleGroup (K := K) (by omega)
    have hl1 : l = 1 := by
      have hcen : (⟨l, hl⟩ : ↥(g2RankOne K g2ia)) ∈ center ↥(g2RankOne K g2ia) := by
        rw [mem_center_iff]
        rintro ⟨j, hj⟩
        apply Subtype.ext
        show j * l = l * j
        have h1 := hc j (mem_sup_right hj)
        set c := l * j * l⁻¹
        have hcL : c ∈ g2RankOne K g2ia := mul_mem (mul_mem hl hj) (inv_mem hl)
        have hq' : c * q⁻¹ * c⁻¹ ∈ g2ShortParabolicRadical K :=
          (mem_normalizer_iff.mp (hLD hcL) _).mp (inv_mem hq)
        have h2 : l * j * l⁻¹ * j⁻¹ ∈ g2ShortParabolicRadical K := by
          have e : l * j * l⁻¹ * j⁻¹ = (q * (c * q⁻¹ * c⁻¹))⁻¹ * (q * l * j * (q * l)⁻¹ * j⁻¹) := by
            simp only [c]
            group
          rw [e]
          exact mul_mem (inv_mem (mul_mem hq hq')) (g2BCGroup_le_g2ShortParabolicRadical h1)
        have h3 := hDL h2 (mul_mem (mul_mem (mul_mem hl hj) (inv_mem hl)) (inv_mem hj)) rfl
        calc j * l = (l * j * l⁻¹ * j⁻¹)⁻¹ * (l * j) := by group
          _ = l * j := by rw [h3, inv_one, one_mul]
      rw [center_eq_bot_of_isPerfect hperf, mem_bot] at hcen
      exact congrArg Subtype.val hcen
    subst hl1
    rw [mul_one] at hc ⊢
    obtain ⟨A, C, D, E, F, rfl⟩ := hq
    have haL : X g2a 1 ∈ g2RankOne K g2ia := by
      rw [← xUnit_g2ia]
      exact xUnit_mem_g2RankOne g2ia 1
    have h1 := hc _ (mem_sup_right haL)
    rw [pinnedX_inv_eq, show g2N A 0 C D E F * X g2a 1 * (g2N A 0 C D E F)⁻¹ * X g2a 1 =
      g2N A 0 C D E F * (X g2a 1 * g2N A 0 C D E F * X g2a 1)⁻¹ by
        rw [mul_inv_rev, mul_inv_rev, pinnedX_inv_eq]; group, conj_a] at h1
    obtain ⟨-, hC, -⟩ := coord_eq_of_mul_inv_mem h1
    have hA : A = 0 := by linear_combination -hC
    subst hA
    have hnL : weylElt .G2 K g2ia 1 ∈ g2RankOne K g2ia := weylElt_mem_g2RankOne g2ia 1
    have h2 := hc _ (mem_sup_right hnL)
    rw [show g2N 0 0 C D E F * weylElt .G2 K g2ia 1 * (g2N 0 0 C D E F)⁻¹ *
        (weylElt .G2 K g2ia 1)⁻¹ = g2N 0 0 C D E F * (weylElt .G2 K g2ia 1 *
          g2N 0 0 C D E F * (weylElt .G2 K g2ia 1)⁻¹)⁻¹ by group, weylElt_a_conj_g2N] at h2
    obtain ⟨hC0, -, -⟩ := coord_eq_of_mul_inv_mem h2
    subst hC0
    rw [g2N_eq_mul_g2BC]
    refine mul_mem (mem_sup_left ?_) (mem_sup_right ⟨E, F, rfl⟩)
    exact mem_rootSubgroup.mpr ⟨D, by simp only [g2N, pinnedX_zero, one_mul, mul_one]⟩
  · intro hdv j hj
    have hdA : d ∈ g2ShortRadical K := by
      have h1 : rootSubgroup .G2 K g2v ≤ g2ShortRadical K := by
        intro g hg
        obtain ⟨s, rfl⟩ := mem_rootSubgroup.mp hg
        exact pinnedX_v_mem_g2ShortRadical s
      have h2 : g2BCGroup K ≤ g2ShortRadical K := by
        rintro _ ⟨y, z, rfl⟩
        exact g2N_mem_g2ShortRadical 0 y z
      exact (sup_le h1 h2) hdv
    obtain ⟨D, E, F, rfl⟩ := hdA
    obtain ⟨q, hq, l, hl, rfl⟩ := hmul hj
    have hdD := g2N_mem_g2ShortParabolicRadical (K := K) 0 0 D E F
    have hqC := g2ShortParabolicRadical_le_centralizer hq
    have hz : g2N (0 : K) 0 0 0 E F ∈ g2BCGroup K := ⟨E, F, rfl⟩
    have hvC := g2ShortParabolicRadical_le_centralizer (K := K) (hvZ (s := D))
    have hlz : l * (g2N 0 0 0 0 E F)⁻¹ * l⁻¹ ∈ g2BCGroup K :=
      (mem_normalizer_iff.mp (g2RankOne_a_le_normalizer hl) _).mp (inv_mem hz)
    have h1 : g2N 0 0 0 D E F * l * (g2N 0 0 0 D E F)⁻¹ * l⁻¹ ∈ g2BCGroup K := by
      have e : g2N (0 : K) 0 0 D E F = X g2v D * g2N 0 0 0 0 E F := by
        simp only [g2N, pinnedX_zero, one_mul, mul_assoc]
      have hcomm := (commute_of_mem_g2RankOne_a hl D).eq
      have hcomm' : (X g2v D)⁻¹ * l⁻¹ = l⁻¹ * (X g2v D)⁻¹ := by
        rw [← mul_inv_rev, ← mul_inv_rev, hcomm]
      have e' : X g2v D * g2N 0 0 0 0 E F * l * (X g2v D * g2N 0 0 0 0 E F)⁻¹ * l⁻¹ =
          X g2v D * (g2N 0 0 0 0 E F * (l * (g2N 0 0 0 0 E F)⁻¹ * l⁻¹)) * (X g2v D)⁻¹ := by
        have : X g2v D * g2N 0 0 0 0 E F * l * (X g2v D * g2N 0 0 0 0 E F)⁻¹ * l⁻¹ =
            X g2v D * g2N 0 0 0 0 E F * l * (g2N 0 0 0 0 E F)⁻¹ * ((X g2v D)⁻¹ * l⁻¹) := by
          group
        rw [this, hcomm']
        group
      have hw := mul_mem hz hlz
      rw [e, e', ← mem_centralizer_iff.mp hvC _ hw, mul_inv_cancel_right]
      exact hw
    have e : g2N 0 0 0 D E F * (q * l) * (g2N 0 0 0 D E F)⁻¹ * (q * l)⁻¹ =
        (g2N 0 0 0 D E F * q * (g2N 0 0 0 D E F)⁻¹ * q⁻¹) *
          (q * (g2N 0 0 0 D E F * l * (g2N 0 0 0 D E F)⁻¹ * l⁻¹) * q⁻¹) := by group
    rw [e, show q * (g2N 0 0 0 D E F * l * (g2N 0 0 0 D E F)⁻¹ * l⁻¹) * q⁻¹ =
      g2N 0 0 0 D E F * l * (g2N 0 0 0 D E F)⁻¹ * l⁻¹ by
        rw [← mem_centralizer_iff.mp hqC _ h1, mul_inv_cancel_right]]
    exact mul_mem (g2ShortParabolicRadical_elem hdD hq).2 h1

theorem rootSubgroup_v_le_g2ShortParabolicRadical :
    rootSubgroup .G2 K g2v ≤ g2ShortParabolicRadical K := by
  intro g hg
  obtain ⟨s, rfl⟩ := mem_rootSubgroup.mp hg
  rw [pinnedX_v_eq_g2N]
  exact g2N_mem_g2ShortParabolicRadical 0 0 s 0 0

theorem commutator_g2ShortParabolicRadical_v :
    ⁅g2ShortParabolicRadical K, rootSubgroup .G2 K g2v⁆ = g2BCGroup K := by
  apply le_antisymm
  · rw [commutator_le]
    intro d hd u hu
    rw [commutatorElement_def]
    exact (g2ShortParabolicRadical_elem hd (rootSubgroup_v_le_g2ShortParabolicRadical hu)).2
  · rintro _ ⟨y, z, rfl⟩
    have hr : X g2r 1 ∈ g2ShortParabolicRadical K := by
      rw [pinnedX_r_eq_g2N]
      exact g2N_mem_g2ShortParabolicRadical 1 0 0 0 0
    have hu : X g2u 1 ∈ g2ShortParabolicRadical K := by
      rw [pinnedX_u_eq_g2N]
      exact g2N_mem_g2ShortParabolicRadical 0 1 0 0 0
    have hvy : X g2v y ∈ rootSubgroup .G2 K g2v := mem_rootSubgroup.mpr ⟨y, rfl⟩
    have hvz : X g2v z ∈ rootSubgroup .G2 K g2v := mem_rootSubgroup.mpr ⟨z, rfl⟩
    have h1 := commutator_mem_commutator hr hvy
    have h2 := commutator_mem_commutator hu hvz
    rw [comm_r_v, one_mul] at h1
    rw [comm_u_v, one_mul] at h2
    have e : g2N (0 : K) 0 0 0 y z = X g2b y * X g2c z := by
      simp only [g2N, pinnedX_zero, one_mul]
    rw [e]
    exact mul_mem h1 h2

end CFSG.ComponentClassification.AS81.G2
