module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2TorusConj
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Levi
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi

public section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.Blueprint.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.LieType.Chevalley (WeylGroup canonicalRep coxeterSystem simple torusGroup borelGroup)

section Defs

variable (K : Type) [Field K]

@[expose] noncomputable def g2LongC
    : Subgroup (ModGL .G2 K) :=
  closure (Set.range (pinnedX .G2 K g2c) ∪ Set.range (pinnedX .G2 K (-g2c)))

@[expose] noncomputable def g2LongA2
    : Subgroup (ModGL .G2 K) :=
  closure (Set.range (pinnedX .G2 K g2a) ∪ Set.range (pinnedX .G2 K (-g2a)) ∪
    Set.range (pinnedX .G2 K g2b) ∪ Set.range (pinnedX .G2 K (-g2b)) ∪
    Set.range (pinnedX .G2 K g2c) ∪ Set.range (pinnedX .G2 K (-g2c)))

end Defs

section Members

variable {K : Type} [Field K]

theorem pinnedX_c_mem_g2LongC
    (x : K) : pinnedX .G2 K g2c x ∈ g2LongC K :=
  subset_closure (Or.inl ⟨x, rfl⟩)

theorem pinnedX_nc_mem_g2LongC
    (x : K) : pinnedX .G2 K (-g2c) x ∈ g2LongC K :=
  subset_closure (Or.inr ⟨x, rfl⟩)

theorem pinnedX_a_mem_g2LongA2
    (x : K) : pinnedX .G2 K g2a x ∈ g2LongA2 K :=
  subset_closure (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨x, rfl⟩)))))

theorem pinnedX_na_mem_g2LongA2
    (x : K) : pinnedX .G2 K (-g2a) x ∈ g2LongA2 K :=
  subset_closure (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨x, rfl⟩)))))

theorem pinnedX_b_mem_g2LongA2
    (x : K) : pinnedX .G2 K g2b x ∈ g2LongA2 K :=
  subset_closure (Or.inl (Or.inl (Or.inl (Or.inr ⟨x, rfl⟩))))

theorem pinnedX_nb_mem_g2LongA2
    (x : K) : pinnedX .G2 K (-g2b) x ∈ g2LongA2 K :=
  subset_closure (Or.inl (Or.inl (Or.inr ⟨x, rfl⟩)))

theorem pinnedX_c_mem_g2LongA2
    (x : K) : pinnedX .G2 K g2c x ∈ g2LongA2 K :=
  subset_closure (Or.inl (Or.inr ⟨x, rfl⟩))

theorem pinnedX_nc_mem_g2LongA2
    (x : K) : pinnedX .G2 K (-g2c) x ∈ g2LongA2 K :=
  subset_closure (Or.inr ⟨x, rfl⟩)

theorem g2LongC_le_g2LongA2
    : g2LongC K ≤ g2LongA2 K := by
  refine (closure_le _).2 ?_
  rintro _ (⟨x, rfl⟩ | ⟨x, rfl⟩)
  exacts [pinnedX_c_mem_g2LongA2 x, pinnedX_nc_mem_g2LongA2 x]

theorem g2na_eq_neg
    : g2na = -g2a := List.ofFn_injective (by decide +kernel)

theorem g2RankOne_a_le_g2LongA2
    : g2RankOne K g2ia ≤ g2LongA2 K := by
  rw [g2RankOne_a_eq]
  refine (closure_le _).2 ?_
  rintro _ (⟨x, rfl⟩ | ⟨x, rfl⟩)
  · exact pinnedX_a_mem_g2LongA2 x
  · rw [g2na_eq_neg]
    exact pinnedX_na_mem_g2LongA2 x

end Members

section Weyl

variable {K : Type} [Field K] [CharP K 2]

theorem canonicalRep_simple_mul
    (i : Fin Tag.G2.rank) (w : WeylGroup .G2) :
    canonicalRep (coxeterSystem .G2) K (simple .G2 i * w) =
      weylElt .G2 K i 1 * canonicalRep (coxeterSystem .G2) K w := by
  rw [LieType.Chevalley.weylElt_mul_canonicalRep]
  split_ifs
  · rfl
  · rw [show (-1 : Kˣ) = 1 from Units.ext (by simp [CharTwo.neg_eq]), torusElt_one, one_mul]

theorem weyl_eq_of_smul
    {w w' : WeylGroup .G2} (ha : w • g2a = w' • g2a)
    (hr : w • g2r = w' • g2r) : w = w' := by
  have h := eq_one_of_smul (w := w'⁻¹ * w) (by rw [mul_smul, ha, inv_smul_smul])
    (by rw [mul_smul, hr, inv_smul_smul])
  exact (inv_mul_eq_one.1 h).symm

end Weyl

section Torus

variable {K : Type} [Field K]

theorem torus_mul_comm
    {h h' : ModGL .G2 K} (hh : h ∈ torusGroup .G2 K)
    (hh' : h' ∈ torusGroup .G2 K) : h * h' = h' * h :=
  LieType.Chevalley.mul_comm_of_mem_diagonalGroup
    (LieType.Chevalley.torusGroup_le_diagonalGroup hh)
    (LieType.Chevalley.torusGroup_le_diagonalGroup hh')

theorem torus_r_g2N
    (t : Kˣ) (A B C D E F : K) :
    torusElt .G2 K g2ir t * g2N A B C D E F * (torusElt .G2 K g2ir t)⁻¹ =
      g2N (((t ^ (2 : ℤ) : Kˣ) : K) * A) (((t ^ (-3 : ℤ) : Kˣ) : K) * B)
        (((t ^ (-1 : ℤ) : Kˣ) : K) * C) ((t : K) * D) (((t ^ (3 : ℤ) : Kˣ) : K) * E) F := by
  have hr : ∑ j, Tag.G2.cartan g2ir j * g2r j = 2 := by decide
  have ha : ∑ j, Tag.G2.cartan g2ir j * g2a j = -3 := by decide
  have hu : ∑ j, Tag.G2.cartan g2ir j * g2u j = -1 := by decide
  have hb : ∑ j, Tag.G2.cartan g2ir j * g2b j = 3 := by decide
  rw [show torusElt .G2 K g2ir t * g2N A B C D E F * (torusElt .G2 K g2ir t)⁻¹ =
      MulAut.conj (torusElt .G2 K g2ir t) (g2N A B C D E F) from rfl]
  simp only [g2N, map_mul, MulAut.conj_apply]
  rw [root_torus_conjugation g2ir isRoot_g2r, root_torus_conjugation g2ir isRoot_g2a,
    root_torus_conjugation g2ir isRoot_g2u, torus_r_v, root_torus_conjugation g2ir isRoot_g2b,
    torus_r_c, hr, ha, hu, hb]

theorem coords_of_commute_torus_r
    {t : Kˣ} {A B C D E F : K}
    (h : torusElt .G2 K g2ir t * g2N A B C D E F = g2N A B C D E F * torusElt .G2 K g2ir t) :
    ((t ^ (2 : ℤ) : Kˣ) : K) * A = A ∧ ((t ^ (-3 : ℤ) : Kˣ) : K) * B = B ∧
      ((t ^ (-1 : ℤ) : Kˣ) : K) * C = C ∧ (t : K) * D = D ∧
        ((t ^ (3 : ℤ) : Kˣ) : K) * E = E := by
  have h' : torusElt .G2 K g2ir t * g2N A B C D E F * (torusElt .G2 K g2ir t)⁻¹ =
      g2N A B C D E F := by rw [h, mul_inv_cancel_right]
  rw [torus_r_g2N] at h'
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := g2N_injective h'
  exact ⟨h1, h2, h3, h4, h5⟩

omit [Field K] in
theorem eq_zero_of_units_mul_eq {L : Type} [Field L] {c : Lˣ} (hc : c ≠ 1) {x : L}
    (h : (c : L) * x = x) : x = 0 := by
  have hc' : (c : L) - 1 ≠ 0 := fun h0 => hc (Units.ext (by simpa [sub_eq_zero] using h0))
  have : ((c : L) - 1) * x = 0 := by rw [sub_mul, h, one_mul, sub_self]
  exact (mul_eq_zero.1 this).resolve_left hc'

end Torus

section Bruhat

variable {K : Type} [Field K]

theorem exists_bruhat_of_commute_torus
    {s g : ModGL .G2 K}
    (hs : s ∈ torusGroup .G2 K) (hg : g ∈ adjointGroup .G2 K) (hsg : s * g = g * s) :
    ∃ w : WeylGroup .G2, ∃ h ∈ torusGroup .G2 K, ∃ u₀ ∈ posUnipotent .G2 K,
      ∃ u ∈ posUnipotent .G2 K, g = h * u₀ * canonicalRep (coxeterSystem .G2) K w * u ∧
        s * u₀ = u₀ * s ∧ s * u = u * s ∧
        s * canonicalRep (coxeterSystem .G2) K w = canonicalRep (coxeterSystem .G2) K w * s := by
  have hg' : g ∈ (adjointGroup .G2 K : Set (ModGL .G2 K)) := hg
  rw [LieType.Chevalley.adjointGroup_eq_iUnion_bruhatCell] at hg'
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
  set n := canonicalRep (coxeterSystem .G2) K w with hn
  have hbij := LieType.Chevalley.bijOn_bruhatCell (τ := .G2) (K := K) w
  obtain ⟨⟨b, u⟩, ⟨hb, hu⟩, hbu⟩ := hbij.surjOn hw
  simp only at hbu hb hu
  have hsB : s ∈ borelGroup .G2 K := LieType.Chevalley.torusGroup_le_borelGroup hs
  have hnT : n ∈ normalizer (torusGroup .G2 K : Set (ModGL .G2 K)) :=
    (LieType.Chevalley.canonical_weyl_root_transport .G2 K).2.2 w
  have hk : s * n * s⁻¹ * n⁻¹ ∈ torusGroup .G2 K := by
    have h1 : n * s⁻¹ * n⁻¹ ∈ torusGroup .G2 K := (mem_normalizer_iff.1 hnT _).1 (inv_mem hs)
    rw [show s * n * s⁻¹ * n⁻¹ = s * (n * s⁻¹ * n⁻¹) by group]
    exact mul_mem hs h1
  have hu' : s * u * s⁻¹ ∈ rootSpan .G2 K (LieType.Chevalley.inversionSet w) :=
    (mem_normalizer_iff.1 (LieType.Chevalley.torusGroup_le_normalizer_rootSpan
      (fun α h => h.1) hs) u).1 hu
  have hb' : s * b * s⁻¹ * (s * n * s⁻¹ * n⁻¹) ∈ borelGroup .G2 K :=
    mul_mem (mul_mem (mul_mem hsB hb) (inv_mem hsB)) (LieType.Chevalley.torusGroup_le_borelGroup hk)
  have heq : s * b * s⁻¹ * (s * n * s⁻¹ * n⁻¹) * n * (s * u * s⁻¹) = b * n * u := by
    calc s * b * s⁻¹ * (s * n * s⁻¹ * n⁻¹) * n * (s * u * s⁻¹) = s * (b * n * u) * s⁻¹ := by
          group
      _ = b * n * u := by rw [hbu, hsg, mul_inv_cancel_right]
  have hinj := hbij.injOn (x₁ := (s * b * s⁻¹ * (s * n * s⁻¹ * n⁻¹), s * u * s⁻¹))
    (x₂ := (b, u)) ⟨hb', hu'⟩ ⟨hb, hu⟩ heq
  simp only [Prod.mk.injEq] at hinj
  obtain ⟨h1, h2⟩ := hinj
  obtain ⟨h₀, hh₀, u₀, hu₀, rfl⟩ := exists_torus_mul_of_mem_borel hb
  have hsu₀ : s * u₀ * s⁻¹ ∈ posUnipotent .G2 K := torus_conj_mem_posUnipotent hs hu₀
  have hc : s * h₀ = h₀ * s := torus_mul_comm hs hh₀
  have e2 : s * u₀ * s⁻¹ * (s * n * s⁻¹ * n⁻¹) = u₀ := by
    calc s * u₀ * s⁻¹ * (s * n * s⁻¹ * n⁻¹) =
        h₀⁻¹ * (s * (h₀ * u₀) * s⁻¹ * (s * n * s⁻¹ * n⁻¹)) := by
          rw [← mul_assoc s h₀, hc]
          group
      _ = u₀ := by rw [h1, inv_mul_cancel_left]
  have hk1 : s * n * s⁻¹ * n⁻¹ = 1 := by
    have hkU : s * n * s⁻¹ * n⁻¹ ∈ posUnipotent .G2 K := by
      rw [eq_inv_mul_of_mul_eq e2]
      exact mul_mem (inv_mem hsu₀) hu₀
    have h := LieType.Chevalley.torusGroup_inf_posUnipotent (τ := .G2) (R := K)
    rw [eq_bot_iff] at h
    exact mem_bot.1 (h (mem_inf.2 ⟨hk, hkU⟩))
  rw [hk1, mul_one] at e2
  refine ⟨w, h₀, hh₀, u₀, hu₀, u, LieType.Chevalley.rootSpan_le_posUnipotent
    (fun α h => LieType.Chevalley.inversionSet_pos (w := w) h) hu, by rw [← hbu, mul_assoc h₀],
    ?_, ?_, ?_⟩
  · calc s * u₀ = s * u₀ * s⁻¹ * s := by group
      _ = u₀ * s := by rw [e2]
  · calc s * u = s * u * s⁻¹ * s := by group
      _ = u * s := by rw [h2]
  · calc s * n = s * n * s⁻¹ * n⁻¹ * (n * s) := by group
      _ = n * s := by rw [hk1, one_mul]

end Bruhat

section WeylTorus

variable {K : Type} [Field K] [CharP K 2]

theorem zpow_eq_of_commute_canonicalRep
    {w : WeylGroup .G2} {t : Kˣ}
    (h : torusElt .G2 K g2ir t * canonicalRep (coxeterSystem .G2) K w =
      canonicalRep (coxeterSystem .G2) K w * torusElt .G2 K g2ir t)
    {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α) :
    t ^ (∑ j, Tag.G2.cartan g2ir j * (w • α) j) = t ^ (∑ j, Tag.G2.cartan g2ir j * α j) := by
  have h1 : torusElt .G2 K g2ir t * pinnedX .G2 K (w • α) 1 * (torusElt .G2 K g2ir t)⁻¹ =
      pinnedX .G2 K (w • α) ((t ^ (∑ j, Tag.G2.cartan g2ir j * α j) : Kˣ) : K) := by
    calc torusElt .G2 K g2ir t * pinnedX .G2 K (w • α) 1 * (torusElt .G2 K g2ir t)⁻¹ =
        torusElt .G2 K g2ir t * (canonicalRep (coxeterSystem .G2) K w * pinnedX .G2 K α 1 *
          (canonicalRep (coxeterSystem .G2) K w)⁻¹) * (torusElt .G2 K g2ir t)⁻¹ := by
          rw [canonicalRep_conj w hα]
      _ = canonicalRep (coxeterSystem .G2) K w * (torusElt .G2 K g2ir t * pinnedX .G2 K α 1 *
          (torusElt .G2 K g2ir t)⁻¹) * (canonicalRep (coxeterSystem .G2) K w)⁻¹ := by
          rw [show torusElt .G2 K g2ir t * (canonicalRep (coxeterSystem .G2) K w *
              pinnedX .G2 K α 1 * (canonicalRep (coxeterSystem .G2) K w)⁻¹) *
              (torusElt .G2 K g2ir t)⁻¹ = (torusElt .G2 K g2ir t *
                canonicalRep (coxeterSystem .G2) K w) * pinnedX .G2 K α 1 *
              (torusElt .G2 K g2ir t * canonicalRep (coxeterSystem .G2) K w)⁻¹ by group, h]
          group
      _ = _ := by
          rw [root_torus_conjugation g2ir hα t 1, canonicalRep_conj w hα, mul_one]
  rw [root_torus_conjugation g2ir (LieType.Chevalley.IsRoot.smul hα w) t 1, mul_one] at h1
  exact Units.ext (pinnedX_injective .G2 K _ h1)

theorem orderOf_dvd_sub_of_zpow_eq {G : Type*} [Group G] {t : G} {m n : ℤ}
    (h : t ^ m = t ^ n) : (orderOf t : ℤ) ∣ m - n :=
  orderOf_dvd_iff_zpow_eq_one.2 (by rw [zpow_sub, h, mul_inv_cancel])

theorem weylElt_a_eq
    : weylElt .G2 K g2ia 1 =
    pinnedX .G2 K g2a 1 * pinnedX .G2 K (-g2a) 1 * pinnedX .G2 K g2a 1 := by
  rw [weylElt_eq_xUnit_mul, xUnit_g2ia, yUnit_g2ia, g2na_eq_neg]
  simp only [inv_one, Units.val_one, CharTwo.neg_eq]

theorem weylElt_r_conj_a
    (x : K) : weylElt .G2 K g2ir 1 * pinnedX .G2 K g2a x *
    (weylElt .G2 K g2ir 1)⁻¹ = pinnedX .G2 K g2b x := by
  rw [UnbalancedCatalog.weylElt_conj g2ir isRoot_g2a, reflect_r_a]

theorem weylElt_r_conj_na
    (x : K) : weylElt .G2 K g2ir 1 * pinnedX .G2 K (-g2a) x *
    (weylElt .G2 K g2ir 1)⁻¹ = pinnedX .G2 K (-g2b) x := by
  rw [UnbalancedCatalog.weylElt_conj g2ir (LieType.Chevalley.IsRoot.neg isRoot_g2a),
    show reflect .G2 g2ir (-g2a) = -g2b from List.ofFn_injective (by decide +kernel)]

theorem weylElt_a_conj_b
    (x : K) : weylElt .G2 K g2ia 1 * pinnedX .G2 K g2b x *
    (weylElt .G2 K g2ia 1)⁻¹ = pinnedX .G2 K g2c x := by
  rw [UnbalancedCatalog.weylElt_conj g2ia isRoot_g2b, reflect_a_b]

theorem weylElt_a_conj_nb
    (x : K) : weylElt .G2 K g2ia 1 * pinnedX .G2 K (-g2b) x *
    (weylElt .G2 K g2ia 1)⁻¹ = pinnedX .G2 K (-g2c) x := by
  rw [UnbalancedCatalog.weylElt_conj g2ia (LieType.Chevalley.IsRoot.neg isRoot_g2b),
    show reflect .G2 g2ia (-g2b) = -g2c from List.ofFn_injective (by decide +kernel)]

theorem weylElt_r_conj_weylElt_a
    : weylElt .G2 K g2ir 1 * weylElt .G2 K g2ia 1 *
    (weylElt .G2 K g2ir 1)⁻¹ =
      pinnedX .G2 K g2b 1 * pinnedX .G2 K (-g2b) 1 * pinnedX .G2 K g2b 1 := by
  rw [weylElt_a_eq, ← weylElt_r_conj_a, ← weylElt_r_conj_na]
  group

theorem weylElt_ar_conj_weylElt_a
    : weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1 *
    weylElt .G2 K g2ia 1 * (weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1)⁻¹ =
      pinnedX .G2 K g2c 1 * pinnedX .G2 K (-g2c) 1 * pinnedX .G2 K g2c 1 := by
  rw [show weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1 * weylElt .G2 K g2ia 1 *
      (weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1)⁻¹ = weylElt .G2 K g2ia 1 *
        (weylElt .G2 K g2ir 1 * weylElt .G2 K g2ia 1 * (weylElt .G2 K g2ir 1)⁻¹) *
          (weylElt .G2 K g2ia 1)⁻¹ by group, weylElt_r_conj_weylElt_a,
    ← weylElt_a_conj_b, ← weylElt_a_conj_nb]
  group

omit [CharP K 2] in
theorem weylElt_ar_conj_torusElt_a
    (t : Kˣ) :
    weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1 * torusElt .G2 K g2ia t *
      (weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1)⁻¹ =
        torusElt .G2 K g2ir t * torusElt .G2 K g2ia (t ^ 2) := by
  have c1 : Tag.G2.cartan g2ia g2ir = -1 := by decide
  have c2 : Tag.G2.cartan g2ir g2ia = -3 := by decide
  have e1 := LieType.Chevalley.weylElt_mul_torusElt .G2 K g2ir g2ia 1 t
  have e2 := LieType.Chevalley.weylElt_mul_torusElt .G2 K g2ia g2ir 1 t
  have e3 := LieType.Chevalley.weylElt_mul_torusElt_mul_inv (τ := .G2) (K := K) g2ia t
  rw [c1, neg_neg, zpow_one] at e1
  rw [c2, neg_neg] at e2
  have e1' : weylElt .G2 K g2ir 1 * torusElt .G2 K g2ia t * (weylElt .G2 K g2ir 1)⁻¹ =
      torusElt .G2 K g2ia t * torusElt .G2 K g2ir t := by rw [e1, mul_inv_cancel_right]
  have e2' : weylElt .G2 K g2ia 1 * torusElt .G2 K g2ir t * (weylElt .G2 K g2ia 1)⁻¹ =
      torusElt .G2 K g2ir t * torusElt .G2 K g2ia (t ^ (3 : ℤ)) := by rw [e2, mul_inv_cancel_right]
  calc weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1 * torusElt .G2 K g2ia t *
      (weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1)⁻¹ =
        weylElt .G2 K g2ia 1 * (weylElt .G2 K g2ir 1 * torusElt .G2 K g2ia t *
          (weylElt .G2 K g2ir 1)⁻¹) * (weylElt .G2 K g2ia 1)⁻¹ := by group
    _ = (weylElt .G2 K g2ia 1 * torusElt .G2 K g2ia t * (weylElt .G2 K g2ia 1)⁻¹) *
        (weylElt .G2 K g2ia 1 * torusElt .G2 K g2ir t * (weylElt .G2 K g2ia 1)⁻¹) := by
          rw [e1']
          group
    _ = torusElt .G2 K g2ia t⁻¹ * (torusElt .G2 K g2ir t * torusElt .G2 K g2ia (t ^ (3 : ℤ))) := by
          rw [e3, e2']
    _ = torusElt .G2 K g2ir t * (torusElt .G2 K g2ia t⁻¹ * torusElt .G2 K g2ia (t ^ (3 : ℤ))) := by
          rw [← mul_assoc, torus_mul_comm (LieType.Chevalley.torusElt_mem_torusGroup _ _)
            (LieType.Chevalley.torusElt_mem_torusGroup _ _), mul_assoc]
    _ = _ := by
          rw [← torusElt_mul]
          congr 2
          rw [zpow_ofNat]
          group

theorem weylElt_ar_conj_mem_g2LongC
    {y : ModGL .G2 K} (hy : y ∈ g2RankOne K g2ia) :
    weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1 * y *
      (weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1)⁻¹ ∈ g2LongC K := by
  rw [g2RankOne_a_eq] at hy
  induction hy using closure_induction with
  | mem z hz =>
    rcases hz with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · rw [show weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1 * pinnedX .G2 K g2a x *
          (weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1)⁻¹ = weylElt .G2 K g2ia 1 *
            (weylElt .G2 K g2ir 1 * pinnedX .G2 K g2a x * (weylElt .G2 K g2ir 1)⁻¹) *
              (weylElt .G2 K g2ia 1)⁻¹ by group, weylElt_r_conj_a, weylElt_a_conj_b]
      exact pinnedX_c_mem_g2LongC x
    · rw [g2na_eq_neg, show weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1 *
          pinnedX .G2 K (-g2a) x * (weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1)⁻¹ =
            weylElt .G2 K g2ia 1 * (weylElt .G2 K g2ir 1 * pinnedX .G2 K (-g2a) x *
              (weylElt .G2 K g2ir 1)⁻¹) * (weylElt .G2 K g2ia 1)⁻¹ by group,
        weylElt_r_conj_na, weylElt_a_conj_nb]
      exact pinnedX_nc_mem_g2LongC x
  | one => simp
  | mul y z _ _ hy hz =>
    rw [show weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1 * (y * z) *
        (weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1)⁻¹ =
          (weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1 * y *
            (weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1)⁻¹) *
          (weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1 * z *
            (weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1)⁻¹) by group]
    exact mul_mem hy hz
  | inv y _ hy =>
    rw [show weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1 * y⁻¹ *
        (weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1)⁻¹ =
          (weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1 * y *
            (weylElt .G2 K g2ia 1 * weylElt .G2 K g2ir 1)⁻¹)⁻¹ by group]
    exact inv_mem hy

theorem torusElt_r_mul_a_sq_mem_g2LongC
    (t : Kˣ) :
    torusElt .G2 K g2ir t * torusElt .G2 K g2ia (t ^ 2) ∈ g2LongC K := by
  rw [← weylElt_ar_conj_torusElt_a]
  exact weylElt_ar_conj_mem_g2LongC (torusElt_mem_g2RankOne g2ia t)

end WeylTorus

section WeylWords

variable {K : Type} [Field K] [CharP K 2]

theorem eq_rar_of_smul
    {w : WeylGroup .G2} (ha : w • g2a = g2c) (hr : w • g2r = -g2v) :
    w = simple .G2 g2ir * (simple .G2 g2ia * simple .G2 g2ir) := by
  refine weyl_eq_of_smul ?_ ?_
  · rw [ha]
    simp only [mul_smul, LieType.Chevalley.simple_smul]
    exact List.ofFn_injective (by decide +kernel)
  · rw [hr]
    simp only [mul_smul, LieType.Chevalley.simple_smul]
    exact List.ofFn_injective (by decide +kernel)

theorem eq_rara_of_smul
    {w : WeylGroup .G2} (ha : w • g2a = -g2c) (hr : w • g2r = g2u) :
    w = simple .G2 g2ir * (simple .G2 g2ia * (simple .G2 g2ir * simple .G2 g2ia)) := by
  refine weyl_eq_of_smul ?_ ?_
  · rw [ha]
    simp only [mul_smul, LieType.Chevalley.simple_smul]
    exact List.ofFn_injective (by decide +kernel)
  · rw [hr]
    simp only [mul_smul, LieType.Chevalley.simple_smul]
    exact List.ofFn_injective (by decide +kernel)

theorem eq_arar_of_smul
    {w : WeylGroup .G2} (ha : w • g2a = g2b) (hr : w • g2r = -g2v) :
    w = simple .G2 g2ia * (simple .G2 g2ir * (simple .G2 g2ia * simple .G2 g2ir)) := by
  refine weyl_eq_of_smul ?_ ?_
  · rw [ha]
    simp only [mul_smul, LieType.Chevalley.simple_smul]
    exact List.ofFn_injective (by decide +kernel)
  · rw [hr]
    simp only [mul_smul, LieType.Chevalley.simple_smul]
    exact List.ofFn_injective (by decide +kernel)

theorem eq_arara_of_smul
    {w : WeylGroup .G2} (ha : w • g2a = -g2b)
    (hr : w • g2r = g2r) : w = simple .G2 g2ia *
      (simple .G2 g2ir * (simple .G2 g2ia * (simple .G2 g2ir * simple .G2 g2ia))) := by
  refine weyl_eq_of_smul ?_ ?_
  · rw [ha]
    simp only [mul_smul, LieType.Chevalley.simple_smul]
    exact List.ofFn_injective (by decide +kernel)
  · rw [hr]
    simp only [mul_smul, LieType.Chevalley.simple_smul]
    exact List.ofFn_injective (by decide +kernel)

theorem canonicalRep_rar :
    canonicalRep (coxeterSystem .G2) K (simple .G2 g2ir * (simple .G2 g2ia * simple .G2 g2ir)) =
      pinnedX .G2 K g2b 1 * pinnedX .G2 K (-g2b) 1 * pinnedX .G2 K g2b 1 := by
  rw [canonicalRep_simple_mul, canonicalRep_simple_mul, LieType.Chevalley.canonicalRep_simple,
    ← weylElt_r_conj_weylElt_a, UnbalancedCatalog.weylElt_inv g2ir, mul_assoc]

theorem canonicalRep_arara :
    canonicalRep (coxeterSystem .G2) K (simple .G2 g2ia *
      (simple .G2 g2ir * (simple .G2 g2ia * (simple .G2 g2ir * simple .G2 g2ia)))) =
      pinnedX .G2 K g2c 1 * pinnedX .G2 K (-g2c) 1 * pinnedX .G2 K g2c 1 := by
  rw [canonicalRep_simple_mul, canonicalRep_simple_mul, canonicalRep_simple_mul,
    canonicalRep_simple_mul, LieType.Chevalley.canonicalRep_simple,
    ← weylElt_ar_conj_weylElt_a, mul_inv_rev, UnbalancedCatalog.weylElt_inv g2ir,
    UnbalancedCatalog.weylElt_inv g2ia]
  group

theorem canonicalRep_rara :
    canonicalRep (coxeterSystem .G2) K (simple .G2 g2ir *
      (simple .G2 g2ia * (simple .G2 g2ir * simple .G2 g2ia))) =
      pinnedX .G2 K g2b 1 * pinnedX .G2 K (-g2b) 1 * pinnedX .G2 K g2b 1 *
        weylElt .G2 K g2ia 1 := by
  rw [← canonicalRep_rar, canonicalRep_simple_mul, canonicalRep_simple_mul,
    canonicalRep_simple_mul, LieType.Chevalley.canonicalRep_simple, canonicalRep_simple_mul,
    canonicalRep_simple_mul, LieType.Chevalley.canonicalRep_simple]
  group

theorem canonicalRep_arar :
    canonicalRep (coxeterSystem .G2) K (simple .G2 g2ia *
      (simple .G2 g2ir * (simple .G2 g2ia * simple .G2 g2ir))) =
      weylElt .G2 K g2ia 1 *
        (pinnedX .G2 K g2b 1 * pinnedX .G2 K (-g2b) 1 * pinnedX .G2 K g2b 1) := by
  rw [← canonicalRep_rar, canonicalRep_simple_mul]

theorem canonicalRep_mem_g2LongA2_of_weyl
    {w : WeylGroup .G2}
    (h : w = 1 ∨ w = simple .G2 g2ia ∨ w = simple .G2 g2ir * (simple .G2 g2ia * simple .G2 g2ir) ∨
      w = simple .G2 g2ir * (simple .G2 g2ia * (simple .G2 g2ir * simple .G2 g2ia)) ∨
      w = simple .G2 g2ia * (simple .G2 g2ir * (simple .G2 g2ia * simple .G2 g2ir)) ∨
      w = simple .G2 g2ia * (simple .G2 g2ir * (simple .G2 g2ia *
        (simple .G2 g2ir * simple .G2 g2ia)))) :
    canonicalRep (coxeterSystem .G2) K w ∈ g2LongA2 K := by
  have hna : weylElt .G2 K g2ia 1 ∈ g2LongA2 K :=
    g2RankOne_a_le_g2LongA2 (weylElt_mem_g2RankOne g2ia 1)
  have hPb : pinnedX .G2 K g2b 1 * pinnedX .G2 K (-g2b) 1 * pinnedX .G2 K g2b 1 ∈ g2LongA2 K :=
    mul_mem (mul_mem (pinnedX_b_mem_g2LongA2 1) (pinnedX_nb_mem_g2LongA2 1))
      (pinnedX_b_mem_g2LongA2 1)
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [LieType.Chevalley.canonicalRep_one]
    exact one_mem _
  · rw [LieType.Chevalley.canonicalRep_simple]
    exact hna
  · rw [canonicalRep_rar]
    exact hPb
  · rw [canonicalRep_rara]
    exact mul_mem hPb hna
  · rw [canonicalRep_arar]
    exact mul_mem hna hPb
  · rw [canonicalRep_arara]
    exact mul_mem (mul_mem (pinnedX_c_mem_g2LongA2 1) (pinnedX_nc_mem_g2LongA2 1))
      (pinnedX_c_mem_g2LongA2 1)

end WeylWords

section Centralizer

variable {K : Type} [Field K]

theorem eq_of_commute_torus_r_posUnipotent
    {t : Kˣ} (ht1 : t ≠ 1)
    (ht2 : t ^ (2 : ℤ) ≠ 1) {v : ModGL .G2 K} (hv : v ∈ posUnipotent .G2 K)
    (hsv : torusElt .G2 K g2ir t * v = v * torusElt .G2 K g2ir t) :
    ∃ B E F : K, v = pinnedX .G2 K g2a B * pinnedX .G2 K g2b E * pinnedX .G2 K g2c F ∧
      (t ^ (3 : ℤ) ≠ 1 → B = 0 ∧ E = 0) := by
  obtain ⟨A, B, C, D, E, F, rfl⟩ := exists_g2N_of_mem_posUnipotent hv
  obtain ⟨h1, h2, h3, h4, h5⟩ := coords_of_commute_torus_r hsv
  have hA : A = 0 := eq_zero_of_units_mul_eq ht2 h1
  have hC : C = 0 :=
    eq_zero_of_units_mul_eq (by rw [zpow_neg_one]; exact inv_ne_one.2 ht1) h3
  have hD : D = 0 := eq_zero_of_units_mul_eq ht1 h4
  subst hA hC hD
  refine ⟨B, E, F, by simp only [g2N, pinnedX_zero, mul_one, one_mul], fun ht3 => ⟨?_, ?_⟩⟩
  · refine eq_zero_of_units_mul_eq ?_ h2
    rw [zpow_neg]
    exact inv_ne_one.2 ht3
  · exact eq_zero_of_units_mul_eq ht3 h5

theorem torusGroup_le_g2LongA2
    [CharP K 2] : torusGroup .G2 K ≤ g2LongA2 K := by
  intro h hh
  obtain ⟨t₁, t₂, rfl⟩ := exists_eq_torusElt_mul hh
  refine mul_mem (g2RankOne_a_le_g2LongA2 (torusElt_mem_g2RankOne g2ia t₁)) ?_
  rw [show torusElt .G2 K g2ir t₂ = torusElt .G2 K g2ir t₂ * torusElt .G2 K g2ia (t₂ ^ 2) *
      (torusElt .G2 K g2ia (t₂ ^ 2))⁻¹ by group]
  exact mul_mem (g2LongC_le_g2LongA2 (torusElt_r_mul_a_sq_mem_g2LongC t₂))
    (inv_mem (g2RankOne_a_le_g2LongA2 (torusElt_mem_g2RankOne g2ia _)))

theorem exists_torusR_mul_of_mem_torusGroup
    [Finite K] [CharP K 2]
    {h : ModGL .G2 K} (hh : h ∈ torusGroup .G2 K) :
    ∃ σ : Kˣ, (torusElt .G2 K g2ir σ)⁻¹ * h ∈ g2LongC K := by
  obtain ⟨t₁, t₂, rfl⟩ := exists_eq_torusElt_mul hh
  obtain ⟨σ, hσ⟩ : ∃ σ : Kˣ, σ ^ 2 = t₁ := by
    have hq1 : 1 < Nat.card K := Finite.one_lt_card
    obtain ⟨k, hk⟩ := odd_card_sub_one (K := K)
    have h2q : 2 ∣ Nat.card K := ⟨k + 1, by omega⟩
    refine ⟨t₁ ^ (Nat.card K / 2), ?_⟩
    rw [← pow_mul, Nat.div_mul_cancel h2q]
    have h1 : t₁ ^ (Nat.card K - 1) = 1 := by
      rw [← Nat.card_units]
      exact pow_card_eq_one'
    calc t₁ ^ Nat.card K = t₁ ^ (Nat.card K - 1 + 1) := by rw [Nat.sub_add_cancel hq1.le]
      _ = t₁ := by rw [pow_succ, h1, one_mul]
  refine ⟨t₂ * σ⁻¹, ?_⟩
  have hinv : (torusElt .G2 K g2ir σ⁻¹)⁻¹ = torusElt .G2 K g2ir σ := by
    rw [inv_eq_iff_eq_inv]
    exact eq_inv_of_mul_eq_one_right (by rw [← torusElt_mul, mul_inv_cancel, torusElt_one])
  have hc : torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂ =
      torusElt .G2 K g2ir t₂ * torusElt .G2 K g2ia t₁ :=
    torus_mul_comm (LieType.Chevalley.torusElt_mem_torusGroup _ _)
      (LieType.Chevalley.torusElt_mem_torusGroup _ _)
  rw [torusElt_mul, mul_inv_rev, hinv, hc, ← hσ]
  rw [show torusElt .G2 K g2ir σ * (torusElt .G2 K g2ir t₂)⁻¹ *
      (torusElt .G2 K g2ir t₂ * torusElt .G2 K g2ia (σ ^ 2)) =
        torusElt .G2 K g2ir σ * torusElt .G2 K g2ia (σ ^ 2) by group]
  exact torusElt_r_mul_a_sq_mem_g2LongC σ

theorem eq_zero_of_dvd_of_small {N : ℕ} {d : ℤ} (hd : (N : ℤ) ∣ d) (hlo : -(N : ℤ) < d)
    (hhi : d < N) : d = 0 := by
  obtain ⟨k, rfl⟩ := hd
  have hN : (0 : ℤ) ≤ N := Nat.cast_nonneg N
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · exfalso
    nlinarith
  · simp
  · exfalso
    nlinarith

variable [Finite K] [CharP K 2]

theorem g2Centralizer_g2TorusR_le_g2LongA2
    (hK4 : Nat.card K = 4) :
    g2Centralizer K (g2TorusR K : Set (ModGL .G2 K)) ≤ g2LongA2 K := by
  intro x hx
  obtain ⟨hxC, hxc⟩ := mem_inf.1 hx
  obtain ⟨t₀, ht₀⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf t₀ = 3 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ht₀, Nat.card_units, hK4]
  have hsx : torusElt .G2 K g2ir t₀ * x = x * torusElt .G2 K g2ir t₀ :=
    mem_centralizer_iff.1 hxc _ ⟨t₀, rfl⟩
  obtain ⟨w, h, hh, u₀, hu₀, u, hu, rfl, hsu₀, hsu, hsn⟩ :=
    exists_bruhat_of_commute_torus (LieType.Chevalley.torusElt_mem_torusGroup _ _) hxC hsx
  have ht1 : t₀ ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hord
    omega
  have ht2 : t₀ ^ (2 : ℤ) ≠ 1 := fun h2 => by
    have h := orderOf_dvd_iff_zpow_eq_one.2 h2
    rw [hord] at h
    omega
  have hU : ∀ v ∈ posUnipotent .G2 K,
      torusElt .G2 K g2ir t₀ * v = v * torusElt .G2 K g2ir t₀ → v ∈ g2LongA2 K := by
    intro v hv hsv
    obtain ⟨B, E, F, rfl, -⟩ := eq_of_commute_torus_r_posUnipotent ht1 ht2 hv hsv
    exact mul_mem (mul_mem (pinnedX_a_mem_g2LongA2 B) (pinnedX_b_mem_g2LongA2 E))
      (pinnedX_c_mem_g2LongA2 F)
  have hn : canonicalRep (coxeterSystem .G2) K w ∈ g2LongA2 K := by
    have hr := orderOf_dvd_sub_of_zpow_eq (zpow_eq_of_commute_canonicalRep hsn isRoot_g2r)
    rw [hord] at hr
    refine canonicalRep_mem_g2LongA2_of_weyl ?_
    rcases g2_weyl_cases w with ⟨ha, hr'⟩ | ⟨ha, hr'⟩ | ⟨ha, hr'⟩ | ⟨ha, hr'⟩ | ⟨ha, hr'⟩ |
      ⟨ha, hr'⟩ | ⟨ha, hr'⟩ | ⟨ha, hr'⟩ | ⟨ha, hr'⟩ | ⟨ha, hr'⟩ | ⟨ha, hr'⟩ | ⟨ha, hr'⟩
    · exact Or.inl (eq_one_of_smul ha hr')
    · exact Or.inr (Or.inl (eq_simple_a_of_smul ha hr'))
    · rw [hr'] at hr
      exact absurd hr (by decide)
    · rw [hr'] at hr
      exact absurd hr (by decide)
    · rw [hr'] at hr
      exact absurd hr (by decide)
    · rw [hr'] at hr
      exact absurd hr (by decide)
    · exact Or.inr (Or.inr (Or.inl (eq_rar_of_smul ha hr')))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (eq_rara_of_smul ha hr'))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (eq_arar_of_smul ha hr')))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (eq_arara_of_smul ha hr')))))
    · rw [hr'] at hr
      exact absurd hr (by decide)
    · rw [hr'] at hr
      exact absurd hr (by decide)
  exact mul_mem (mul_mem (mul_mem (torusGroup_le_g2LongA2 hh) (hU u₀ hu₀ hsu₀)) hn)
    (hU u hu hsu)

theorem exists_mem_g2TorusR_mul_g2LongC
    (hK8 : 8 ≤ Nat.card K) {x : ModGL .G2 K}
    (hx : x ∈ g2Centralizer K (g2TorusR K : Set (ModGL .G2 K))) :
    ∃ h ∈ g2TorusR K, h⁻¹ * x ∈ g2LongC K := by
  obtain ⟨hxC, hxc⟩ := mem_inf.1 hx
  obtain ⟨t₀, ht₀⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf t₀ = Nat.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ht₀, Nat.card_units]
  have hsx : torusElt .G2 K g2ir t₀ * x = x * torusElt .G2 K g2ir t₀ :=
    mem_centralizer_iff.1 hxc _ ⟨t₀, rfl⟩
  obtain ⟨w, h, hh, u₀, hu₀, u, hu, rfl, hsu₀, hsu, hsn⟩ :=
    exists_bruhat_of_commute_torus (LieType.Chevalley.torusElt_mem_torusGroup _ _) hxC hsx
  have hsmall : ∀ d : ℤ, (orderOf t₀ : ℤ) ∣ d → -6 ≤ d → d ≤ 6 → d = 0 := by
    intro d hd hlo hhi
    rw [hord] at hd
    have h7 : (7 : ℤ) ≤ ((Nat.card K - 1 : ℕ) : ℤ) := by
      have : 7 ≤ Nat.card K - 1 := by omega
      exact_mod_cast this
    exact eq_zero_of_dvd_of_small hd (by omega) (by omega)
  have ht1 : t₀ ≠ 1 := fun h1 => by
    have h := hsmall 1 (orderOf_dvd_iff_zpow_eq_one.2 (by rw [h1, one_zpow])) (by norm_num)
      (by norm_num)
    norm_num at h
  have ht2 : t₀ ^ (2 : ℤ) ≠ 1 := fun h2 => by
    have h := hsmall 2 (orderOf_dvd_iff_zpow_eq_one.2 h2) (by norm_num) (by norm_num)
    norm_num at h
  have ht3 : t₀ ^ (3 : ℤ) ≠ 1 := fun h3 => by
    have h := hsmall 3 (orderOf_dvd_iff_zpow_eq_one.2 h3) (by norm_num) (by norm_num)
    norm_num at h
  have hU : ∀ v ∈ posUnipotent .G2 K,
      torusElt .G2 K g2ir t₀ * v = v * torusElt .G2 K g2ir t₀ → v ∈ g2LongC K := by
    intro v hv hsv
    obtain ⟨B, E, F, rfl, hBE⟩ := eq_of_commute_torus_r_posUnipotent ht1 ht2 hv hsv
    obtain ⟨rfl, rfl⟩ := hBE ht3
    rw [pinnedX_zero, pinnedX_zero, one_mul, one_mul]
    exact pinnedX_c_mem_g2LongC F
  have hn : canonicalRep (coxeterSystem .G2) K w ∈ g2LongC K := by
    have hr := orderOf_dvd_sub_of_zpow_eq (zpow_eq_of_commute_canonicalRep hsn isRoot_g2r)
    rcases g2_weyl_cases w with ⟨ha, hr'⟩ | ⟨ha, hr'⟩ | ⟨ha, hr'⟩ | ⟨ha, hr'⟩ | ⟨ha, hr'⟩ |
      ⟨ha, hr'⟩ | ⟨ha, hr'⟩ | ⟨ha, hr'⟩ | ⟨ha, hr'⟩ | ⟨ha, hr'⟩ | ⟨ha, hr'⟩ | ⟨ha, hr'⟩
    · rw [eq_one_of_smul ha hr', LieType.Chevalley.canonicalRep_one]
      exact one_mem _
    all_goals first
      | (rw [eq_arara_of_smul ha hr', canonicalRep_arara]
         exact mul_mem (mul_mem (pinnedX_c_mem_g2LongC 1) (pinnedX_nc_mem_g2LongC 1))
           (pinnedX_c_mem_g2LongC 1))
      | (rw [hr'] at hr
         exact absurd (hsmall _ hr (by decide) (by decide)) (by decide))
  obtain ⟨σ, hσ⟩ := exists_torusR_mul_of_mem_torusGroup hh
  refine ⟨torusElt .G2 K g2ir σ, ⟨σ, rfl⟩, ?_⟩
  rw [show (torusElt .G2 K g2ir σ)⁻¹ * (h * u₀ * canonicalRep (coxeterSystem .G2) K w * u) =
      (torusElt .G2 K g2ir σ)⁻¹ * h * u₀ * canonicalRep (coxeterSystem .G2) K w * u by group]
  exact mul_mem (mul_mem (mul_mem hσ (hU u₀ hu₀ hsu₀)) hn) (hU u hu hsu)

end Centralizer

section Four

variable {K : Type} [Field K]

theorem g2LongA2_le_adjointGroup
    : g2LongA2 K ≤ adjointGroup .G2 K := by
  refine (closure_le _).2 ?_
  rintro _ (((((⟨x, rfl⟩ | ⟨x, rfl⟩) | ⟨x, rfl⟩) | ⟨x, rfl⟩) | ⟨x, rfl⟩) | ⟨x, rfl⟩) <;>
    exact pinnedX_mem_adjointGroup _ x

theorem g2LongA2_le_centralizer_torusElt
    {t : Kˣ} (ht : t ^ 3 = 1) :
    g2LongA2 K ≤ centralizer {torusElt .G2 K g2ir t} := by
  have key : ∀ (β : Fin Tag.G2.rank → ℤ), IsRoot .G2 β →
      (t ^ (∑ j, Tag.G2.cartan g2ir j * β j) : Kˣ) = 1 → ∀ x : K,
        pinnedX .G2 K β x ∈ centralizer {torusElt .G2 K g2ir t} := by
    intro β hβ h1 x
    refine mem_centralizer_singleton_iff.2 ?_
    have e := root_torus_conjugation g2ir hβ t x
    rw [h1, Units.val_one, one_mul] at e
    calc pinnedX .G2 K β x * torusElt .G2 K g2ir t =
        torusElt .G2 K g2ir t * pinnedX .G2 K β x * (torusElt .G2 K g2ir t)⁻¹ *
          torusElt .G2 K g2ir t := by rw [e]
      _ = torusElt .G2 K g2ir t * pinnedX .G2 K β x := by group
  have h3 : t ^ (3 : ℤ) = 1 := by rw [zpow_ofNat, ht]
  have hm3 : t ^ (-3 : ℤ) = 1 := by rw [zpow_neg, h3, inv_one]
  refine (closure_le _).2 ?_
  rintro _ (((((⟨x, rfl⟩ | ⟨x, rfl⟩) | ⟨x, rfl⟩) | ⟨x, rfl⟩) | ⟨x, rfl⟩) | ⟨x, rfl⟩)
  · exact key _ isRoot_g2a
      (by rw [show ∑ j, Tag.G2.cartan g2ir j * g2a j = -3 by decide]; exact hm3) x
  · exact key _ (LieType.Chevalley.IsRoot.neg isRoot_g2a)
      (by rw [show ∑ j, Tag.G2.cartan g2ir j * (-g2a) j = 3 by decide]; exact h3) x
  · exact key _ isRoot_g2b
      (by rw [show ∑ j, Tag.G2.cartan g2ir j * g2b j = 3 by decide]; exact h3) x
  · exact key _ (LieType.Chevalley.IsRoot.neg isRoot_g2b)
      (by rw [show ∑ j, Tag.G2.cartan g2ir j * (-g2b) j = -3 by decide]; exact hm3) x
  · exact key _ isRoot_g2c
      (by rw [show ∑ j, Tag.G2.cartan g2ir j * g2c j = 0 by decide, zpow_zero]) x
  · exact key _ (LieType.Chevalley.IsRoot.neg isRoot_g2c)
      (by rw [show ∑ j, Tag.G2.cartan g2ir j * (-g2c) j = 0 by decide, zpow_zero]) x

variable [Finite K] [CharP K 2]

theorem g2Centralizer_g2TorusR_eq_g2LongA2
    (hK4 : Nat.card K = 4) :
    g2Centralizer K (g2TorusR K : Set (ModGL .G2 K)) = g2LongA2 K := by
  refine le_antisymm (g2Centralizer_g2TorusR_le_g2LongA2 hK4) fun x hx =>
    mem_inf.2 ⟨g2LongA2_le_adjointGroup hx, mem_centralizer_iff.2 ?_⟩
  rintro _ ⟨t, rfl⟩
  have ht : t ^ 3 = 1 := by
    have h := pow_card_eq_one' (x := t)
    rwa [Nat.card_units, hK4] at h
  exact (mem_centralizer_singleton_iff.1 (g2LongA2_le_centralizer_torusElt ht hx)).symm

theorem eq_g2LongA2_of_levi
    (hK4 : Nat.card K = 4) {L : Subgroup (ModGL .G2 K)}
    (hLC : L ≤ adjointGroup .G2 K) (hLH : L ≤ centralizer (g2TorusR K : Set (ModGL .G2 K)))
    (hCdec : ∀ x ∈ g2Centralizer K (g2TorusR K : Set (ModGL .G2 K)), ∃ h ∈ g2TorusR K,
      h⁻¹ * x ∈ L) (hZL : (center ↥L).map L.subtype = g2TorusR K) : L = g2LongA2 K := by
  have hHL : g2TorusR K ≤ L := by
    rw [← hZL]
    exact map_subtype_le _
  rw [← g2Centralizer_g2TorusR_eq_g2LongA2 hK4]
  refine le_antisymm (fun x hx => mem_inf.2 ⟨hLC hx, hLH hx⟩) fun x hx => ?_
  obtain ⟨h, hh, hhx⟩ := hCdec x hx
  rw [show x = h * (h⁻¹ * x) by group]
  exact mul_mem (hHL hh) hhx

end Four

end CFSG.ComponentClassification.RankTwoExceptional
