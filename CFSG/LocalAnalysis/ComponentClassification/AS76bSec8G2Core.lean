module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Radical

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.Blueprint.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
open scoped Pointwise commutatorElement

section Core

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem g2RankOne_le_shortCent
    : g2RankOne K g2ia ≤ g2ShortCent K := by
  obtain ⟨-, -, -, hsup, -⟩ := even_G2_highest_short_root_centralizer K
  intro l hl
  have h : l ∈ g2ShortRadical K ⊔ g2RankOne K g2ia := mem_sup_right hl
  rw [← hsup] at h
  exact h

theorem g2ShortRadical_le_shortCent
    : g2ShortRadical K ≤ g2ShortCent K := by
  obtain ⟨-, -, -, hsup, -⟩ := even_G2_highest_short_root_centralizer K
  intro l hl
  have h : l ∈ g2ShortRadical K ⊔ g2RankOne K g2ia := mem_sup_left hl
  rw [← hsup] at h
  exact h

theorem g2RankOne_isPerfect_isSimpleGroup
    (hK4 : 4 ≤ Nat.card K) :
    Group.IsPerfect ↥(g2RankOne K g2ia) ∧ IsSimpleGroup ↥(g2RankOne K g2ia) ∧
      Nontrivial ↥(g2RankOne K g2ia) := by
  obtain ⟨-, -, -, -, -, -, -, ⟨ρ, -, -, hrange, hinj⟩, -⟩ :=
    even_G2_highest_short_root_centralizer K
  have := Fintype.ofFinite K
  have h4 : ∃ s : Finset K, s.card = 4 := by
    have hle : 4 ≤ (Finset.univ : Finset K).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact hK4
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hle
    exact ⟨s, hs⟩
  obtain ⟨hnt, hsimple, -⟩ :=
    CFSG.LinearGroups.linear_projective_simple (K := K) (n := 2) le_rfl (Or.inr h4)
  have hperf := CFSG.LinearGroups.linear_projective_perfect (K := K) (n := 2) le_rfl (Or.inr h4)
  let e₁ := CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := K)
  let e₂ : LieType.Chevalley.SL2 K ≃* ↥(g2RankOne K g2ia) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  let e := e₁.trans e₂
  have := hperf
  have := hsimple
  have := hnt
  exact ⟨Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective, e.symm.isSimpleGroup,
    e.injective.nontrivial⟩

theorem g2RankOne_commutator
    (hK4 : 4 ≤ Nat.card K) :
    ⁅g2RankOne K g2ia, g2RankOne K g2ia⁆ = g2RankOne K g2ia :=
  have := (g2RankOne_isPerfect_isSimpleGroup hK4).1
  Subgroup.commutator_eq_self

theorem g2RankOne_le_commutator
    (hK4 : 4 ≤ Nat.card K) :
    g2RankOne K g2ia ≤ ⁅g2ShortCent K, g2ShortCent K⁆ := by
  rw [← g2RankOne_commutator hK4]
  exact commutator_mono g2RankOne_le_shortCent g2RankOne_le_shortCent

theorem g2BCGroup_le_commutator
    : g2BCGroup K ≤ ⁅g2ShortCent K, g2ShortCent K⁆ := by
  have hXa : pinnedX .G2 K g2a 1 ∈ g2ShortCent K := by
    refine g2RankOne_le_shortCent ?_
    rw [g2RankOne_a_eq]
    exact subset_closure (Or.inl ⟨1, rfl⟩)
  have hXna : pinnedX .G2 K g2na 1 ∈ g2ShortCent K := by
    refine g2RankOne_le_shortCent ?_
    rw [g2RankOne_a_eq]
    exact subset_closure (Or.inr ⟨1, rfl⟩)
  have hA : ∀ y z : K, g2N 0 0 0 0 y z ∈ g2ShortCent K := fun y z =>
    g2ShortRadical_le_shortCent (g2N_mem_g2ShortRadical 0 y z)
  have hc : ∀ y : K, g2N 0 0 0 0 0 y ∈ ⁅g2ShortCent K, g2ShortCent K⁆ := by
    intro y
    have h1 := commutator_mem_commutator hXa (hA y 0)
    have e : ⁅pinnedX .G2 K g2a 1, g2N 0 0 0 0 y 0⁆ = g2N 0 0 0 0 0 y := by
      rw [commutatorElement_def]
      obtain ⟨-, -, h⟩ := actsOnShort_pinnedX_a (K := K) 1
      have h2 := h ![y, 0]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h2
      rw [h2, g2N_zero_inv, g2N_zero_mul_g2N_zero]
      refine g2N_eq_g2N rfl (by ring) (by ring) (by ring) ?_ ?_
      · simp [shMa, CharTwo.add_self_eq_zero]
      · simp [shMa, CharTwo.add_self_eq_zero]
    rw [e] at h1
    exact h1
  have hb : ∀ z : K, g2N 0 0 0 0 z 0 ∈ ⁅g2ShortCent K, g2ShortCent K⁆ := by
    intro z
    have h1 := commutator_mem_commutator hXna (hA 0 z)
    have e : ⁅pinnedX .G2 K g2na 1, g2N 0 0 0 0 0 z⁆ = g2N 0 0 0 0 z 0 := by
      rw [commutatorElement_def]
      obtain ⟨-, -, h⟩ := actsOnShort_pinnedX_na (K := K) 1
      have h2 := h ![0, z]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h2
      rw [h2, g2N_zero_inv, g2N_zero_mul_g2N_zero]
      refine g2N_eq_g2N rfl (by ring) (by ring) (by ring) ?_ ?_
      · simp [shMa, shSwap]
      · simp [shMa, shSwap, CharTwo.add_self_eq_zero]
    rw [e] at h1
    exact h1
  rintro _ ⟨y, z, rfl⟩
  have e : g2N 0 0 0 0 y z = g2N 0 0 0 0 y 0 * g2N 0 0 0 0 0 z := by
    rw [g2N_zero_mul_g2N_zero]
    exact g2N_eq_g2N rfl (by ring) (by ring) (by ring) (by ring) (by ring)
  rw [e]
  exact mul_mem (hb y) (hc z)

theorem g2ShortRadical_inf_commutator
    {x : ModGL .G2 K} (hx : x ∈ g2ShortRadical K)
    (hx' : x ∈ ⁅g2ShortCent K, g2ShortCent K⁆) : x ∈ g2BCGroup K := by
  obtain ⟨D, E, F, rfl⟩ := hx
  have hbc : g2N 0 0 0 0 E F ∈ ⁅g2ShortCent K, g2ShortCent K⁆ :=
    g2BCGroup_le_commutator ⟨E, F, rfl⟩
  have e : pinnedX .G2 K g2v D = g2N 0 0 0 D E F * (g2N 0 0 0 0 E F)⁻¹ := by
    rw [g2N_zero_inv, pinnedX_v_eq_g2N, g2N_zero_mul_g2N_zero]
    exact g2N_eq_g2N rfl (by ring) (by ring) (by ring) (by char2_ring) (by char2_ring)
  have hv : pinnedX .G2 K g2v D ∈ rootSubgroup .G2 K g2v ⊓ ⁅g2ShortCent K, g2ShortCent K⁆ :=
    mem_inf.2 ⟨mem_rootSubgroup.2 ⟨D, rfl⟩, by rw [e]; exact mul_mem hx' (inv_mem hbc)⟩
  rw [rootSubgroup_v_inf_commutator_eq_bot, mem_bot] at hv
  have hD : D = 0 := pinnedX_injective .G2 K g2v (by rw [hv, pinnedX_zero])
  subst hD
  exact ⟨E, F, rfl⟩

theorem conj_mem_g2BCGroup
    {c w : ModGL .G2 K} (hc : c ∈ g2ShortCent K)
    (hw : w ∈ g2BCGroup K) : c * w * c⁻¹ ∈ g2BCGroup K := by
  obtain ⟨-, -, -, -, hset, -⟩ := even_G2_highest_short_root_centralizer K
  have hc' : c ∈ ((adjointGroup .G2 K ⊓ Subgroup.centralizer {pinnedX .G2 K g2v 1} :
      Subgroup (ModGL .G2 K)) : Set (ModGL .G2 K)) := hc
  rw [hset] at hc'
  obtain ⟨q, hq, l, hl, rfl⟩ := hc'
  obtain ⟨y, z, rfl⟩ := hw
  obtain ⟨T, -, -, hT⟩ := exists_actsOnShort hl
  have h1 := hT ![y, z]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1
  have h2 : q * g2N 0 0 0 0 (T ![y, z] 0) (T ![y, z] 1) * q⁻¹ =
      g2N 0 0 0 0 (T ![y, z] 0) (T ![y, z] 1) := by
    rw [(commute_of_mem_g2ShortRadical hq (g2N_mem_g2ShortRadical 0 _ _)).eq, mul_inv_cancel_right]
  rw [show q * l * g2N 0 0 0 0 y z * (q * l)⁻¹ = q * (l * g2N 0 0 0 0 y z * l⁻¹) * q⁻¹ by group,
    h1, h2]
  exact ⟨_, _, rfl⟩

theorem le_g2BCGroup_of_normal
    (hK4 : 4 ≤ Nat.card K) {N : Subgroup (ModGL .G2 K)}
    (hN : N ≤ ⁅g2ShortCent K, g2ShortCent K⁆) (hN2 : IsPGroup 2 N)
    (hLN : ∀ l ∈ g2RankOne K g2ia, ∀ n ∈ N, l * n * l⁻¹ ∈ N) : N ≤ g2BCGroup K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL .G2 K) := LieType.Chevalley.finite_modGL
  obtain ⟨hperf, hsimple, hnt⟩ := g2RankOne_isPerfect_isSimpleGroup hK4
  obtain ⟨-, -, hAel, -, hset, hLA, -⟩ := even_G2_highest_short_root_centralizer K
  have hAv2 : IsPGroup 2 (g2ShortRadical K) := by
    rintro ⟨a, D, E, F, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, pow_one, sq, g2N_mul_self, OneMemClass.coe_one, ← g2N_zero]
    exact g2N_eq_g2N rfl rfl (by ring) (by ring) (by ring) (by ring)
  have hSS : ⁅g2ShortCent K, g2ShortCent K⁆ ≤ g2ShortCent K :=
    (commutator_le).2 fun a ha b hb => RankTwoL3Even.commutatorElement_mem' ha hb
  have hmul : ∀ n ∈ g2ShortCent K, ∃ q ∈ g2ShortRadical K, ∃ l ∈ g2RankOne K g2ia, q * l = n := by
    intro n hn
    have hn' : n ∈ ((adjointGroup .G2 K ⊓ Subgroup.centralizer {pinnedX .G2 K g2v 1} :
        Subgroup (ModGL .G2 K)) : Set (ModGL .G2 K)) := hn
    rw [hset, Set.mem_mul] at hn'
    exact hn'
  have hNA : N ≤ normalizer (g2ShortRadical K : Set (ModGL .G2 K)) := by
    intro n hnN
    obtain ⟨q, hq, l, hl, rfl⟩ := hmul n (hSS (hN hnN))
    exact mul_mem (le_normalizer hq) (hLA hl)
  have hP2 : IsPGroup 2 (N ⊔ g2ShortRadical K : Subgroup (ModGL .G2 K)) :=
    IsPGroup.to_sup_of_normal_right' hN2 hAv2 hNA
  have hLnorm : ∀ l ∈ g2RankOne K g2ia,
      l ∈ normalizer ((N ⊔ g2ShortRadical K : Subgroup (ModGL .G2 K)) : Set (ModGL .G2 K)) := by
    intro l hl
    refine RankTwoClassical.mem_normalizer_sup ?_ (hLA hl)
    refine mem_normalizer_iff.2 fun n => ⟨fun hn => hLN l hl n hn, fun hn => ?_⟩
    have h1 := hLN l⁻¹ (inv_mem hl) _ hn
    rwa [inv_inv, show l⁻¹ * (l * n * l⁻¹) * l = n by group] at h1
  set P : Subgroup ↥(g2RankOne K g2ia) :=
    ((N ⊔ g2ShortRadical K) ⊓ g2RankOne K g2ia).subgroupOf (g2RankOne K g2ia) with hP
  have hPn : P.Normal := by
    refine ⟨fun p hp l => ?_⟩
    rw [hP, mem_subgroupOf] at hp ⊢
    obtain ⟨hp1, hp2⟩ := mem_inf.1 hp
    refine mem_inf.2 ⟨(mem_normalizer_iff.1 (hLnorm l l.2) p).1 hp1, ?_⟩
    exact mul_mem (mul_mem l.2 hp2) (inv_mem l.2)
  have hPbot : P = ⊥ := by
    have := hsimple
    have := hPn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with h | h
    · exact h
    · exfalso
      have hL2 : IsPGroup 2 ↥(g2RankOne K g2ia) := by
        intro l
        have hl : (l : ModGL .G2 K) ∈ N ⊔ g2ShortRadical K := by
          have : l ∈ P := by rw [h]; exact mem_top l
          rw [hP, mem_subgroupOf] at this
          exact (mem_inf.1 this).1
        obtain ⟨k, hk⟩ := hP2 ⟨l, hl⟩
        exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
      have := hperf
      have := hnt
      exact Group.IsPerfect.not_isNilpotent (G := ↥(g2RankOne K g2ia)) hL2.isNilpotent
  intro n hnN
  obtain ⟨q, hq, l, hl, hqln⟩ := hmul n (hSS (hN hnN))
  have hlP : (⟨l, hl⟩ : ↥(g2RankOne K g2ia)) ∈ P := by
    rw [hP, mem_subgroupOf]
    refine mem_inf.2 ⟨?_, hl⟩
    have e : l = q⁻¹ * n := by rw [← hqln]; group
    show l ∈ N ⊔ g2ShortRadical K
    rw [e]
    exact mul_mem (mem_sup_right (inv_mem hq)) (mem_sup_left hnN)
  rw [hPbot, mem_bot] at hlP
  have hl1 : l = 1 := congrArg Subtype.val hlP
  rw [hl1, mul_one] at hqln
  rw [← hqln] at hnN ⊢
  exact g2ShortRadical_inf_commutator hq (hN hnN)

end Core

end CFSG.ComponentClassification.RankTwoExceptional
