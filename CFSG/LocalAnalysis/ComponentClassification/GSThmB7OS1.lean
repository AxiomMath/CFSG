module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Set
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSecHyp
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Core
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB8Statements

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace OS1

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X} {y : X}

theorem secImage_sup_secB0 {Y : Subgroup X} (hY : Y ≤ h.secG0 y) :
    h.secImage y (Y ⊔ h.secB0 y) = h.secImage y Y := by
  show ((Y ⊔ h.secB0 y).subgroupOf (h.secG0 y)).map (h.secMk y) =
    (Y.subgroupOf (h.secG0 y)).map (h.secMk y)
  rw [subgroupOf_sup hY (h.secB0_le_G0 y), Subgroup.map_sup]
  have h1 : ((h.secB0 y).subgroupOf (h.secG0 y)).map (h.secMk y) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, Hyp52.ker_secMk]
  rw [h1, sup_bot_eq]

omit [Finite X] in
theorem mem_normalizer_sup {A C : Subgroup X} {g : X} (hA : g ∈ normalizer (A : Set X))
    (hC : g ∈ normalizer (C : Set X)) : g ∈ normalizer ((A ⊔ C : Subgroup X) : Set X) := by
  apply mem_normalizer_of_conjugate_eq
  show (A ⊔ C).map (MulAut.conj g⁻¹).toMonoidHom = A ⊔ C
  rw [Subgroup.map_sup]
  exact congrArg₂ (· ⊔ ·) (conjugate_eq_of_mem_normalizer hA) (conjugate_eq_of_mem_normalizer hC)

theorem mem_normalizer_of_secMk {Y : Subgroup X} (hBY : h.secB0 y ≤ Y) (hYG : Y ≤ h.secG0 y)
    {g : ↥(h.secG0 y)} (hg : h.secMk y g ∈ normalizer (h.secImage y Y : Set (h.secBar y))) :
    (g : X) ∈ normalizer (Y : Set X) := by
  rw [Hyp52.normalizer_secImage hBY hYG] at hg
  exact (Hyp52.secMk_mem_secImage_iff (hBY.trans le_normalizer) g).mp hg

omit [Finite X] in
theorem mem_of_isSylowIn {Q Y : Subgroup X} (hQ : Seven.IsSylowIn Q Y) {g : X} (hgY : g ∈ Y)
    (hgN : g ∈ normalizer (Q : Set X)) (hg2 : IsPGroup 2 (zpowers g)) : g ∈ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQY, R, hR⟩ := hQ
  set g' : ↥Y := ⟨g, hgY⟩
  have hg'2 : IsPGroup 2 (zpowers g') := by
    have h1 : (zpowers g').map Y.subtype = zpowers g := by rw [MonoidHom.map_zpowers]; rfl
    exact (hg2.comap_of_injective Y.subtype Y.subtype_injective).to_le (by
      rw [← h1]
      exact le_comap_map _ _)
  have hg'N : g' ∈ normalizer ((R : Subgroup ↥Y) : Set ↥Y) := by
    rw [hR, mem_normalizer_iff]
    intro w
    show (w : X) ∈ Q ↔ g * w * g⁻¹ ∈ Q
    exact mem_normalizer_iff.mp hgN w
  have h1 := hg'2.inf_normalizer_sylow R
  have h2 : g' ∈ zpowers g' ⊓ normalizer (R : Set ↥Y) :=
    mem_inf.mpr ⟨mem_zpowers g', hg'N⟩
  rw [h1] at h2
  have h3 := (mem_inf.mp h2).2
  rw [hR] at h3
  exact h3

end OS1

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X} {y : X}

theorem secSylow_of_noFusion (haG : h.a ∈ h.secG0 y)
    (hA : ∀ g : X, g ∈ h.secG0 y →
      g ∈ normalizer ((h.secJ0 y ⊔ h.secB0 y : Subgroup X) : Set X) →
      g ∈ normalizer ((h.S ⊓ h.secG0 y : Subgroup X) : Set X) → IsPGroup 2 (zpowers g) →
      g * h.a * g⁻¹ * h.a⁻¹ ∈ h.secB0 y → g * h.a = h.a * g)
    (hB : Seven.IsSylowIn (h.S ⊓ h.secG0 y) (centralizer ({h.a} : Set X) ⊓ h.secG0 y)) :
    h.SecSylow y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup (h.secBar y) :=
    centralizer (h.secImage y (zpowers h.a) : Set (h.secBar y)) ⊓
      normalizer (h.secImage y (GSLit.fixedLayer h.J (h.secB0 y)) : Set (h.secBar y)) with hCdef
  set Sb := h.secImage y h.S with hSb
  have hJ0G : h.secJ0 y ≤ h.secG0 y := h.secJ0_le_G0 y
  have hJBG : h.secJ0 y ⊔ h.secB0 y ≤ h.secG0 y := sup_le hJ0G (h.secB0_le_G0 y)
  have hBS : h.secB0 y ≤ h.S ⊓ h.secG0 y :=
    le_inf ((h.secB0_le_B y).trans (h.B_le.trans inf_le_left)) (h.secB0_le_G0 y)
  have hSG : h.S ⊓ h.secG0 y ≤ h.secG0 y := inf_le_right
  have hNJ : normalizer (h.secImage y (GSLit.fixedLayer h.J (h.secB0 y)) : Set (h.secBar y)) =
      h.secImage y (normalizer ((h.secJ0 y ⊔ h.secB0 y : Subgroup X) : Set X)) := by
    rw [← Hyp52.normalizer_secImage le_sup_right hJBG, OS1.secImage_sup_secB0 hJ0G]
  have hNS : normalizer (Sb : Set (h.secBar y)) =
      h.secImage y (normalizer ((h.S ⊓ h.secG0 y : Subgroup X) : Set X)) := by
    rw [← Hyp52.normalizer_secImage hBS hSG, hSb, Hyp52.secImage_W_inf]
  have hSC : Sb ≤ C := by
    rintro _ ⟨s, hs, rfl⟩
    have hsS : (s : X) ∈ h.S := hs
    have hsa : (s : X) * h.a = h.a * s :=
      mem_centralizer_singleton_iff.mp ((mem_inf.mp (h.S_le hsS)).1)
    refine mem_inf.mpr ⟨?_, ?_⟩
    · rw [mem_centralizer_iff]
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (show (w : X) ∈ zpowers h.a from hw)
      have hcomm : s * w = w * s := by
        apply Subtype.ext
        simp only [coe_mul, ← hk]
        exact ((Commute.zpow_right (show Commute (s : X) h.a from hsa) k)).eq
      rw [← map_mul, ← map_mul, hcomm]
    · rw [hNJ]
      refine mem_map_of_mem _ (show s ∈ (normalizer ((h.secJ0 y ⊔ h.secB0 y : Subgroup X) :
        Set X)).subgroupOf (h.secG0 y) from ?_)
      exact OS1.mem_normalizer_sup (mem_normalizer_secJ0 s.2 ((mem_inf.mp (h.S_le hsS)).2)) s.2
  have hS2 : IsPGroup 2 Sb := (h.isPGroup_S.comap_subtype).map _
  set S' := Sb.subgroupOf C with hS'
  have hS'2 : IsPGroup 2 S' := hS2.comap_subtype
  obtain ⟨R, hRS⟩ := hS'2.exists_le_sylow
  refine ⟨R, ?_⟩
  by_contra hne
  have hlt : S'.subgroupOf R < ⊤ := by
    refine lt_of_le_of_ne le_top fun he => hne (le_antisymm ?_ hRS)
    intro w hw
    have : (⟨w, hw⟩ : ↥R) ∈ S'.subgroupOf R := he ▸ mem_top _
    exact this
  have hnil : Group.IsNilpotent ↥R := R.isPGroup'.isNilpotent
  obtain ⟨r, hrN, hrS⟩ := Set.exists_of_ssubset
    (Group.normalizerCondition_of_isNilpotent _ hlt)
  set gb : h.secBar y := ((r : ↥C) : h.secBar y) with hgb
  have hgbC : gb ∈ C := (r : ↥C).2
  have hfwd : ∀ (r' : ↥R), r' ∈ normalizer ((S'.subgroupOf R : Subgroup ↥R) : Set ↥R) →
      ∀ t ∈ Sb, ((r' : ↥C) : h.secBar y) * t * ((r' : ↥C) : h.secBar y)⁻¹ ∈ Sb := by
    intro r' hr' t ht
    have htR : (⟨t, hSC ht⟩ : ↥C) ∈ (R : Subgroup ↥C) := hRS ht
    have h1 := (mem_normalizer_iff.mp hr' ⟨⟨t, hSC ht⟩, htR⟩).mp ht
    exact h1
  have hgbN : gb ∈ normalizer (Sb : Set (h.secBar y)) := by
    rw [mem_normalizer_iff]
    intro t
    constructor
    · exact hfwd r hrN t
    · intro ht
      have h1 := hfwd r⁻¹ (inv_mem hrN) _ ht
      simp only [InvMemClass.coe_inv] at h1
      rwa [show gb⁻¹ * (gb * t * gb⁻¹) * gb⁻¹⁻¹ = t by group] at h1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp R.isPGroup') r
  have hgbk : gb ^ 2 ^ k = 1 := by
    have h1 : r ^ 2 ^ k = 1 := by rw [← hk, pow_orderOf_eq_one]
    have h2 := congrArg (fun w : ↥R => (((w : ↥C) : h.secBar y))) h1
    simpa using h2
  obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk'_surjective (h.secB0' y) gb
  have hg₀ : h.secMk y g₀ = gb := hg₀
  have hg₀2 : IsPGroup 2 (zpowers (g₀ : X)) := by
    have h1 : ((g₀ ^ 2 ^ k : ↥(h.secG0 y)) : X) ∈ h.secB0 y := by
      have h2 : g₀ ^ 2 ^ k ∈ h.secB0' y := by
        rw [← Hyp52.ker_secMk, MonoidHom.mem_ker, map_pow, hg₀, hgbk]
      exact h2
    obtain ⟨m, hm⟩ := (h.isPGroup_secB0 y) ⟨_, h1⟩
    have h2 : (g₀ : X) ^ 2 ^ (k + m) = 1 := by
      have h3 := congrArg Subtype.val hm
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h3
      rw [pow_add, pow_mul]
      exact h3
    rintro ⟨x, hx⟩
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    refine ⟨k + m, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h2, one_zpow]
  have hgN : (g₀ : X) ∈ normalizer ((h.secJ0 y ⊔ h.secB0 y : Subgroup X) : Set X) := by
    have h1 : gb ∈ normalizer (h.secImage y (GSLit.fixedLayer h.J (h.secB0 y)) :
        Set (h.secBar y)) := (mem_inf.mp hgbC).2
    rw [hNJ, ← hg₀] at h1
    exact (Hyp52.secMk_mem_secImage_iff (le_sup_right.trans le_normalizer) g₀).mp h1
  have hgS : (g₀ : X) ∈ normalizer ((h.S ⊓ h.secG0 y : Subgroup X) : Set X) := by
    rw [hNS, ← hg₀] at hgbN
    exact (Hyp52.secMk_mem_secImage_iff (hBS.trans le_normalizer) g₀).mp hgbN
  have hga : (g₀ : X) * h.a * (g₀ : X)⁻¹ * h.a⁻¹ ∈ h.secB0 y := by
    have h1 : gb ∈ centralizer (h.secImage y (zpowers h.a) : Set (h.secBar y)) :=
      (mem_inf.mp hgbC).1
    have haI : h.secMk y ⟨h.a, haG⟩ ∈ h.secImage y (zpowers h.a) :=
      mem_map_of_mem _ (show (⟨h.a, haG⟩ : ↥(h.secG0 y)) ∈ (zpowers h.a).subgroupOf _ from
        mem_zpowers h.a)
    have h2 := mem_centralizer_iff.mp h1 _ haI
    rw [← hg₀] at h2
    have h3 : g₀ * ⟨h.a, haG⟩ * g₀⁻¹ * (⟨h.a, haG⟩ : ↥(h.secG0 y))⁻¹ ∈ h.secB0' y := by
      rw [← Hyp52.ker_secMk, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
        ← h2]
      group
    exact h3
  have hgaC := hA g₀ g₀.2 hgN hgS hg₀2 hga
  have hgY : (g₀ : X) ∈ centralizer ({h.a} : Set X) ⊓ h.secG0 y :=
    mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hgaC, g₀.2⟩
  have hgSG := OS1.mem_of_isSylowIn hB hgY hgS hg₀2
  apply hrS
  show (⟨gb, hgbC⟩ : ↥C) ∈ S'
  show gb ∈ Sb
  rw [← hg₀]
  exact mem_map_of_mem _ (show g₀ ∈ h.S.subgroupOf (h.secG0 y) from (mem_inf.mp hgSG).1)

end Hyp52

namespace Seven

variable {X : Type} [Group X] [Finite X]

@[expose] def CaseTwoSylowStatement71 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ u v : X, u * v ≠ v * u) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ h : Hyp52 X, GSMaximalUnbalancingTriple h.a h.x h.J →
      GSIsoAt h.a h.J →
      ¬ ConclusionB1 h.J → ¬ ConclusionB2a h.a h.J → h.Sec8Case →
      ∀ y : X, h.IsX0Min y → ∀ h' : Hyp52 X, Prop62Output h h' y →
      ∀ b : X, Lemma61Case2 h' y b →
        IsSylowIn (h'.S ⊓ h'.secG0 y) (centralizer ({h'.a} : Set X) ⊓ h'.secG0 y)

end Seven

end CFSG.ComponentClassification.GSThmB
