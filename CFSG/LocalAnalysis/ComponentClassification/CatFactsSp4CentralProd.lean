module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingSymmetric
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.ComponentClassification.CatFactsSp4

open Subgroup CFSG.ComponentClassification

variable {G : Type*} [Group G]

theorem commutator_eq_of_isPComponent {p : ℕ} {X M : Subgroup G} (hMX : M ≤ X)
    (hM : CFSG.IsPComponent p (M.subgroupOf X)) : ⁅M, M⁆ = M := by
  have h := Subgroup.isPerfect_iff.mp (CatalogueBAlternating.pComponent_perfect hM)
  have h2 := congrArg (Subgroup.map X.subtype) h
  rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hMX] at h2

theorem ne_bot_of_isPComponent {p : ℕ} {X M : Subgroup G}
    (hM : CFSG.IsPComponent p (M.subgroupOf X)) : M ≠ ⊥ := by
  have : Nontrivial (M.subgroupOf X) := CatalogueBAlternating.pComponent_nontrivial hM
  intro hbot
  rw [hbot, Subgroup.bot_subgroupOf] at this
  exact not_nontrivial _ this

theorem exists_mul_ne_of_isQuasisimple {E : Subgroup G} (hE : CFSG.IsQuasisimple E) :
    ∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x := by
  obtain ⟨-, -, a, b, hab⟩ := hE
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨x, x.2, y, y.2, fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext h

variable [Finite G]

theorem pComponent_eq_of_centralProduct {p : ℕ} {C X E₁ E₂ M : Subgroup G} (hXC : X ≤ C)
    (hXn : ∀ c ∈ C, ∀ x ∈ X, c * x * c⁻¹ ∈ X) (hE₁X : E₁ ≤ X) (hE₂X : E₂ ≤ X)
    (hE₁n : ∀ x ∈ X, ∀ e ∈ E₁, x * e * x⁻¹ ∈ E₁) (hE₂n : ∀ x ∈ X, ∀ e ∈ E₂, x * e * x⁻¹ ∈ E₂)
    (hq₁ : CFSG.IsQuasisimple E₁) (hq₂ : CFSG.IsQuasisimple E₂)
    (hgen : ∀ x ∈ X, ∃ a ∈ E₁, ∃ b ∈ E₂, x = a * b)
    (hcomm : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a)
    (hc₁ : ∀ x ∈ X, (∀ b ∈ E₂, x * b = b * x) → x ∈ E₁)
    (hc₂ : ∀ x ∈ X, (∀ a ∈ E₁, x * a = a * x) → x ∈ E₂)
    (hperf : ∀ N : Subgroup G, N ≤ C → ⁅N, N⁆ = N → N ≤ X)
    (hMC : M ≤ C) (hM : CFSG.IsPComponent p (M.subgroupOf C)) : M = E₁ ∨ M = E₂ := by
  have hMX : M ≤ X := hperf M hMC (commutator_eq_of_isPComponent hMC hM)
  have hM1 := ne_bot_of_isPComponent hM
  have hMperf := commutator_eq_of_isPComponent hMC hM
  have hcomp : ∀ E : Subgroup G, E ≤ X → (∀ x ∈ X, ∀ e ∈ E, x * e * x⁻¹ ∈ E) →
      CFSG.IsQuasisimple E → CFSG.IsComponent (E.subgroupOf C) := by
    intro E hEX hEn hq
    refine ⟨(LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (Subgroup.subgroupOfEquivOfLe (hEX.trans hXC))).mpr hq, ?_⟩
    refine Subgroup.IsSubnormal.step _ (X.subgroupOf C) (Subgroup.subgroupOf_mono _ hEX)
      ?_ ?_
    · refine (Subgroup.Normal.isSubnormal ?_)
      exact (normal_subgroupOf_iff hXC).mpr fun x c hx hc => hXn c hc x hx
    · rw [normal_subgroupOf_iff (Subgroup.subgroupOf_mono _ hEX)]
      intro e x he hx
      exact hEn x hx e he
  have hE₁c := hcomp E₁ hE₁X hE₁n hq₁
  have hE₂c := hcomp E₂ hE₂X hE₂n hq₂
  have hMsub : (M.subgroupOf C).IsSubnormal := hM.choose_spec.2.1
  have hdich : ∀ E : Subgroup G, E ≤ C → CFSG.IsComponent (E.subgroupOf C) →
      E ≤ M ∨ ∀ e ∈ E, ∀ m ∈ M, e * m = m * e := by
    intro E hEC hE
    rcases LocalComponents.subnormal_contains_or_commutes (E.subgroupOf C) (M.subgroupOf C)
        ((CFSG.isComponent_iff_open _).mp hE) (Components.chain_of_mathlib_subnormal hMsub)
      with h | h
    · left
      intro e he
      exact h (show (⟨e, hEC he⟩ : C) ∈ E.subgroupOf C from he)
    · right
      intro e he m hm
      have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
        (show (⟨e, hEC he⟩ : C) ∈ E.subgroupOf C from he)
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hc ⟨m, hMC hm⟩ hm).symm
  have hall : ∀ m ∈ M, ∀ m' ∈ M, (∀ a ∈ E₁, m * a = a * m) → (∀ b ∈ E₂, m * b = b * m) →
      m * m' = m' * m := by
    intro m _ m' hm' ha hb
    obtain ⟨a, haE, b, hbE, rfl⟩ := hgen m' (hMX hm')
    rw [← mul_assoc, ha a haE, mul_assoc, hb b hbE, mul_assoc]
  rcases hdich E₁ (hE₁X.trans hXC) hE₁c with h1 | h1 <;>
    rcases hdich E₂ (hE₂X.trans hXC) hE₂c with h2 | h2
  ·
    exfalso
    obtain ⟨Kc, hKc, -, hmap, hmin⟩ := hM
    set q := QuotientGroup.mk' (CFSG.pPrimeCore p C) with hq
    have hlt : ∀ E : Subgroup G, E ≤ M → (∃ x ∈ M, x ∉ E) →
        E.subgroupOf C < M.subgroupOf C := by
      rintro E hEM ⟨x, hxM, hxE⟩
      refine lt_of_le_of_ne (Subgroup.subgroupOf_mono _ hEM) fun heq => hxE ?_
      have : (⟨x, hMC hxM⟩ : C) ∈ E.subgroupOf C := heq ▸ hxM
      exact this
    have hw : ∀ E E' : Subgroup G, CFSG.IsQuasisimple E' →
        (∀ a ∈ E, ∀ b ∈ E', a * b = b * a) → ∃ x ∈ E', x ∉ E := by
      intro E E' hq' hc
      by_contra hcon
      push Not at hcon
      obtain ⟨x, hx, y, hy, hxy⟩ := exists_mul_ne_of_isQuasisimple hq'
      exact hxy (hc x (hcon x hx) y hy)
    obtain ⟨x₂, hx₂, hx₂'⟩ := hw E₁ E₂ hq₂ hcomm
    obtain ⟨x₁, hx₁, hx₁'⟩ := hw E₂ E₁ hq₁ fun a ha b hb => (hcomm b hb a ha).symm
    have hne₁ := hmin _ (hlt E₁ h1 ⟨x₂, h2 hx₂, hx₂'⟩) hE₁c.2
    have hne₂ := hmin _ (hlt E₂ h2 ⟨x₁, h1 hx₁, hx₁'⟩) hE₂c.2
    have hcen : ∀ E : Subgroup G, E ≤ M → (∀ x ∈ X, ∀ e ∈ E, x * e * x⁻¹ ∈ E) →
        (E.subgroupOf C).map q ≠ Kc → ∀ e : C, (e : G) ∈ E → ∀ k ∈ Kc, q e * k = k * q e := by
      intro E hEM hEn hne e he k hk
      have hle : (E.subgroupOf C).map q ≤ Kc :=
        hmap ▸ Subgroup.map_mono (Subgroup.subgroupOf_mono _ hEM)
      have hnorm : (((E.subgroupOf C).map q).subgroupOf Kc).Normal := by
        rw [normal_subgroupOf_iff hle]
        rintro _ k ⟨e', he', rfl⟩ hk
        rw [← hmap] at hk
        obtain ⟨m, hm, rfl⟩ := hk
        refine ⟨m * e' * m⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
        exact hEn m (hMX hm) e' he'
      rcases LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hKc.1 hnorm with htop | hc
      · exfalso
        apply hne
        apply le_antisymm hle
        intro k hk
        exact Subgroup.subgroupOf_eq_top.mp htop hk
      · have hmem : (⟨q e, hle ⟨e, he, rfl⟩⟩ : Kc) ∈ ((E.subgroupOf C).map q).subgroupOf Kc :=
          ⟨e, he, rfl⟩
        have h := Subgroup.mem_center_iff.mp (hc hmem) ⟨k, hk⟩
        exact (congrArg Subtype.val h).symm
    obtain ⟨k₁, hk₁, k₂, hk₂, hk⟩ := exists_mul_ne_of_isQuasisimple hKc.1
    apply hk
    rw [← hmap] at hk₁
    obtain ⟨m, hm, rfl⟩ := hk₁
    obtain ⟨a, ha, b, hb, hab⟩ := hgen m (hMX hm)
    have hm' : m = ⟨a, hE₁X.trans hXC ha⟩ * ⟨b, hE₂X.trans hXC hb⟩ := Subtype.ext hab
    rw [hm', map_mul, mul_assoc, hcen E₂ h2 hE₂n hne₂ _ hb k₂ hk₂, ← mul_assoc,
      hcen E₁ h1 hE₁n hne₁ _ ha k₂ hk₂, mul_assoc]
  · left
    refine le_antisymm (fun m hm => hc₁ m (hMX hm) fun b hb => (h2 b hb m hm).symm) h1
  · right
    refine le_antisymm (fun m hm => hc₂ m (hMX hm) fun a ha => (h1 a ha m hm).symm) h2
  · exfalso
    apply hM1
    have hab : ⁅M, M⁆ = ⊥ := by
      rw [eq_bot_iff, commutator_le]
      intro m hm m' hm'
      rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hall m hm m' hm' (fun a ha => (h1 a ha m hm).symm) (fun b hb => (h2 b hb m hm).symm)
    rw [← hMperf, hab]

end CFSG.ComponentClassification.CatFactsSp4
