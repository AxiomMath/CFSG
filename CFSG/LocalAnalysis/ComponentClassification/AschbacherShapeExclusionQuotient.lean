module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Open.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.ShapeExclusion

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G] (A : Subgroup G)

@[expose] noncomputable def bar (g : G) : A ⧸ center A := by
  classical
  exact if hg : g ∈ A then QuotientGroup.mk ⟨g, hg⟩ else 1

variable {A}

theorem bar_of_mem {g : G} (hg : g ∈ A) : bar A g = QuotientGroup.mk ⟨g, hg⟩ := by
  simp [bar, hg]

theorem bar_mul {g h : G} (hg : g ∈ A) (hh : h ∈ A) : bar A (g * h) = bar A g * bar A h := by
  rw [bar_of_mem (mul_mem hg hh), bar_of_mem hg, bar_of_mem hh, ← QuotientGroup.mk_mul]
  rfl

theorem bar_one : bar A (1 : G) = 1 := by
  rw [bar_of_mem (one_mem A)]
  rfl

theorem bar_inv {g : G} (hg : g ∈ A) : bar A g⁻¹ = (bar A g)⁻¹ := by
  rw [bar_of_mem (inv_mem hg), bar_of_mem hg, ← QuotientGroup.mk_inv]
  rfl

theorem bar_pow {g : G} (hg : g ∈ A) (n : ℕ) : bar A (g ^ n) = bar A g ^ n := by
  rw [bar_of_mem (pow_mem hg n), bar_of_mem hg, ← QuotientGroup.mk_pow]
  rfl

theorem bar_zpow {g : G} (hg : g ∈ A) (n : ℤ) : bar A (g ^ n) = bar A g ^ n := by
  rw [bar_of_mem (zpow_mem hg n), bar_of_mem hg, ← QuotientGroup.mk_zpow]
  rfl

theorem bar_eq_one_iff {g : G} (hg : g ∈ A) : bar A g = 1 ↔ g ∈ centralizer (A : Set G) := by
  rw [bar_of_mem hg, QuotientGroup.eq_one_iff, mem_center_iff, mem_centralizer_iff]
  constructor
  · intro h a ha
    exact congrArg Subtype.val (h ⟨a, ha⟩)
  · intro h a
    exact Subtype.ext (h a a.2)

theorem bar_eq_bar_iff {g h : G} (hg : g ∈ A) (hh : h ∈ A) :
    bar A g = bar A h ↔ g⁻¹ * h ∈ centralizer (A : Set G) := by
  rw [← bar_eq_one_iff (mul_mem (inv_mem hg) hh), bar_mul (inv_mem hg) hh, bar_inv hg,
    inv_mul_eq_one]

theorem bar_surjective (q : A ⧸ center A) : ∃ g ∈ A, bar A g = q := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨a, a.2, bar_of_mem a.2⟩

@[expose] noncomputable def sylowBar [Finite G] (S₀ : Sylow 2 A) : Sylow 2 (A ⧸ center A) :=
  S₀.mapSurjective (QuotientGroup.mk'_surjective (center A))

theorem mem_sylowBar_iff [Finite G] (S₀ : Sylow 2 A) {q : A ⧸ center A} :
    q ∈ (sylowBar S₀ : Subgroup (A ⧸ center A)) ↔
      ∃ g ∈ (S₀ : Subgroup A).map A.subtype, bar A g = q := by
  rw [sylowBar, Sylow.coe_mapSurjective]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ⟨a, ha, rfl⟩, bar_of_mem a.2⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, (bar_of_mem a.2).symm⟩

theorem bar_mem_sylowBar [Finite G] (S₀ : Sylow 2 A) {g : G}
    (hg : g ∈ (S₀ : Subgroup A).map A.subtype) :
    bar A g ∈ (sylowBar S₀ : Subgroup (A ⧸ center A)) :=
  (mem_sylowBar_iff S₀).2 ⟨g, hg, rfl⟩

theorem card_sylowBar [Finite G] (S₀ : Sylow 2 A) :
    Nat.card (sylowBar S₀ : Subgroup (A ⧸ center A)) *
        Nat.card ((S₀ : Subgroup A).map A.subtype ⊓ centralizer (A : Set G) : Subgroup G) =
      Nat.card ((S₀ : Subgroup A).map A.subtype) := by
  set S := (S₀ : Subgroup A).map A.subtype with hS
  set φ : (S₀ : Subgroup A) →* A ⧸ center A :=
    (QuotientGroup.mk' (center A)).comp (S₀ : Subgroup A).subtype with hφ
  have hrange : φ.range = (sylowBar S₀ : Subgroup (A ⧸ center A)) := by
    rw [sylowBar, Sylow.coe_mapSurjective, hφ, MonoidHom.range_comp, range_subtype]
  have hker : Nat.card φ.ker = Nat.card (S ⊓ centralizer (A : Set G) : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun a => ⟨((a : (S₀ : Subgroup A)) : A), ?_⟩
        invFun := fun w => ⟨⟨⟨w, ?_⟩, ?_⟩, ?_⟩
        left_inv := fun a => rfl
        right_inv := fun w => rfl }
    · obtain ⟨a, ha⟩ := a
      refine mem_inf.2 ⟨⟨a, a.2, rfl⟩, ?_⟩
      have h1 : φ a = 1 := ha
      rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        mem_center_iff] at h1
      rw [mem_centralizer_iff]
      intro b hb
      exact congrArg Subtype.val (h1 ⟨b, hb⟩)
    · exact map_subtype_le _ (mem_inf.1 w.2).1
    · obtain ⟨a, ha, haw⟩ := (mem_inf.1 w.2).1
      have : a = ⟨w, map_subtype_le _ (mem_inf.1 w.2).1⟩ := Subtype.ext haw
      rw [← this]
      exact ha
    · change (QuotientGroup.mk' (center A)) ⟨w, _⟩ = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_center_iff]
      intro b
      exact Subtype.ext (mem_centralizer_iff.1 (mem_inf.1 w.2).2 b b.2)
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hrange, hker] at h1
  rw [hS, Subgroup.card_map_of_injective A.subtype_injective, h1]

@[expose] noncomputable def conjA {t : G} (ht : t ∈ normalizer (A : Set G)) : A ≃* A where
  toFun a := ⟨t * a * t⁻¹, (mem_normalizer_iff.1 ht a).1 a.2⟩
  invFun a := ⟨t⁻¹ * a * t, by
    have := (mem_normalizer_iff.1 (inv_mem ht) a).1 a.2
    simpa using this⟩
  left_inv a := Subtype.ext (by simp only; group)
  right_inv a := Subtype.ext (by simp only; group)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

@[expose] noncomputable def conjBar {t : G} (ht : t ∈ normalizer (A : Set G)) :
    (A ⧸ center A) ≃* (A ⧸ center A) :=
  QuotientGroup.congr (center A) (center A) (conjA ht) (map_center_eq _)

theorem conjBar_bar {t : G} (ht : t ∈ normalizer (A : Set G)) {g : G} (hg : g ∈ A) :
    conjBar ht (bar A g) = bar A (t * g * t⁻¹) := by
  rw [bar_of_mem hg, bar_of_mem ((mem_normalizer_iff.1 ht g).1 hg), conjBar,
    QuotientGroup.congr_mk]
  rfl

theorem commutator_eq_self_of_quasisimple (hA : CFSG.Open.IsQuasisimple A) : ⁅A, A⁆ = A := by
  rw [← Subgroup.map_subtype_commutator, hA.1, ← MonoidHom.range_eq_map, range_subtype]

theorem coprime_relIndex [Finite G] (S₀ : Sylow 2 A) :
    Nat.Coprime 2 (((S₀ : Subgroup A).map A.subtype).relIndex A) := by
  have : ((S₀ : Subgroup A).map A.subtype).subgroupOf A = S₀ :=
    Subgroup.comap_map_eq_self_of_injective A.subtype_injective _
  rw [Subgroup.relIndex, this]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 S₀.not_dvd_index

theorem nonabelian_bar (hA : CFSG.Open.IsQuasisimple A) :
    ∃ a b : A ⧸ center A, a * b ≠ b * a := by
  have := hA.2
  by_contra hcon
  push Not at hcon
  have hle : commutator A ≤ center A := by
    rw [_root_.commutator_def, commutator_le]
    intro a _ b _
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (center A) ⁅a, b⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcon _ _
  rw [hA.1] at hle
  obtain ⟨q, hq⟩ := exists_ne (1 : A ⧸ center A)
  apply hq
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  exact (QuotientGroup.eq_one_iff a).2 (hle (mem_top a))

theorem bar_injective_of_trivial [Finite G] (S₀ : Sylow 2 A)
    (hW : ∀ w ∈ (S₀ : Subgroup A).map A.subtype, w ∈ centralizer (A : Set G) → w = 1)
    {g h : G} (hg : g ∈ (S₀ : Subgroup A).map A.subtype) (hh : h ∈ (S₀ : Subgroup A).map A.subtype)
    (hgh : bar A g = bar A h) : g = h := by
  have hSA : (S₀ : Subgroup A).map A.subtype ≤ A := map_subtype_le _
  rw [bar_eq_bar_iff (hSA hg) (hSA hh)] at hgh
  have := hW _ (mul_mem (inv_mem hg) hh) hgh
  rw [inv_mul_eq_one] at this
  exact this

theorem orderOf_bar_of_trivial [Finite G] (S₀ : Sylow 2 A)
    (hW : ∀ w ∈ (S₀ : Subgroup A).map A.subtype, w ∈ centralizer (A : Set G) → w = 1)
    {g : G} (hg : g ∈ (S₀ : Subgroup A).map A.subtype) : orderOf (bar A g) = orderOf g := by
  have hSA : (S₀ : Subgroup A).map A.subtype ≤ A := map_subtype_le _
  rw [orderOf_eq_orderOf_iff]
  intro n
  rw [← bar_pow (hSA hg), ← bar_one]
  constructor
  · intro h1
    exact bar_injective_of_trivial S₀ hW (pow_mem hg n) (one_mem _) h1
  · intro h1
    rw [h1]

end CFSG.ComponentClassification.AschbacherKnownGroup.ShapeExclusion
