module

public import CFSG.LieType.Chevalley.SimpleRootComplement
public import Mathlib.GroupTheory.Nilpotent

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley
open scoped commutatorElement

variable {τ : Tag}

theorem commutator_closure_le_of_le_normalizer {G : Type*} [Group G] {s t : Set G}
    {N G₀ : Subgroup G} (hs : Subgroup.closure s ≤ G₀) (ht : Subgroup.closure t ≤ G₀)
    (hN : G₀ ≤ Subgroup.normalizer (N : Set G)) (h : ∀ x ∈ s, ∀ y ∈ t, ⁅x, y⁆ ∈ N) :
    ⁅Subgroup.closure s, Subgroup.closure t⁆ ≤ N := by
  have conj : ∀ g ∈ G₀, ∀ n ∈ N, g * n * g⁻¹ ∈ N := fun g hg n hn =>
    (Subgroup.mem_normalizer_iff.1 (hN hg) n).1 hn
  have step1 : ∀ x ∈ s, ∀ y ∈ Subgroup.closure t, ⁅x, y⁆ ∈ N := by
    intro x hx y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy => exact h x hx y hy
    | one => rw [commutatorElement_one_right]; exact N.one_mem
    | mul y₁ y₂ hy₁ hy₂ ih₁ ih₂ =>
      have : ⁅x, y₁ * y₂⁆ = ⁅x, y₁⁆ * (y₁ * ⁅x, y₂⁆ * y₁⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [this]
      exact mul_mem ih₁ (conj _ (ht hy₁) _ ih₂)
    | inv y hy ih =>
      have : ⁅x, y⁻¹⁆ = y⁻¹ * ⁅x, y⁆⁻¹ * y⁻¹⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [this]
      exact conj _ (inv_mem (ht hy)) _ (inv_mem ih)
  rw [Subgroup.commutator_le]
  intro x hx y hy
  induction hx using Subgroup.closure_induction generalizing y with
  | mem x hx => exact step1 x hx y hy
  | one => rw [commutatorElement_one_left]; exact N.one_mem
  | mul x₁ x₂ hx₁ hx₂ ih₁ ih₂ =>
    have : ⁅x₁ * x₂, y⁆ = (x₁ * ⁅x₂, y⁆ * x₁⁻¹) * ⁅x₁, y⁆ := by
      simp only [commutatorElement_def]; group
    rw [this]
    exact mul_mem (conj _ (hs hx₁) _ (ih₂ y hy)) (ih₁ y hy)
  | inv x hx ih =>
    have : ⁅x⁻¹, y⁆ = x⁻¹ * ⁅x, y⁆⁻¹ * x⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [this]
    exact conj _ (inv_mem (hs hx)) _ (inv_mem (ih y hy))

theorem rootSpan_eq_closure
    (R : Type*) [CommRing R] (S : Set (Fin τ.rank → ℤ)) :
    rootSpan τ R S = Subgroup.closure {g | ∃ α ∈ S, ∃ c : R, pinnedX τ R α c = g} := by
  refine le_antisymm (iSup₂_le fun α hα => Subgroup.closure_mono ?_) ((Subgroup.closure_le _).2 ?_)
  · rintro _ ⟨c, rfl⟩
    exact ⟨α, hα, c, rfl⟩
  · rintro _ ⟨α, hα, c, rfl⟩
    exact (le_iSup₂_of_le α hα le_rfl : rootSubgroup τ R α ≤ rootSpan τ R S)
      (Subgroup.subset_closure ⟨c, rfl⟩)

variable (τ)

@[expose] def maxHeight : ℤ := sSup (height '' {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α})

theorem bddAbove_height_posRoots :
    BddAbove (height '' {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}) :=
  (((finite_setOf_isRoot τ).subset fun _ hα => hα.1).image _).bddAbove

variable {τ}

theorem height_le_maxHeight
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hpos : 0 < height α) :
    height α ≤ maxHeight τ :=
  le_csSup (bddAbove_height_posRoots τ) ⟨α, ⟨hα, hpos⟩, rfl⟩

variable (τ)

theorem one_le_maxHeight
    : 1 ≤ maxHeight τ := by
  have h := height_le_maxHeight (isRoot_single τ ⟨0, by cases τ <;> decide⟩)
    (by rw [height_single]; exact one_pos)
  rwa [height_single] at h

variable (R : Type*) [CommRing R]

@[expose] def heightSeries
    (h : ℤ) : Subgroup (Module.End R (RootModule τ R))ˣ :=
  rootSpan τ R {α | IsRoot τ α ∧ 0 < height α ∧ h ≤ height α}

variable {τ R}

theorem heightSeries_le_posUnipotent
    (h : ℤ) : heightSeries τ R h ≤ posUnipotent τ R :=
  iSup₂_le fun α hα => le_iSup₂_of_le α ⟨hα.1, hα.2.1⟩ le_rfl

theorem heightSeries_one
    : heightSeries τ R 1 = posUnipotent τ R := by
  refine le_antisymm (heightSeries_le_posUnipotent 1)
    (iSup₂_le fun α hα => le_iSup₂_of_le α ⟨hα.1, hα.2, hα.2⟩ le_rfl)

theorem heightSeries_maxHeight_add_one
    : heightSeries τ R (maxHeight τ + 1) = ⊥ :=
  iSup₂_eq_bot.2 fun α hα => absurd (height_le_maxHeight hα.1 hα.2.1) (by linarith [hα.2.2])

theorem nsmul_add_nsmul_mem_heightSet {α β : Fin τ.rank → ℤ} {h k : ℤ}
    (hα : 0 < height α ∧ h ≤ height α) (hβ : 0 < height β ∧ k ≤ height β) {a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hr : IsRoot τ (a • α + b • β)) :
    a • α + b • β ∈ {γ | IsRoot τ γ ∧ 0 < height γ ∧ h + k ≤ height γ} := by
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  refine ⟨hr, ?_, ?_⟩ <;> rw [height_nsmul_add_nsmul] <;> nlinarith [hα.1, hβ.1]

theorem heightSeries_normal
    (R : Type) [CommRing R] (h : ℤ) :
    ((heightSeries τ R h).subgroupOf (posUnipotent τ R)).Normal := by
  refine (positive_root_ideal_normality τ R (J := {α | IsRoot τ α ∧ 0 < height α ∧ h ≤ height α})
    (S := {α | IsRoot τ α ∧ 0 < height α}) (fun γ hγ => ⟨hγ.1, hγ.2.1⟩) (fun γ hγ => hγ)
    (fun α hα β hβ a b ha hb hr => ?_)).2
  obtain ⟨hr', hp, hle⟩ := nsmul_add_nsmul_mem_heightSet (k := h) (h := 1) ⟨hα.2, hα.2⟩
    ⟨hβ.2.1, hβ.2.2⟩ ha hb hr
  exact ⟨hr', hp, by linarith⟩

theorem heightSeries_le_normalizer
    (R : Type) [CommRing R] (h : ℤ) :
    posUnipotent τ R ≤
      Subgroup.normalizer (heightSeries τ R h : Set (Module.End R (RootModule τ R))ˣ) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (heightSeries_le_posUnipotent h)).1
    (heightSeries_normal R h)

theorem commutator_heightSeries_le
    (R : Type) [CommRing R] (h k : ℤ) :
    ⁅heightSeries τ R h, heightSeries τ R k⁆ ≤ heightSeries τ R (h + k) := by
  have e1 := rootSpan_eq_closure R {α | IsRoot τ α ∧ 0 < height α ∧ h ≤ height α}
  have e2 := rootSpan_eq_closure R {α | IsRoot τ α ∧ 0 < height α ∧ k ≤ height α}
  have hs := heightSeries_le_posUnipotent (τ := τ) (R := R) h
  have ht := heightSeries_le_posUnipotent (τ := τ) (R := R) k
  rw [heightSeries, e1] at hs ⊢
  rw [heightSeries, e2] at ht ⊢
  refine commutator_closure_le_of_le_normalizer hs ht
    (heightSeries_le_normalizer R (h + k)) ?_
  rintro _ ⟨α, hα, c, rfl⟩ _ ⟨β, hβ, d, rfl⟩
  by_cases hab : α = β
  · subst hab
    rw [commutatorElement_def, rootSubgroup_mul_comm R (Subgroup.subset_closure ⟨c, rfl⟩)
      (Subgroup.subset_closure ⟨d, rfl⟩), mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hmem := commutator_rootSubgroup_le R hα.1 hβ.1 hα.2.1 hβ.2.1 hab
    (Subgroup.commutator_mem_commutator (Subgroup.subset_closure ⟨c, rfl⟩)
      (Subgroup.subset_closure ⟨d, rfl⟩))
  have hle : (⨆ (γ : Fin τ.rank → ℤ) (_ : IsRoot τ γ ∧
      ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ = a • α + b • β), rootSubgroup τ R γ) ≤
      heightSeries τ R (h + k) := by
    refine iSup₂_le fun γ hγ => ?_
    obtain ⟨hγr, a, b, ha, hb, rfl⟩ := hγ
    exact le_iSup₂_of_le _ (nsmul_add_nsmul_mem_heightSet ⟨hα.2.1, hα.2.2⟩ ⟨hβ.2.1, hβ.2.2⟩ ha
      hb hγr) le_rfl
  exact hle hmem

theorem lowerCentralSeries_le_heightSeries
    (R : Type) [CommRing R] (n : ℕ) :
    (posUnipotent τ R).lowerCentralSeries n ≤ heightSeries τ R (n + 1) := by
  induction n with
  | zero => simp [heightSeries_one]
  | succ n ih =>
    rw [Subgroup.lowerCentralSeries_succ]
    refine (Subgroup.commutator_mono ih (heightSeries_one (τ := τ) (R := R)).ge).trans ?_
    have := commutator_heightSeries_le (τ := τ) R (n + 1) 1
    convert this using 2
    push_cast
    ring

theorem positive_root_height_series
    (τ : Tag) (R : Type) [CommRing R] :
    heightSeries τ R 1 = posUnipotent τ R ∧
    heightSeries τ R (maxHeight τ + 1) = ⊥ ∧
    (∀ h : ℤ, 1 ≤ h → heightSeries τ R h ≤ posUnipotent τ R ∧
      ((heightSeries τ R h).subgroupOf (posUnipotent τ R)).Normal) ∧
    (∀ h k : ℤ, 1 ≤ h → 1 ≤ k →
      ⁅heightSeries τ R h, heightSeries τ R k⁆ ≤ heightSeries τ R (h + k)) ∧
    Group.IsNilpotent (posUnipotent τ R) ∧
    (Group.nilpotencyClass (posUnipotent τ R) : ℤ) ≤ maxHeight τ ∧
    ∀ [Finite R] (h : ℤ), 1 ≤ h →
      Nat.card (heightSeries τ R h) =
        Nat.card R ^ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α ∧ h ≤ height α}.ncard := by
  have hH := one_le_maxHeight τ
  have hbot : (posUnipotent τ R).lowerCentralSeries (maxHeight τ).toNat = ⊥ := by
    refine eq_bot_iff.2 ((lowerCentralSeries_le_heightSeries R _).trans ?_)
    rw [Int.toNat_of_nonneg (by omega), heightSeries_maxHeight_add_one]
  have hnil : Group.IsNilpotent (posUnipotent τ R) :=
    (Subgroup.isNilpotent_iff_lowerCentralSeries _).2 ⟨_, hbot⟩
  have htop : (⊤ : Subgroup (posUnipotent τ R)).lowerCentralSeries (maxHeight τ).toNat = ⊥ := by
    rw [← Subgroup.map_eq_bot_iff_of_injective _ (posUnipotent τ R).subtype_injective,
      Subgroup.top_subtype_lowerCentralSeries, hbot]
  refine ⟨heightSeries_one, heightSeries_maxHeight_add_one,
    fun h _ => ⟨heightSeries_le_posUnipotent h, heightSeries_normal R h⟩,
    fun h k _ _ => commutator_heightSeries_le R h k, hnil, ?_, fun h hh => ?_⟩
  · have := (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le).1 htop
    omega
  · set J := {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α ∧ h ≤ height α}
    have hfin : J.Finite := (finite_setOf_isRoot τ).subset fun γ hγ => hγ.1
    set s := hfin.toFinset
    let β : Fin s.card → Fin τ.rank → ℤ := fun k => (s.equivFin.symm k : Fin τ.rank → ℤ)
    have hβinj : Function.Injective β := fun k l hkl =>
      s.equivFin.symm.injective (Subtype.ext hkl)
    have hβrange : Set.range β = J := by
      ext γ
      refine ⟨fun ⟨k, hk⟩ => hk ▸ hfin.mem_toFinset.1 (s.equivFin.symm k).2,
        fun hγ => ⟨s.equivFin ⟨γ, hfin.mem_toFinset.2 hγ⟩, ?_⟩⟩
      simp [β]
    have hbij := bijOn_prod_pinnedX R (S := J) (fun γ hγ => ⟨hγ.1, hγ.2.1⟩)
      (fun α hα β' hβ' a b ha hb hr => by
        obtain ⟨hr', hp, hle⟩ := nsmul_add_nsmul_mem_heightSet ⟨hα.2.1, hα.2.2⟩
          ⟨hβ'.2.1, hβ'.2.2⟩ ha hb hr
        exact ⟨hr', hp, by linarith⟩) β hβinj hβrange
    rw [Set.ncard_eq_toFinset_card J hfin]
    calc Nat.card (heightSeries τ R h) = Nat.card (Set.univ : Set (Fin s.card → R)) :=
          (Nat.card_congr hbij.equiv).symm
      _ = Nat.card (Fin s.card → R) := Nat.card_univ
      _ = Nat.card R ^ s.card := by rw [Nat.card_fun]; simp

end CFSG.LieType.Chevalley
