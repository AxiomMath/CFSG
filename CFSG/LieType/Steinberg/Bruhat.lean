module

public import CFSG.LieType.Steinberg.BruhatWeyl
import Mathlib.Tactic.Group

public section

namespace CFSG.LieType.Steinberg

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
open scoped commutatorElement Pointwise

variable {K : Type*} [Group K]

section Defs

variable (D : UniversalRootDatum K)

@[expose] def posUnipotentExcept (i : Fin D.rank) : Subgroup K :=
  ⨆ γ ∈ (RootSystem.ofCartan D.isFiniteType D.divisible).posExcept i, D.rootGroup γ

@[expose] def inversionUnipotent (w : (coxeterMatrix D.isFiniteType).Group) : Subgroup K :=
  ⨆ γ ∈ {γ | γ ∈ D.roots ∧ 0 < ht γ ∧ ht (weylAction D.isFiniteType w γ) < 0}, D.rootGroup γ

end Defs

section Bruhat

variable {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem
set_option hygiene false in
local notation "ρ" => weylAction D.isFiniteType
set_option hygiene false in
local notation "Φ" => RootSystem.ofCartan D.isFiniteType D.divisible

theorem rootGroup_le_posUnipotentExcept {i : Fin D.rank} {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ (Φ).posExcept i) : D.rootGroup γ ≤ posUnipotentExcept D i :=
  le_iSup₂_of_le (f := fun γ (_ : γ ∈ (Φ).posExcept i) => D.rootGroup γ) γ hγ le_rfl

theorem posUnipotentExcept_le_posUnipotent (i : Fin D.rank) :
    posUnipotentExcept D i ≤ posUnipotent D :=
  iSup₂_le fun _ hγ => rootGroup_le_posUnipotent hγ.1.1 hγ.1.2

theorem posUnipotent_eq_sup (hext : SteinbergExtras D n H) (i : Fin D.rank) :
    posUnipotent D = posUnipotentExcept D i ⊔ D.rootGroup (Pi.single i 1) := by
  apply le_antisymm
  · refine iSup₂_le fun γ hγ => ?_
    by_cases h1 : γ = Pi.single i 1
    · subst h1
      exact le_sup_right
    by_cases h2 : γ = 2 • Pi.single i 1
    · subst h2
      exact (hext.two_smul_le _ ((Φ).single_mem i) hγ.1).trans le_sup_right
    refine le_sup_of_le_left (rootGroup_le_posUnipotentExcept ⟨hγ, ?_⟩)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h1, h2⟩
  · exact sup_le (posUnipotentExcept_le_posUnipotent i)
      (rootGroup_le_posUnipotent ((Φ).single_mem i) (ht_single_pos i))

theorem rootGroup_single_le_normalizer (hext : SteinbergExtras D n H) (i : Fin D.rank) :
    D.rootGroup (Pi.single i 1) ≤ Subgroup.normalizer (posUnipotentExcept D i : Set K) :=
  le_normalizer_iSup₂ fun x hx γ hγ y hy => by
    have hc := hext.commutator_mem _ ((Φ).single_mem i) γ hγ.1.1
      ((Φ).linIndepPair_of_mem_posExcept (Or.inl rfl) hγ) x hx y hy
    have hle : ⨆ ε ∈ openCone D.roots (Pi.single i 1) γ, D.rootGroup ε ≤
        posUnipotentExcept D i := iSup₂_le fun _ hε =>
      rootGroup_le_posUnipotentExcept ((Φ).openCone_subset_posExcept (Or.inl rfl) hγ hε)
    have h : ⁅x, y⁆ * y ∈ posUnipotentExcept D i :=
      mul_mem (hle hc) (rootGroup_le_posUnipotentExcept hγ hy)
    rwa [commutatorElement_def, inv_mul_cancel_right] at h

theorem inversionUnipotent_le_posUnipotent (w : W) : inversionUnipotent D w ≤ posUnipotent D :=
  iSup₂_le fun _ hγ => rootGroup_le_posUnipotent hγ.1 hγ.2.1

theorem rootGroup_le_inversionUnipotent {w : W} {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots)
    (h₁ : 0 < ht γ) (h₂ : ht (ρ w γ) < 0) : D.rootGroup γ ≤ inversionUnipotent D w :=
  le_iSup₂_of_le (f := fun γ (_ : γ ∈ {γ | γ ∈ D.roots ∧ 0 < ht γ ∧ ht (ρ w γ) < 0}) =>
    D.rootGroup γ) γ ⟨hγ, h₁, h₂⟩ le_rfl

theorem inversionUnipotent_le_simple_mul {w : W} {i : Fin D.rank}
    (hw : ¬ (cs).IsLeftDescent w i) :
    inversionUnipotent D w ≤ inversionUnipotent D ((cs).simple i * w) := by
  refine iSup₂_le fun γ hγ => rootGroup_le_inversionUnipotent hγ.1 hγ.2.1 ?_
  obtain ⟨hγr, h₁, h₂⟩ := hγ
  have hpos := ht_weylAction_inv_single_pos hw
  have hback := weylAction_inv_apply_apply D.isFiniteType w γ
  have hne : ρ w γ ∈ (Φ).negExcept i := by
    refine ⟨⟨weylAction_mem_roots _ w hγr, h₂⟩, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro h
      rw [h, map_neg] at hback
      rw [← hback, ht_neg] at h₁
      omega
    · intro h
      rw [h, map_neg, map_nsmul] at hback
      rw [← hback, ht_neg, ht_two_smul] at h₁
      omega
  rw [weylAction_mul_apply, weylAction_simple]
  exact ((Φ).refl_mem_negExcept hne).1.2

theorem rootGroup_inv_single_le_inversionUnipotent {w : W} {i : Fin D.rank}
    (hw : ¬ (cs).IsLeftDescent w i) :
    D.rootGroup (ρ w⁻¹ (Pi.single i 1)) ≤ inversionUnipotent D ((cs).simple i * w) := by
  refine rootGroup_le_inversionUnipotent (weylAction_mem_roots _ _ ((Φ).single_mem i))
    (ht_weylAction_inv_single_pos hw) ?_
  rw [weylAction_mul_apply, weylAction_apply_inv_apply, weylAction_simple_single, ht_neg,
    ht_single]
  exact neg_one_lt_zero

variable (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)

include hct in
theorem coe_borel :
    (borel D H : Set K) = ((⨆ i, H i : Subgroup K) : Set K) * (posUnipotent D : Set K) :=
  Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (iSup_le_borel.trans (borel_le_normalizer_posUnipotent hct))

include hct in
theorem exists_eq_mul_mul_of_mem_borel (hext : SteinbergExtras D n H) (i : Fin D.rank) {b : K}
    (hb : b ∈ borel D H) : ∃ t ∈ ⨆ k, H k, ∃ u ∈ posUnipotentExcept D i,
      ∃ x ∈ D.rootGroup (Pi.single i 1), b = t * u * x := by
  rw [← SetLike.mem_coe, coe_borel hct, Set.mem_mul] at hb
  obtain ⟨t, ht, v, hv, rfl⟩ := hb
  rw [SetLike.mem_coe, posUnipotent_eq_sup hext i, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ (rootGroup_single_le_normalizer hext i),
    Set.mem_mul] at hv
  obtain ⟨u, hu, x, hx, rfl⟩ := hv
  exact ⟨t, ht, u, hu, x, hx, (mul_assoc _ _ _).symm⟩

include hct in
theorem conj_n_mem_posUnipotentExcept (i : Fin D.rank) {u : K}
    (hu : u ∈ posUnipotentExcept D i) : n i * u * (n i)⁻¹ ∈ posUnipotentExcept D i :=
  conj_mem_of_forall_mem (P := (Φ).posExcept i) (X := D.rootGroup) (fun γ hγ y hy => by
    have h := (actsAs_n hct i).conj_mem hγ.1.1 hy
    rw [weylAction_simple] at h
    exact rootGroup_le_posUnipotentExcept ((Φ).refl_mem_posExcept hγ) h) hu

theorem nrep_inv_conj_mem (w : W) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) {x : K}
    (hx : x ∈ D.rootGroup γ) : (nrep hct w)⁻¹ * x * nrep hct w ∈ D.rootGroup (ρ w⁻¹ γ) :=
  (actsAs_nrep hct w).inv_conj_mem hγ hx

theorem nrep_inv_conj_mem_iSup (w : W) {t : K} (ht : t ∈ ⨆ i, H i) :
    (nrep hct w)⁻¹ * t * nrep hct w ∈ ⨆ i, H i :=
  inv_conj_mem_iSup_of_mem_weylN hct (nrep_mem_weylN hct w) ht

@[expose] def bruhatCell (w : W) : Set K :=
  {g | ∃ b₁ ∈ borel D H, ∃ b₂ ∈ borel D H, g = b₁ * nrep hct w * b₂}

theorem nrep_mem_bruhatCell (w : W) : nrep hct w ∈ bruhatCell hct w :=
  ⟨1, one_mem _, 1, one_mem _, by group⟩

theorem bruhatCell_one : bruhatCell hct 1 = borel D H := by
  ext g
  refine ⟨fun ⟨b₁, hb₁, b₂, hb₂, he⟩ => ?_, fun hg => ⟨g, hg, 1, one_mem _, ?_⟩⟩
  · rw [he, nrep_one, mul_one]
    exact mul_mem hb₁ hb₂
  · rw [nrep_one, mul_one, mul_one]

theorem mul_mem_bruhatCell {w : W} {b g : K} (hb : b ∈ borel D H) (hg : g ∈ bruhatCell hct w) :
    b * g ∈ bruhatCell hct w := by
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hg
  exact ⟨b * b₁, mul_mem hb hb₁, b₂, hb₂, by group⟩

theorem mul_mem_bruhatCell_right {w : W} {b g : K} (hg : g ∈ bruhatCell hct w)
    (hb : b ∈ borel D H) : g * b ∈ bruhatCell hct w := by
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hg
  exact ⟨b₁, hb₁, b₂ * b, mul_mem hb₂ hb, by group⟩

theorem exists_n_mul_mul_nrep (hext : SteinbergExtras D n H) {w : W} {i : Fin D.rank}
    (hw : ¬ (cs).IsLeftDescent w i) {b : K} (hb : b ∈ borel D H) :
    ∃ b' ∈ borel D H, ∃ x ∈ D.rootGroup (ρ w⁻¹ (Pi.single i 1)),
      n i * b * nrep hct w = b' * nrep hct ((cs).simple i * w) * x := by
  obtain ⟨t, ht, u, hu, x, hx, rfl⟩ := exists_eq_mul_mul_of_mem_borel hct hext i hb
  refine ⟨n i * t * (n i)⁻¹ * (n i * u * (n i)⁻¹),
    mul_mem (iSup_le_borel (conj_n_mem_iSup hct i ht)) (posUnipotent_le_borel
      (posUnipotentExcept_le_posUnipotent i (conj_n_mem_posUnipotentExcept hct i hu))),
    (nrep hct w)⁻¹ * x * nrep hct w, nrep_inv_conj_mem hct w ((Φ).single_mem i) hx, ?_⟩
  rw [nrep_simple_mul hct hw]
  group

theorem n_mul_mul_nrep_mem_of_isLeftDescent (hext : SteinbergExtras D n H) {w : W}
    {i : Fin D.rank} (hw : (cs).IsLeftDescent w i) {b : K} (hb : b ∈ borel D H) :
    n i * b * nrep hct w ∈ bruhatCell hct w ∪ bruhatCell hct ((cs).simple i * w) := by
  have hw' : ¬ (cs).IsLeftDescent ((cs).simple i * w) i :=
    (cs).isLeftDescent_iff_not_isLeftDescent_mul.mp hw
  have hnw : nrep hct w = n i * nrep hct ((cs).simple i * w) := by
    rw [← nrep_simple_mul hct hw', (cs).simple_mul_simple_cancel_left]
  have hpos := ht_weylAction_inv_single_pos hw'
  have hα := (Φ).single_mem i
  have hαw := weylAction_mem_roots D.isFiniteType ((cs).simple i * w)⁻¹ hα
  obtain ⟨t, ht, u, hu, x, hx, rfl⟩ := exists_eq_mul_mul_of_mem_borel hct hext i hb
  have hb₀ : n i * t * (n i)⁻¹ * (n i * u * (n i)⁻¹) ∈ borel D H :=
    mul_mem (iSup_le_borel (conj_n_mem_iSup hct i ht)) (posUnipotent_le_borel
      (posUnipotentExcept_le_posUnipotent i (conj_n_mem_posUnipotentExcept hct i hu)))
  have hg : n i * x * n i ∈ rankOne D.rootGroup i :=
    mul_mem (mul_mem (hct.n_mem i) (Subgroup.mem_sup_left hx)) (hct.n_mem i)
  have e : n i * (t * u * x) * nrep hct w = n i * t * (n i)⁻¹ * (n i * u * (n i)⁻¹) *
      (n i * x * n i) * nrep hct ((cs).simple i * w) := by
    rw [hnw]
    group
  rw [e]
  rcases hext.rankOne_bruhat i _ hg with ⟨h, hh, y, hy, hxy⟩ | ⟨y, hy, h, hh, z, hz, hxy⟩
  ·
    refine Or.inr ⟨_ * h, mul_mem hb₀ (iSup_le_borel (le_iSup H i hh)),
      (nrep hct ((cs).simple i * w))⁻¹ * y * nrep hct ((cs).simple i * w),
      rootGroup_le_borel hαw hpos (nrep_inv_conj_mem hct _ hα hy), ?_⟩
    rw [hxy]
    group
  ·
    have hhz : (nrep hct ((cs).simple i * w))⁻¹ * (h * z) * nrep hct ((cs).simple i * w) ∈
        borel D H := by
      have e' : (nrep hct ((cs).simple i * w))⁻¹ * (h * z) * nrep hct ((cs).simple i * w) =
          (nrep hct ((cs).simple i * w))⁻¹ * h * nrep hct ((cs).simple i * w) *
            ((nrep hct ((cs).simple i * w))⁻¹ * z * nrep hct ((cs).simple i * w)) := by group
      rw [e']
      exact mul_mem (iSup_le_borel (nrep_inv_conj_mem_iSup hct _ (le_iSup H i hh)))
        (rootGroup_le_borel hαw hpos (nrep_inv_conj_mem hct _ hα hz))
    refine Or.inl ⟨_ * y, mul_mem hb₀ (rootGroup_le_borel hα (ht_single_pos i) hy), _, hhz, ?_⟩
    rw [hxy, hnw]
    group

theorem n_mul_mul_nrep_mem (hext : SteinbergExtras D n H) (w : W) (i : Fin D.rank) {b : K}
    (hb : b ∈ borel D H) :
    n i * b * nrep hct w ∈ bruhatCell hct w ∪ bruhatCell hct ((cs).simple i * w) := by
  by_cases hw : (cs).IsLeftDescent w i
  · exact n_mul_mul_nrep_mem_of_isLeftDescent hct hext hw hb
  · obtain ⟨b', hb', x, hx, he⟩ := exists_n_mul_mul_nrep hct hext hw hb
    exact Or.inr ⟨b', hb', x, rootGroup_le_borel (weylAction_mem_roots _ _ ((Φ).single_mem i))
      (ht_weylAction_inv_single_pos hw) hx, he⟩

theorem n_mul_mem_bruhatCell (hext : SteinbergExtras D n H) {w : W} {g : K}
    (hg : g ∈ bruhatCell hct w) (i : Fin D.rank) :
    n i * g ∈ bruhatCell hct w ∪ bruhatCell hct ((cs).simple i * w) := by
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hg
  rw [show n i * (b₁ * nrep hct w * b₂) = n i * b₁ * nrep hct w * b₂ by group]
  rcases n_mul_mul_nrep_mem hct hext w i hb₁ with h | h
  · exact Or.inl (mul_mem_bruhatCell_right hct h hb₂)
  · exact Or.inr (mul_mem_bruhatCell_right hct h hb₂)

include hct in
theorem closure_borel_union_range :
    Subgroup.closure ((borel D H : Set K) ∪ Set.range n) = ⊤ := by
  have hB : borel D H ≤ Subgroup.closure ((borel D H : Set K) ∪ Set.range n) :=
    fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hn : ∀ i, n i ∈ Subgroup.closure ((borel D H : Set K) ∪ Set.range n) :=
    fun i => Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)
  have hL : ∀ i, rankOne D.rootGroup i ≤ Subgroup.closure ((borel D H : Set K) ∪ Set.range n) := by
    intro i
    have hα := (Φ).single_mem i
    refine sup_le ((rootGroup_le_borel hα (ht_single_pos i)).trans hB) fun y hy => ?_
    have h1 := (actsAs_n hct i).inv_conj_mem ((Φ).neg_mem _ hα) hy
    rw [(cs).inv_simple, map_neg, weylAction_simple_single, neg_neg] at h1
    have e : y = n i * ((n i)⁻¹ * y * n i) * (n i)⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (hn i) (hB (rootGroup_le_borel hα (ht_single_pos i) h1)))
      (inv_mem (hn i))
  rw [eq_top_iff, ← iSup_leviAmalgam_eq_top (isCTRootSystem D.isFiniteType D.divisible) hct]
  exact iSup_le fun J => iSup₂_le fun j _ => hL j

include hct in
theorem not_map_conj_n_borel_le (hext : SteinbergExtras D n H) (i : Fin D.rank) :
    ¬ (borel D H).map (MulAut.conj (n i)).toMonoidHom ≤ borel D H := by
  intro hle
  have hα := (Φ).single_mem i
  have hneg : D.rootGroup (-Pi.single i 1) ≤ borel D H := by
    rw [← weylAction_simple_single D.isFiniteType i, ← (actsAs_n hct i) _ hα]
    exact (Subgroup.map_mono (rootGroup_le_borel hα (ht_single_pos i))).trans hle
  have hn : n i ∈ borel D H ⊓ weylN n H :=
    ⟨sup_le (rootGroup_le_borel hα (ht_single_pos i)) hneg (hct.n_mem i), n_mem_weylN i⟩
  rw [borel_inf_weylN hct hext] at hn
  have h1 := (actsAs_n hct i).unique hext (actsAs_of_mem_iSup hct hn)
  exact (cs).simple_ne_one i h1

theorem exists_mem_bruhatCell (hext : SteinbergExtras D n H) (g : K) :
    ∃ w, g ∈ bruhatCell hct w := by
  have hg : g ∈ Subgroup.closure ((borel D H : Set K) ∪ Set.range n) := by
    rw [closure_borel_union_range hct]
    exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction_left with
  | one => exact ⟨1, ⟨1, one_mem _, 1, one_mem _, by rw [nrep_one]; group⟩⟩
  | mul_left x hx y _ ih =>
    obtain ⟨w, hw⟩ := ih
    rcases hx with hx | ⟨i, rfl⟩
    · exact ⟨w, mul_mem_bruhatCell hct hx hw⟩
    · rcases n_mul_mem_bruhatCell hct hext hw i with h | h
      exacts [⟨_, h⟩, ⟨_, h⟩]
  | inv_mul_cancel x hx y _ ih =>
    obtain ⟨w, hw⟩ := ih
    rcases hx with hx | ⟨i, rfl⟩
    · exact ⟨w, mul_mem_bruhatCell hct (inv_mem hx) hw⟩
    · have hsq : (n i ^ 2)⁻¹ ∈ borel D H := inv_mem (iSup_le_borel (sq_n_mem_iSup hct i))
      rw [show (n i)⁻¹ * y = (n i ^ 2)⁻¹ * (n i * y) by group]
      rcases n_mul_mem_bruhatCell hct hext hw i with h | h
      exacts [⟨_, mul_mem_bruhatCell hct hsq h⟩, ⟨_, mul_mem_bruhatCell hct hsq h⟩]

theorem iUnion_bruhatCell (hext : SteinbergExtras D n H) : ⋃ w, bruhatCell hct w = Set.univ :=
  Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 (exists_mem_bruhatCell hct hext g)

theorem eq_of_nrep_mem_bruhatCell_of_length_le (hext : SteinbergExtras D n H) (m : ℕ) :
    ∀ w w' : W, (cs).length w = m → (cs).length w ≤ (cs).length w' →
      nrep hct w ∈ bruhatCell hct w' → w = w' := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro w w' hm hle hmem
  by_cases hw1 : w = 1
  ·
    subst hw1
    obtain ⟨b₁, hb₁, b₂, hb₂, he⟩ := hmem
    rw [nrep_one] at he
    have hB : nrep hct w' ∈ borel D H := by
      rw [show nrep hct w' = b₁⁻¹ * (b₁ * nrep hct w' * b₂) * b₂⁻¹ by group, ← he, mul_one]
      exact mul_mem (inv_mem hb₁) (inv_mem hb₂)
    exact ((nrep_mem_borel_iff hct hext).1 hB).symm
  obtain ⟨i, hi⟩ := (cs).exists_leftDescent_of_ne_one hw1
  have hui : ¬ (cs).IsLeftDescent ((cs).simple i * w) i :=
    (cs).isLeftDescent_iff_not_isLeftDescent_mul.mp hi
  have hlu : (cs).length ((cs).simple i * w) + 1 = (cs).length w := (cs).isLeftDescent_iff.mp hi
  have hnw : nrep hct w = n i * nrep hct ((cs).simple i * w) := by
    rw [← nrep_simple_mul hct hui, (cs).simple_mul_simple_cancel_left]
  obtain ⟨b₁, hb₁, b₂, hb₂, he⟩ := hmem
  have hsq : (n i ^ 2)⁻¹ ∈ borel D H := inv_mem (iSup_le_borel (sq_n_mem_iSup hct i))
  have e : nrep hct ((cs).simple i * w) = (n i ^ 2)⁻¹ * (n i * b₁ * nrep hct w' * b₂) := by
    rw [mul_assoc (n i * b₁) _ b₂, mul_assoc (n i) b₁, ← mul_assoc b₁, ← he, hnw]
    group
  have hmem : nrep hct ((cs).simple i * w) ∈
      bruhatCell hct w' ∪ bruhatCell hct ((cs).simple i * w') := by
    rw [e]
    rcases n_mul_mul_nrep_mem hct hext w' i hb₁ with h | h
    · exact Or.inl (mul_mem_bruhatCell hct hsq (mul_mem_bruhatCell_right hct h hb₂))
    · exact Or.inr (mul_mem_bruhatCell hct hsq (mul_mem_bruhatCell_right hct h hb₂))
  rcases hmem with h | h
  · exfalso
    have h' := ih _ (by omega) _ w' rfl (by omega) h
    rw [← h'] at hle
    omega
  · have hlen : (cs).length ((cs).simple i * w) ≤ (cs).length ((cs).simple i * w') := by
      rcases (cs).length_simple_mul w' i with h' | h' <;> omega
    exact mul_left_cancel (ih _ (by omega) _ _ rfl hlen h)

theorem eq_of_nrep_mem_bruhatCell (hext : SteinbergExtras D n H) {w w' : W}
    (h : nrep hct w ∈ bruhatCell hct w') : w = w' := by
  rcases le_total ((cs).length w) ((cs).length w') with hle | hle
  · exact eq_of_nrep_mem_bruhatCell_of_length_le hct hext _ w w' rfl hle h
  · refine (eq_of_nrep_mem_bruhatCell_of_length_le hct hext _ w' w rfl hle ?_).symm
    obtain ⟨b₁, hb₁, b₂, hb₂, he⟩ := h
    exact ⟨b₁⁻¹, inv_mem hb₁, b₂⁻¹, inv_mem hb₂, by rw [he]; group⟩

theorem eq_of_mem_bruhatCell (hext : SteinbergExtras D n H) {g : K} {w w' : W}
    (h : g ∈ bruhatCell hct w) (h' : g ∈ bruhatCell hct w') : w = w' := by
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := h
  obtain ⟨b₁', hb₁', b₂', hb₂', he⟩ := h'
  refine eq_of_nrep_mem_bruhatCell hct hext ⟨b₁⁻¹ * b₁', mul_mem (inv_mem hb₁) hb₁',
    b₂' * b₂⁻¹, mul_mem hb₂' (inv_mem hb₂), ?_⟩
  rw [show nrep hct w = b₁⁻¹ * (b₁ * nrep hct w * b₂) * b₂⁻¹ by group, he]
  group

theorem existsUnique_mem_bruhatCell (hext : SteinbergExtras D n H) (g : K) :
    ∃! w, g ∈ bruhatCell hct w := by
  obtain ⟨w, hw⟩ := exists_mem_bruhatCell hct hext g
  exact ⟨w, hw, fun w' hw' => eq_of_mem_bruhatCell hct hext hw' hw⟩

theorem pairwise_disjoint_bruhatCell (hext : SteinbergExtras D n H) :
    Pairwise fun w w' : W => Disjoint (bruhatCell hct w) (bruhatCell hct w') :=
  fun _ _ hne => Set.disjoint_left.2 fun _ h h' => hne (eq_of_mem_bruhatCell hct hext h h')

theorem bruhatCell_injective (hext : SteinbergExtras D n H) :
    Function.Injective (bruhatCell hct) := fun _ _ h =>
  eq_of_nrep_mem_bruhatCell hct hext (h ▸ nrep_mem_bruhatCell hct _)

theorem bruhatCell_eq_of_actsAs (hext : SteinbergExtras D n H) {x : K} (hx : x ∈ weylN n H)
    {w : W} (h : ActsAs D x w) :
    bruhatCell hct w = {g | ∃ b₁ ∈ borel D H, ∃ b₂ ∈ borel D H, g = b₁ * x * b₂} := by
  have ht : (nrep hct w)⁻¹ * x ∈ ⨆ i, H i := by
    refine mem_iSup_of_actsAs_one hct hext (mul_mem (inv_mem (nrep_mem_weylN hct w)) hx) ?_
    have h' := (actsAs_nrep hct w).inv.mul h
    rwa [inv_mul_cancel] at h'
  have htB := iSup_le_borel ht
  ext g
  constructor
  · rintro ⟨b₁, hb₁, b₂, hb₂, rfl⟩
    exact ⟨b₁, hb₁, ((nrep hct w)⁻¹ * x)⁻¹ * b₂, mul_mem (inv_mem htB) hb₂, by group⟩
  · rintro ⟨b₁, hb₁, b₂, hb₂, rfl⟩
    exact ⟨b₁, hb₁, (nrep hct w)⁻¹ * x * b₂, mul_mem htB hb₂, by group⟩

theorem exists_nrep_mul_eq (hext : SteinbergExtras D n H) (w : W) {u : K}
    (hu : u ∈ posUnipotent D) :
    ∃ b ∈ borel D H, ∃ v ∈ inversionUnipotent D w, nrep hct w * u = b * nrep hct w * v := by
  induction hm : (cs).length w using Nat.strong_induction_on generalizing w u with
  | _ m ih =>
  by_cases hw1 : w = 1
  · subst hw1
    exact ⟨u, posUnipotent_le_borel hu, 1, one_mem _, by rw [nrep_one]; group⟩
  obtain ⟨i, hi⟩ := (cs).exists_leftDescent_of_ne_one hw1
  have hw' : ¬ (cs).IsLeftDescent ((cs).simple i * w) i :=
    (cs).isLeftDescent_iff_not_isLeftDescent_mul.mp hi
  have hlen : (cs).length ((cs).simple i * w) + 1 = (cs).length w := (cs).isLeftDescent_iff.mp hi
  have hsw : (cs).simple i * ((cs).simple i * w) = w := (cs).simple_mul_simple_cancel_left i
  have hnw : nrep hct w = n i * nrep hct ((cs).simple i * w) := by
    rw [← nrep_simple_mul hct hw', hsw]
  obtain ⟨b', hb', v', hv', he'⟩ := ih _ (by omega) ((cs).simple i * w) hu rfl
  obtain ⟨b'', hb'', x, hx, he''⟩ := exists_n_mul_mul_nrep hct hext hw' hb'
  rw [hsw] at he''
  have hx' := rootGroup_inv_single_le_inversionUnipotent hw' hx
  have hv'' := inversionUnipotent_le_simple_mul hw' hv'
  rw [hsw] at hx' hv''
  refine ⟨b'', hb'', x * v', mul_mem hx' hv'', ?_⟩
  calc nrep hct w * u = n i * (nrep hct ((cs).simple i * w) * u) := by rw [hnw, mul_assoc]
    _ = n i * b' * nrep hct ((cs).simple i * w) * v' := by rw [he']; group
    _ = b'' * nrep hct w * x * v' := by rw [he'']
    _ = b'' * nrep hct w * (x * v') := by group

theorem exists_eq_mul_nrep_mul (hext : SteinbergExtras D n H) {g : K} {w : W}
    (hg : g ∈ bruhatCell hct w) :
    ∃ b ∈ borel D H, ∃ u ∈ inversionUnipotent D w, g = b * nrep hct w * u := by
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hg
  rw [← SetLike.mem_coe, coe_borel hct, Set.mem_mul] at hb₂
  obtain ⟨t, ht, u, hu, rfl⟩ := hb₂
  obtain ⟨b, hb, v, hv, he⟩ := exists_nrep_mul_eq hct hext w hu
  refine ⟨b₁ * (nrep hct w * t * (nrep hct w)⁻¹) * b, mul_mem (mul_mem hb₁ (iSup_le_borel
    (conj_mem_iSup_of_mem_weylN hct (nrep_mem_weylN hct w) ht))) hb, v, hv, ?_⟩
  calc b₁ * nrep hct w * (t * u) =
      b₁ * (nrep hct w * t * (nrep hct w)⁻¹) * (nrep hct w * u) := by group
    _ = _ := by rw [he]; group

theorem nrep_conj_mem_negUnipotent {w : W} {v : K} (hv : v ∈ inversionUnipotent D w) :
    nrep hct w * v * (nrep hct w)⁻¹ ∈ negUnipotent D :=
  conj_mem_of_forall_mem (fun _ hγ _ hy => rootGroup_le_negUnipotent
    (weylAction_mem_roots _ w hγ.1) hγ.2.2 ((actsAs_nrep hct w).conj_mem hγ.1 hy)) hv

theorem eq_of_mul_nrep_mul_eq (hBU : BruhatExtras D H) {w : W} {b b' u u' : K}
    (hb : b ∈ borel D H) (hb' : b' ∈ borel D H) (hu : u ∈ inversionUnipotent D w)
    (hu' : u' ∈ inversionUnipotent D w) (h : b * nrep hct w * u = b' * nrep hct w * u') :
    b = b' ∧ u = u' := by
  have hmem : b'⁻¹ * b ∈ borel D H ⊓ negUnipotent D := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hb') hb, ?_⟩
    have e : b'⁻¹ * b = nrep hct w * (u' * u⁻¹) * (nrep hct w)⁻¹ := by
      rw [show b'⁻¹ * b = b'⁻¹ * (b * nrep hct w * u) * u⁻¹ * (nrep hct w)⁻¹ by group, h]
      group
    rw [e]
    exact nrep_conj_mem_negUnipotent hct (mul_mem hu' (inv_mem hu))
  rw [hBU.borel_inf_negUnipotent, Subgroup.mem_bot] at hmem
  obtain rfl : b' = b := inv_mul_eq_one.1 hmem
  exact ⟨rfl, mul_left_cancel h⟩

theorem existsUnique_mul_nrep_mul (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H)
    {g : K} {w : W} (hg : g ∈ bruhatCell hct w) :
    ∃! p : K × K, (p.1 ∈ borel D H ∧ p.2 ∈ inversionUnipotent D w) ∧
      g = p.1 * nrep hct w * p.2 := by
  obtain ⟨b, hb, u, hu, rfl⟩ := exists_eq_mul_nrep_mul hct hext hg
  refine ⟨(b, u), ⟨⟨hb, hu⟩, rfl⟩, fun p hp => ?_⟩
  obtain ⟨⟨hb', hu'⟩, he⟩ := hp
  obtain ⟨h1, h2⟩ := eq_of_mul_nrep_mul_eq hct hBU hb' hb hu' hu he.symm
  exact Prod.ext h1 h2

theorem injOn_bruhat_normalForm (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) :
    Set.InjOn (fun q : W × K × K => q.2.1 * nrep hct q.1 * q.2.2)
      {q | q.2.1 ∈ borel D H ∧ q.2.2 ∈ inversionUnipotent D q.1} := by
  rintro ⟨w, b, u⟩ ⟨hb, hu⟩ ⟨w', b', u'⟩ ⟨hb', hu'⟩ h
  simp only at hb hu hb' hu' h
  have hu₀ : u ∈ borel D H := posUnipotent_le_borel (inversionUnipotent_le_posUnipotent w hu)
  have hu₀' : u' ∈ borel D H := posUnipotent_le_borel (inversionUnipotent_le_posUnipotent w' hu')
  obtain rfl : w = w' := eq_of_mem_bruhatCell hct hext ⟨b, hb, u, hu₀, rfl⟩ ⟨b', hb', u', hu₀', h⟩
  obtain ⟨rfl, rfl⟩ := eq_of_mul_nrep_mul_eq hct hBU hb hb' hu hu' h
  rfl

theorem existsUnique_bruhat_normalForm (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H)
    (g : K) :
    ∃! q : W × K × K, (q.2.1 ∈ borel D H ∧ q.2.2 ∈ inversionUnipotent D q.1) ∧
      g = q.2.1 * nrep hct q.1 * q.2.2 := by
  obtain ⟨w, hw⟩ := exists_mem_bruhatCell hct hext g
  obtain ⟨b, hb, u, hu, rfl⟩ := exists_eq_mul_nrep_mul hct hext hw
  refine ⟨(w, b, u), ⟨⟨hb, hu⟩, rfl⟩, fun q hq => ?_⟩
  obtain ⟨⟨hb', hu'⟩, he⟩ := hq
  have hw' : q.1 = w := eq_of_mem_bruhatCell hct hext ⟨q.2.1, hb', q.2.2,
    posUnipotent_le_borel (inversionUnipotent_le_posUnipotent q.1 hu'), he⟩ hw
  obtain ⟨w', b', u'⟩ := q
  simp only at hw' hb' hu' he
  subst hw'
  obtain ⟨h1, h2⟩ := eq_of_mul_nrep_mul_eq hct hBU hb' hb hu' hu he.symm
  rw [h1, h2]

end Bruhat

end CFSG.LieType.Steinberg
