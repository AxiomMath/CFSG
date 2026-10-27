module

public import CFSG.LieType.HighestRoot.RootsBasic
public import CFSG.LieType.Steinberg.Bruhat
public import CFSG.LieType.Steinberg.CentralExt.Unipotent
import Mathlib.Tactic.Group

public section

namespace CFSG.LieType.HighestRoot

open CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.Universal
  CFSG.LieType.CurtisTits
open scoped commutatorElement

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem
set_option hygiene false in
local notation "ρ" => weylAction D.isFiniteType

section Roots

theorem rootForm_nsmul_add_nsmul (a b : ℕ) (δ γ r : Fin D.rank → ℤ) :
    rootForm D (a • δ + b • γ) r = a * rootForm D δ r + b * rootForm D γ r := by
  simp only [rootForm, map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply]
  simp only [nsmul_eq_mul]

theorem rootForm_neg_right (γ r : Fin D.rank → ℤ) : rootForm D γ (-r) = -rootForm D γ r := by
  simp only [rootForm, map_neg]

theorem rootForm_weylAction (w : W) (γ δ : Fin D.rank → ℤ) :
    rootForm D (ρ w γ) (ρ w δ) = rootForm D γ δ :=
  form_weylAction D.isFiniteType w γ δ

theorem nonneg_of_rootForm_pos {r γ : Fin D.rank → ℤ}
    (hr : ∀ i, 0 ≤ rootForm D (Pi.single i 1) r) (hγ : γ ∈ D.roots)
    (h : 0 < rootForm D γ r) : 0 ≤ γ := by
  rcases nonneg_or_nonpos D.isFiniteType D.divisible hγ with h' | h'
  · exact h'
  · exact absurd h (not_lt.2 (form_nonpos_of_nonpos D.isFiniteType hr h'))

theorem ht_pos_of_rootForm_pos {r γ : Fin D.rank → ℤ}
    (hr : ∀ i, 0 ≤ rootForm D (Pi.single i 1) r) (hγ : γ ∈ D.roots)
    (h : 0 < rootForm D γ r) : 0 < ht γ :=
  ht_pos_of_nonneg hγ (nonneg_of_rootForm_pos hr hγ h)

theorem rootForm_nonneg_of_ht_pos {r δ : Fin D.rank → ℤ}
    (hr : ∀ i, 0 ≤ rootForm D (Pi.single i 1) r) (hδ : δ ∈ D.roots) (h : 0 < ht δ) :
    0 ≤ rootForm D δ r := by
  rcases nonneg_or_nonpos D.isFiniteType D.divisible hδ with h' | h'
  · exact form_nonneg_of_nonneg D.isFiniteType hr h'
  · exact absurd h (not_lt.2 (ht_neg_of_nonpos hδ h').le)

theorem linIndepPair_of_rootForm {δ γ r : Fin D.rank → ℤ} (hδ0 : δ ≠ 0)
    (hδ : rootForm D δ r = 0) (hγ : rootForm D γ r ≠ 0) : LinIndepPair δ γ := by
  intro a b hab
  have h := congrArg (fun v => rootForm D v r) hab
  simp only [rootForm, map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, map_zero,
    LinearMap.zero_apply] at h
  simp only [zsmul_eq_mul] at h
  have hδ' : form D.isFiniteType (toRat δ) (toRat r) = 0 := hδ
  rw [hδ', mul_zero, zero_add] at h
  have hb : b = 0 := by
    rcases mul_eq_zero.1 h with h1 | h1
    · exact_mod_cast h1
    · exact absurd h1 hγ
  refine ⟨?_, hb⟩
  rw [hb, zero_smul, add_zero] at hab
  rcases smul_eq_zero.1 hab with h1 | h1
  · exact h1
  · exact absurd h1 hδ0

end Roots

section Action

theorem rootGroup_eq_of_actsAs {x : K} {w : W} (hx : ActsAs D x w) {γ δ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) (hδ : δ ∈ D.roots) (h : D.rootGroup γ = D.rootGroup δ) :
    D.rootGroup (ρ w γ) = D.rootGroup (ρ w δ) := by
  rw [← hx γ hγ, ← hx δ hδ, h]

theorem conj_mem_highestRootRadical_of_actsAs {x : K} {w : W} (hx : ActsAs D x w)
    {r : Fin D.rank → ℤ} (hw : ρ w r = r) {y : K} (hy : y ∈ highestRootRadical D r) :
    x * y * x⁻¹ ∈ highestRootRadical D r := by
  refine conj_mem_of_forall_mem (fun γ hγ z hz => ?_) hy
  have hmem := weylAction_mem_roots D.isFiniteType w hγ.1
  refine le_iSup₂_of_le (f := fun γ (_ : γ ∈ {γ | γ ∈ D.roots ∧ 0 < rootForm D γ r}) =>
    D.rootGroup γ) (ρ w γ) ⟨hmem, ?_⟩ le_rfl (hx.conj_mem hγ.1 hz)
  rw [← hw, rootForm_weylAction]
  exact hγ.2

theorem mem_normalizer_highestRootRadical_of_actsAs {x : K} {w : W} (hx : ActsAs D x w)
    {r : Fin D.rank → ℤ} (hw : ρ w r = r) :
    x ∈ Subgroup.normalizer (highestRootRadical D r : Set K) := by
  have hw' : ρ w⁻¹ r = r := by
    conv_lhs => rw [← hw]
    rw [weylAction_inv_apply_apply]
  refine Subgroup.mem_normalizer_iff.2 fun y =>
    ⟨fun hy => conj_mem_highestRootRadical_of_actsAs hx hw hy, fun hy => ?_⟩
  have h := conj_mem_highestRootRadical_of_actsAs hx.inv hw' hy
  rwa [inv_inv, show x⁻¹ * (x * y * x⁻¹) * x = y by group] at h

theorem rootGroup_le_highestRootRadical {r γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots)
    (h : 0 < rootForm D γ r) : D.rootGroup γ ≤ highestRootRadical D r :=
  le_iSup₂_of_le (f := fun γ (_ : γ ∈ {γ | γ ∈ D.roots ∧ 0 < rootForm D γ r}) =>
    D.rootGroup γ) γ ⟨hγ, h⟩ le_rfl

end Action

section Radical

variable {r : Fin D.rank → ℤ}

theorem highestRootRadical_le_posUnipotent (hr : ∀ i, 0 ≤ rootForm D (Pi.single i 1) r) :
    highestRootRadical D r ≤ posUnipotent D :=
  iSup₂_le fun _ hγ => rootGroup_le_posUnipotent hγ.1 (ht_pos_of_rootForm_pos hr hγ.1 hγ.2)

theorem isPGroup_highestRootRadical (hext : SteinbergExtras D n H) {p : ℕ}
    (hX : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ))
    (hr : ∀ i, 0 ≤ rootForm D (Pi.single i 1) r) : IsPGroup p (highestRootRadical D r) :=
  (isPGroup_iSup_pos hext hX).to_le (highestRootRadical_le_posUnipotent hr)

theorem rootGroup_le_normalizer_highestRootRadical (hext : SteinbergExtras D n H)
    {δ : Fin D.rank → ℤ} (hδ : δ ∈ D.roots) (h : 0 ≤ rootForm D δ r) :
    D.rootGroup δ ≤ Subgroup.normalizer (highestRootRadical D r : Set K) := by
  rcases h.lt_or_eq with hpos | hzero
  · exact (rootGroup_le_highestRootRadical hδ hpos).trans Subgroup.le_normalizer
  refine le_normalizer_iSup₂ fun x hx γ hγ y hy => ?_
  rw [Steinberg.conj_eq_commutatorElement_mul]
  refine mul_mem ?_ (rootGroup_le_highestRootRadical hγ.1 hγ.2 hy)
  have hind := linIndepPair_of_rootForm (ne_zero_of_mem_roots _ _ hδ) hzero.symm hγ.2.ne'
  refine (iSup₂_le fun ε hε => ?_ : ⨆ ε ∈ openCone D.roots δ γ, D.rootGroup ε ≤ _)
    (hext.commutator_mem δ hδ γ hγ.1 hind x hx y hy)
  obtain ⟨hεR, a, b, -, hb, rfl⟩ := hε
  refine rootGroup_le_highestRootRadical hεR ?_
  rw [rootForm_nsmul_add_nsmul, ← hzero, mul_zero, zero_add]
  exact mul_pos (by exact_mod_cast hb) hγ.2

theorem borel_le_normalizer_highestRootRadical
    (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
    (hr : ∀ i, 0 ≤ rootForm D (Pi.single i 1) r) :
    borel D H ≤ Subgroup.normalizer (highestRootRadical D r : Set K) := by
  refine sup_le ?_ (iSup₂_le fun δ hδ => rootGroup_le_normalizer_highestRootRadical hext hδ.1
    (rootForm_nonneg_of_ht_pos hr hδ.1 hδ.2))
  refine le_normalizer_of_map_conj_le fun x hx => map_conj_le_iff.2 fun y hy =>
    conj_mem_of_forall_mem (fun γ hγ z hz => ?_) hy
  exact rootGroup_le_highestRootRadical hγ.1 hγ.2
    ((Subgroup.mem_normalizer_iff.1 (iSup_le_normalizer_rootGroup hct hγ.1 hx) z).1 hz)

end Radical

section RootGroup

@[expose] def DivisibleNormalizes (D : UniversalRootDatum K) : Prop :=
  ∀ i ∈ D.divisible, D.rootGroup (Pi.single i 1) ≤
    Subgroup.normalizer (D.rootGroup (2 • Pi.single i 1) : Set K)

@[expose] def DivisibleWeylMem (D : UniversalRootDatum K) (n : Fin D.rank → K) : Prop :=
  ∀ i ∈ D.divisible, n i ∈ rankOneGroup D (2 • Pi.single i 1)

theorem divisibleNormalizes_of_divisible_eq_empty (h : D.divisible = ∅) :
    DivisibleNormalizes D := fun i hi => absurd (h ▸ hi) (Set.notMem_empty i)

theorem divisibleWeylMem_of_divisible_eq_empty (h : D.divisible = ∅) :
    DivisibleWeylMem D n := fun i hi => absurd (h ▸ hi) (Set.notMem_empty i)

theorem le_normalizer_of_forall_commute {A B : Subgroup K}
    (h : ∀ x ∈ A, ∀ y ∈ B, Commute x y) : A ≤ Subgroup.normalizer (B : Set K) :=
  le_normalizer_of_map_conj_le fun x hx => map_conj_le_iff.2 fun y hy => by
    rw [(h x hx y hy).eq, mul_inv_cancel_right]
    exact hy

theorem IsHighestRoot.ht_pos {r : Fin D.rank → ℤ} (hr : IsHighestRoot D r) : 0 < ht r :=
  ht_pos_of_nonneg hr.mem_roots
    (nonneg_of_isDominant D.isFiniteType (D := D.divisible) hr.mem_roots hr.dominant)

theorem rootGroup_le_normalizer_two_smul (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hN : DivisibleNormalizes D) (u : W) {i : Fin D.rank} (hi : i ∈ D.divisible) :
    D.rootGroup (ρ u (Pi.single i 1)) ≤
      Subgroup.normalizer (D.rootGroup (2 • ρ u (Pi.single i 1)) : Set K) := by
  have hα : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots := Or.inl ⟨1, i, by simp⟩
  have h2α : (2 • Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots := Or.inr ⟨1, i, hi, by simp⟩
  have e1 := actsAs_nrep hct u _ hα
  have e2 := actsAs_nrep hct u _ h2α
  rw [map_nsmul] at e2
  rw [← e1, ← e2]
  rintro _ ⟨a, ha, rfl⟩
  rw [mem_normalizer_iff_map_conj, ← map_conj_mul]
  have e : (MulAut.conj (nrep hct u)).toMonoidHom a * nrep hct u = nrep hct u * a := by
    simp [mul_assoc]
  rw [e, map_conj_mul, mem_normalizer_iff_map_conj.1 (hN i hi ha)]

theorem borel_le_normalizer_rootGroup (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hN : DivisibleNormalizes D) {r : Fin D.rank → ℤ}
    (hr : IsHighestRoot D r) : borel D H ≤ Subgroup.normalizer (D.rootGroup r : Set K) := by
  refine sup_le (iSup_le_normalizer_rootGroup hct hr.mem_roots) (iSup₂_le fun δ hδ => ?_)
  obtain ⟨hδR, hδp⟩ := hδ
  have hrp := hr.ht_pos
  by_cases hind : LinIndepPair δ r
  · refine le_normalizer_of_forall_commute fun x hx y hy => ?_
    have hc := hext.commutator_mem δ hδR r hr.mem_roots hind x hx y hy
    have hbot : ⨆ ε ∈ openCone D.roots δ r, D.rootGroup ε = ⊥ := by
      refine iSup₂_eq_bot.2 fun ε hε => ?_
      exfalso
      obtain ⟨hεR, a, b, ha, hb, rfl⟩ := hε
      have h1 := hr.height_le _ hεR
      rw [ht_add, ht_nsmul, ht_nsmul] at h1
      have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
      have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
      nlinarith
    rw [hbot, Subgroup.mem_bot] at hc
    exact commutatorElement_eq_one_iff_commute.1 hc
  rcases (RootSystem.ofCartan D.isFiniteType D.divisible).proportional δ hδR r hr.mem_roots hind
    with h | h | h | h | h | h
  · rw [h]
    exact Subgroup.le_normalizer
  · rw [h, ht_neg] at hδp
    omega
  · have := hr.height_le δ hδR
    rw [h, ht_two_smul] at this
    omega
  · rw [h, ht_neg, ht_two_smul] at hδp
    omega
  ·
    rcases hr.mem_roots with ⟨u, i, hu⟩ | ⟨u, i, hi, hu⟩
    · exfalso
      have e := congrArg (ρ u⁻¹) hu
      rw [weylAction_inv_apply_apply, h, map_nsmul] at e
      have := congrFun e i
      simp only [Pi.single_eq_same, Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at this
      omega
    · have hδu : δ = ρ u (Pi.single i 1) := by
        funext j
        have := congrFun (h.symm.trans hu) j
        simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at this
        omega
      rw [hu, hδu]
      exact rootGroup_le_normalizer_two_smul hct hN u hi
  · rw [h, ht_neg, ht_two_smul] at hrp
    omega

theorem highestRootRadical_le_normalizer (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hN : DivisibleNormalizes D) {r : Fin D.rank → ℤ}
    (hr : IsHighestRoot D r) :
    highestRootRadical D r ≤ Subgroup.normalizer (D.rootGroup r : Set K) :=
  (highestRootRadical_le_posUnipotent hr.dominant).trans
    ((posUnipotent_le_borel (H := H)).trans (borel_le_normalizer_rootGroup hct hext hN hr))

theorem eq_single_of_rootGroup_eq (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {c : ℕ} (hc : 0 < c) {i : Fin D.rank}
    (hci : c • (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots) {v : W}
    (h : D.rootGroup (ρ v (c • Pi.single i 1)) = D.rootGroup (c • Pi.single i 1)) :
    ρ v (Pi.single i 1) = Pi.single i 1 := by
  have hβR : ρ v (Pi.single i 1) ∈ D.roots := Or.inl ⟨v, i, rfl⟩
  have hcβR : c • ρ v (Pi.single i 1) ∈ D.roots := by
    have := weylAction_mem_roots D.isFiniteType v hci
    rwa [map_nsmul] at this
  rw [map_nsmul] at h
  have hcα : 0 < ht (c • (Pi.single i 1 : Fin D.rank → ℤ)) := by
    rw [ht_nsmul, ht_single, mul_one]
    exact_mod_cast hc
  have hneg : -(c • (Pi.single i 1 : Fin D.rank → ℤ)) ∈ D.roots :=
    OfCartan.neg_mem_roots D.isFiniteType hci
  by_contra hne
  rcases nonneg_or_nonpos D.isFiniteType D.divisible hβR with h0 | h0
  · obtain ⟨j, hji, hj⟩ : ∃ j, j ≠ i ∧ 0 < ρ v (Pi.single i 1) j := by
      by_contra hcon
      push Not at hcon
      have hβeq : ρ v (Pi.single i 1) = ρ v (Pi.single i 1) i • Pi.single i 1 := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp
        · simp only [Pi.smul_apply, Pi.single_eq_of_ne hj, smul_eq_mul, mul_zero]
          exact le_antisymm (hcon j hj) (h0 j)
      rcases OfCartan.eq_one_or_eq_neg_one_of_weylAction_eq_smul D.isFiniteType hβeq with h1 | h1
      · exact hne (by rw [hβeq, h1, one_smul])
      · have := h0 i
        rw [h1] at this
        exact absurd this (by norm_num)
    have hs := actsAs_n hct i _ hcβR
    have hs' := actsAs_n hct i _ hci
    rw [h, hs'] at hs
    have e1 : ρ ((cs).simple i) (c • Pi.single i 1) = -(c • Pi.single i 1) := by
      rw [map_nsmul, weylAction_simple_single, smul_neg]
    rw [e1] at hs
    have hmem := weylAction_mem_roots D.isFiniteType ((cs).simple i) hcβR
    have hpos : 0 ≤ ρ ((cs).simple i) (c • ρ v (Pi.single i 1)) := by
      rcases nonneg_or_nonpos D.isFiniteType D.divisible hmem with h2 | h2
      · exact h2
      · exfalso
        have h3 := h2 j
        rw [weylAction_simple_apply_of_ne _ _ _ hji] at h3
        simp only [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply] at h3
        have : (0 : ℤ) < c := by exact_mod_cast hc
        nlinarith
    apply hext.ne_bot _ hneg
    rw [eq_bot_iff, ← posUnipotent_inf_negUnipotent hext]
    refine le_inf ?_ (rootGroup_le_negUnipotent hneg (by rw [ht_neg]; linarith))
    rw [hs]
    exact rootGroup_le_posUnipotent hmem (ht_pos_of_nonneg hmem hpos)
  · apply hext.ne_bot _ hci
    rw [eq_bot_iff, ← posUnipotent_inf_negUnipotent hext]
    refine le_inf (rootGroup_le_posUnipotent hci hcα) ?_
    rw [← h]
    refine rootGroup_le_negUnipotent hcβR ?_
    have h4 := ht_neg_of_nonpos hβR h0
    rw [ht_nsmul]
    have : (0 : ℤ) < c := by exact_mod_cast hc
    nlinarith

theorem exists_eq_weylAction_smul_single {r : Fin D.rank → ℤ} (hr : r ∈ D.roots) :
    ∃ c : ℕ, 0 < c ∧ ∃ (u : W) (i : Fin D.rank),
      c • (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots ∧ r = ρ u (c • Pi.single i 1) := by
  rcases hr with ⟨u, i, rfl⟩ | ⟨u, i, hi, rfl⟩
  · exact ⟨1, one_pos, u, i, by rw [one_nsmul]; exact Or.inl ⟨1, i, by simp⟩,
      by rw [one_nsmul]⟩
  · exact ⟨2, two_pos, u, i, Or.inr ⟨1, i, hi, by simp⟩, by rw [map_nsmul]⟩

theorem weylAction_eq_of_rootGroup_eq (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {r : Fin D.rank → ℤ} (hr : r ∈ D.roots) {w : W}
    (h : D.rootGroup (ρ w r) = D.rootGroup r) : ρ w r = r := by
  obtain ⟨c, hc, u, i, hci, rfl⟩ := exists_eq_weylAction_smul_single hr
  have hwr := weylAction_mem_roots D.isFiniteType w hr
  have h' := rootGroup_eq_of_actsAs (actsAs_nrep hct u).inv hwr hr h
  rw [weylAction_inv_apply_apply, ← weylAction_mul_apply, ← weylAction_mul_apply] at h'
  have h1 := eq_single_of_rootGroup_eq hct hext hc hci h'
  have h2 : ρ (u⁻¹ * w * u) (c • Pi.single i 1) = c • Pi.single i 1 := by
    rw [map_nsmul, h1]
  calc ρ w (ρ u (c • Pi.single i 1))
      = ρ u (ρ (u⁻¹ * w * u) (c • Pi.single i 1)) := by
        rw [weylAction_mul_apply, weylAction_mul_apply, weylAction_apply_inv_apply]
    _ = ρ u (c • Pi.single i 1) := by rw [h2]

theorem normalizer_rootGroup_le_normalizer_highestRootRadical
    (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
    (hN : DivisibleNormalizes D) {r : Fin D.rank → ℤ} (hr : IsHighestRoot D r) :
    Subgroup.normalizer (D.rootGroup r : Set K) ≤
      Subgroup.normalizer (highestRootRadical D r : Set K) := by
  intro g hg
  have hcell : g ∈ ⋃ w, bruhatCell hct w := by
    rw [iUnion_bruhatCell hct hext]
    exact Set.mem_univ g
  obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl⟩ := Set.mem_iUnion.1 hcell
  have hB := borel_le_normalizer_rootGroup hct hext hN hr
  have hBQ := borel_le_normalizer_highestRootRadical hct hext hr.dominant
  have hn : nrep hct w ∈ Subgroup.normalizer (D.rootGroup r : Set K) := by
    have e : nrep hct w = b₁⁻¹ * (b₁ * nrep hct w * b₂) * b₂⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (hB hb₁)) hg) (inv_mem (hB hb₂))
  have hwr : ρ w r = r := weylAction_eq_of_rootGroup_eq hct hext hr.mem_roots (by
    rw [← actsAs_nrep hct w r hr.mem_roots]
    exact mem_normalizer_iff_map_conj.1 hn)
  exact mul_mem (mul_mem (hBQ hb₁)
    (mem_normalizer_highestRootRadical_of_actsAs (actsAs_nrep hct w) hwr)) (hBQ hb₂)

end RootGroup

section RankOne

theorem commute_of_rootForm_eq_zero (hext : SteinbergExtras D n H) {r : Fin D.rank → ℤ}
    (hr : r ∈ D.roots) (hl : ∀ δ ∈ D.roots, rootForm D δ δ ≤ rootForm D r r)
    {δ r' : Fin D.rank → ℤ} (hδ : δ ∈ D.roots) (hr' : r' = r ∨ r' = -r)
    (h0 : rootForm D δ r = 0) {x y : K} (hx : x ∈ D.rootGroup δ) (hy : y ∈ D.rootGroup r') :
    Commute x y := by
  have hr'R : r' ∈ D.roots := by
    rcases hr' with rfl | rfl
    exacts [hr, OfCartan.neg_mem_roots D.isFiniteType hr]
  have h0' : rootForm D δ r' = 0 := by
    rcases hr' with rfl | rfl
    exacts [h0, by rw [rootForm_neg_right, h0, neg_zero]]
  have hrr' : rootForm D r' r' = rootForm D r r := by
    rcases hr' with rfl | rfl
    · rfl
    · simp only [rootForm, map_neg, LinearMap.neg_apply, neg_neg]
  have hpos : ∀ {γ}, γ ∈ D.roots → 0 < rootForm D γ γ := fun hγ =>
    form_pos D.isFiniteType fun e =>
      ne_zero_of_mem_roots _ _ hγ (toRat_injective (by rw [e, map_zero]))
  have hδδ := hpos hδ
  have hrr := hpos hr
  have hind : LinIndepPair δ r' :=
    linIndepPair_of_rootForm (ne_zero_of_mem_roots _ _ hδ) h0' (by rw [hrr']; exact hrr.ne')
  have hc := hext.commutator_mem δ hδ r' hr'R hind x hx y hy
  have hbot : ⨆ ε ∈ openCone D.roots δ r', D.rootGroup ε = ⊥ := by
    refine iSup₂_eq_bot.2 fun ε hε => ?_
    exfalso
    obtain ⟨hεR, a, b, ha, hb, rfl⟩ := hε
    have h1 := hl _ hεR
    have h2 : form D.isFiniteType (toRat r') (toRat δ) = 0 := by
      rw [form_comm]
      exact h0'
    have h3 : form D.isFiniteType (toRat δ) (toRat r') = 0 := h0'
    have e : rootForm D (a • δ + b • r') (a • δ + b • r') =
        (a : ℚ) ^ 2 * rootForm D δ δ + (b : ℚ) ^ 2 * rootForm D r' r' := by
      simp only [rootForm, map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, h2,
        h3]
      simp only [nsmul_eq_mul]
      ring
    rw [e, hrr'] at h1
    have ha' : (1 : ℚ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℚ) ≤ b := by exact_mod_cast hb
    have ha2 : (1 : ℚ) ≤ (a : ℚ) ^ 2 := by nlinarith
    have hb2 : (1 : ℚ) ≤ (b : ℚ) ^ 2 := by nlinarith
    have h4 := mul_le_mul_of_nonneg_right ha2 hδδ.le
    have h5 := mul_le_mul_of_nonneg_right hb2 hrr.le
    rw [one_mul] at h4 h5
    linarith
  rw [hbot, Subgroup.mem_bot] at hc
  exact commutatorElement_eq_one_iff_commute.1 hc

theorem rootGroup_le_normalizer_rankOneGroup (hext : SteinbergExtras D n H)
    {r : Fin D.rank → ℤ} (hr : r ∈ D.roots) (hl : ∀ δ ∈ D.roots, rootForm D δ δ ≤ rootForm D r r)
    {δ : Fin D.rank → ℤ} (hδ : δ ∈ D.roots) (h0 : rootForm D δ r = 0) :
    D.rootGroup δ ≤ Subgroup.normalizer (rankOneGroup D r : Set K) := by
  refine le_normalizer_of_forall_commute fun x hx y hy => ?_
  have hJ : rankOneGroup D r ≤ Subgroup.centralizer {x} := sup_le
    (fun z hz => Subgroup.mem_centralizer_singleton_iff.2
      (commute_of_rootForm_eq_zero hext hr hl hδ (Or.inl rfl) h0 hx hz).eq.symm)
    (fun z hz => Subgroup.mem_centralizer_singleton_iff.2
      (commute_of_rootForm_eq_zero hext hr hl hδ (Or.inr rfl) h0 hx hz).eq.symm)
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hJ hy)).symm

theorem exists_mem_rankOneGroup_actsAs (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hW : DivisibleWeylMem D n) {r : Fin D.rank → ℤ} (hr : r ∈ D.roots) :
    ∃ m ∈ rankOneGroup D r, ∃ s : W, ActsAs D m s ∧ ρ s r = -r := by
  obtain ⟨u, i, β, hβR, hβn, hβs, rfl⟩ : ∃ (u : W) (i : Fin D.rank) (β : Fin D.rank → ℤ),
      β ∈ D.roots ∧ n i ∈ rankOneGroup D β ∧ ρ ((cs).simple i) β = -β ∧ r = ρ u β := by
    rcases hr with ⟨u, i, rfl⟩ | ⟨u, i, hi, rfl⟩
    · exact ⟨u, i, _, Or.inl ⟨1, i, by simp⟩, hct.n_mem i, weylAction_simple_single _ i, rfl⟩
    · refine ⟨u, i, _, Or.inr ⟨1, i, hi, by simp⟩, hW i hi, ?_, by rw [map_nsmul]⟩
      rw [map_nsmul, weylAction_simple_single, smul_neg]
  refine ⟨nrep hct u * n i * (nrep hct u)⁻¹, ?_, u * (cs).simple i * u⁻¹,
    ((actsAs_nrep hct u).mul (actsAs_n hct i)).mul (actsAs_nrep hct u).inv, ?_⟩
  · have e : (rankOneGroup D β).map (MulAut.conj (nrep hct u)).toMonoidHom =
        rankOneGroup D (ρ u β) := by
      rw [rankOneGroup, Subgroup.map_sup, actsAs_nrep hct u _ hβR,
        actsAs_nrep hct u _ (OfCartan.neg_mem_roots D.isFiniteType hβR), map_neg]
    rw [← e]
    exact ⟨n i, hβn, rfl⟩
  · rw [weylAction_mul_apply, weylAction_mul_apply, weylAction_inv_apply_apply, hβs, map_neg]

end RankOne

end CFSG.LieType.HighestRoot
