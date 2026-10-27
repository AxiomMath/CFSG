module

public import CFSG.LieType.Steinberg.Bridge
public import CFSG.LieType.Steinberg.CoreTorus
import Mathlib.Tactic.Group

public section

namespace CFSG.LieType.Steinberg

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem

variable {K : Type*} [Group K]

section Defs

variable (D : UniversalRootDatum K)

@[expose] def posUnipotent : Subgroup K := ⨆ γ ∈ {γ | γ ∈ D.roots ∧ 0 < ht γ}, D.rootGroup γ

@[expose] def negUnipotent : Subgroup K := ⨆ γ ∈ {γ | γ ∈ D.roots ∧ ht γ < 0}, D.rootGroup γ

@[expose] def borel (H : Fin D.rank → Subgroup K) : Subgroup K := (⨆ i, H i) ⊔ posUnipotent D

structure BruhatExtras (H : Fin D.rank → Subgroup K) : Prop where
  borel_inf_negUnipotent : borel D H ⊓ negUnipotent D = ⊥

@[expose] def ActsAs (x : K) (w : (coxeterMatrix D.isFiniteType).Group) : Prop :=
  ∀ γ ∈ D.roots,
    (D.rootGroup γ).map (MulAut.conj x).toMonoidHom = D.rootGroup (weylAction D.isFiniteType w γ)

end Defs

@[expose] def weylN {ι : Type*} (n : ι → K) (H : ι → Subgroup K) : Subgroup K :=
  (⨆ i, H i) ⊔ Subgroup.closure (Set.range n)

theorem conj_mem_of_forall_mem {V : Type*} {X : V → Subgroup K} {P : Set V} {M : Subgroup K}
    {c : K} (h : ∀ γ ∈ P, ∀ y ∈ X γ, c * y * c⁻¹ ∈ M) {u : K} (hu : u ∈ ⨆ γ ∈ P, X γ) :
    c * u * c⁻¹ ∈ M := by
  have hle : ⨆ γ ∈ P, X γ ≤ M.comap (MulAut.conj c).toMonoidHom :=
    iSup₂_le fun γ hγ y hy => h γ hγ y hy
  exact hle hu

theorem le_normalizer_iSup₂ {V : Type*} {X : V → Subgroup K} {P : Set V} {A : Subgroup K}
    (h : ∀ x ∈ A, ∀ γ ∈ P, ∀ y ∈ X γ, x * y * x⁻¹ ∈ ⨆ γ ∈ P, X γ) :
    A ≤ Subgroup.normalizer ((⨆ γ ∈ P, X γ : Subgroup K) : Set K) :=
  le_normalizer_of_map_conj_le fun x hx => Subgroup.map_le_iff_le_comap.2 fun _ hu =>
    conj_mem_of_forall_mem (h x hx) hu

section Weyl

variable {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem
set_option hygiene false in
local notation "ρ" => weylAction D.isFiniteType
set_option hygiene false in
local notation "Φ" => RootSystem.ofCartan D.isFiniteType D.divisible

theorem ht_pos_of_nonneg {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) (h : 0 ≤ γ) : 0 < ht γ :=
  lt_of_lt_of_le one_pos (one_le_sum_of_nonneg h (ne_zero_of_mem_roots _ _ hγ))

theorem ht_neg_of_nonpos {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) (h : γ ≤ 0) : ht γ < 0 := by
  have h1 := one_le_sum_of_nonneg (neg_nonneg.2 h) (neg_ne_zero.2 (ne_zero_of_mem_roots _ _ hγ))
  simp only [Pi.neg_apply, Finset.sum_neg_distrib] at h1
  change ∑ j, γ j < 0
  omega

theorem ht_weylAction_single_pos {w : W} {i : Fin D.rank} (h : ¬ (cs).IsRightDescent w i) :
    0 < ht (ρ w (Pi.single i 1)) :=
  ht_pos_of_nonneg (weylAction_mem_roots _ w ((Φ).single_mem i))
    (nonneg_of_not_isRightDescent _ w i h)

theorem ht_weylAction_single_neg {w : W} {i : Fin D.rank} (h : (cs).IsRightDescent w i) :
    ht (ρ w (Pi.single i 1)) < 0 :=
  ht_neg_of_nonpos (weylAction_mem_roots _ w ((Φ).single_mem i))
    ((isRightDescent_iff _ w i).1 h)

theorem ht_weylAction_inv_single_pos {w : W} {i : Fin D.rank} (h : ¬ (cs).IsLeftDescent w i) :
    0 < ht (ρ w⁻¹ (Pi.single i 1)) :=
  ht_weylAction_single_pos (by rwa [CoxeterSystem.isRightDescent_inv_iff])

theorem ht_single_pos (i : Fin D.rank) : 0 < ht (Pi.single i 1 : Fin D.rank → ℤ) := by
  rw [ht_single]
  exact one_pos

theorem wordAct_ofCartan (ω : List (Fin D.rank)) (v : Fin D.rank → ℤ) :
    wordAct (Φ).refl ω v = ρ ((cs).wordProd ω) v :=
  (OfCartan.weylAction_wordProd D.isFiniteType ω v).symm

theorem rootGroup_le_posUnipotent {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) (h : 0 < ht γ) :
    D.rootGroup γ ≤ posUnipotent D :=
  le_iSup₂_of_le (f := fun γ (_ : γ ∈ {γ | γ ∈ D.roots ∧ 0 < ht γ}) => D.rootGroup γ) γ ⟨hγ, h⟩
    le_rfl

theorem rootGroup_le_negUnipotent {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) (h : ht γ < 0) :
    D.rootGroup γ ≤ negUnipotent D :=
  le_iSup₂_of_le (f := fun γ (_ : γ ∈ {γ | γ ∈ D.roots ∧ ht γ < 0}) => D.rootGroup γ) γ ⟨hγ, h⟩
    le_rfl

theorem posUnipotent_inf_negUnipotent (hext : SteinbergExtras D n H) :
    posUnipotent D ⊓ negUnipotent D = ⊥ :=
  hext.posPart_inf_negPart

theorem iSup_le_borel : ⨆ i, H i ≤ borel D H := le_sup_left

theorem posUnipotent_le_borel : posUnipotent D ≤ borel D H := le_sup_right

theorem rootGroup_le_borel {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) (h : 0 < ht γ) :
    D.rootGroup γ ≤ borel D H :=
  (rootGroup_le_posUnipotent hγ h).trans posUnipotent_le_borel

theorem bruhatExtras_iff : BruhatExtras D H ↔
    ((⨆ i, H i) ⊔ ⨆ γ ∈ {γ | γ ∈ D.roots ∧ 0 < ht γ}, D.rootGroup γ) ⊓
      (⨆ γ ∈ {γ | γ ∈ D.roots ∧ ht γ < 0}, D.rootGroup γ) = ⊥ :=
  ⟨fun h => h.borel_inf_negUnipotent, fun h => ⟨h⟩⟩

namespace ActsAs

theorem one : ActsAs D 1 1 := fun γ _ => by
  rw [map_conj_one, map_one, Module.End.one_apply]

theorem mul {x y : K} {w w' : W} (hx : ActsAs D x w) (hy : ActsAs D y w') :
    ActsAs D (x * y) (w * w') := fun γ hγ => by
  rw [map_conj_mul, hy γ hγ, hx _ (weylAction_mem_roots _ w' hγ), weylAction_mul_apply]

theorem inv {x : K} {w : W} (hx : ActsAs D x w) : ActsAs D x⁻¹ w⁻¹ := fun γ hγ => by
  have h := hx _ (weylAction_mem_roots _ w⁻¹ hγ)
  rw [weylAction_apply_inv_apply] at h
  exact map_conj_inv_of_map_conj h

theorem conj_mem {x y : K} {w : W} (hx : ActsAs D x w) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots)
    (hy : y ∈ D.rootGroup γ) : x * y * x⁻¹ ∈ D.rootGroup (ρ w γ) := by
  rw [← hx γ hγ]
  exact conj_mem_map_conj hy

theorem inv_conj_mem {x y : K} {w : W} (hx : ActsAs D x w) {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) (hy : y ∈ D.rootGroup γ) : x⁻¹ * y * x ∈ D.rootGroup (ρ w⁻¹ γ) := by
  have h := hx.inv.conj_mem hγ hy
  rwa [inv_inv] at h

end ActsAs

theorem eq_one_of_forall_rootGroup_eq (hext : SteinbergExtras D n H) {v : W}
    (h : ∀ γ ∈ D.roots, D.rootGroup (ρ v γ) = D.rootGroup γ) : v = 1 := by
  by_contra hv
  obtain ⟨i, hi⟩ := (cs).exists_rightDescent_of_ne_one hv
  have hα : Pi.single i 1 ∈ D.roots := (Φ).single_mem i
  apply hext.ne_bot _ hα
  rw [eq_bot_iff, ← posUnipotent_inf_negUnipotent hext]
  refine le_inf (rootGroup_le_posUnipotent hα (ht_single_pos i)) ?_
  rw [← h _ hα]
  exact rootGroup_le_negUnipotent (weylAction_mem_roots _ v hα) (ht_weylAction_single_neg hi)

theorem ActsAs.unique (hext : SteinbergExtras D n H) {x : K} {w w' : W} (hw : ActsAs D x w)
    (hw' : ActsAs D x w') : w = w' := by
  have h := eq_one_of_forall_rootGroup_eq hext (v := w * w'⁻¹) fun γ hγ => by
    have hγ' := weylAction_mem_roots D.isFiniteType w'⁻¹ hγ
    rw [weylAction_mul_apply, ← hw _ hγ', hw' _ hγ', weylAction_apply_inv_apply]
  exact mul_inv_eq_one.1 h

variable (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)

include hct in
theorem actsAs_n (i : Fin D.rank) : ActsAs D (n i) ((cs).simple i) := fun γ hγ => by
  rw [map_conj_rootGroup hct i hγ, weylAction_simple]
  rfl

include hct in
theorem actsAs_list_prod (ω : List (Fin D.rank)) : ActsAs D (ω.map n).prod ((cs).wordProd ω) := by
  induction ω with
  | nil =>
    rw [List.map_nil, List.prod_nil, CoxeterSystem.wordProd_nil]
    exact ActsAs.one
  | cons i ω ih =>
    rw [List.map_cons, List.prod_cons, CoxeterSystem.wordProd_cons]
    exact (actsAs_n hct i).mul ih

@[expose] noncomputable def nrep (w : W) : K := posLift (cs) n hct.braid w

theorem nrep_eq_posLift (w : W) : nrep hct w = posLift (cs) n hct.braid w := rfl

theorem nrep_wordProd {ω : List (Fin D.rank)} (hω : (cs).IsReduced ω) :
    nrep hct ((cs).wordProd ω) = (ω.map n).prod :=
  posLift_wordProd _ _ _ hω

theorem nrep_one : nrep hct 1 = 1 := posLift_one ..

theorem nrep_simple_mul {w : W} {i : Fin D.rank} (h : ¬ (cs).IsLeftDescent w i) :
    nrep hct ((cs).simple i * w) = n i * nrep hct w :=
  posLift_simple_mul _ _ _ h

theorem nrep_mul {w w' : W} (h : (cs).length (w * w') = (cs).length w + (cs).length w') :
    nrep hct (w * w') = nrep hct w * nrep hct w' :=
  posLift_mul _ _ _ h

theorem nrep_simple (i : Fin D.rank) : nrep hct ((cs).simple i) = n i := by
  have h := nrep_simple_mul hct ((cs).not_isLeftDescent_one i)
  rwa [mul_one, nrep_one, mul_one] at h

theorem actsAs_nrep (w : W) : ActsAs D (nrep hct w) w := by
  obtain ⟨ω, hω, rfl⟩ := (cs).exists_isReduced w
  rw [nrep_wordProd hct hω]
  exact actsAs_list_prod hct ω

include hct in
theorem iSup_le_normalizer_rootGroup {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) :
    ⨆ i, H i ≤ Subgroup.normalizer (D.rootGroup γ : Set K) :=
  iSup_le fun _ _ hh => mem_normalizer_rootGroup hct hh hγ

include hct in
theorem actsAs_of_mem_iSup {t : K} (ht : t ∈ ⨆ i, H i) : ActsAs D t 1 := fun γ hγ => by
  rw [mem_normalizer_iff_map_conj.1 (iSup_le_normalizer_rootGroup hct hγ ht), map_one,
    Module.End.one_apply]

include hct in
theorem sq_n_mem_iSup (i : Fin D.rank) : n i ^ 2 ∈ ⨆ k, H k := le_iSup H i (hct.sq_mem i)

include hct in
theorem conj_n_mem_iSup (i : Fin D.rank) {t : K} (ht : t ∈ ⨆ k, H k) :
    n i * t * (n i)⁻¹ ∈ ⨆ k, H k := by
  have hle : (⨆ k, H k).map (MulAut.conj (n i)).toMonoidHom ≤ ⨆ k, H k := by
    rw [Subgroup.map_iSup]
    exact iSup_le fun k => map_conj_le_iff.2 fun x hx =>
      sup_le (le_iSup H i) (le_iSup H k) (hct.conj_H_mem i k x hx)
  exact hle (conj_mem_map_conj ht)

include hct in
theorem inv_conj_n_mem_iSup (i : Fin D.rank) {t : K} (ht : t ∈ ⨆ k, H k) :
    (n i)⁻¹ * t * n i ∈ ⨆ k, H k := by
  have e : (n i)⁻¹ * t * n i = (n i ^ 2)⁻¹ * (n i * t * (n i)⁻¹) * n i ^ 2 := by group
  rw [e]
  exact mul_mem (mul_mem (inv_mem (sq_n_mem_iSup hct i)) (conj_n_mem_iSup hct i ht))
    (sq_n_mem_iSup hct i)

include hct in
theorem n_mem_normalizer_iSup (i : Fin D.rank) :
    n i ∈ Subgroup.normalizer ((⨆ k, H k : Subgroup K) : Set K) :=
  Subgroup.mem_normalizer_iff.2 fun t => ⟨conj_n_mem_iSup hct i, fun h => by
    have h' := inv_conj_n_mem_iSup hct i h
    rwa [show (n i)⁻¹ * (n i * t * (n i)⁻¹) * n i = t by group] at h'⟩

theorem iSup_le_weylN : ⨆ i, H i ≤ weylN n H := le_sup_left

theorem n_mem_weylN (i : Fin D.rank) : n i ∈ weylN n H :=
  (le_sup_right : Subgroup.closure (Set.range n) ≤ weylN n H) (Subgroup.subset_closure ⟨i, rfl⟩)

theorem list_prod_mem_weylN (ω : List (Fin D.rank)) : (ω.map n).prod ∈ weylN n H :=
  Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact n_mem_weylN i

theorem nrep_mem_weylN (w : W) : nrep hct w ∈ weylN n H :=
  posLift_mem _ _ _ _ n_mem_weylN w

include hct in
theorem weylN_le_normalizer : weylN n H ≤ Subgroup.normalizer ((⨆ k, H k : Subgroup K) : Set K) :=
  sup_le Subgroup.le_normalizer
    ((Subgroup.closure_le _).2 (Set.range_subset_iff.2 (n_mem_normalizer_iSup hct)))

include hct in
theorem conj_mem_iSup_of_mem_weylN {x t : K} (hx : x ∈ weylN n H) (ht : t ∈ ⨆ i, H i) :
    x * t * x⁻¹ ∈ ⨆ i, H i :=
  (Subgroup.mem_normalizer_iff.1 (weylN_le_normalizer hct hx) t).1 ht

include hct in
theorem inv_conj_mem_iSup_of_mem_weylN {x t : K} (hx : x ∈ weylN n H) (ht : t ∈ ⨆ i, H i) :
    x⁻¹ * t * x ∈ ⨆ i, H i := by
  simpa using conj_mem_iSup_of_mem_weylN hct (inv_mem hx) ht

include hct in
theorem mem_weylN_iff {x : K} :
    x ∈ weylN n H ↔ ∃ t ∈ ⨆ i, H i, ∃ ω : List (Fin D.rank), x = t * (ω.map n).prod := by
  refine ⟨fun hx => ?_, fun ⟨t, ht, ω, he⟩ => he ▸ mul_mem (iSup_le_weylN ht)
    (list_prod_mem_weylN ω)⟩
  have hx' : x ∈ Subgroup.closure (((⨆ i, H i : Subgroup K) : Set K) ∪ Set.range n) := by
    rwa [Subgroup.closure_union, Subgroup.closure_eq]
  clear hx
  induction hx' using Subgroup.closure_induction_left with
  | one => exact ⟨1, one_mem _, [], by simp⟩
  | mul_left x hx y _ ih =>
    obtain ⟨t, ht, ω, rfl⟩ := ih
    rcases hx with hx | ⟨i, rfl⟩
    · exact ⟨x * t, mul_mem hx ht, ω, by group⟩
    · refine ⟨n i * t * (n i)⁻¹, conj_n_mem_iSup hct i ht, i :: ω, ?_⟩
      rw [List.map_cons, List.prod_cons]
      group
  | inv_mul_cancel x hx y _ ih =>
    obtain ⟨t, ht, ω, rfl⟩ := ih
    rcases hx with hx | ⟨i, rfl⟩
    · exact ⟨x⁻¹ * t, mul_mem (inv_mem hx) ht, ω, by group⟩
    · refine ⟨(n i)⁻¹ * t * n i * (n i ^ 2)⁻¹,
        mul_mem (inv_conj_n_mem_iSup hct i ht) (inv_mem (sq_n_mem_iSup hct i)), i :: ω, ?_⟩
      rw [List.map_cons, List.prod_cons]
      group

include hct in
theorem exists_actsAs {x : K} (hx : x ∈ weylN n H) : ∃ w : W, ActsAs D x w := by
  obtain ⟨t, ht, ω, rfl⟩ := (mem_weylN_iff hct).1 hx
  exact ⟨1 * (cs).wordProd ω, (actsAs_of_mem_iSup hct ht).mul (actsAs_list_prod hct ω)⟩

include hct in
theorem existsUnique_actsAs (hext : SteinbergExtras D n H) {x : K} (hx : x ∈ weylN n H) :
    ∃! w : W, ActsAs D x w :=
  let ⟨w, hw⟩ := exists_actsAs hct hx
  ⟨w, hw, fun _ hw' => hw'.unique hext hw⟩

include hct in
theorem exists_conj_n_eq (hext : SteinbergExtras D n H) {x : K} {w : W} (hx : ActsAs D x w)
    {j a : Fin D.rank} (h : ρ w (Pi.single j 1) = Pi.single a 1) :
    ∃ t ∈ H a, x * n j * x⁻¹ = n a * t := by
  have hα := (Φ).single_mem j
  have hα' := (Φ).neg_mem _ hα
  have h1 : (D.rootGroup (Pi.single j 1)).map (MulAut.conj x).toMonoidHom =
      D.rootGroup (Pi.single a 1) := by
    rw [hx _ hα, h]
  have h2 : (D.rootGroup (-Pi.single j 1)).map (MulAut.conj x).toMonoidHom =
      D.rootGroup (-Pi.single a 1) := by
    rw [hx _ hα', map_neg, h]
  have hnj := actsAs_n hct j
  have hL : (rankOne D.rootGroup j).map (MulAut.conj x).toMonoidHom = rankOne D.rootGroup a := by
    simp only [rankOne, Subgroup.map_sup, h1, h2]
  have hg : x * n j * x⁻¹ ∈ rankOne D.rootGroup a := hL ▸ conj_mem_map_conj (hct.n_mem j)
  have hg1 : (D.rootGroup (Pi.single a 1)).map (MulAut.conj (x * n j * x⁻¹)).toMonoidHom =
      D.rootGroup (-Pi.single a 1) := by
    rw [map_conj_mul, map_conj_mul, map_conj_inv_of_map_conj h1, hnj _ hα,
      weylAction_simple_single, h2]
  have hg2 : (D.rootGroup (-Pi.single a 1)).map (MulAut.conj (x * n j * x⁻¹)).toMonoidHom =
      D.rootGroup (Pi.single a 1) := by
    rw [map_conj_mul, map_conj_mul, map_conj_inv_of_map_conj h2, hnj _ hα', map_neg,
      weylAction_simple_single, neg_neg, h1]
  obtain ⟨t, ht, he⟩ := (isSteinberg_of hct hext).exists_eq_n_mul (i := a) hg hg1 hg2
  rw [torus_toRootGroupData_apply hct hext] at ht
  exact ⟨t, ht, he⟩

include hct in
theorem list_prod_mem_iSup_of_wordProd_eq_one (hext : SteinbergExtras D n H)
    (ω : List (Fin D.rank)) (hω : (cs).wordProd ω = 1) : (ω.map n).prod ∈ ⨆ i, H i := by
  induction hm : ω.length using Nat.strong_induction_on generalizing ω with
  | _ m ih =>
  rcases List.eq_nil_or_concat' ω with rfl | ⟨l, j, rfl⟩
  · simp
  have hl : (cs).wordProd l = (cs).simple j := by
    rw [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_singleton] at hω
    rw [← (cs).inv_simple j]
    exact eq_inv_of_mul_eq_one_left hω
  have hρ : wordAct (Φ).refl l (Pi.single j 1) ∉ (Φ).pos := by
    rw [wordAct_ofCartan, hl, weylAction_simple_single]
    intro h
    have h' := h.2
    rw [ht_neg, ht_single] at h'
    omega
  obtain ⟨p, a, v, rfl, hv, hav⟩ :=
    exists_split_wordAct (Φ).refl (P := (· ∈ (Φ).pos)) ((Φ).single_mem_pos j) l hρ
  have hβ : wordAct (Φ).refl v (Pi.single j 1) = Pi.single a 1 := by
    by_contra hne
    have hne2 : wordAct (Φ).refl v (Pi.single j 1) ≠ 2 • Pi.single a 1 :=
      (Φ).isIndiv_wordAct v ((Φ).isIndiv_single j) _ ((Φ).single_mem a)
    have hmem : wordAct (Φ).refl v (Pi.single j 1) ∈ (Φ).posExcept a := by
      refine ⟨hv, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hne, hne2⟩
    exact hav ((Φ).refl_mem_posExcept hmem).1
  rw [wordAct_ofCartan] at hβ
  obtain ⟨t, ht, he⟩ := exists_conj_n_eq hct hext (actsAs_list_prod hct v) hβ
  have hT : ((v.map n).prod)⁻¹ * (n a * n a * t) * (v.map n).prod ∈ ⨆ i, H i :=
    inv_conj_mem_iSup_of_mem_weylN hct (list_prod_mem_weylN v)
      (mul_mem (by rw [← pow_two]; exact sq_n_mem_iSup hct a) (le_iSup H a ht))
  have key : ((p ++ a :: v ++ [j]).map n).prod =
      ((p ++ v).map n).prod * (((v.map n).prod)⁻¹ * (n a * n a * t) * (v.map n).prod) := by
    simp only [List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons,
      List.prod_nil, mul_one]
    generalize (v.map n).prod = c at he ⊢
    have hnj : n j = c⁻¹ * (n a * t) * c := by rw [← he]; group
    rw [hnj]
    group
  have hpv : (cs).wordProd (p ++ v) = 1 := by
    have h1 := actsAs_list_prod hct (p ++ a :: v ++ [j])
    rw [hω, key] at h1
    have h2 := h1.mul (actsAs_of_mem_iSup hct hT).inv
    rw [mul_inv_cancel_right, inv_one, mul_one] at h2
    exact (actsAs_list_prod hct (p ++ v)).unique hext h2
  rw [key]
  refine mul_mem (ih _ ?_ (p ++ v) hpv rfl) hT
  rw [← hm]
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

include hct in
theorem mem_iSup_of_actsAs_one (hext : SteinbergExtras D n H) {x : K} (hx : x ∈ weylN n H)
    (h : ActsAs D x 1) : x ∈ ⨆ i, H i := by
  obtain ⟨t, ht, ω, rfl⟩ := (mem_weylN_iff hct).1 hx
  have h1 : (cs).wordProd ω = 1 := by
    have h2 := (actsAs_of_mem_iSup hct ht).inv.mul h
    rw [inv_mul_cancel_left, inv_one, one_mul] at h2
    exact (actsAs_list_prod hct ω).unique hext h2
  exact mul_mem ht (list_prod_mem_iSup_of_wordProd_eq_one hct hext ω h1)

noncomputable def weylNHom (hext : SteinbergExtras D n H) : weylN n H →* W where
  toFun x := (exists_actsAs hct x.2).choose
  map_one' := (exists_actsAs hct (1 : weylN n H).2).choose_spec.unique hext ActsAs.one
  map_mul' x y := (exists_actsAs hct (x * y).2).choose_spec.unique hext
    ((exists_actsAs hct x.2).choose_spec.mul (exists_actsAs hct y.2).choose_spec)

variable (hext : SteinbergExtras D n H)

theorem actsAs_weylNHom (x : weylN n H) : ActsAs D x (weylNHom hct hext x) :=
  (exists_actsAs hct x.2).choose_spec

theorem weylNHom_eq_iff {x : weylN n H} {w : W} : weylNHom hct hext x = w ↔ ActsAs D x w :=
  ⟨fun h => h ▸ actsAs_weylNHom hct hext x, (actsAs_weylNHom hct hext x).unique hext⟩

theorem weylNHom_n (i : Fin D.rank) : weylNHom hct hext ⟨n i, n_mem_weylN i⟩ = (cs).simple i :=
  (weylNHom_eq_iff hct hext).2 (actsAs_n hct i)

theorem weylNHom_nrep (w : W) : weylNHom hct hext ⟨nrep hct w, nrep_mem_weylN hct w⟩ = w :=
  (weylNHom_eq_iff hct hext).2 (actsAs_nrep hct w)

theorem weylNHom_of_mem_iSup {t : K} (ht : t ∈ ⨆ i, H i) :
    weylNHom hct hext ⟨t, iSup_le_weylN ht⟩ = 1 :=
  (weylNHom_eq_iff hct hext).2 (actsAs_of_mem_iSup hct ht)

theorem weylNHom_surjective : Function.Surjective (weylNHom hct hext) :=
  fun w => ⟨_, weylNHom_nrep hct hext w⟩

theorem ker_weylNHom : (weylNHom hct hext).ker = (⨆ i, H i).subgroupOf (weylN n H) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  exact ⟨fun h => mem_iSup_of_actsAs_one hct hext x.2 ((weylNHom_eq_iff hct hext).1 h),
    fun h => (weylNHom_eq_iff hct hext).2 (actsAs_of_mem_iSup hct h)⟩

include hct hext in
theorem iSup_subgroupOf_weylN_normal : ((⨆ i, H i).subgroupOf (weylN n H)).Normal :=
  ker_weylNHom hct hext ▸ (weylNHom hct hext).normal_ker

noncomputable def weylNQuotientEquiv :
    haveI := iSup_subgroupOf_weylN_normal hct hext
    weylN n H ⧸ (⨆ i, H i).subgroupOf (weylN n H) ≃* W :=
  haveI := iSup_subgroupOf_weylN_normal hct hext
  (QuotientGroup.quotientMulEquivOfEq (ker_weylNHom hct hext).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (weylNHom_surjective hct hext))

include hct in
theorem borel_le_normalizer_posUnipotent :
    borel D H ≤ Subgroup.normalizer (posUnipotent D : Set K) :=
  sup_le (iSup_le fun _ => le_normalizer_iSup fun _ => le_normalizer_iSup fun hγ =>
    fun _ hh => mem_normalizer_rootGroup hct hh hγ.1) Subgroup.le_normalizer

include hct hext in
theorem eq_one_of_actsAs_of_mem_borel {x : K} {w : W} (hx : x ∈ borel D H) (h : ActsAs D x w) :
    w = 1 := by
  by_contra hw
  obtain ⟨i, hi⟩ := (cs).exists_rightDescent_of_ne_one hw
  have hα := (Φ).single_mem i
  have hγ := weylAction_mem_roots D.isFiniteType w hα
  apply hext.ne_bot _ hγ
  rw [eq_bot_iff, ← posUnipotent_inf_negUnipotent hext]
  refine le_inf ?_ (rootGroup_le_negUnipotent hγ (ht_weylAction_single_neg hi))
  rw [← h _ hα, ← mem_normalizer_iff_map_conj.1 (borel_le_normalizer_posUnipotent hct hx)]
  exact Subgroup.map_mono (rootGroup_le_posUnipotent hα (ht_single_pos i))

include hct hext in
theorem borel_inf_weylN : borel D H ⊓ weylN n H = ⨆ i, H i := by
  refine le_antisymm (fun x hx => ?_) (le_inf iSup_le_borel iSup_le_weylN)
  obtain ⟨hB, hN⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨w, hw⟩ := exists_actsAs hct hN
  exact mem_iSup_of_actsAs_one hct hext hN (eq_one_of_actsAs_of_mem_borel hct hext hB hw ▸ hw)

include hext in
theorem nrep_mem_borel_iff {w : W} : nrep hct w ∈ borel D H ↔ w = 1 :=
  ⟨fun h => eq_one_of_actsAs_of_mem_borel hct hext h (actsAs_nrep hct w),
    fun h => h ▸ (nrep_one hct).symm ▸ one_mem _⟩

end Weyl

end CFSG.LieType.Steinberg
