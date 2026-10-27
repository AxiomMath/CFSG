module

public import CFSG.LieType.Steinberg.Bruhat
public import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic.Group

public section

namespace CFSG.LieType.TitsSimplicity

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg
open scoped commutatorElement

variable {K : Type*} [Group K]

structure RootGroupCommutators (D : UniversalRootDatum K) : Prop where
  commutator_le : ∀ γ ∈ D.roots, 2 • γ ∈ D.roots →
    ⁅D.rootGroup γ, D.rootGroup γ⁆ ≤ D.rootGroup (2 • γ)
  commutator_eq_bot : ∀ γ ∈ D.roots, 2 • γ ∉ D.roots → ⁅D.rootGroup γ, D.rootGroup γ⁆ = ⊥
  commutator_two_smul_eq_bot : ∀ γ ∈ D.roots, 2 • γ ∈ D.roots →
    ⁅D.rootGroup γ, D.rootGroup (2 • γ)⁆ = ⊥

@[expose] def heightUnipotent (D : UniversalRootDatum K) (k : ℤ) : Subgroup K :=
  ⨆ γ ∈ {γ | γ ∈ D.roots ∧ k ≤ ht γ}, D.rootGroup γ

variable {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem
set_option hygiene false in
local notation "ρ" => weylAction D.isFiniteType

theorem iSup_le_centralizer_iSup (hext : SteinbergExtras D n H) :
    ⨆ i, H i ≤ Subgroup.centralizer ((⨆ i, H i : Subgroup K) : Set K) := by
  refine iSup_le fun i => ?_
  rw [Subgroup.le_centralizer_iff]
  exact iSup_le fun j h' hh' h hh => (hext.torus_commute i j h hh h' hh').eq

variable (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)

include hct hext in
theorem isSolvable_borel (hU : Group.IsSolvable (posUnipotent D)) :
    Group.IsSolvable (borel D H) := by
  have := hU
  set U : Subgroup (borel D H) := (posUnipotent D).subgroupOf (borel D H) with hUdef
  have : U.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer posUnipotent_le_borel).2
    (borel_le_normalizer_posUnipotent hct)
  have : Group.IsSolvable U :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe posUnipotent_le_borel).toMonoidHom)
      (MulEquiv.injective _)
  have key : ∀ x : borel D H, ∃ t : borel D H, (t : K) ∈ ⨆ i, H i ∧
      (QuotientGroup.mk x : borel D H ⧸ U) = QuotientGroup.mk t := by
    rintro ⟨x, hx⟩
    have hx' := hx
    rw [← SetLike.mem_coe, coe_borel hct, Set.mem_mul] at hx'
    obtain ⟨t, ht, u, hu, rfl⟩ := hx'
    refine ⟨⟨t, iSup_le_borel ht⟩, ht, ?_⟩
    rw [QuotientGroup.eq, hUdef, Subgroup.mem_subgroupOf]
    change (t * u)⁻¹ * t ∈ posUnipotent D
    rw [show (t * u)⁻¹ * t = u⁻¹ by group]
    exact inv_mem hu
  have : Group.IsSolvable (borel D H ⧸ U) := Group.isSolvable_of_comm fun a b => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨t, ht, hxt⟩ := key x
    obtain ⟨t', ht', hyt⟩ := key y
    rw [hxt, hyt, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg _ (Subtype.ext (iSup_le_centralizer_iSup hext ht' t ht))
  exact Group.isSolvable_of_subgroup_quotient U

omit [Group K] in
theorem ht_nsmul_add_nsmul {ι : Type*} [Fintype ι] (a b : ℕ) (δ γ : ι → ℤ) :
    ht (a • δ + b • γ) = a * ht δ + b * ht γ := by
  rw [ht_add, ht_nsmul, ht_nsmul]

theorem rootGroup_le_heightUnipotent {k : ℤ} {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots)
    (h : k ≤ ht γ) : D.rootGroup γ ≤ heightUnipotent D k :=
  le_iSup₂_of_le (f := fun γ (_ : γ ∈ {γ | γ ∈ D.roots ∧ k ≤ ht γ}) => D.rootGroup γ) γ ⟨hγ, h⟩
    le_rfl

theorem heightUnipotent_anti {k l : ℤ} (h : k ≤ l) : heightUnipotent D l ≤ heightUnipotent D k :=
  iSup₂_le fun _ hγ => rootGroup_le_heightUnipotent hγ.1 (h.trans hγ.2)

theorem heightUnipotent_one : heightUnipotent D 1 = posUnipotent D := by
  have : {γ | γ ∈ D.roots ∧ (1 : ℤ) ≤ ht γ} = {γ | γ ∈ D.roots ∧ 0 < ht γ} := by
    ext γ
    simp only [Set.mem_ofPred_eq]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
  rw [heightUnipotent, posUnipotent, this]

theorem heightUnipotent_le_posUnipotent {k : ℤ} (hk : 1 ≤ k) :
    heightUnipotent D k ≤ posUnipotent D :=
  heightUnipotent_one (D := D) ▸ heightUnipotent_anti hk

theorem exists_forall_ht_le : ∃ h : ℤ, ∀ γ ∈ D.roots, ht γ ≤ h := by
  obtain ⟨h, hh⟩ := ((finite_roots D.isFiniteType D.divisible).image ht).bddAbove
  exact ⟨h, fun γ hγ => hh ⟨γ, hγ, rfl⟩⟩

theorem heightUnipotent_eq_bot {k : ℤ} (h : ∀ γ ∈ D.roots, ht γ < k) :
    heightUnipotent D k = ⊥ :=
  eq_bot_iff.2 (iSup₂_le fun γ hγ => absurd hγ.2 (not_le.2 (h γ hγ.1)))

theorem iSup₂_induction {V : Type*} {X : V → Subgroup K} {P : Set V} {C : K → Prop} {x : K}
    (hx : x ∈ ⨆ γ ∈ P, X γ) (mem : ∀ γ ∈ P, ∀ y ∈ X γ, C y) (one : C 1)
    (mul : ∀ y z, C y → C z → C (y * z)) : C x :=
  Subgroup.iSup_induction (C := C) _ hx (fun γ _ hy => Subgroup.iSup_induction (C := C) _ hy
    (fun hγ y hy => mem γ hγ y hy) one mul) one mul

include hext in
theorem commutator_mem_heightUnipotent_of_mem (hE : RootGroupCommutators D) {k : ℤ}
    (hk : 1 ≤ k) {δ γ : Fin D.rank → ℤ} (hδ : δ ∈ D.roots) (hδp : 0 < ht δ) (hγ : γ ∈ D.roots)
    (hγk : k ≤ ht γ) {x y : K} (hx : x ∈ D.rootGroup δ) (hy : y ∈ D.rootGroup γ) :
    ⁅x, y⁆ ∈ heightUnipotent D (k + 1) := by
  by_cases hli : LinIndepPair δ γ
  · refine (iSup₂_le fun ε hε => ?_ : ⨆ ε ∈ openCone D.roots δ γ, D.rootGroup ε ≤ _)
      (hext.commutator_mem δ hδ γ hγ hli x hx y hy)
    obtain ⟨hεr, a, b, ha, hb, rfl⟩ := hε
    refine rootGroup_le_heightUnipotent hεr ?_
    rw [ht_nsmul_add_nsmul]
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith
  rcases OfCartan.proportional D.isFiniteType hδ hγ hli with h | h | h | h | h | h
  ·
    rw [h] at hx
    by_cases h2 : 2 • γ ∈ D.roots
    · refine rootGroup_le_heightUnipotent h2 ?_
        (hE.commutator_le γ hγ h2 (Subgroup.commutator_mem_commutator hx hy))
      rw [ht_two_smul]
      omega
    · have h' := Subgroup.commutator_mem_commutator hx hy
      rw [hE.commutator_eq_bot γ hγ h2, Subgroup.mem_bot] at h'
      rw [h']
      exact one_mem _
  ·
    rw [h, ht_neg] at hδp
    omega
  ·
    rw [h] at hx hδ
    have h' := Subgroup.commutator_mem_commutator hy hx
    rw [hE.commutator_two_smul_eq_bot γ hγ hδ, Subgroup.mem_bot] at h'
    rw [← commutatorElement_inv, h', inv_one]
    exact one_mem _
  ·
    rw [h, ht_neg, ht_two_smul] at hδp
    omega
  ·
    rw [h] at hy hγ
    have h' := Subgroup.commutator_mem_commutator hx hy
    rw [hE.commutator_two_smul_eq_bot δ hδ hγ, Subgroup.mem_bot] at h'
    rw [h']
    exact one_mem _
  ·
    rw [h, ht_neg, ht_two_smul] at hγk
    omega

include hext in
theorem commutator_mem_heightUnipotent (hE : RootGroupCommutators D) {k : ℤ} (hk : 1 ≤ k)
    (hN : posUnipotent D ≤ Subgroup.normalizer (heightUnipotent D (k + 1) : Set K))
    {δ : Fin D.rank → ℤ} (hδ : δ ∈ D.roots) (hδp : 0 < ht δ) {x y : K}
    (hx : x ∈ D.rootGroup δ) (hy : y ∈ heightUnipotent D k) :
    ⁅x, y⁆ ∈ heightUnipotent D (k + 1) := by
  have hy' : y ∈ ⨆ γ ∈ {γ | γ ∈ D.roots ∧ k ≤ ht γ}, D.rootGroup γ := hy
  have h := iSup₂_induction
    (C := fun y => y ∈ posUnipotent D ∧ ⁅x, y⁆ ∈ heightUnipotent D (k + 1)) hy'
    (fun γ hγ y hy => ⟨heightUnipotent_le_posUnipotent hk
      (rootGroup_le_heightUnipotent hγ.1 hγ.2 hy),
      commutator_mem_heightUnipotent_of_mem hext hE hk hδ hδp hγ.1 hγ.2 hx hy⟩)
    ⟨one_mem _, by rw [commutatorElement_one_right]; exact one_mem _⟩
    (fun y z hy hz => ⟨mul_mem hy.1 hz.1, by
      have e : ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact mul_mem hy.2 ((Subgroup.mem_normalizer_iff.1 (hN hy.1) _).1 hz.2)⟩)
  exact h.2

theorem le_normalizer_heightUnipotent {k : ℤ}
    (h : ∀ δ ∈ D.roots, 0 < ht δ → ∀ x ∈ D.rootGroup δ, ∀ y ∈ heightUnipotent D k,
      ⁅x, y⁆ ∈ heightUnipotent D (k + 1)) :
    posUnipotent D ≤ Subgroup.normalizer (heightUnipotent D k : Set K) :=
  iSup₂_le fun δ hδ => le_normalizer_of_map_conj_le fun x hx => map_conj_le_iff.2 fun y hy => by
    have e : x * y * x⁻¹ = ⁅x, y⁆ * y := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (heightUnipotent_anti (by omega) (h δ hδ.1 hδ.2 x hx y hy)) hy

include hext in
theorem posUnipotent_le_normalizer_heightUnipotent (hE : RootGroupCommutators D) {k : ℤ}
    (hk : 1 ≤ k) : posUnipotent D ≤ Subgroup.normalizer (heightUnipotent D k : Set K) := by
  obtain ⟨h, hh⟩ := exists_forall_ht_le (D := D)
  have htop : ∀ l, h < l → posUnipotent D ≤ Subgroup.normalizer (heightUnipotent D l : Set K) :=
    fun l hl => by
      rw [heightUnipotent_eq_bot fun γ hγ => (hh γ hγ).trans_lt hl,
        Subgroup.normalizer_eq_top_iff.2 inferInstance]
      exact le_top
  by_cases hkh : h < k
  · exact htop k hkh
  rw [not_lt] at hkh
  refine Int.leInductionDown (m := h + 1)
    (motive := fun l _ => 1 ≤ l →
      posUnipotent D ≤ Subgroup.normalizer (heightUnipotent D l : Set K))
    (fun _ => htop (h + 1) (by omega)) (fun l _ ih hl1 => ?_) k (by omega) hk
  have ih' := ih (by omega)
  rw [show l = l - 1 + 1 by ring] at ih'
  exact le_normalizer_heightUnipotent fun δ hδ hδp x hx y hy =>
    commutator_mem_heightUnipotent hext hE hl1 ih' hδ hδp hx hy

include hext in
theorem commutator_posUnipotent_heightUnipotent_le (hE : RootGroupCommutators D) {k : ℤ}
    (hk : 1 ≤ k) : ⁅posUnipotent D, heightUnipotent D k⁆ ≤ heightUnipotent D (k + 1) := by
  have hN := posUnipotent_le_normalizer_heightUnipotent hext hE (k := k + 1) (by omega)
  rw [Subgroup.commutator_le]
  intro g hg y hy
  have hg' : g ∈ ⨆ δ ∈ {γ | γ ∈ D.roots ∧ 0 < ht γ}, D.rootGroup δ := hg
  have h := iSup₂_induction
    (C := fun g => g ∈ posUnipotent D ∧ ⁅g, y⁆ ∈ heightUnipotent D (k + 1)) hg'
    (fun δ hδ x hx => ⟨rootGroup_le_posUnipotent hδ.1 hδ.2 hx,
      commutator_mem_heightUnipotent hext hE hk hN hδ.1 hδ.2 hx hy⟩)
    ⟨one_mem _, by rw [commutatorElement_one_left]; exact one_mem _⟩
    (fun g g' hg hg' => ⟨mul_mem hg.1 hg'.1, by
      have e : ⁅g * g', y⁆ = g * ⁅g', y⁆ * g⁻¹ * ⁅g, y⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact mul_mem ((Subgroup.mem_normalizer_iff.1 (hN hg.1) _).1 hg'.2) hg.2⟩)
  exact h.2

include hext in
theorem isNilpotent_posUnipotent (hE : RootGroupCommutators D) :
    Group.IsNilpotent (posUnipotent D) := by
  have hlcs : ∀ m : ℕ, (posUnipotent D).lowerCentralSeries m ≤ heightUnipotent D (m + 1) := by
    intro m
    induction m with
    | zero => rw [Subgroup.lowerCentralSeries_zero, Nat.cast_zero, zero_add, heightUnipotent_one]
    | succ m ih =>
      rw [Subgroup.lowerCentralSeries_succ, Subgroup.commutator_comm]
      refine (Subgroup.commutator_mono le_rfl ih).trans ?_
      push_cast
      exact commutator_posUnipotent_heightUnipotent_le hext hE (by omega)
  obtain ⟨h, hh⟩ := exists_forall_ht_le (D := D)
  obtain ⟨N, hN⟩ := exists_nat_gt h
  rw [Subgroup.isNilpotent_iff_lowerCentralSeries]
  refine ⟨N, eq_bot_iff.2 ((hlcs N).trans (heightUnipotent_eq_bot fun γ hγ => ?_).le)⟩
  have := hh γ hγ
  omega

include hext in
theorem isSolvable_posUnipotent (hE : RootGroupCommutators D) :
    Group.IsSolvable (posUnipotent D) := by
  have := isNilpotent_posUnipotent hext hE
  infer_instance

theorem two_smul_notMem_roots (hD : D.divisible = ∅) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) :
    2 • γ ∉ D.roots := by
  have hconj : ∀ δ ∈ D.roots, ∃ (w : W) (i : Fin D.rank), δ = ρ w (Pi.single i 1) := by
    rintro δ (h | ⟨w, i, hi, -⟩)
    · exact h
    · rw [hD] at hi
      exact absurd hi (Set.notMem_empty i)
  intro h2
  obtain ⟨w, i, rfl⟩ := hconj γ hγ
  obtain ⟨w', j, hj⟩ := hconj _ h2
  have h1 : 2 • ρ w'⁻¹ (ρ w (Pi.single i 1)) = Pi.single j 1 := by
    rw [← map_nsmul, hj, weylAction_inv_apply_apply]
  have h3 := congrFun h1 j
  rw [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul] at h3
  omega

theorem RootGroupCommutators.of_commute (h2 : ∀ γ ∈ D.roots, 2 • γ ∉ D.roots)
    (hc : ∀ γ ∈ D.roots, ∀ x ∈ D.rootGroup γ, ∀ y ∈ D.rootGroup γ, Commute x y) :
    RootGroupCommutators D where
  commutator_le γ hγ h := absurd h (h2 γ hγ)
  commutator_eq_bot γ hγ _ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
    exact hc γ hγ x hx y hy
  commutator_two_smul_eq_bot γ hγ h := absurd h (h2 γ hγ)

theorem RootGroupCommutators.of_divisible_eq_empty (hD : D.divisible = ∅)
    (hc : ∀ γ ∈ D.roots, ∀ x ∈ D.rootGroup γ, ∀ y ∈ D.rootGroup γ, Commute x y) :
    RootGroupCommutators D :=
  .of_commute (fun _ hγ => two_smul_notMem_roots hD hγ) hc

end CFSG.LieType.TitsSimplicity
