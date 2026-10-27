module

public import CFSG.LieType.RootSystem.Restrict
public import CFSG.LieType.TitsSimplicity.Simplicity

public section

namespace CFSG.LieType.TitsSimplicity.Levi

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.RootSystem.Restrict

variable {G : Type*} [Group G] (D : UniversalRootDatum G) {m : ℕ} {e : Fin m → Fin D.rank}

abbrev leviC (e : Fin m → Fin D.rank) : Subgroup G :=
  levi D.rootGroup (Finset.univ.image e)

@[expose] noncomputable def restrict (he : Function.Injective e) :
    UniversalRootDatum ↥(leviC D e) where
  rank := m
  cartan := D.cartan.submatrix e e
  isFiniteType := D.isFiniteType.submatrix he
  divisible := ∅
  rootGroup γ := (D.rootGroup (ext e γ)).subgroupOf (leviC D e)

@[expose] noncomputable def nC (n : Fin D.rank → G) (e : Fin m → Fin D.rank) (i : Fin m) :
    ↥(leviC D e) :=
  open _root_.Classical in
  if h : n (e i) ∈ leviC D e then ⟨n (e i), h⟩ else 1

@[expose] noncomputable def HC (H : Fin D.rank → Subgroup G) (e : Fin m → Fin D.rank)
    (i : Fin m) : Subgroup ↥(leviC D e) :=
  (H (e i)).subgroupOf (leviC D e)

variable {D} (he : Function.Injective e) {n : Fin D.rank → G} {H : Fin D.rank → Subgroup G}
  (hdiv : D.divisible = ∅)

set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem
set_option hygiene false in
local notation "ρ" => weylAction D.isFiniteType

include hdiv in
theorem restrict_roots (γ : Fin m → ℤ) :
    γ ∈ (restrict D he).roots ↔ ext e γ ∈ D.roots := by
  have h₁ : (restrict D he).roots = roots (D.isFiniteType.submatrix he) ∅ := rfl
  have h₂ : D.roots = roots D.isFiniteType ∅ := by
    rw [UniversalRootDatum.roots, hdiv]
  rw [h₁, h₂]
  exact (ext_mem_roots_iff he D.isFiniteType γ).symm

theorem rankOne_le_leviC_of_mem_range {j : Fin D.rank} (hj : j ∈ Set.range e) :
    rankOne D.rootGroup j ≤ leviC D e := by
  obtain ⟨i, rfl⟩ := hj
  exact rankOne_le_levi D.rootGroup (Finset.mem_image_of_mem e (Finset.mem_univ i))

theorem rootGroup_single_le_leviC_of_mem_range {j : Fin D.rank} (hj : j ∈ Set.range e) :
    D.rootGroup (Pi.single j 1) ≤ leviC D e :=
  le_sup_left.trans (rankOne_le_leviC_of_mem_range hj)

variable (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)

include hct in
theorem n_mem_leviC_of_mem_range {j : Fin D.rank} (hj : j ∈ Set.range e) : n j ∈ leviC D e :=
  rankOne_le_leviC_of_mem_range hj (hct.n_mem j)

include hct in
theorem rootGroup_simple_reflect_le {K : Subgroup G} {j : Fin D.rank} (hj : n j ∈ K)
    {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) (hX : D.rootGroup γ ≤ K) :
    D.rootGroup (ρ ((cs).simple j) γ) ≤ K := by
  intro y hy
  have hmem : ρ ((cs).simple j) γ ∈ D.roots :=
    weylAction_mem_roots D.isFiniteType ((cs).simple j) hγ
  have hss : ρ ((cs).simple j) (ρ ((cs).simple j) γ) = γ := by
    rw [← weylAction_mul_apply D.isFiniteType, CoxeterSystem.simple_mul_simple_self cs j, map_one,
      Module.End.one_apply]
  have h₁ : n j * y * (n j)⁻¹ ∈ D.rootGroup γ := by
    simpa only [hss] using hct.conj_mem j _ hmem y hy
  have h₂ : (n j)⁻¹ * (n j * y * (n j)⁻¹) * n j ∈ K :=
    K.mul_mem (K.mul_mem (K.inv_mem hj) (hX h₁)) hj
  simpa [mul_assoc] using h₂

include hct in
theorem rootGroup_wordProd_single_le_leviC {ω : List (Fin D.rank)}
    (hω : ∀ j ∈ ω, j ∈ Set.range e) {m' : Fin D.rank} (hm' : m' ∈ Set.range e) :
    D.rootGroup (ρ ((cs).wordProd ω) (Pi.single m' 1)) ≤ leviC D e := by
  induction ω with
  | nil => simpa using rootGroup_single_le_leviC_of_mem_range (D := D) hm'
  | cons j ω ih =>
    rw [CoxeterSystem.wordProd_cons cs, map_mul, Module.End.mul_apply]
    have hΦ := isCTRootSystem D.isFiniteType D.divisible
    exact rootGroup_simple_reflect_le hct (n_mem_leviC_of_mem_range hct (hω j (by simp)))
      (weylAction_mem_roots D.isFiniteType _ (hΦ.single_mem m'))
      (ih fun i hi => hω i (List.mem_cons_of_mem j hi))

include hct hdiv in
theorem rootGroup_le_leviC_of_support {δ : Fin D.rank → ℤ} (hδ : δ ∈ D.roots)
    (hsupp : ∀ k ∉ Set.range e, δ k = 0) : D.rootGroup δ ≤ leviC D e := by
  obtain ⟨w, i, hwi⟩ : ∃ (w : (coxeterMatrix D.isFiniteType).Group) (i : Fin D.rank),
      δ = ρ w (Pi.single i 1) := by
    rcases hδ with ⟨w, i, h⟩ | ⟨w, i, hi, -⟩
    · exact ⟨w, i, h⟩
    · rw [hdiv] at hi
      exact (Set.notMem_empty i hi).elim
  obtain ⟨z, hz, m', hm', hzm⟩ :=
    (isCTRootSystem D.isFiniteType D.divisible).exists_parabolic (Set.range e) w i
      fun k hk => hwi ▸ hsupp k hk
  obtain ⟨ω, hω, hωz⟩ := CoxeterSystem.exists_wordProd_eq_of_mem_parabolic cs (inv_mem hz)
  have hδω : δ = ρ ((cs).wordProd ω) (Pi.single m' 1) := by
    rw [hωz, ← hzm, weylAction_inv_apply_apply, hwi]
  rw [hδω]
  exact rootGroup_wordProd_single_le_leviC hct hω hm'

include hct hdiv in
theorem rootGroup_ext_le_leviC {γ : Fin m → ℤ} (hγ : ext e γ ∈ D.roots) :
    D.rootGroup (ext e γ) ≤ leviC D e :=
  rootGroup_le_leviC_of_support hdiv hct hγ fun _ hk => ext_apply_of_notMem_range γ hk

include hct in
theorem coe_nC (i : Fin m) : (nC D n e i : G) = n (e i) := by
  have h : n (e i) ∈ leviC D e := n_mem_leviC_of_mem_range hct ⟨i, rfl⟩
  rw [nC, dif_pos h]

end CFSG.LieType.TitsSimplicity.Levi
