module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall
public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitMaps

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

section SL2Commutators

variable {F : Type*} [Field F]

theorem uSL_inv (s : F) : (uSL s)⁻¹ = uSL (-s) := by
  rw [inv_eq_iff_mul_eq_one, ← uSL_add_eq_mul, add_neg_cancel, uSL_zero_eq_one]

theorem vSL_inv (s : F) : (vSL s)⁻¹ = vSL (-s) := by
  rw [inv_eq_iff_mul_eq_one, ← vSL_add_eq_mul, add_neg_cancel, vSL_zero_eq_one]

theorem HSL_inv (t : Fˣ) : (HSL t)⁻¹ = HSL t⁻¹ := by
  rw [inv_eq_iff_mul_eq_one]
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_HSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem commutatorElement_HSL_uSL (t : Fˣ) (s : F) :
    ⁅HSL t, uSL s⁆ = uSL (((t : F) ^ 2 - 1) * s) := by
  rw [commutatorElement_def, HSL_inv, uSL_inv]
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_HSL, coe_uSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem commutatorElement_HSL_vSL (t : Fˣ) (s : F) :
    ⁅HSL t, vSL s⁆ = vSL ((((t⁻¹ : Fˣ) : F) ^ 2 - 1) * s) := by
  rw [commutatorElement_def, HSL_inv, vSL_inv]
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_HSL, coe_vSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  ring

end SL2Commutators

theorem rootTorusSL2_conj_pinnedX_of_isRoot
    {τ : Tag} {K : Type} [Field K]
    {β α : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hα : IsRoot τ α) (c : Kˣ) (z : K) :
    rootTorusSL2 τ K β c * pinnedX τ K α z * (rootTorusSL2 τ K β c)⁻¹ =
      pinnedX τ K α (((c ^ (2 * iform β α / iform β β) : Kˣ) : K) * z) := by
  obtain ⟨-, hdH, -, -, hv, hH, -, -⟩ := exceptional_Lang_root_rank_one_torus_transport τ K hβ
  obtain ⟨a, ha, -⟩ := hH _ (hdH c)
  have h1 := (hv c).2 α hα
  rw [ha] at h1
  change rootDiag a (rootVec τ K α) = _ at h1
  rw [rootDiag_rootVec a hα] at h1
  have hne : rootVec τ K α ≠ 0 := by
    rw [rootVec_eq_single_of_isRoot hα]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  have h2 := smul_left_injective K hne h1
  rw [ha, rootDiagUnit_conj_pinnedX a hα]
  congr 2

theorem list_prod_rootTorusSL2_conj_pinnedX
    {τ : Tag} {K : Type} [Field K]
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (l : List ((Fin τ.rank → ℤ) × Kˣ))
    (hl : ∀ p ∈ l, IsRoot τ p.1) (z : K) :
    (l.map fun p => rootTorusSL2 τ K p.1 p.2).prod * pinnedX τ K α z *
        ((l.map fun p => rootTorusSL2 τ K p.1 p.2).prod)⁻¹ =
      pinnedX τ K α ((((l.map fun p => p.2 ^ (2 * iform p.1 α / iform p.1 p.1)).prod : Kˣ) : K) *
        z) := by
  induction l generalizing z with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons]
    have e : rootTorusSL2 τ K p.1 p.2 * (l.map fun p => rootTorusSL2 τ K p.1 p.2).prod *
        pinnedX τ K α z *
          (rootTorusSL2 τ K p.1 p.2 * (l.map fun p => rootTorusSL2 τ K p.1 p.2).prod)⁻¹ =
        rootTorusSL2 τ K p.1 p.2 * ((l.map fun p => rootTorusSL2 τ K p.1 p.2).prod *
          pinnedX τ K α z * ((l.map fun p => rootTorusSL2 τ K p.1 p.2).prod)⁻¹) *
          (rootTorusSL2 τ K p.1 p.2)⁻¹ := by group
    rw [e, ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)),
      rootTorusSL2_conj_pinnedX_of_isRoot (hl p List.mem_cons_self) hα, Units.val_mul, mul_assoc]

theorem val_list_prod_range {K : Type*} [Field K] (f : ℕ → Kˣ) (d : ℕ) :
    ((((List.range d).map f).prod : Kˣ) : K) = ∏ j ∈ Finset.range d, (f j : K) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [List.range_succ, List.map_append, List.prod_append, Units.val_mul, ih,
      Finset.prod_range_succ]
    simp

namespace OrthogonalSemilinearFixedRootDatum

variable
    {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

theorem orbitMapHom_HSL
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) (t : (D.orbitField O)ˣ) :
    D.orbitMapHom hO (HSL t) = D.orbitH O t :=
  rfl

theorem orbitX_mem_commutator_of_sq_ne_one
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    {t : (D.orbitField O)ˣ} (ht : (t : D.orbitField O) ^ 2 ≠ 1) (c : D.orbitField O) :
    D.orbitX O c ∈ ⁅D.orbitGroup, D.orbitGroup⁆ := by
  have hne : (t : D.orbitField O) ^ 2 - 1 ≠ 0 := sub_ne_zero.2 ht
  have h := map_commutatorElement (D.orbitMapHom hO) (HSL t) (uSL (c / ((t : _) ^ 2 - 1)))
  rw [commutatorElement_HSL_uSL, mul_div_cancel₀ _ hne] at h
  rw [orbitX, ← D.orbitMapHom_apply hO, h]
  exact Subgroup.commutator_mem_commutator (D.orbitMap_mem_orbitGroup hO _)
    (D.orbitMap_mem_orbitGroup hO _)

theorem orbitY_mem_commutator_of_sq_ne_one
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    {t : (D.orbitField O)ˣ} (ht : (t : D.orbitField O) ^ 2 ≠ 1) (c : D.orbitField O) :
    D.orbitY O c ∈ ⁅D.orbitGroup, D.orbitGroup⁆ := by
  have ht' : (((t⁻¹ : (D.orbitField O)ˣ) : D.orbitField O)) ^ 2 ≠ 1 := by
    intro h
    apply ht
    have h1 : ((t : D.orbitField O) * ((t⁻¹ : (D.orbitField O)ˣ) : D.orbitField O)) ^ 2 = 1 := by
      rw [Units.mul_inv, one_pow]
    rw [mul_pow, h, mul_one] at h1
    exact h1
  have hne : (((t⁻¹ : (D.orbitField O)ˣ) : D.orbitField O)) ^ 2 - 1 ≠ 0 := sub_ne_zero.2 ht'
  have h := map_commutatorElement (D.orbitMapHom hO) (HSL t)
    (vSL (c / ((((t⁻¹ : (D.orbitField O)ˣ) : D.orbitField O)) ^ 2 - 1)))
  rw [commutatorElement_HSL_vSL, mul_div_cancel₀ _ hne] at h
  rw [orbitY, ← D.orbitMapHom_apply hO, h]
  exact Subgroup.commutator_mem_commutator (D.orbitMap_mem_orbitGroup hO _)
    (D.orbitMap_mem_orbitGroup hO _)

theorem exists_sq_ne_one
    {O : Set (Fin τ.rank → ℤ)} (h3 : 3 < Nat.card (D.orbitField O)) :
    ∃ t : (D.orbitField O)ˣ, (t : D.orbitField O) ^ 2 ≠ 1 := by
  by_contra h
  push Not at h
  have hsub : (Set.univ : Set (D.orbitField O)) ⊆ {0, 1, -1} := by
    intro x _
    by_cases hx : x = 0
    · exact Or.inl hx
    · have h1 := h (Units.mk0 x hx)
      rw [Units.val_mk0] at h1
      have h2 : (x - 1) * (x + 1) = 0 := by linear_combination h1
      rcases mul_eq_zero.1 h2 with h3 | h3
      · exact Or.inr (Or.inl (sub_eq_zero.1 h3))
      · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h3))
  have hfin : ({0, 1, -1} : Set (D.orbitField O)).Finite := Set.toFinite _
  have hle := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_univ] at hle
  have h4 : ({0, 1, -1} : Set (D.orbitField O)).ncard ≤ 3 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
    rw [Set.ncard_singleton]
  omega

theorem three_le_q :
    3 ≤ D.q := by
  have hp : 2 ≤ p₀ := (Fact.out : p₀.Prime).two_le
  have hp3 : 3 ≤ p₀ := by
    have := D.odd
    omega
  calc 3 ≤ p₀ := hp3
    _ = p₀ ^ 1 := (pow_one p₀).symm
    _ ≤ p₀ ^ D.e := Nat.pow_le_pow_right (by omega) D.one_le_e

theorem odd_q
    : Odd D.q := by
  have hp : Odd p₀ := (Fact.out : p₀.Prime).odd_of_ne_two D.odd
  exact hp.pow

theorem orbitCard_eq_one_of_card
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (h3 : Nat.card (D.orbitField O) ≤ 3) : orbitCard O = 1 := by
  rw [D.card_orbitField hO] at h3
  have hpos := D.orbitCard_pos hO
  have hq := D.three_le_q
  by_contra hne
  have h2 : 2 ≤ orbitCard O := by omega
  have : D.q ^ 2 ≤ D.q ^ orbitCard O := Nat.pow_le_pow_right (by omega) h2
  nlinarith

theorem three_le_card_orbitField
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    3 ≤ Nat.card (D.orbitField O) := by
  rw [D.card_orbitField hO]
  calc 3 ≤ D.q := D.three_le_q
    _ = D.q ^ 1 := (pow_one _).symm
    _ ≤ D.q ^ orbitCard O := Nat.pow_le_pow_right (by have := D.three_le_q; omega)
        (D.orbitCard_pos hO)

theorem theta_orbitRoot_of_orbitCard_eq_one
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (h1 : orbitCard O = 1) : D.θ (toReal (orbitRoot O)) = toReal (orbitRoot O) := by
  have h := D.theta_orbitVec hO 0
  have h2 := D.orbitVec_orbitCard hO
  rw [h1] at h2
  rw [zero_add, h2, D.orbitVec_zero] at h
  exact h

theorem eq_singleton_of_orbitCard_eq_one
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (h1 : orbitCard O = 1) : O = {orbitRoot O} := by
  obtain ⟨β, hβ⟩ := Set.ncard_eq_one.1 h1
  rw [hβ]
  have := D.orbitRoot_mem hO
  rw [hβ, Set.mem_singleton_iff] at this
  rw [this]

theorem orbitX_of_orbitCard_eq_one
    {O : Set (Fin τ.rank → ℤ)} (h1 : orbitCard O = 1)
    (c : D.orbitField O) : D.orbitX O c = rootSL2 τ k (orbitRoot O) (uSL (c : k)) := by
  rw [orbitX, orbitMap_eq_prod, h1, show List.range 1 = [0] from rfl, List.map_singleton,
    List.prod_singleton, D.orbitFactor_uSL, pow_zero, pow_one, D.orbitVec_zero]

theorem orbitY_of_orbitCard_eq_one
    {O : Set (Fin τ.rank → ℤ)} (h1 : orbitCard O = 1)
    (c : D.orbitField O) : D.orbitY O c = rootSL2 τ k (orbitRoot O) (vSL (c : k)) := by
  rw [orbitY, orbitMap_eq_prod, h1, show List.range 1 = [0] from rfl, List.map_singleton,
    List.prod_singleton, D.orbitFactor_vSL, pow_zero, pow_one, D.orbitVec_zero]

theorem orbitH_eq_prod
    (O : Set (Fin τ.rank → ℤ)) (t : (D.orbitField O)ˣ) :
    D.orbitH O t = ((List.range (orbitCard O)).map fun j => rootTorusSL2 τ k (D.orbitVec O j)
      (Units.map (iterateFrobenius k p₀ (D.e * j)).toMonoidHom
        (Units.map (D.orbitField O).subtype.toMonoidHom t))).prod := by
  rw [orbitH, orbitMap_eq_prod]
  refine congrArg List.prod (List.map_congr_left fun j _ => ?_)
  rw [D.orbitFactor_apply, map_HSL, map_HSL]
  rfl

end OrthogonalSemilinearFixedRootDatum

namespace OrthogonalSemilinearFixedRootDatum

variable
    {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

theorem rform_pow_theta
    (m : ℕ) (x y : Fin τ.rank → ℝ) :
    rform ((D.θ ^ m) x) ((D.θ ^ m) y) = rform x y := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, D.isometry, ih]

theorem iform_eq_neg_one_of_adjacent
    {O P : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (hP : P ∈ D.orbits) (hOP : O ≠ P) (h1 : orbitCard O = 1) {γ₀ : Fin τ.rank → ℤ}
    (hγ₀ : γ₀ ∈ P) (hadj : iform (orbitRoot O) γ₀ ≠ 0) {γ : Fin τ.rank → ℤ} (hγ : γ ∈ P) :
    iform (orbitRoot O) γ = -1 := by
  have hβO := D.orbitRoot_mem hO
  have hθβ := D.theta_orbitRoot_of_orbitCard_eq_one hO h1
  have hθβm : ∀ m, (D.θ ^ m) (toReal (orbitRoot O)) = toReal (orbitRoot O) := fun m => by
    rw [Module.End.pow_apply]
    exact Function.iterate_fixed hθβ m
  have hγP := hγ
  rw [D.eq_thetaOrbit_of_mem_orbits hP hγ₀] at hγ
  obtain ⟨m, hm⟩ := hγ
  have heq : iform (orbitRoot O) γ = iform (orbitRoot O) γ₀ := by
    have h := D.rform_pow_theta m (toReal (orbitRoot O)) (toReal γ₀)
    rw [hθβm, hm, rform_toReal, rform_toReal] at h
    exact_mod_cast h
  have hne : orbitRoot O ≠ γ := by
    intro h
    apply hOP
    rw [D.eq_thetaOrbit_of_mem_orbits hO hβO, h, ← D.eq_thetaOrbit_of_mem_orbits hP hγP]
  have hβΔ := D.mem_unionSimpleRoots_of_mem_orbits hO hβO
  have hγΔ := D.mem_unionSimpleRoots_of_mem_orbits hP hγP
  have hle := iform_nonpos_of_mem_unionSimpleRoots hβΔ hγΔ hne
  have hsum : orbitRoot O + γ ≠ 0 := by
    intro h
    have h2 := congrArg height h
    rw [height_add] at h2
    have h0 : height (0 : Fin τ.rank → ℤ) = 0 := by simp [height]
    rw [h0] at h2
    have := (mem_posRoots_of_mem_unionSimpleRoots hβΔ).2
    have := (mem_posRoots_of_mem_unionSimpleRoots hγΔ).2
    omega
  have hpos := iform_self_pos hsum
  rw [iform_add_left, iform_add_right, iform_add_right, iform_comm γ (orbitRoot O),
    D.iform_self_eq_two (isRoot_of_mem_unionSimpleRoots hβΔ),
    D.iform_self_eq_two (isRoot_of_mem_unionSimpleRoots hγΔ)] at hpos
  have : iform (orbitRoot O) γ ≠ 0 := by rw [heq]; exact hadj
  omega

theorem exists_adjacent_orbit
    (h2 : 2 ≤ D.orbits.ncard) {O : Set (Fin τ.rank → ℤ)}
    (hO : O ∈ D.orbits) : ∃ P ∈ D.orbits, O ≠ P ∧ ∃ β ∈ O, ∃ γ ∈ P, iform β γ ≠ 0 := by
  obtain ⟨P', hP', hne⟩ := Set.exists_ne_of_one_lt_ncard (s := D.orbits) (by omega) O
  rcases (D.orbits_connected hO hP').cases_head with heq | ⟨P, ⟨-, hP, hOP, hadj⟩, -⟩
  · exact absurd heq.symm hne
  · exact ⟨P, hP, hOP, hadj⟩

theorem exists_unit_pow_eq_neg_one
    {P : Set (Fin τ.rank → ℤ)} (hP : P ∈ D.orbits) :
    ∃ t : (D.orbitField P)ˣ,
      ((t : D.orbitField P) : k) ^ (∑ j ∈ Finset.range (orbitCard P), D.q ^ j) = -1 := by
  set n := ∑ j ∈ Finset.range (orbitCard P), D.q ^ j with hn
  have hd := D.orbitCard_pos hP
  have hnpos : 0 < n := by
    rw [hn]
    exact Finset.sum_pos (fun j _ => pow_pos (by have := D.three_le_q; omega) j)
      ⟨0, Finset.mem_range.2 hd⟩
  obtain ⟨t₀, ht₀⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : k) hnpos
  have ht₀0 : t₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow hnpos.ne'] at ht₀
    exact one_ne_zero (neg_eq_zero.1 ht₀.symm)
  have hgeom : n * (D.q - 1) + 1 = D.q ^ orbitCard P := by
    have h := geom_sum_mul_add (D.q - 1) (orbitCard P)
    rwa [Nat.sub_add_cancel (by have := D.three_le_q; omega)] at h
  have heven : Even (D.q - 1) := by
    obtain ⟨m, hm⟩ := D.odd_q
    exact ⟨m, by omega⟩
  have hmem : t₀ ∈ D.orbitField P := by
    rw [D.mem_orbitField, ← hgeom, pow_add, pow_one, pow_mul, ht₀, heven.neg_one_pow, one_mul]
  refine ⟨Units.mk0 ⟨t₀, hmem⟩ fun h => ht₀0 (congrArg Subtype.val h), ?_⟩
  rw [Units.val_mk0]
  exact ht₀

theorem orbitH_conj_orbitX
    {O P : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) (hP : P ∈ D.orbits)
    (h1 : orbitCard O = 1) (hadj : ∀ γ ∈ P, iform (orbitRoot O) γ = -1) (t : (D.orbitField P)ˣ)
    (ht : ((t : D.orbitField P) : k) ^ (∑ j ∈ Finset.range (orbitCard P), D.q ^ j) = -1)
    (c : D.orbitField O) :
    D.orbitH P t * D.orbitX O c * (D.orbitH P t)⁻¹ = D.orbitX O (-c) := by
  set β := orbitRoot O with hβdef
  have hβr : IsRoot τ β := D.isRoot_of_mem_orbits hO (D.orbitRoot_mem hO)
  set s : ℕ → kˣ := fun j => Units.map (iterateFrobenius k p₀ (D.e * j)).toMonoidHom
    (Units.map (D.orbitField P).subtype.toMonoidHom t) with hsdef
  have hs : ∀ j, (s j : k) = ((t : D.orbitField P) : k) ^ D.q ^ j := fun j => by
    change iterateFrobenius k p₀ (D.e * j) ((t : D.orbitField P) : k) = _
    rw [iterateFrobenius_def, q, ← pow_mul]
  have hex : ∀ j ∈ List.range (orbitCard P),
      s j ^ (2 * iform (D.orbitVec P j) β / iform (D.orbitVec P j) (D.orbitVec P j)) = (s j)⁻¹ := by
    intro j _
    have h := hadj _ (D.orbitVec_mem hP j)
    rw [iform_comm, h, D.iform_self_eq_two (D.isRoot_orbitVec hP j)]
    norm_num
  rw [D.orbitX_of_orbitCard_eq_one h1, D.orbitX_of_orbitCard_eq_one h1, rootSL2_uSL_eq,
    rootSL2_uSL_eq, D.orbitH_eq_prod]
  have hlist := list_prod_rootTorusSL2_conj_pinnedX hβr
    ((List.range (orbitCard P)).map fun j => (D.orbitVec P j, s j))
    (fun p hp => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hp
      exact D.isRoot_orbitVec hP j) ((pinnedData τ β).2.2 • ((c : D.orbitField O) : k))
  simp only [List.map_map, Function.comp_def] at hlist
  rw [hlist, List.map_congr_left hex, val_list_prod_range]
  congr 1
  simp only [Units.val_inv_eq_inv_val, hs, Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum, ht]
  push_cast
  rw [smul_neg]
  ring

theorem orbitH_conj_orbitY
    {O P : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) (hP : P ∈ D.orbits)
    (h1 : orbitCard O = 1) (hadj : ∀ γ ∈ P, iform (orbitRoot O) γ = -1) (t : (D.orbitField P)ˣ)
    (ht : ((t : D.orbitField P) : k) ^ (∑ j ∈ Finset.range (orbitCard P), D.q ^ j) = -1)
    (c : D.orbitField O) :
    D.orbitH P t * D.orbitY O c * (D.orbitH P t)⁻¹ = D.orbitY O (-c) := by
  set β := orbitRoot O with hβdef
  have hβr : IsRoot τ β := D.isRoot_of_mem_orbits hO (D.orbitRoot_mem hO)
  obtain ⟨ε, -, hv⟩ := exists_rootSL2_vSL_eq (K := k) hβr
  set s : ℕ → kˣ := fun j => Units.map (iterateFrobenius k p₀ (D.e * j)).toMonoidHom
    (Units.map (D.orbitField P).subtype.toMonoidHom t) with hsdef
  have hs : ∀ j, (s j : k) = ((t : D.orbitField P) : k) ^ D.q ^ j := fun j => by
    change iterateFrobenius k p₀ (D.e * j) ((t : D.orbitField P) : k) = _
    rw [iterateFrobenius_def, q, ← pow_mul]
  have hex : ∀ j ∈ List.range (orbitCard P),
      s j ^ (2 * iform (D.orbitVec P j) (-β) / iform (D.orbitVec P j) (D.orbitVec P j)) = s j := by
    intro j _
    have h := hadj _ (D.orbitVec_mem hP j)
    rw [iform_neg_right, iform_comm, h, D.iform_self_eq_two (D.isRoot_orbitVec hP j)]
    norm_num
  rw [D.orbitY_of_orbitCard_eq_one h1, D.orbitY_of_orbitCard_eq_one h1, hv, hv, D.orbitH_eq_prod]
  have hlist := list_prod_rootTorusSL2_conj_pinnedX (IsRoot.neg hβr)
    ((List.range (orbitCard P)).map fun j => (D.orbitVec P j, s j))
    (fun p hp => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hp
      exact D.isRoot_orbitVec hP j) (ε * ((c : D.orbitField O) : k))
  simp only [List.map_map, Function.comp_def] at hlist
  rw [hlist, List.map_congr_left hex, val_list_prod_range]
  congr 1
  simp only [hs, Finset.prod_pow_eq_pow_sum, ht]
  push_cast
  ring

theorem two_ne_zero_orbitField
    (O : Set (Fin τ.rank → ℤ)) : (2 : D.orbitField O) ≠ 0 := by
  have h : ringChar (D.orbitField O) = p₀ := ringChar.eq (D.orbitField O) p₀
  exact Ring.two_ne_zero (by rw [h]; exact D.odd)

theorem orbitX_mem_commutator_of_conj
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    {h : ModGL τ k} (hh : h ∈ D.orbitGroup) (hconj : ∀ c, h * D.orbitX O c * h⁻¹ = D.orbitX O (-c))
    (c : D.orbitField O) : D.orbitX O c ∈ ⁅D.orbitGroup, D.orbitGroup⁆ := by
  set c' := -c / 2 with hc'
  have hX0 : D.orbitX O 0 = 1 := by rw [orbitX, uSL_zero_eq_one, D.orbitMap_one]
  have hinv : (D.orbitX O c')⁻¹ = D.orbitX O (-c') := by
    rw [inv_eq_iff_mul_eq_one, ← D.orbitX_add hO, add_neg_cancel, hX0]
  have e : ⁅h, D.orbitX O c'⁆ = D.orbitX O c := by
    rw [commutatorElement_def, hconj, hinv, ← D.orbitX_add hO]
    congr 1
    rw [hc']
    field_simp [D.two_ne_zero_orbitField O]
    ring
  rw [← e]
  exact Subgroup.commutator_mem_commutator hh (D.orbitMap_mem_orbitGroup hO _)

theorem orbitY_mem_commutator_of_conj
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    {h : ModGL τ k} (hh : h ∈ D.orbitGroup) (hconj : ∀ c, h * D.orbitY O c * h⁻¹ = D.orbitY O (-c))
    (c : D.orbitField O) : D.orbitY O c ∈ ⁅D.orbitGroup, D.orbitGroup⁆ := by
  set c' := -c / 2 with hc'
  have hY0 : D.orbitY O 0 = 1 := by rw [orbitY, vSL_zero_eq_one, D.orbitMap_one]
  have hinv : (D.orbitY O c')⁻¹ = D.orbitY O (-c') := by
    rw [inv_eq_iff_mul_eq_one, ← D.orbitY_add hO, add_neg_cancel, hY0]
  have e : ⁅h, D.orbitY O c'⁆ = D.orbitY O c := by
    rw [commutatorElement_def, hconj, hinv, ← D.orbitY_add hO]
    congr 1
    rw [hc']
    field_simp [D.two_ne_zero_orbitField O]
    ring
  rw [← e]
  exact Subgroup.commutator_mem_commutator hh (D.orbitMap_mem_orbitGroup hO _)

end OrthogonalSemilinearFixedRootDatum

namespace OrthogonalSemilinearFixedRootDatum

variable
    {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

theorem isPerfect_orbitGroup_of_forall
    (h : ∀ O ∈ D.orbits, ∀ c, D.orbitX O c ∈ ⁅D.orbitGroup, D.orbitGroup⁆ ∧
      D.orbitY O c ∈ ⁅D.orbitGroup, D.orbitGroup⁆) : Group.IsPerfect D.orbitGroup := by
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm (Subgroup.commutator_le_self _) ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨O, hO, c, rfl | rfl⟩
  exacts [(h O hO c).1, (h O hO c).2]

theorem gens_mem_commutator_of_three_lt
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (h3 : 3 < Nat.card (D.orbitField O)) (c : D.orbitField O) :
    D.orbitX O c ∈ ⁅D.orbitGroup, D.orbitGroup⁆ ∧ D.orbitY O c ∈ ⁅D.orbitGroup, D.orbitGroup⁆ := by
  obtain ⟨t, ht⟩ := D.exists_sq_ne_one h3
  exact ⟨D.orbitX_mem_commutator_of_sq_ne_one hO ht c, D.orbitY_mem_commutator_of_sq_ne_one hO ht c⟩

theorem gens_mem_commutator_of_two_le
    (h2 : 2 ≤ D.orbits.ncard) {O : Set (Fin τ.rank → ℤ)}
    (hO : O ∈ D.orbits) (c : D.orbitField O) :
    D.orbitX O c ∈ ⁅D.orbitGroup, D.orbitGroup⁆ ∧ D.orbitY O c ∈ ⁅D.orbitGroup, D.orbitGroup⁆ := by
  by_cases h3 : 3 < Nat.card (D.orbitField O)
  · exact D.gens_mem_commutator_of_three_lt hO h3 c
  have h1 := D.orbitCard_eq_one_of_card hO (by omega)
  obtain ⟨P, hP, hOP, β, hβ, γ₀, hγ₀, hadj⟩ := D.exists_adjacent_orbit h2 hO
  rw [D.eq_singleton_of_orbitCard_eq_one hO h1, Set.mem_singleton_iff] at hβ
  subst hβ
  have hall : ∀ γ ∈ P, iform (orbitRoot O) γ = -1 := fun γ hγ =>
    D.iform_eq_neg_one_of_adjacent hO hP hOP h1 hγ₀ hadj hγ
  obtain ⟨t, ht⟩ := D.exists_unit_pow_eq_neg_one hP
  have hH := D.orbitMap_mem_orbitGroup hP (HSL t)
  exact ⟨D.orbitX_mem_commutator_of_conj hO hH (D.orbitH_conj_orbitX hO hP h1 hall t ht) c,
    D.orbitY_mem_commutator_of_conj hO hH (D.orbitH_conj_orbitY hO hP h1 hall t ht) c⟩

theorem range_orbitMap_eq_of_orbits_eq
    {O : Set (Fin τ.rank → ℤ)} (hA : D.orbits = {O}) :
    Set.range (D.orbitMap O) = D.orbitGroup := by
  have hO : O ∈ D.orbits := by rw [hA]; exact Set.mem_singleton O
  refine Set.Subset.antisymm (D.range_orbitMap_subset hO) ?_
  rw [D.range_orbitMap hO]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨O', hO', c, rfl | rfl⟩
  · rw [hA, Set.mem_singleton_iff] at hO'
    subst hO'
    exact Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)
  · rw [hA, Set.mem_singleton_iff] at hO'
    subst hO'
    exact Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)

@[expose] def orbitGroupHom
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    SL2 (D.orbitField O) →* D.orbitGroup :=
  (D.orbitMapHom hO).codRestrict D.orbitGroup fun A => D.orbitMap_mem_orbitGroup hO A

theorem orbitGroupHom_surjective
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (hA : D.orbits = {O}) : Function.Surjective (D.orbitGroupHom hO) := by
  rintro ⟨g, hg⟩
  have hg' : g ∈ Set.range (D.orbitMap O) := by
    rw [D.range_orbitMap_eq_of_orbits_eq hA]
    exact hg
  obtain ⟨A, rfl⟩ := hg'
  exact ⟨A, rfl⟩

theorem neg_one_mem_center_SL2 {F : Type*} [Field F] :
    (-1 : SL2 F) ∈ Subgroup.center (SL2 F) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨-1, by simp, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end OrthogonalSemilinearFixedRootDatum

theorem orthogonal_semilinear_fixed_root_perfectness
    {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime]
    {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
    (D : OrthogonalSemilinearFixedRootDatum τ p₀ k) :
    (2 ≤ D.orbits.ncard → Group.IsPerfect D.orbitGroup) ∧
    (∀ O, D.orbits = {O} → 3 < Nat.card (D.orbitField O) → Group.IsPerfect D.orbitGroup) ∧
    (∀ O, D.orbits = {O} → Nat.card (D.orbitField O) = 3 →
      Set.range (D.orbitMap O) = D.orbitGroup ∧
      (∃ f : SL2 (ZMod 3) →* D.orbitGroup, Function.Surjective f ∧
        f.ker ≤ Subgroup.center (SL2 (ZMod 3))) ∧
      Group.IsSolvable D.orbitGroup) := by
  refine ⟨fun h2 => D.isPerfect_orbitGroup_of_forall fun O hO c =>
    D.gens_mem_commutator_of_two_le h2 hO c, fun O hA h3 => ?_, fun O hA h3 => ?_⟩
  · refine D.isPerfect_orbitGroup_of_forall fun O' hO' c => ?_
    rw [hA, Set.mem_singleton_iff] at hO'
    subst hO'
    exact D.gens_mem_commutator_of_three_lt (by rw [hA]; exact Set.mem_singleton _) h3 c
  · have hO : O ∈ D.orbits := by rw [hA]; exact Set.mem_singleton O
    have hfin : Finite (D.orbitField O) := Nat.finite_of_card_ne_zero (by omega)
    have : Fintype (D.orbitField O) := Fintype.ofFinite _
    have hp3 : p₀ = 3 := by
      have hcard := D.card_orbitField hO
      rw [h3, D.orbitCard_eq_one_of_card hO h3.le, pow_one,
        OrthogonalSemilinearFixedRootDatum.q] at hcard
      have hdvd : p₀ ∣ 3 := by
        rw [hcard]
        exact dvd_pow_self p₀ (by have := D.one_le_e; omega)
      exact (Nat.prime_dvd_prime_iff_eq (Fact.out : p₀.Prime) Nat.prime_three).1 hdvd
    have : CharP (D.orbitField O) 3 := hp3 ▸ inferInstance
    have hcard3 : Fintype.card (D.orbitField O) = 3 := by rw [← Nat.card_eq_fintype_card, h3]
    set φ := ZMod.ringEquiv (D.orbitField O) hcard3 with hφ
    set f := (D.orbitGroupHom hO).comp (Matrix.SpecialLinearGroup.map φ.toRingHom) with hf
    have hmapinj : Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2)
        φ.toRingHom) := by
      intro A B h
      ext i j
      have := congrArg (fun M : SL2 (D.orbitField O) =>
        (M : Matrix (Fin 2) (Fin 2) (D.orbitField O)) i j) h
      simpa [Matrix.SpecialLinearGroup.map_apply_coe] using this
    have hmapsurj : Function.Surjective (Matrix.SpecialLinearGroup.map (n := Fin 2)
        φ.toRingHom) := by
      intro A
      refine ⟨Matrix.SpecialLinearGroup.map φ.symm.toRingHom A, ?_⟩
      ext i j
      simp [Matrix.SpecialLinearGroup.map_apply_coe]
    refine ⟨D.range_orbitMap_eq_of_orbits_eq hA, ⟨f, ?_, ?_⟩, ?_⟩
    · exact (D.orbitGroupHom_surjective hO hA).comp hmapsurj
    · intro A hA'
      rw [MonoidHom.mem_ker] at hA'
      have h1 : D.orbitMap O (Matrix.SpecialLinearGroup.map φ.toRingHom A) = 1 :=
        congrArg Subtype.val hA'
      rcases D.eq_one_or_neg_one_of_orbitMap_eq_one hO h1 with h | h
      · rw [← map_one (Matrix.SpecialLinearGroup.map (n := Fin 2) φ.toRingHom)] at h
        rw [hmapinj h]
        exact one_mem _
      · have hneg : Matrix.SpecialLinearGroup.map (n := Fin 2) φ.toRingHom (-1) = -1 := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.map_apply_coe]
        rw [← hneg] at h
        rw [hmapinj h]
        exact OrthogonalSemilinearFixedRootDatum.neg_one_mem_center_SL2
    · have : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) (D.orbitField O)) :=
        CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable
          (D.orbitField O) (Or.inr h3)
      have : Group.IsSolvable (SL2 (D.orbitField O)) :=
        Group.isSolvable_of_isSolvable_injective Matrix.SpecialLinearGroup.toGL_injective
      exact Group.isSolvable_of_surjective (D.orbitGroupHom_surjective hO hA)

end CFSG.LieType.Chevalley
