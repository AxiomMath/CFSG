module

public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddBasic
public import CFSG.LieType.AlgebraicGroups.RationalCentralizerCocycleComponents
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedTotalComponents

public noncomputable section

namespace CFSG.ComponentClassification.ExcSelector

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open CFSG.LieType.AlgebraicGroups CFSG.ComponentClassification.CatalogueBPrimeJoin
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

section Torus

variable {τ : Tag} {k : Type} [Field k]

theorem torus_conj_pinnedX_of_smul {t : ModGL τ k} (ht : t ∈ torusGroup τ k)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) {s : k}
    (hs : (t : Module.End k (RootModule τ k)) (rootVec τ k γ) = s • rootVec τ k γ) (z : k) :
    t * pinnedX τ k γ z * t⁻¹ = pinnedX τ k γ (s * z) := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  rw [rootDiagUnit_conj_pinnedX a hγ]
  congr 2
  have h1 := rootDiag_rootVec a hγ
  change rootDiag a (rootVec τ k γ) = _ at hs
  have hne : rootVec τ k γ ≠ 0 := by
    rw [rootVec_eq_single_of_isRoot hγ]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  exact smul_left_injective k hne (h1.symm.trans hs)

theorem torus_conj_rootSL2_uSL_of_smul {t : ModGL τ k} (ht : t ∈ torusGroup τ k)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) {s : k}
    (hs : (t : Module.End k (RootModule τ k)) (rootVec τ k γ) = s • rootVec τ k γ) (z : k) :
    t * rootSL2 τ k γ (uSL z) * t⁻¹ = rootSL2 τ k γ (uSL (s * z)) := by
  rw [rootSL2_uSL_eq, rootSL2_uSL_eq, torus_conj_pinnedX_of_smul ht hγ hs]
  congr 1
  rcases pinnedSign_eq τ γ with h | h <;> rw [h] <;> simp

end Torus


section Pairings

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

theorem map_neg_one_sl2' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    Matrix.SpecialLinearGroup.map f (-1 : SL(2, R)) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.map_apply_coe]

theorem list_prod_units_act_scalar' {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {ι : Type*} (l : List ι) (g : ι → (Module.End R M)ˣ) (s : ι → R) (v : M)
    (hg : ∀ i, ((g i : Module.End R M)) v = s i • v) :
    (((l.map g).prod : (Module.End R M)ˣ) : Module.End R M) v = (l.map s).prod • v := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, Units.val_mul, Module.End.mul_apply, ih, map_smul, hg i,
      List.map_cons, List.prod_cons, smul_smul, mul_comm]

@[expose] def orbitPairing' (O : Set (Fin τ.rank → ℤ)) (δ : Fin τ.rank → ℤ) : ℤ :=
  ∑ j ∈ Finset.range (orbitCard O), corootPair (D.orbitVec O j) δ

theorem orbitMap_neg_one_act' {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) :
    ((D.orbitMap O (-1) : ModGL τ k) : Module.End k (RootModule τ k)) (rootVec τ k δ) =
      (((-1 : kˣ) ^ orbitPairing' D O δ : kˣ) : k) • rootVec τ k δ := by
  rw [orbitMap_eq_prod]
  have hfac : ∀ j, ((D.orbitFactor O j (-1) : ModGL τ k) :
      Module.End k (RootModule τ k)) (rootVec τ k δ) =
      (((-1 : kˣ) ^ corootPair (D.orbitVec O j) δ : kˣ) : k) • rootVec τ k δ := by
    intro j
    rw [orbitFactor_apply, map_neg_one_sl2', map_neg_one_sl2', ← HSL_neg_one_eq]
    exact (exceptional_Lang_root_rank_one_torus_transport τ k
      (D.isRoot_orbitVec hO j)).2.2.2.2.1 (-1) |>.2 δ hδ
  have h := list_prod_units_act_scalar' (List.range (orbitCard O))
    (fun j => D.orbitFactor O j (-1))
    (fun j => (((-1 : kˣ) ^ corootPair (D.orbitVec O j) δ : kˣ) : k)) (rootVec τ k δ) hfac
  rw [h]
  congr 1
  have key : ∀ n : ℕ, (((List.range n).map fun j =>
      (((-1 : kˣ) ^ corootPair (D.orbitVec O j) δ : kˣ) : k)).prod) =
      (((-1 : kˣ) ^ ∑ j ∈ Finset.range n, corootPair (D.orbitVec O j) δ : kˣ) : k) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.sum_range_succ,
        zpow_add]
      simp
  rw [orbitPairing']
  exact key _

include D in
theorem corootPair_eq_iform' {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (δ : Fin τ.rank → ℤ) :
    corootPair β δ = iform β δ := by
  have h := corootPair_mul hβ δ
  rw [D.iform_self_eq_two hβ] at h
  omega

theorem iform_orbitVec_succ' {O₁ O₂ : Set (Fin τ.rank → ℤ)} (hO₁ : O₁ ∈ D.orbits)
    (hO₂ : O₂ ∈ D.orbits) (j i : ℕ) :
    iform (D.orbitVec O₁ (j + 1)) (D.orbitVec O₂ (i + 1)) =
      iform (D.orbitVec O₁ j) (D.orbitVec O₂ i) := by
  have h := D.isometry (toReal (D.orbitVec O₁ j)) (toReal (D.orbitVec O₂ i))
  rw [D.theta_orbitVec hO₁, D.theta_orbitVec hO₂, rform_toReal, rform_toReal] at h
  exact_mod_cast h

theorem orbitVec_add_card' {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) (n : ℕ) :
    D.orbitVec O (n + orbitCard O) = D.orbitVec O n := by
  rw [D.orbitVec_eq_iff hO, Function.iterate_add_apply, D.orbitCard_eq_minimalPeriod hO,
    Function.iterate_minimalPeriod]

theorem sum_range_shift' (f : ℕ → ℤ) (d : ℕ) (h : f d = f 0) :
    ∑ i ∈ Finset.range d, f (i + 1) = ∑ i ∈ Finset.range d, f i := by
  have h1 := Finset.sum_range_succ f d
  have h2 := Finset.sum_range_succ' f d
  linarith

theorem iform_orbitVec_eq' {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) {j j' : ℕ}
    (hj : j < orbitCard O) (hj' : j' < orbitCard O) :
    iform (D.orbitVec O j) (D.orbitVec O j') = if j = j' then 2 else 0 := by
  split_ifs with h
  · subst h
    exact D.iform_self_eq_two (D.isRoot_orbitVec hO j)
  · have hK := D.orbitRoot_mem_kernelRoots hO
    have hne : D.orbitVec O j ≠ D.orbitVec O j' := fun h' => h (D.orbitVec_injOn hO hj hj' h')
    exact D.orbit_orthogonal _ hK _ (D.thetaPowVec_spec hK j).2.1 _
      (D.thetaPowVec_spec hK j').2.1 hne

theorem orbitVec_ne_of_ne' {O₁ O₂ : Set (Fin τ.rank → ℤ)} (hO₁ : O₁ ∈ D.orbits)
    (hO₂ : O₂ ∈ D.orbits) (hne : O₁ ≠ O₂) (j i : ℕ) : D.orbitVec O₁ j ≠ D.orbitVec O₂ i := by
  intro h
  apply hne
  rw [D.eq_thetaOrbit_of_mem_orbits hO₁ (D.orbitVec_mem hO₁ j),
    D.eq_thetaOrbit_of_mem_orbits hO₂ (D.orbitVec_mem hO₂ i), h]

theorem iform_orbitVec_nonpos' {O₁ O₂ : Set (Fin τ.rank → ℤ)} (hO₁ : O₁ ∈ D.orbits)
    (hO₂ : O₂ ∈ D.orbits) (hne : O₁ ≠ O₂) (j i : ℕ) :
    iform (D.orbitVec O₁ j) (D.orbitVec O₂ i) ≤ 0 :=
  iform_nonpos_of_mem_unionSimpleRoots (D.orbitVec_mem_unionSimpleRoots hO₁ j)
    (D.orbitVec_mem_unionSimpleRoots hO₂ i) (orbitVec_ne_of_ne' D hO₁ hO₂ hne j i)

theorem exists_odd_orbitPairing' {O₁ O₂ : Set (Fin τ.rank → ℤ)} (hO₁ : O₁ ∈ D.orbits)
    (hO₂ : O₂ ∈ D.orbits) (hne : O₁ ≠ O₂) (hadj : ∃ β ∈ O₁, ∃ γ ∈ O₂, iform β γ ≠ 0) :
    (∃ γ ∈ O₂, Odd (orbitPairing' D O₁ γ)) ∨ ∃ β ∈ O₁, Odd (orbitPairing' D O₂ β) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hev₂', hev₁'⟩ := hcon
  have he₁ : ∀ γ ∈ O₂, Even (orbitPairing' D O₁ γ) := fun γ hγ => by
    simpa using hev₂' γ hγ
  have he₂ : ∀ β ∈ O₁, Even (orbitPairing' D O₂ β) := fun β hβ => by
    simpa using hev₁' β hβ
  obtain ⟨β₀, hβ₀, γ₀, hγ₀, hadj⟩ := hadj
  set d₁ := orbitCard O₁ with hd₁
  set d₂ := orbitCard O₂ with hd₂
  have hd₁pos : 0 < d₁ := D.orbitCard_pos hO₁
  have hd₂pos : 0 < d₂ := D.orbitCard_pos hO₂
  set M : ℕ → ℕ → ℤ := fun j i => iform (D.orbitVec O₁ j) (D.orbitVec O₂ i) with hM
  have hMθ : ∀ j i, M (j + 1) (i + 1) = M j i := fun j i => iform_orbitVec_succ' D hO₁ hO₂ j i
  have hMper₁ : ∀ j i, M (j + d₁) i = M j i := fun j i => by
    simp only [hM]
    rw [orbitVec_add_card' D hO₁]
  have hMper₂ : ∀ j i, M j (i + d₂) = M j i := fun j i => by
    simp only [hM]
    rw [orbitVec_add_card' D hO₂]
  have hrow : ∀ j, ∑ i ∈ Finset.range d₂, M j i = ∑ i ∈ Finset.range d₂, M 0 i := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [← sum_range_shift' (M (j + 1)) d₂ (by simpa using hMper₂ (j + 1) 0)]
      simp only [hMθ]
      exact ih
  have hcol : ∀ i, ∑ j ∈ Finset.range d₁, M j i = ∑ j ∈ Finset.range d₁, M j 0 := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [← sum_range_shift' (fun j => M j (i + 1)) d₁ (by simpa using hMper₁ 0 (i + 1))]
      simp only [hMθ]
      exact ih
  have hpair₂ : ∀ j, orbitPairing' D O₂ (D.orbitVec O₁ j) = ∑ i ∈ Finset.range d₂, M j i := by
    intro j
    rw [orbitPairing']
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [corootPair_eq_iform' D (D.isRoot_orbitVec hO₂ i), iform_comm]
  have hpair₁ : ∀ i, orbitPairing' D O₁ (D.orbitVec O₂ i) = ∑ j ∈ Finset.range d₁, M j i := by
    intro i
    rw [orbitPairing']
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [corootPair_eq_iform' D (D.isRoot_orbitVec hO₁ j)]
  set c := ∑ i ∈ Finset.range d₂, M 0 i with hc
  set a := ∑ j ∈ Finset.range d₁, M j 0 with ha
  have hc_even : Even c := by
    have := he₂ _ (D.orbitVec_mem hO₁ 0)
    rwa [hpair₂ 0] at this
  have ha_even : Even a := by
    have := he₁ _ (D.orbitVec_mem hO₂ 0)
    rwa [hpair₁ 0] at this
  obtain ⟨j₀, hj₀, hβ₀eq⟩ := D.exists_orbitVec_eq hO₁ hβ₀
  obtain ⟨i₀, hi₀, hγ₀eq⟩ := D.exists_orbitVec_eq hO₂ hγ₀
  have hMneg : M j₀ i₀ < 0 := by
    have h1 : M j₀ i₀ = iform β₀ γ₀ := by simp only [hM, hβ₀eq, hγ₀eq]
    have h2 : M j₀ i₀ ≤ 0 := iform_orbitVec_nonpos' D hO₁ hO₂ hne j₀ i₀
    rcases h2.lt_or_eq with h | h
    · exact h
    · exact absurd (h1 ▸ h) hadj
  have hc_neg : c < 0 := by
    have h1 : c = ∑ i ∈ Finset.range d₂, M j₀ i := (hrow j₀).symm
    have h2 : ∑ i ∈ Finset.range d₂, M j₀ i ≤ M j₀ i₀ := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 hi₀)]
      have : ∑ i ∈ (Finset.range d₂).erase i₀, M j₀ i ≤ 0 :=
        Finset.sum_nonpos fun i _ => iform_orbitVec_nonpos' D hO₁ hO₂ hne j₀ i
      linarith
    linarith
  have ha_neg : a < 0 := by
    have h1 : a = ∑ j ∈ Finset.range d₁, M j i₀ := (hcol i₀).symm
    have h2 : ∑ j ∈ Finset.range d₁, M j i₀ ≤ M j₀ i₀ := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 hj₀)]
      have : ∑ j ∈ (Finset.range d₁).erase j₀, M j i₀ ≤ 0 :=
        Finset.sum_nonpos fun j _ => iform_orbitVec_nonpos' D hO₁ hO₂ hne j i₀
      linarith
    linarith
  have hc2 : c ≤ -2 := by
    obtain ⟨m, hm⟩ := hc_even
    omega
  have ha2 : a ≤ -2 := by
    obtain ⟨m, hm⟩ := ha_even
    omega
  set b₁ : Fin τ.rank → ℤ := ∑ j ∈ Finset.range d₁, D.orbitVec O₁ j with hb₁
  set b₂ : Fin τ.rank → ℤ := ∑ i ∈ Finset.range d₂, D.orbitVec O₂ i with hb₂
  set S : ℤ := ∑ j ∈ Finset.range d₁, ∑ i ∈ Finset.range d₂, M j i with hS
  have hSb : iform b₁ b₂ = S := by
    rw [hb₁, hb₂, iform_finset_sum_left]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [iform_finset_sum_right]
  have hS1 : S = d₁ * c := by
    rw [hS]
    rw [Finset.sum_congr rfl fun j _ => hrow j]
    simp [hc]
  have hS2 : S = d₂ * a := by
    rw [hS, Finset.sum_comm]
    rw [Finset.sum_congr rfl fun i _ => hcol i]
    simp [ha]
  have hN₁ : iform b₁ b₁ = 2 * d₁ := by
    have h1 : ∀ j ∈ Finset.range d₁, iform (D.orbitVec O₁ j) b₁ = 2 := by
      intro j hj
      have hjlt : j < orbitCard O₁ := Finset.mem_range.1 hj
      rw [hb₁, iform_finset_sum_right, Finset.sum_eq_single j]
      · exact D.iform_self_eq_two (D.isRoot_orbitVec hO₁ j)
      · intro j' hj' hne'
        have := iform_orbitVec_eq' D hO₁ hjlt (Finset.mem_range.1 hj' : j' < orbitCard O₁)
        simpa [Ne.symm hne'] using this
      · intro h
        exact absurd hj h
    conv_lhs => rw [hb₁, iform_finset_sum_left]
    rw [Finset.sum_congr rfl h1]
    simp [mul_comm]
  have hN₂ : iform b₂ b₂ = 2 * d₂ := by
    have h1 : ∀ i ∈ Finset.range d₂, iform (D.orbitVec O₂ i) b₂ = 2 := by
      intro i hi
      have hilt : i < orbitCard O₂ := Finset.mem_range.1 hi
      rw [hb₂, iform_finset_sum_right, Finset.sum_eq_single i]
      · exact D.iform_self_eq_two (D.isRoot_orbitVec hO₂ i)
      · intro i' hi' hne'
        have := iform_orbitVec_eq' D hO₂ hilt (Finset.mem_range.1 hi' : i' < orbitCard O₂)
        simpa [Ne.symm hne'] using this
      · intro h
        exact absurd hi h
    conv_lhs => rw [hb₂, iform_finset_sum_left]
    rw [Finset.sum_congr rfl h1]
    simp [mul_comm]
  have hd₁z : (0 : ℤ) < d₁ := by exact_mod_cast hd₁pos
  have hd₂z : (0 : ℤ) < d₂ := by exact_mod_cast hd₂pos
  set v : Fin τ.rank → ℤ := (2 * (d₂ : ℤ)) • b₁ - S • b₂ with hv
  have hvv : iform v v = 2 * d₂ * (4 * d₁ * d₂ - S ^ 2) := by
    rw [hv]
    simp only [iform_sub_left, iform_sub_right, iform_smul_left, iform_smul_right]
    rw [iform_comm b₂ b₁, hSb, hN₁, hN₂]
    ring
  have hSsq : S ^ 2 = d₁ * d₂ * (a * c) := by
    calc S ^ 2 = S * S := pow_two S
      _ = (d₁ * c) * (d₂ * a) := by rw [← hS1, ← hS2]
      _ = d₁ * d₂ * (a * c) := by ring
  have hac : 4 ≤ a * c := by nlinarith
  have hpos : 0 ≤ (d₁ : ℤ) * d₂ * (a * c - 4) := mul_nonneg (by positivity) (by linarith)
  have hle : iform v v ≤ 0 := by
    rw [hvv, hSsq]
    nlinarith
  have hv0 : v = 0 := by
    by_contra hne0
    have := iform_self_pos hne0
    linarith
  have hvv0 : iform v v = 0 := by
    rw [hv0]
    simp [iform]
  have hSsq4 : S ^ 2 = 4 * d₁ * d₂ := by
    rw [hvv] at hvv0
    have h2d : (2 : ℤ) * d₂ ≠ 0 := by positivity
    have := (mul_eq_zero.mp hvv0).resolve_left h2d
    linarith
  have hac4 : a * c = 4 := by
    rw [hSsq] at hSsq4
    have h12 : (d₁ : ℤ) * d₂ ≠ 0 := by positivity
    have : (d₁ : ℤ) * d₂ * (a * c) = (d₁ : ℤ) * d₂ * 4 := by linarith
    exact mul_left_cancel₀ h12 this
  have ha_eq : a = -2 := by nlinarith
  have hc_eq : c = -2 := by nlinarith
  have hSval : S = -(2 * (d₂ : ℤ)) := by rw [hS2, ha_eq]; ring
  have hsum0 : (2 * (d₂ : ℤ)) • (b₁ + b₂) = 0 := by
    have h := sub_eq_zero.mp hv0
    rw [hSval, neg_smul] at h
    rw [smul_add, h]
    simp
  have hb12 : b₁ + b₂ = 0 := by
    rcases smul_eq_zero.mp hsum0 with h | h
    · exact absurd h (by positivity)
    · exact h
  have hheight : height (b₁ + b₂) = 0 := by rw [hb12]; simp [height]
  have hh₁ : 0 < height b₁ := by
    rw [hb₁, height_finset_sum]
    refine Finset.sum_pos (fun j _ => ?_) ⟨0, Finset.mem_range.2 hd₁pos⟩
    exact (mem_posRoots_of_mem_unionSimpleRoots (D.orbitVec_mem_unionSimpleRoots hO₁ j)).2
  have hh₂ : 0 < height b₂ := by
    rw [hb₂, height_finset_sum]
    refine Finset.sum_pos (fun i _ => ?_) ⟨0, Finset.mem_range.2 hd₂pos⟩
    exact (mem_posRoots_of_mem_unionSimpleRoots (D.orbitVec_mem_unionSimpleRoots hO₂ i)).2
  rw [height_add] at hheight
  omega

theorem finite_orbits' : D.orbits.Finite := by
  have : D.orbits = (thetaOrbit D.θ) '' D.simpleRootsJ := by
    ext O
    exact ⟨fun ⟨β, hβ, e⟩ => ⟨β, hβ, e.symm⟩, fun ⟨β, hβ, e⟩ => ⟨β, hβ, e.symm⟩⟩
  rw [this]
  exact (D.finite_roots.subset fun _ h => h.2).image _

theorem orbitMap_neg_one_mem_torusGroup' {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    D.orbitMap O (-1) ∈ torusGroup τ k := by
  rw [← HSL_neg_one_eq]
  exact D.orbitH_mem_torusGroup hO (-1)

theorem finite_orbitField' {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    Finite (D.orbitField O) := by
  have hpos : 0 < Nat.card (D.orbitField O) := by
    rw [D.card_orbitField hO]
    exact pow_pos (by have := D.three_le_q; omega) _
  exact Nat.finite_of_card_ne_zero hpos.ne'

theorem orbitMap_of_orbitCard_eq_one' {O : Set (Fin τ.rank → ℤ)} (h1 : orbitCard O = 1)
    (A : SL2 (D.orbitField O)) :
    D.orbitMap O A =
      rootSL2 τ k (orbitRoot O) (Matrix.SpecialLinearGroup.map (D.orbitField O).subtype A) := by
  rw [D.orbitMap_eq_prod, h1, show List.range 1 = [0] from rfl, List.map_singleton,
    List.prod_singleton, D.orbitFactor_zero, D.orbitVec_zero]

theorem orbitMap_injective_of_orbitCard_eq_one' {O : Set (Fin τ.rank → ℤ)}
    (h1 : orbitCard O = 1) : Function.Injective (D.orbitMap O) := fun A A' h => by
  rw [orbitMap_of_orbitCard_eq_one' D h1, orbitMap_of_orbitCard_eq_one' D h1] at h
  exact D.map_subtype_injective O (D.rootSL2_injective _ h)

end Pairings

section Datum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

theorem orbitPairing_orbitVec {O P : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (hP : P ∈ D.orbits) (i : ℕ) :
    orbitPairing' D O (D.orbitVec P i) = orbitPairing' D O (D.orbitVec P 0) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [← ih, orbitPairing', orbitPairing']
    have e : ∀ j, corootPair (D.orbitVec O j) (D.orbitVec P i) =
        iform (D.orbitVec O j) (D.orbitVec P i) := fun j =>
      corootPair_eq_iform' D (D.isRoot_orbitVec hO j) _
    have e' : ∀ j, corootPair (D.orbitVec O j) (D.orbitVec P (i + 1)) =
        iform (D.orbitVec O j) (D.orbitVec P (i + 1)) := fun j =>
      corootPair_eq_iform' D (D.isRoot_orbitVec hO j) _
    simp only [e, e']
    have hd : D.orbitVec O (orbitCard O) = D.orbitVec O 0 := by
      simpa using orbitVec_add_card' D hO 0
    rw [← sum_range_shift' (fun j => iform (D.orbitVec O j) (D.orbitVec P (i + 1))) (orbitCard O)
      (by
        show iform (D.orbitVec O (orbitCard O)) (D.orbitVec P (i + 1)) =
          iform (D.orbitVec O 0) (D.orbitVec P (i + 1))
        rw [hd])]
    simp only [iform_orbitVec_succ' D hO hP]

theorem orbitMap_neg_one_conj_orbitX {O P : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (hP : P ∈ D.orbits) (hodd : Odd (orbitPairing' D O (D.orbitVec P 0)))
    (c : D.orbitField P) :
    D.orbitMap O (-1) * D.orbitX P c * (D.orbitMap O (-1))⁻¹ = D.orbitX P (-c) := by
  set t := D.orbitMap O (-1) with ht_def
  have ht : t ∈ torusGroup τ k := orbitMap_neg_one_mem_torusGroup' D hO
  have hs : ∀ j, (t : Module.End k (RootModule τ k)) (rootVec τ k (D.orbitVec P j)) =
      (-1 : k) • rootVec τ k (D.orbitVec P j) := fun j => by
    rw [ht_def, orbitMap_neg_one_act' D hO (D.isRoot_orbitVec hP j),
      orbitPairing_orbitVec D hO hP j, hodd.neg_one_zpow]
    simp
  have hq : Odd D.q := D.odd_q
  rw [OrthogonalSemilinearFixedRootDatum.orbitX, OrthogonalSemilinearFixedRootDatum.orbitX,
    D.orbitMap_eq_prod, D.orbitMap_eq_prod]
  rw [show t * ((List.range (orbitCard P)).map fun j => D.orbitFactor P j (uSL c)).prod * t⁻¹ =
      (MulAut.conj t) ((List.range (orbitCard P)).map fun j => D.orbitFactor P j (uSL c)).prod
      from rfl, map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun j _ => ?_)
  simp only [Function.comp_apply, MulAut.conj_apply]
  rw [D.orbitFactor_uSL, D.orbitFactor_uSL, torus_conj_rootSL2_uSL_of_smul ht
    (D.isRoot_orbitVec hP j) (hs j)]
  congr 2
  push_cast
  rw [(hq.pow).neg_pow]
  ring

theorem orbitGroup_not_smallType_of_odd {O P : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (hP : P ∈ D.orbits) (hodd : Odd (orbitPairing' D O (D.orbitVec P 0))) :
    ¬ SmallType D.orbitGroup := by
  have : Finite (D.orbitField O) := finite_orbitField' D hO
  have hF : ringChar (D.orbitField O) ≠ 2 := ringChar_subfield_ne_two D.ringChar_ne_two _
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero D.ringChar_ne_two
  have hconj := orbitMap_neg_one_conj_orbitX D hO hP hodd 1
  have hne : D.orbitMap O (-1) ≠ 1 := fun h => by
    rw [h, one_mul, inv_one, mul_one] at hconj
    have h1 := D.orbitX_injective hP hconj
    have h1' := congrArg (fun c : D.orbitField P => (c : k)) h1
    simp only [OneMemClass.coe_one, NegMemClass.coe_neg] at h1'
    exact h2 (by linear_combination h1')
  set φ := D.orbitGroupHom hO
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro A hA
    have h1 : D.orbitMap O A = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hA)
    rcases D.eq_one_or_neg_one_of_orbitMap_eq_one hO h1 with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · exact absurd (h ▸ h1) hne
  refine not_smallType_of_sl2 hF φ hinj fun hz => ?_
  have hX : D.orbitX P 1 ∈ D.orbitGroup := D.orbitMap_mem_orbitGroup hP _
  have hc := congrArg Subtype.val ((mem_center_iff.1 hz) ⟨_, hX⟩)
  change D.orbitX P 1 * D.orbitMap O (-1) = D.orbitMap O (-1) * D.orbitX P 1 at hc
  rw [← hc, mul_inv_cancel_right] at hconj
  have h1 := D.orbitX_injective hP hconj
  have h1' := congrArg (fun c : D.orbitField P => (c : k)) h1
  simp only [OneMemClass.coe_one, NegMemClass.coe_neg] at h1'
  exact h2 (by linear_combination h1')

theorem orbitGroup_not_smallType_of_single {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (hA : D.orbits = {O}) (hne : D.orbitMap O (-1) ≠ 1) : ¬ SmallType D.orbitGroup := by
  have : Finite (D.orbitField O) := finite_orbitField' D hO
  have hF : ringChar (D.orbitField O) ≠ 2 := ringChar_subfield_ne_two D.ringChar_ne_two _
  have hinj : Function.Injective (D.orbitGroupHom hO) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro A hA'
    have h1 : D.orbitMap O A = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hA')
    rcases D.eq_one_or_neg_one_of_orbitMap_eq_one hO h1 with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · exact absurd (h ▸ h1) hne
  let e : SL2 (D.orbitField O) ≃* D.orbitGroup :=
    MulEquiv.ofBijective _ ⟨hinj, D.orbitGroupHom_surjective hO hA⟩
  exact not_smallType_of_equiv_sl2 hF e.symm

theorem orbitGroup_not_smallType [Nontrivial D.orbitGroup]
    (hsingle : ∀ O ∈ D.orbits, D.orbits = {O} → D.orbitMap O (-1) ≠ 1) :
    ¬ SmallType D.orbitGroup := by
  by_cases h2 : 2 ≤ D.orbits.ncard
  · obtain ⟨O₁, hO₁⟩ := Set.nonempty_of_ncard_ne_zero (s := D.orbits) (by omega)
    obtain ⟨P, hP, hne, hadj⟩ := D.exists_adjacent_orbit h2 hO₁
    rcases exists_odd_orbitPairing' D hO₁ hP hne hadj with ⟨γ, hγ, hodd⟩ | ⟨β, hβ, hodd⟩
    · obtain ⟨i, -, rfl⟩ := D.exists_orbitVec_eq hP hγ
      rw [orbitPairing_orbitVec D hO₁ hP] at hodd
      exact orbitGroup_not_smallType_of_odd D hO₁ hP hodd
    · obtain ⟨i, -, rfl⟩ := D.exists_orbitVec_eq hO₁ hβ
      rw [orbitPairing_orbitVec D hP hO₁] at hodd
      exact orbitGroup_not_smallType_of_odd D hP hO₁ hodd
  · have hfin := finite_orbits' D
    rcases Nat.lt_or_ge D.orbits.ncard 1 with h0 | h1
    · exfalso
      have he : D.orbits = ∅ := by
        rw [← Set.ncard_eq_zero hfin]
        omega
      have hbot : D.orbitGroup = ⊥ := by
        rw [eq_bot_iff]
        refine (Subgroup.closure_le _).2 ?_
        rintro _ ⟨O, hO, -⟩
        rw [he] at hO
        exact absurd hO (Set.notMem_empty O)
      obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := exists_pair_ne D.orbitGroup
      rw [hbot, Subgroup.mem_bot] at hx hy
      exact hxy (Subtype.ext (hx.trans hy.symm))
    · obtain ⟨O, hO⟩ := Set.ncard_eq_one.1 (by omega : D.orbits.ncard = 1)
      have hOm : O ∈ D.orbits := by rw [hO]; exact Set.mem_singleton O
      exact orbitGroup_not_smallType_of_single D hOm hO (hsingle O hOm hO)

end Datum

section TwoComponents

theorem eq_top_of_isPComponent_of_isQuasisimple' {G : Type*} [Group G]
    (hG : CFSG.IsQuasisimple G) {p : ℕ} {L : Subgroup G} (hL : CFSG.IsPComponent p L) :
    L = ⊤ := by
  have := CFSG.ComponentClassification.CatalogueBAlternating.pComponent_nontrivial hL
  have := CFSG.ComponentClassification.CatalogueBAlternating.pComponent_perfect hL
  rcases quasisimple_subnormal_subgroups hG hL.choose_spec.2.1 with h | h
  · exact h
  · exfalso
    exact Group.IsPerfect.not_isMulCommutative L
      ⟨⟨fun x y => Subtype.ext (Subgroup.mem_center_iff.1 (h x.2) y).symm⟩⟩

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

theorem eq_orbitGroupC_of_isPComponent_fixedGroup' {J₀ : Subgroup (adjointGroup τ k)}
    (hle : J₀ ≤ D.fixedGroup) (hJ₀ : CFSG.IsPComponent 2 (J₀.subgroupOf D.fixedGroup)) :
    J₀ = D.orbitGroupC ∧ CFSG.IsQuasisimple D.orbitGroup := by
  have := D.finite_fixedGroup
  obtain ⟨hN, hS⟩ := normal_isSolvable_subgroupOf (A := D.orbitGroupC) (B := D.fixedGroup)
    (fun x hx a ha => by
      have h1 := D.orbitGroupC_normal.conj_mem ⟨a, D.orbitGroupC_le_fixedGroup ha⟩
        (Subgroup.mem_subgroupOf.2 ha) ⟨x, hx⟩
      exact Subgroup.mem_subgroupOf.1 h1)
    (fun x hx y hy => D.commutator_fixedGroup_le (Subgroup.commutator_mem_commutator hx hy))
  obtain ⟨hJN, hJ₀N⟩ := (isPComponent_subgroupOf_iff_of_isSolvable D.orbitGroupC_le_fixedGroup 2
    Nat.prime_two J₀).1 ⟨hle, hJ₀⟩
  have hequiv : ↥D.orbitGroupC ≃* ↥D.orbitGroup :=
    (Subgroup.subgroupOfEquivOfLe D.orbitGroupC_le_fixedGroup).symm.trans D.orbitGroupEquiv
  rcases D.isQuasisimple_or_isSolvable with hq | hs
  · have hqN : CFSG.IsQuasisimple ↥D.orbitGroupC := (isQuasisimple_congr hequiv).2 hq
    exact ⟨le_antisymm hJN (Subgroup.subgroupOf_eq_top.1
      (eq_top_of_isPComponent_of_isQuasisimple' hqN hJ₀N)), hq⟩
  · exfalso
    have : Group.IsSolvable ↥D.orbitGroupC := by
      have := hs
      exact Group.isSolvable_of_surjective (f := hequiv.symm.toMonoidHom) hequiv.symm.surjective
    exact CFSG.ComponentClassification.CatalogueBGeneralLinear.no_pComponent_of_solvable 2 _ hJ₀N

theorem exists_eq_orbitGroupC_of_isPComponent' (hX : Finite D.totalFixedGroup)
    {J₀ : Subgroup (adjointGroup τ k)} (hle : J₀ ≤ D.totalFixedGroup)
    (hJ₀ : CFSG.IsPComponent 2 (J₀.subgroupOf D.totalFixedGroup)) :
    ∃ J' : Set.range D.classOrbit, J₀ = (D.withOrbit J').orbitGroupC ∧
      CFSG.IsQuasisimple (D.withOrbit J').orbitGroup := by
  classical
  have hRX := D.kernelFixedGroup_le_totalFixedGroup
  have hUR := D.orbitFixedJoin_le_kernelFixedGroup
  have hR : Finite D.kernelFixedGroup := Finite.of_injective _ (Subgroup.inclusion_injective hRX)
  have hU : Finite D.orbitFixedJoin := Finite.of_injective _ (Subgroup.inclusion_injective hUR)
  obtain ⟨hN1, hS1⟩ := normal_isSolvable_subgroupOf (A := D.kernelFixedGroup)
    (B := D.totalFixedGroup) (fun x hx a ha => D.conj_mem_kernelFixedGroup hx ha)
    (fun x hx y hy => D.commutatorElement_mem_kernelFixedGroup hx hy)
  obtain ⟨hN2, hS2⟩ := normal_isSolvable_subgroupOf (A := D.orbitFixedJoin)
    (B := D.kernelFixedGroup) (fun x hx a ha => D.conj_mem_orbitFixedJoin hx ha)
    (fun x hx y hy => D.commutatorElement_mem_orbitFixedJoin hx hy)
  have := hN1
  have := hS1
  obtain ⟨hJR, hJR'⟩ := (isPComponent_subgroupOf_iff_of_isSolvable hRX 2 Nat.prime_two J₀).1
    ⟨hle, hJ₀⟩
  have := hN2
  have := hS2
  obtain ⟨hJU, hJU'⟩ := (isPComponent_subgroupOf_iff_of_isSolvable hUR 2 Nat.prime_two J₀).1
    ⟨hJR, hJR'⟩
  have hnorm : ∀ J' : Set.range D.classOrbit,
      ((D.withOrbit J').fixedGroup.subgroupOf D.orbitFixedJoin).Normal := fun J' =>
    ⟨fun n hn g => Subgroup.mem_subgroupOf.2
      (D.conj_mem_fixedGroup_withOrbit (hUR g.2) (Subgroup.mem_subgroupOf.1 hn))⟩
  have hjoin : ⨆ J' : Set.range D.classOrbit,
      (D.withOrbit J').fixedGroup.subgroupOf D.orbitFixedJoin = ⊤ :=
    iSup_subgroupOf_iSup_eq_top (fun J' : Set.range D.classOrbit => (D.withOrbit J').fixedGroup)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨J', hJ'⟩ := exists_le_of_le_iSup 2 (J₀.subgroupOf D.orbitFixedJoin) hJU'
    (fun J' : Set.range D.classOrbit =>
      (D.withOrbit J').fixedGroup.subgroupOf D.orbitFixedJoin)
    (fun J' => (hnorm J').isSubnormal) (by rw [hjoin]; exact le_top)
  have hJΓ : J₀ ≤ (D.withOrbit J').fixedGroup := fun x hx =>
    Subgroup.mem_subgroupOf.1 (hJ' (Subgroup.mem_subgroupOf.2 hx : (⟨x, hJU hx⟩ : D.orbitFixedJoin)
      ∈ J₀.subgroupOf D.orbitFixedJoin))
  have hΓfin : Finite (D.withOrbit J').fixedGroup := (D.withOrbit J').finite_fixedGroup
  have hJΓ' : CFSG.IsPComponent 2 (J₀.subgroupOf (D.withOrbit J').fixedGroup) :=
    (isPComponent_subgroupOf_subgroupOf_iff (A := (D.withOrbit J').fixedGroup)
      (B := D.orbitFixedJoin) (L := J₀) (D.fixedGroup_withOrbit_le_orbitFixedJoin J') 2
      Nat.prime_two).1 (pComponent_restrict_overgroup 2 hJU' hJ')
  obtain ⟨heq, hq⟩ := eq_orbitGroupC_of_isPComponent_fixedGroup' (D.withOrbit J') hJΓ hJΓ'
  exact ⟨J', heq, hq⟩

end TwoComponents

end CFSG.ComponentClassification.ExcSelector
