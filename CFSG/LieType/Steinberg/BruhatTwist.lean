module

public import CFSG.LieType.Steinberg.Bruhat
import Mathlib.Tactic.Group

public section

namespace CFSG.LieType.Steinberg

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem

section PermVec

variable {ι : Type*} (π : Equiv.Perm ι)

@[expose] def permVec (v : ι → ℤ) : ι → ℤ := v ∘ π.symm

theorem permVec_apply (v : ι → ℤ) (j : ι) : permVec π v j = v (π.symm j) := rfl

theorem permVec_single [DecidableEq ι] (i : ι) : permVec π (Pi.single i 1) = Pi.single (π i) 1 := by
  ext j
  simp only [permVec_apply, Pi.single_apply, Equiv.symm_apply_eq]

theorem permVec_add (v v' : ι → ℤ) : permVec π (v + v') = permVec π v + permVec π v' := rfl

theorem permVec_neg (v : ι → ℤ) : permVec π (-v) = -permVec π v := rfl

theorem permVec_nsmul (c : ℕ) (v : ι → ℤ) : permVec π (c • v) = c • permVec π v := rfl

theorem permVec_symm_permVec (v : ι → ℤ) : permVec π.symm (permVec π v) = v := by
  ext j
  simp [permVec_apply]

theorem ht_permVec [Fintype ι] (v : ι → ℤ) : ht (permVec π v) = ht v :=
  Equiv.sum_comp π.symm v

end PermVec

section WeylPerm

variable {I : Type} [Fintype I] {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)
  {π : Equiv.Perm I} (hπ : ∀ i j, A (π i) (π j) = A i j)

set_option hygiene false in
local notation "W" => (coxeterMatrix hA).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix hA).toCoxeterSystem

include hπ in
theorem coxeterMatrix_perm (i j : I) :
    (coxeterMatrix hA).M (π i) (π j) = (coxeterMatrix hA).M i j := by
  simp only [coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply, hπ]

include hπ in
theorem isLiftable_simple_perm : (coxeterMatrix hA).IsLiftable fun i => (cs).simple (π i) :=
  fun i j => by
    have h := (cs).simple_mul_simple_pow (π i) (π j)
    rwa [coxeterMatrix_perm hA hπ] at h

noncomputable def weylPerm : W →* W :=
  (cs).lift ⟨fun i => (cs).simple (π i), isLiftable_simple_perm hA hπ⟩

theorem weylPerm_simple (i : I) : weylPerm hA hπ ((cs).simple i) = (cs).simple (π i) :=
  (cs).lift_apply_simple _ i

theorem weylPerm_wordProd (ω : List I) :
    weylPerm hA hπ ((cs).wordProd ω) = (cs).wordProd (ω.map π) := by
  induction ω with
  | nil => simp [CoxeterSystem.wordProd_nil]
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, map_mul, weylPerm_simple, ih, List.map_cons,
      CoxeterSystem.wordProd_cons]

omit [Fintype I] in
include hπ in
theorem cartan_perm_symm (i j : I) : A (π.symm i) (π.symm j) = A i j := by
  simpa using (hπ (π.symm i) (π.symm j)).symm

theorem weylPerm_symm_weylPerm (w : W) :
    weylPerm hA (cartan_perm_symm hπ) (weylPerm hA hπ w) = w := by
  obtain ⟨ω, rfl⟩ := (cs).wordProd_surjective w
  rw [weylPerm_wordProd, weylPerm_wordProd, List.map_map]
  simp

theorem length_weylPerm_le (w : W) : (cs).length (weylPerm hA hπ w) ≤ (cs).length w := by
  obtain ⟨ω, hω, rfl⟩ := (cs).exists_isReduced w
  rw [weylPerm_wordProd, (show (cs).length ((cs).wordProd ω) = ω.length from hω)]
  exact ((cs).length_wordProd_le _).trans (by rw [List.length_map])

theorem length_weylPerm (w : W) : (cs).length (weylPerm hA hπ w) = (cs).length w := by
  refine le_antisymm (length_weylPerm_le hA hπ w) ?_
  have h := length_weylPerm_le hA (cartan_perm_symm hπ) (weylPerm hA hπ w)
  rwa [weylPerm_symm_weylPerm] at h

include hπ in
theorem isReduced_map_perm {ω : List I} (hω : (cs).IsReduced ω) : (cs).IsReduced (ω.map π) := by
  change (cs).length ((cs).wordProd (ω.map π)) = (ω.map π).length
  rw [← weylPerm_wordProd hA hπ, length_weylPerm, List.length_map]
  exact hω

theorem isLeftDescent_weylPerm_iff (w : W) (i : I) :
    (cs).IsLeftDescent (weylPerm hA hπ w) (π i) ↔ (cs).IsLeftDescent w i := by
  unfold CoxeterSystem.IsLeftDescent
  rw [← weylPerm_simple hA hπ, ← map_mul, length_weylPerm, length_weylPerm]

variable [DecidableEq I]

include hπ in
theorem permVec_reflection (i : I) (v : I → ℤ) :
    permVec π (reflection A i v) = reflection A (π i) (permVec π v) := by
  have hsum : ∑ l, A (π i) l * v (π.symm l) = ∑ l, A i l * v l := by
    rw [← Equiv.sum_comp π]
    simp [hπ]
  ext j
  simp only [permVec_apply, reflection_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hsum,
    Pi.single_apply, Equiv.symm_apply_eq]

theorem permVec_weylAction (w : W) (v : I → ℤ) :
    permVec π (weylAction hA w v) = weylAction hA (weylPerm hA hπ w) (permVec π v) := by
  induction w using (cs).simple_induction_left generalizing v with
  | one => simp [map_one]
  | mul_simple_left w i ih =>
    rw [weylAction_mul_apply, weylAction_simple, permVec_reflection hπ, ih, map_mul,
      weylPerm_simple, weylAction_mul_apply, weylAction_simple]

include hπ in
theorem permVec_mem_roots {D : Set I} (hD : ∀ i ∈ D, π i ∈ D) {γ : I → ℤ}
    (hγ : γ ∈ roots hA D) : permVec π γ ∈ roots hA D := by
  rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, hi, rfl⟩
  · exact Or.inl ⟨weylPerm hA hπ w, π i, by rw [permVec_weylAction hA hπ, permVec_single]⟩
  · exact Or.inr ⟨weylPerm hA hπ w, π i, hD i hi, by
      rw [permVec_nsmul, permVec_weylAction hA hπ, permVec_single]⟩

theorem reflection_single_of_eq_zero {i j : I} (h : A i j = 0) :
    reflection A i (Pi.single j 1) = Pi.single j 1 := by
  rw [reflection_apply_coroot, coroot_single, h, zero_smul, sub_zero]

omit [DecidableEq I] in
theorem simple_mul_simple_comm {i j : I} (h : A i j = 0) :
    (cs).simple i * (cs).simple j = (cs).simple j * (cs).simple i := by
  have hM : (coxeterMatrix hA).M i j = 2 := by
    simp only [coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply, h, zero_mul,
      TauCeti.coxeterOrder_zero]
  have h2 := (cs).simple_mul_simple_pow i j
  rw [hM, pow_two] at h2
  calc (cs).simple i * (cs).simple j
      = ((cs).simple i * (cs).simple j)⁻¹ := (eq_inv_of_mul_eq_one_left h2)
    _ = (cs).simple j * (cs).simple i := by
        rw [mul_inv_rev, CoxeterSystem.inv_simple, CoxeterSystem.inv_simple]

theorem isLeftDescent_simple_mul_of_eq_zero {w : W} {i j : I} (h : A i j = 0)
    (hj : (cs).IsLeftDescent w j) : (cs).IsLeftDescent ((cs).simple i * w) j := by
  rw [← CoxeterSystem.isRightDescent_inv_iff, isRightDescent_iff] at hj ⊢
  rwa [mul_inv_rev, CoxeterSystem.inv_simple, weylAction_mul_apply, weylAction_simple,
    reflection_single_of_eq_zero h]

theorem induction_weylPerm_fixed (hπ2 : ∀ i, π (π i) = i)
    (horth : ∀ i, π i ≠ i → A i (π i) = 0) {P : W → Prop} (h1 : P 1)
    (hfix : ∀ w i, π i = i → weylPerm hA hπ w = w → ¬ (cs).IsLeftDescent w i → P w →
      P ((cs).simple i * w))
    (hpair : ∀ w i, π i ≠ i → weylPerm hA hπ w = w → ¬ (cs).IsLeftDescent w (π i) →
      ¬ (cs).IsLeftDescent ((cs).simple (π i) * w) i → P w →
      P ((cs).simple i * ((cs).simple (π i) * w)))
    {w : W} (hw : weylPerm hA hπ w = w) : P w := by
  induction hm : (cs).length w using Nat.strong_induction_on generalizing w with
  | _ m ih =>
  by_cases hw1 : w = 1
  · rw [hw1]
    exact h1
  obtain ⟨i, hi⟩ := (cs).exists_leftDescent_of_ne_one hw1
  have hli : (cs).length ((cs).simple i * w) + 1 = (cs).length w := (cs).isLeftDescent_iff.1 hi
  by_cases hπi : π i = i
  ·
    have hw' : weylPerm hA hπ ((cs).simple i * w) = (cs).simple i * w := by
      rw [map_mul, weylPerm_simple, hπi, hw]
    have h := hfix _ i hπi hw' ((cs).isLeftDescent_iff_not_isLeftDescent_mul.1 hi)
      (ih _ (by omega) hw' rfl)
    rwa [(cs).simple_mul_simple_cancel_left] at h
  ·
    have hπi' : (cs).IsLeftDescent w (π i) := by
      have h := (isLeftDescent_weylPerm_iff hA hπ w i).2 hi
      rwa [hw] at h
    have h0 := horth i hπi
    have hj := isLeftDescent_simple_mul_of_eq_zero hA h0 hπi'
    set v := (cs).simple (π i) * ((cs).simple i * w) with hv
    have hlj : (cs).length v + 1 = (cs).length ((cs).simple i * w) := (cs).isLeftDescent_iff.1 hj
    have hcomm := simple_mul_simple_comm hA h0
    have hv' : weylPerm hA hπ v = v := by
      rw [hv, map_mul, map_mul, weylPerm_simple, weylPerm_simple, hπ2, hw, ← mul_assoc,
        ← mul_assoc, hcomm]
    have hvj : ¬ (cs).IsLeftDescent v (π i) :=
      (cs).isLeftDescent_iff_not_isLeftDescent_mul.1 hj
    have hvi : ¬ (cs).IsLeftDescent ((cs).simple (π i) * v) i := by
      rw [hv, (cs).simple_mul_simple_cancel_left]
      exact (cs).isLeftDescent_iff_not_isLeftDescent_mul.1 hi
    have h := hpair v i hπi hv' hvj hvi (ih _ (by omega) hv' rfl)
    rwa [hv, (cs).simple_mul_simple_cancel_left, (cs).simple_mul_simple_cancel_left] at h

end WeylPerm

section Twist

variable {K : Type*} [Group K]

structure IsTwist (D : UniversalRootDatum K) (n : Fin D.rank → K) (H : Fin D.rank → Subgroup K)
    (π : Equiv.Perm (Fin D.rank)) (σ : K →* K) : Prop where
  cartan_perm : ∀ i j, D.cartan (π i) (π j) = D.cartan i j
  divisible_perm : ∀ i ∈ D.divisible, π i ∈ D.divisible
  map_rootGroup : ∀ γ ∈ D.roots, ∀ x ∈ D.rootGroup γ, σ x ∈ D.rootGroup (permVec π γ)
  map_n : ∀ i, σ (n i) = n (π i)
  map_torus : ∀ i, ∀ h ∈ H i, σ h ∈ H (π i)

variable {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
  {π : Equiv.Perm (Fin D.rank)} {σ : K →* K}

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem
set_option hygiene false in
local notation "ρ" => weylAction D.isFiniteType

namespace IsTwist

variable (hσ : IsTwist D n H π σ)
include hσ

theorem perm_mem_roots {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) : permVec π γ ∈ D.roots :=
  permVec_mem_roots D.isFiniteType hσ.cartan_perm hσ.divisible_perm hγ

theorem map_nrep (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H) (w : W) :
    σ (nrep hct w) = nrep hct (weylPerm D.isFiniteType hσ.cartan_perm w) := by
  obtain ⟨ω, hω, rfl⟩ := (cs).exists_isReduced w
  rw [nrep_wordProd hct hω, weylPerm_wordProd,
    nrep_wordProd hct (isReduced_map_perm D.isFiniteType hσ.cartan_perm hω), map_list_prod,
    List.map_map, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun i _ => hσ.map_n i)

theorem map_iSup_torus {t : K} (ht : t ∈ ⨆ i, H i) : σ t ∈ ⨆ i, H i := by
  have hle : ⨆ i, H i ≤ (⨆ i, H i).comap σ :=
    iSup_le fun i h hh => le_iSup H (π i) (hσ.map_torus i h hh)
  exact hle ht

theorem map_posUnipotent {u : K} (hu : u ∈ posUnipotent D) : σ u ∈ posUnipotent D := by
  have hle : posUnipotent D ≤ (posUnipotent D).comap σ := iSup₂_le fun γ hγ x hx =>
    rootGroup_le_posUnipotent (hσ.perm_mem_roots hγ.1) (by rw [ht_permVec]; exact hγ.2)
      (hσ.map_rootGroup γ hγ.1 x hx)
  exact hle hu

theorem map_borel {b : K} (hb : b ∈ borel D H) : σ b ∈ borel D H := by
  have hle : borel D H ≤ (borel D H).comap σ :=
    sup_le (fun _ ht => iSup_le_borel (hσ.map_iSup_torus ht))
      (fun _ hu => posUnipotent_le_borel (hσ.map_posUnipotent hu))
  exact hle hb

theorem map_inversionUnipotent {w : W} {u : K} (hu : u ∈ inversionUnipotent D w) :
    σ u ∈ inversionUnipotent D (weylPerm D.isFiniteType hσ.cartan_perm w) := by
  have hle : inversionUnipotent D w ≤
      (inversionUnipotent D (weylPerm D.isFiniteType hσ.cartan_perm w)).comap σ :=
    iSup₂_le fun γ hγ x hx => rootGroup_le_inversionUnipotent (hσ.perm_mem_roots hγ.1)
      (by rw [ht_permVec]; exact hγ.2.1)
      (by rw [← permVec_weylAction, ht_permVec]; exact hγ.2.2) (hσ.map_rootGroup γ hγ.1 x hx)
  exact hle hu

variable (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)

include hext in
theorem fixed_normalForm (hBU : BruhatExtras D H) {g : K} (hg : σ g = g) :
    ∃ w : W, weylPerm D.isFiniteType hσ.cartan_perm w = w ∧ ∃ b ∈ borel D H, σ b = b ∧
      ∃ u ∈ inversionUnipotent D w, σ u = u ∧ g = b * nrep hct w * u := by
  obtain ⟨w, hw⟩ := exists_mem_bruhatCell hct hext g
  obtain ⟨b, hb, u, hu, rfl⟩ := exists_eq_mul_nrep_mul hct hext hw
  have hσg : σ (b * nrep hct w * u) =
      σ b * nrep hct (weylPerm D.isFiniteType hσ.cartan_perm w) * σ u := by
    rw [map_mul, map_mul, hσ.map_nrep hct]
  have hu' := hσ.map_inversionUnipotent hu
  have hww : weylPerm D.isFiniteType hσ.cartan_perm w = w := by
    refine eq_of_mem_bruhatCell hct hext ?_ hw
    rw [← hg, hσg]
    exact ⟨σ b, hσ.map_borel hb, σ u,
      posUnipotent_le_borel (inversionUnipotent_le_posUnipotent _ hu'), rfl⟩
  rw [hww] at hσg hu'
  obtain ⟨h1, h2⟩ := eq_of_mul_nrep_mul_eq hct hBU (hσ.map_borel hb) hb hu' hu (hσg.symm.trans hg)
  exact ⟨w, hww, b, hb, h1, u, hu, h2, rfl⟩

include hct hext in
theorem fixed_borel {b : K} (hb : b ∈ borel D H)
    (hfix : σ b = b) :
    ∃ t ∈ ⨆ i, H i, σ t = t ∧ ∃ v ∈ posUnipotent D, σ v = v ∧ b = t * v := by
  rw [← SetLike.mem_coe, coe_borel hct, Set.mem_mul] at hb
  obtain ⟨t, ht, v, hv, rfl⟩ := hb
  have ht' := hσ.map_iSup_torus ht
  have hv' := hσ.map_posUnipotent hv
  rw [map_mul] at hfix
  have heq : t⁻¹ * σ t = v * (σ v)⁻¹ := by
    calc t⁻¹ * σ t = t⁻¹ * (σ t * σ v) * (σ v)⁻¹ := by group
      _ = v * (σ v)⁻¹ := by rw [hfix]; group
  have hmem : t⁻¹ * σ t ∈ (⨆ i, H i) ⊓ posUnipotent D :=
    Subgroup.mem_inf.2 ⟨mul_mem (inv_mem ht) ht', heq ▸ mul_mem hv (inv_mem hv')⟩
  rw [show (⨆ i, H i) ⊓ posUnipotent D = ⊥ from hext.torus_inf_posPart, Subgroup.mem_bot,
    inv_mul_eq_one] at hmem
  rw [← hmem, mul_right_inj] at hfix
  exact ⟨t, ht, hmem.symm, v, hv, hfix, rfl⟩

end IsTwist

theorem nrep_mem_of_weylPerm_eq (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hπ : ∀ i j, D.cartan (π i) (π j) = D.cartan i j) (hπ2 : ∀ i, π (π i) = i)
    (horth : ∀ i, π i ≠ i → D.cartan i (π i) = 0) {S : Subgroup K}
    (hfixS : ∀ i, π i = i → n i ∈ S) (hpairS : ∀ i, π i ≠ i → n i * n (π i) ∈ S) {w : W}
    (hw : weylPerm D.isFiniteType hπ w = w) : nrep hct w ∈ S := by
  refine induction_weylPerm_fixed D.isFiniteType hπ hπ2 horth (P := fun w => nrep hct w ∈ S)
    (by rw [nrep_one]; exact one_mem S) (fun w i hi _ hwi h => ?_)
    (fun w i hi _ hwi hwi' h => ?_) hw
  · rw [nrep_simple_mul hct hwi]
    exact mul_mem (hfixS i hi) h
  · rw [nrep_simple_mul hct hwi', nrep_simple_mul hct hwi, ← mul_assoc]
    exact mul_mem (hpairS i hi) h

end Twist

end CFSG.LieType.Steinberg
