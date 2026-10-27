module

public import CFSG.LieType.Steinberg.CentralExt.SUThreeFieldTwo
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2Torus

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Module Submodule CFSG.Assembly.LowTwoRank
open CFSG.Fischer.Classification (CubeRel)
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open scoped commutatorElement

section GLCard

variable {K : Type*} [Field K] [Finite K]

theorem not_dvd_card_GL_of_le_four (hK : Nat.card K = 2) {d : ℕ} (hd : d ≤ 4) :
    ¬ 27 ∣ Nat.card (Matrix.GeneralLinearGroup (Fin d) K) := by
  have : Fintype K := Fintype.ofFinite K
  rw [Matrix.card_GL_field, ← Nat.card_eq_fintype_card, hK]
  interval_cases d <;> simp [Fin.prod_univ_succ]

omit [Finite K] in
theorem card_units_end_eq (W : Type*) [AddCommGroup W] [Module K W] [FiniteDimensional K W] :
    Nat.card (Module.End K W)ˣ = Nat.card (Matrix.GeneralLinearGroup (Fin (finrank K W)) K) :=
  Nat.card_congr (Units.mapEquiv
    (LinearMap.toMatrixAlgEquiv (Module.finBasis K W)).toMulEquiv).toEquiv

end GLCard

section Linear

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def commSpaceStab (W : Submodule K V) : Subgroup (Module.End K V)ˣ where
  carrier := {u | (∀ w ∈ W, (u : Module.End K V) w ∈ W) ∧
    (∀ w ∈ W, ((u⁻¹ : (Module.End K V)ˣ) : Module.End K V) w ∈ W) ∧
    ∀ v, (u : Module.End K V) v - v ∈ W}
  mul_mem' {u u'} hu hu' := by
    refine ⟨fun w hw => hu.1 _ (hu'.1 w hw), fun w hw => ?_, fun v => ?_⟩
    · rw [mul_inv_rev, Units.val_mul, Module.End.mul_apply]
      exact hu'.2.1 _ (hu.2.1 w hw)
    · have h : ((u * u' : (Module.End K V)ˣ) : Module.End K V) v - v =
          (u : Module.End K V) ((u' : Module.End K V) v - v) +
            ((u : Module.End K V) v - v) := by
        rw [Units.val_mul, Module.End.mul_apply, map_sub]
        abel
      rw [h]
      exact W.add_mem (hu.1 _ (hu'.2.2 v)) (hu.2.2 v)
  one_mem' := ⟨fun w hw => hw, fun w hw => by simpa using hw, fun v => by simp⟩
  inv_mem' {u} hu := by
    refine ⟨hu.2.1, fun w hw => by simpa using hu.1 w hw, fun v => ?_⟩
    have h : ((u⁻¹ : (Module.End K V)ˣ) : Module.End K V) v - v =
        -((u⁻¹ : (Module.End K V)ˣ) : Module.End K V)
          ((u : Module.End K V) v - v) := by
      rw [map_sub, ← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Module.End.one_apply]
      abel
    rw [h]
    exact W.neg_mem (hu.2.1 _ (hu.2.2 v))

@[expose] noncomputable def commSpaceRes (W : Submodule K V) :
    commSpaceStab W →* (Module.End K W)ˣ where
  toFun u :=
    { val := LinearMap.restrict ((u : (Module.End K V)ˣ) : Module.End K V) u.2.1
      inv := LinearMap.restrict ((u⁻¹ : (Module.End K V)ˣ) : Module.End K V) u.2.2.1
      val_inv := LinearMap.ext fun w => Subtype.ext (by
        change ((u : (Module.End K V)ˣ) : Module.End K V)
          (((u⁻¹ : (Module.End K V)ˣ) : Module.End K V) w) = w
        rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Module.End.one_apply])
      inv_val := LinearMap.ext fun w => Subtype.ext (by
        change ((u⁻¹ : (Module.End K V)ˣ) : Module.End K V)
          (((u : (Module.End K V)ˣ) : Module.End K V) w) = w
        rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Module.End.one_apply]) }
  map_one' := Units.ext (LinearMap.ext fun w => Subtype.ext rfl)
  map_mul' u u' := Units.ext (LinearMap.ext fun w => Subtype.ext rfl)

end Linear

section Main

variable {K V : Type*} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem mem_commSpaceStab {W : Submodule K V} {u : (Module.End K V)ˣ} (hu3 : u ^ 3 = 1)
    (hu : LinearMap.range ((u : Module.End K V) - 1) ≤ W) : u ∈ commSpaceStab W := by
  have hsub : ∀ v, (u : Module.End K V) v - v ∈ W := fun v => hu ⟨v, rfl⟩
  have hmapW : ∀ w ∈ W, (u : Module.End K V) w ∈ W := fun w hw => by
    have h := W.add_mem hw (hsub w)
    rwa [add_sub_cancel] at h
  have hinv : u⁻¹ = u ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ', hu3])
  refine ⟨hmapW, fun w hw => ?_, hsub⟩
  rw [hinv, Units.val_pow_eq_pow_val, pow_two, Module.End.mul_apply]
  exact hmapW _ (hmapW w hw)

theorem commute_of_cubeRel_of_finrank_le (hK : Nat.card K = 2) {f g : (Module.End K V)ˣ}
    (hf : finrank K (LinearMap.range ((f : Module.End K V) - 1)) ≤ 2)
    (hg : finrank K (LinearMap.range ((g : Module.End K V) - 1)) ≤ 2)
    (hR : CubeRel f g) : f * g = g * f := by
  classical
  by_contra hfg
  set W : Submodule K V := LinearMap.range ((f : Module.End K V) - 1) ⊔
    LinearMap.range ((g : Module.End K V) - 1) with hWdef
  have hW : finrank K W ≤ 4 :=
    (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (by omega)
  have hfS : f ∈ commSpaceStab W := mem_commSpaceStab hR.cube_left le_sup_left
  have hgS : g ∈ commSpaceStab W := mem_commSpaceStab hR.cube_right le_sup_right
  set fS : commSpaceStab W := ⟨f, hfS⟩ with hfSdef
  set gS : commSpaceStab W := ⟨g, hgS⟩ with hgSdef
  have hRS : CubeRel fS gS :=
    ⟨Subtype.ext (by simpa using hR.cube_left), Subtype.ext (by simpa using hR.cube_right),
      Subtype.ext (by simpa using hR.cube_mul), Subtype.ext (by simpa using hR.cube_mul_inv)⟩
  set ρ := commSpaceRes W with hρ
  have hRW : CubeRel (ρ fS) (ρ gS) :=
    ⟨by rw [← map_pow, hRS.cube_left, map_one], by rw [← map_pow, hRS.cube_right, map_one],
      by rw [← map_mul, ← map_pow, hRS.cube_mul, map_one],
      by rw [← map_inv, ← map_mul, ← map_pow, hRS.cube_mul_inv, map_one]⟩
  have hne : ρ fS * ρ gS ≠ ρ gS * ρ fS := by
    intro heq
    apply hfg
    set c : commSpaceStab W := ⁅fS, gS⁆ with hc
    have hρc : ρ c = 1 := by
      rw [hc, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, heq]
    have hcW : ∀ w ∈ W, ((c : (Module.End K V)ˣ) : Module.End K V) w = w := by
      intro w hw
      have h1 : ((((ρ c : (Module.End K W)ˣ) : Module.End K W) ⟨w, hw⟩ : W) : V) = w := by
        rw [hρc]
        rfl
      exact h1
    have h2 : ∀ x : V, x + x = 0 := fun x => by
      rw [← two_smul K x, show (2 : K) = 0 from by exact_mod_cast CharP.cast_eq_zero K 2,
        zero_smul]
    have hc2 : c ^ 2 = 1 := by
      apply Subtype.ext
      apply Units.ext
      refine LinearMap.ext fun v => ?_
      have hv := hcW _ (c.2.2.2 v)
      rw [map_sub] at hv
      have h3 : ((c : (Module.End K V)ˣ) : Module.End K V)
          (((c : (Module.End K V)ˣ) : Module.End K V) v) = v := by
        rw [sub_eq_iff_eq_add] at hv
        rw [hv, sub_add_eq_add_sub, h2, zero_sub, neg_eq_iff_add_eq_zero, h2]
      simpa [pow_two] using h3
    have hc1 : c = 1 := by
      have h3 := hRS.commutator_pow_three
      rw [← hc] at h3
      calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
        _ = 1 := by rw [h3, hc2, inv_one, one_mul]
    have h5 : fS * gS = gS * fS := by
      rw [← commutatorElement_eq_one_iff_mul_comm, ← hc, hc1]
    exact congrArg Subtype.val h5
  have : Finite (Module.End K W) := Module.finite_of_finite K
  have : Finite (Module.End K W)ˣ :=
    Finite.of_injective (fun u : (Module.End K W)ˣ => (u : Module.End K W))
      fun _ _ h => Units.ext h
  have h27 := CFSG.LieType.Steinberg.CentralExt.SUThreeFieldTwo.card_closure_eq_of_cubeRel hRW hne
  have hdvd := Subgroup.card_subgroup_dvd_card (Subgroup.closure ({ρ fS, ρ gS} :
    Set (Module.End K W)ˣ))
  rw [h27, card_units_end_eq W] at hdvd
  exact not_dvd_card_GL_of_le_four hK hW hdvd

end Main

section Sp

open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)

variable {K : Type} [Field K] {n : ℕ}

@[expose] noncomputable def spLin (n : ℕ) (K : Type) [Field K] :
    StatedSp n K →* (Module.End K (Fin n ⊕ Fin n → K))ˣ :=
  (Matrix.GeneralLinearGroup.toLin).toMonoidHom.comp (StatedSp n K).subtype

theorem spLin_apply (y : StatedSp n K) (v : Fin n ⊕ Fin n → K) :
    (spLin n K y).val v = (mat n K y).mulVec v := rfl

theorem spLin_injective : Function.Injective (spLin n K) := by
  intro y z h
  apply mat_injective
  ext r t
  have h1 := congrArg (fun u : (Module.End K (Fin n ⊕ Fin n → K))ˣ =>
    (u.val (Pi.single t 1)) r) h
  simpa [spLin_apply, Matrix.mulVec_single] using h1

theorem range_spLin_nsElt_sub_one_le (k : Fin n) :
    LinearMap.range ((spLin n K (nsElt k)).val - 1) ≤
      span K (Set.range ![(Pi.single (Sum.inl k) (1 : K) : Fin n ⊕ Fin n → K),
        Pi.single (Sum.inr k) (1 : K)]) := by
  classical
  rintro _ ⟨v, rfl⟩
  set M := mat n K (nsElt k) with hM
  have hsupp : IsSupp (coords k) M := isSupp_longBlock k zThreeSL
  set u : Fin n ⊕ Fin n → K := M.mulVec v - v with hu
  have hval : ((spLin n K (nsElt k)).val - 1) v = u := by
    rw [LinearMap.sub_apply, spLin_apply, Module.End.one_apply]
  rw [hval]
  have hzero : ∀ j, j ≠ Sum.inl k → j ≠ Sum.inr k → u j = 0 := by
    intro j hj1 hj2
    have hj : j ∉ coords k := by
      rw [mem_coords]
      tauto
    have hrow : ∀ t, M j t = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) j t :=
      fun t => hsupp j t fun h => hj h.1
    rw [hu, Pi.sub_apply, Matrix.mulVec, dotProduct]
    simp_rw [hrow, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, sub_self]
  have heq : u = u (Sum.inl k) • (Pi.single (Sum.inl k) (1 : K) : Fin n ⊕ Fin n → K) +
      u (Sum.inr k) • (Pi.single (Sum.inr k) (1 : K) : Fin n ⊕ Fin n → K) := by
    funext j
    by_cases h1 : j = Sum.inl k
    · subst h1
      simp
    by_cases h2 : j = Sum.inr k
    · subst h2
      simp
    simp [h1, h2, hzero j h1 h2]
  rw [heq]
  exact add_mem (smul_mem _ _ (subset_span ⟨0, rfl⟩)) (smul_mem _ _ (subset_span ⟨1, rfl⟩))

theorem finrank_range_spLin_conj_nsElt_sub_one_le (h : StatedSp n K) (k : Fin n) :
    finrank K (LinearMap.range ((spLin n K (h * nsElt k * h⁻¹)).val - 1)) ≤ 2 := by
  set H : Module.End K (Fin n ⊕ Fin n → K) := (spLin n K h).val with hH
  set X : Module.End K (Fin n ⊕ Fin n → K) := (spLin n K (nsElt k)).val with hX
  have hrange : LinearMap.range ((spLin n K (h * nsElt k * h⁻¹)).val - 1) ≤
      (LinearMap.range (X - 1)).map H := by
    rintro _ ⟨v, rfl⟩
    refine ⟨(X - 1) ((spLin n K h⁻¹).val v), ⟨_, rfl⟩, ?_⟩
    have hHi : H ((spLin n K h⁻¹).val v) = v := by
      rw [hH, ← Module.End.mul_apply, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
        Units.val_one, Module.End.one_apply]
    simp only [map_mul, Units.val_mul, LinearMap.sub_apply, Module.End.mul_apply,
      Module.End.one_apply, map_sub, ← hH, ← hX, hHi]
  calc finrank K _ ≤ finrank K ((LinearMap.range (X - 1)).map H) := Submodule.finrank_mono hrange
    _ ≤ finrank K (LinearMap.range (X - 1)) := Submodule.finrank_map_le _ _
    _ ≤ finrank K (span K (Set.range ![(Pi.single (Sum.inl k) (1 : K) : Fin n ⊕ Fin n → K),
        Pi.single (Sum.inr k) (1 : K)])) :=
        Submodule.finrank_mono (range_spLin_nsElt_sub_one_le k)
    _ ≤ 2 := (finrank_range_le_card _).trans (by simp)

theorem commute_of_cubeRel_of_conj_nsElt [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {y₁ y₂ : StatedSp n K} (h₁ : ∃ (h : StatedSp n K) (k : Fin n), y₁ = h * nsElt k * h⁻¹)
    (h₂ : ∃ (h : StatedSp n K) (k : Fin n), y₂ = h * nsElt k * h⁻¹) (hR : CubeRel y₁ y₂) :
    y₁ * y₂ = y₂ * y₁ := by
  obtain ⟨g₁, k₁, rfl⟩ := h₁
  obtain ⟨g₂, k₂, rfl⟩ := h₂
  set φ := spLin n K with hφ
  have hR' : CubeRel (φ (g₁ * nsElt k₁ * g₁⁻¹)) (φ (g₂ * nsElt k₂ * g₂⁻¹)) :=
    ⟨by rw [← map_pow, hR.cube_left, map_one], by rw [← map_pow, hR.cube_right, map_one],
      by rw [← map_mul, ← map_pow, hR.cube_mul, map_one],
      by rw [← map_inv, ← map_mul, ← map_pow, hR.cube_mul_inv, map_one]⟩
  have h := commute_of_cubeRel_of_finrank_le hK (finrank_range_spLin_conj_nsElt_sub_one_le g₁ k₁)
    (finrank_range_spLin_conj_nsElt_sub_one_le g₂ k₂) hR'
  rw [← map_mul, ← map_mul] at h
  exact spLin_injective h

end Sp

end CFSG.SeitzReduction.SymplecticPilot
