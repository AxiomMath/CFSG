module

public import CFSG.Adapters.TauCetiExceptional.BigCellNative
public import CFSG.LieType.Chevalley.ProductInjectivity

public noncomputable section

namespace CFSG.TauCetiBridge.BigCell

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag} {R : Type} [CommRing R]

theorem IntegralIn.add
    {S : Subring R} {A B : Module.End R (RootModule τ R)}
    (hA : IntegralIn S A) (hB : IntegralIn S B) : IntegralIn S (A + B) := fun i j => by
  rw [map_add, Matrix.add_apply]
  exact S.add_mem (hA i j) (hB i j)

theorem IntegralIn.smul
    {S : Subring R} {A : Module.End R (RootModule τ R)} {x : R}
    (hx : x ∈ S) (hA : IntegralIn S A) : IntegralIn S (x • A) := fun i j => by
  rw [map_smul, Matrix.smul_apply, smul_eq_mul]
  exact S.mul_mem hx (hA i j)

theorem IntegralIn.sum {S : Subring R} {ι : Type*} (s : Finset ι)
    {A : ι → Module.End R (RootModule τ R)} (hA : ∀ i ∈ s, IntegralIn S (A i)) :
    IntegralIn S (∑ i ∈ s, A i) := fun i j => by
  rw [map_sum, Matrix.sum_apply]
  exact S.sum_mem fun k hk => hA k hk i j

theorem integralIn_D
    (S : Subring R) (F : RootOperatorFamily τ) (α : Root τ) (k : ℕ) :
    IntegralIn S (F.D R α k) :=
  integralIn_of_baseChange S (BaseChange.D (f := Int.castRingHom R) F α k)

theorem integralIn_eltOr
    (S : Subring R) (F : RootOperatorFamily τ) (γ : Fin τ.rank → ℤ)
    {x : R} (hx : x ∈ S) : IntegralIn S (RootOperatorFamily'.eltOr F R γ x) := by
  by_cases hγ : IsRoot τ γ
  · rw [RootOperatorFamily'.eltOr_of_isRoot F R hγ, RootOperatorFamily.elt]
    exact IntegralIn.sum _ fun k _ => (integralIn_D S F _ k).smul (S.pow_mem hx k)
  · rw [RootOperatorFamily'.eltOr_of_not_isRoot F R hγ]
    exact IntegralIn.one S

theorem integralIn_prod_weylElt
    (S : Subring R) (w : List (Fin τ.rank)) :
    IntegralIn S (((w.map fun i => weylElt τ R i 1).prod : (Module.End R (RootModule τ R))ˣ) :
      Module.End R (RootModule τ R)) :=
  integralIn_of_baseChange S (BaseChange.prod_weylElt (f := Int.castRingHom R) w)

theorem integralIn_prod_weylElt_inv
    (S : Subring R) (w : List (Fin τ.rank)) :
    IntegralIn S ((((w.map fun i => weylElt τ R i 1).prod)⁻¹ :
      (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R)) :=
  integralIn_of_baseChange S
    (BaseChange.units_inv (BaseChange.prod_weylElt (f := Int.castRingHom R) w))

theorem mem_of_integralIn_smul_D
    (S : Subring R) (F : RootOperatorFamily τ) (α : Root τ)
    {x : R} (h : IntegralIn S (x • F.D R α 1)) : x ∈ S := by
  obtain ⟨j, ε, w, hε, hw⟩ := RootOperatorFamily'.exists_D_eq_word F α
  set W := (w.map fun i => weylElt τ R i 1).prod with hWdef
  have hconj : ((W⁻¹ : (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R)) *
      (x • F.D R α 1) * (W : Module.End R (RootModule τ R)) =
        (x * (ε : R)) • xCoeff τ R j 1 := by
    rw [hw R 1, ← hWdef, pow_one, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc,
      smul_smul]
    congr 1
    simp only [mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one]
  have hint : IntegralIn S ((x * (ε : R)) • xCoeff τ R j 1) := by
    rw [← hconj]
    exact ((integralIn_prod_weylElt_inv S w).mul h).mul (integralIn_prod_weylElt S w)
  have he := hint (posEquiv τ (Sum.inl j))
    (posEquiv τ (Sum.inr ⟨-Pi.single j 1, isRoot_neg_single τ j⟩))
  have hv : Finsupp.single (Sum.inr ⟨-Pi.single j 1, isRoot_neg_single τ j⟩) (1 : R) =
      rootVec τ R (-Pi.single j 1) := by
    rw [rootVec, dite_eq_left (isRoot_neg_single τ j)]
  rw [natMat_apply_posEquiv, LinearMap.smul_apply, xCoeff_one, hv, infE_rootVec_neg_single,
    hVec, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at he
  have hx : x = x * (ε : R) * (ε : R) := by
    rw [mul_assoc, sign_cast_eq hε, mul_one]
  rw [hx]
  exact S.mul_mem he (intCast_mem S ε)

@[expose] def heightHom : (Fin τ.rank → ℤ) →+ ℤ :=
  AddMonoidHom.mk' (height (τ := τ)) fun u v => by
    simp only [height, Pi.add_apply, Finset.sum_add_distrib]

theorem mem_of_integralIn_prod_eltOr
    (S : Subring R) (F : RootOperatorFamily τ)
    {φ : (Fin τ.rank → ℤ) →+ ℤ} (L : List (Fin τ.rank → ℤ)) (hnd : L.Nodup)
    (hL : ∀ γ ∈ L, IsRoot τ γ ∧ 0 < φ γ) (c : (Fin τ.rank → ℤ) → R)
    (hP : IntegralIn S (L.map fun γ => RootOperatorFamily'.eltOr F R γ (c γ)).prod) :
    ∀ γ ∈ L, c γ ∈ S := by
  classical
  have hL1 : ∀ γ ∈ L, 1 ≤ φ γ := fun γ hγ => (hL γ hγ).2
  have key : ∀ m : ℕ, ∀ γ ∈ L, φ γ < m → c γ ∈ S := by
    intro m
    induction m with
    | zero =>
      intro γ hγ hm
      have := (hL γ hγ).2
      omega
    | succ m ih =>
      intro γ hγ hm
      by_cases hlt : φ γ < m
      · exact ih γ hγ hlt
      obtain ⟨h₀, h₀φ⟩ := hL γ hγ
      set c' : (Fin τ.rank → ℤ) → R := fun δ => if φ δ < φ γ then c δ else 0 with hc'
      have hlow : ∀ δ ∈ L, φ δ < φ γ → c δ = c' δ := fun δ _ hδ => by
        simp only [hc', hδ, ite_true]
      have hP' : IntegralIn S (L.map fun δ => RootOperatorFamily'.eltOr F R δ (c' δ)).prod := by
        refine IntegralIn.list_prod _ fun A hA => ?_
        obtain ⟨δ, hδ, rfl⟩ := List.mem_map.1 hA
        refine integralIn_eltOr S F δ ?_
        by_cases hδφ : φ δ < φ γ
        · rw [← hlow δ hδ hδφ]
          exact ih δ hδ (by omega)
        · simp only [hc', hδφ, ite_false]
          exact S.zero_mem
      refine mem_of_integralIn_smul_D S F ⟨γ, h₀⟩ (x := c γ) fun i j => ?_
      rw [natMat_apply, LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul]
      set a := (posEquiv τ).symm i
      set b := (posEquiv τ).symm j
      by_cases hD : F.D R ⟨γ, h₀⟩ 1 (Finsupp.single b 1) a = 0
      · rw [hD, mul_zero]
        exact S.zero_mem
      have hab : labelWt τ a = labelWt τ b + γ := by
        have := F.mapsLabelWt_D (R := R) ⟨γ, h₀⟩ le_rfl a b hD
        rwa [one_nsmul] at this
      have h := RootOperatorFamily.prod_sub_prod_apply_of_shift F h₀ h₀φ c c' hab L hL1 hlow
      have hc'γ : c' γ = 0 := by simp [hc']
      rw [List.count_eq_one_of_mem hnd hγ, Nat.cast_one, one_mul, hc'γ, sub_zero] at h
      rw [← h, LinearMap.sub_apply, Finsupp.sub_apply]
      have e1 := hP (posEquiv τ a) (posEquiv τ b)
      have e2 := hP' (posEquiv τ a) (posEquiv τ b)
      rw [natMat_apply_posEquiv] at e1 e2
      exact S.sub_mem e1 e2
  intro γ hγ
  exact key ((φ γ).toNat + 1) γ hγ (by have := Int.self_le_toNat (φ γ); push_cast; omega)

theorem mem_of_integralIn_list_prod_pinnedX
    (S : Subring R) (L : List (Fin τ.rank → ℤ))
    (hnd : L.Nodup) (hL : ∀ γ ∈ L, IsRoot τ γ ∧ 0 < height γ) (c : (Fin τ.rank → ℤ) → R)
    (hP : IntegralIn S (((L.map fun γ => pinnedX τ R γ (c γ)).prod :
      (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R))) :
    ∀ γ ∈ L, c γ ∈ S := by
  rw [coe_list_prod_pinnedX c L fun γ hγ => (hL γ hγ).1] at hP
  have h := mem_of_integralIn_prod_eltOr S (rootOperatorFamily τ) (φ := heightHom) L hnd
    (fun γ hγ => ⟨(hL γ hγ).1, (hL γ hγ).2⟩) _ hP
  intro γ hγ
  have h1 := S.mul_mem (intCast_mem S ((rootOperatorFamily τ).pinnedFamilySign γ)) (h γ hγ)
  rwa [← mul_assoc, (rootOperatorFamily τ).pinnedFamilySign_mul_self, one_mul] at h1

theorem mem_of_integralIn_prod_ofFn_pinnedX
    (S : Subring R) {m : ℕ}
    (α : Fin m → Fin τ.rank → ℤ) (hα : Function.Injective α)
    (hpos : ∀ i, IsRoot τ (α i) ∧ 0 < height (α i)) (c : Fin m → R)
    (hP : IntegralIn S (((List.ofFn fun i => pinnedX τ R (α i) (c i)).prod :
      (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R))) (i : Fin m) :
    c i ∈ S := by
  have hprod : (List.ofFn fun i => pinnedX τ R (α i) (c i)) =
      (List.ofFn α).map fun γ => pinnedX τ R γ (Function.extend α c 0 γ) := by
    rw [List.map_ofFn]
    congr 1
    funext k
    simp only [Function.comp_apply, hα.extend_apply]
  rw [hprod] at hP
  have h := mem_of_integralIn_list_prod_pinnedX S (List.ofFn α) (List.nodup_ofFn.2 hα)
    (fun γ hγ => by obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hγ; exact hpos k) _ hP (α i)
    (List.mem_ofFn.2 ⟨i, rfl⟩)
  rwa [hα.extend_apply] at h

end CFSG.TauCetiBridge.BigCell
