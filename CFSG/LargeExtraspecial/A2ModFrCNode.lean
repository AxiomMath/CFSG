module

public import CFSG.LargeExtraspecial.A2ModFrCGen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.A2Mod.FrC

open Module Matrix CFSG.RankThree.OrthogonalInvolutions CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Symplectic

variable {k : ℕ} {X : Type} [Group X] {D : Set X}

theorem levi_map_mem (hDc : ∀ g, ∀ d ∈ D, g * d * g⁻¹ ∈ D)
    (Ψ : SpecialLinearGroup (Fin k) (ZMod 2) →* X) {i j : Fin k} (hij : i ≠ j)
    (h : Ψ (elemTv i j) ∈ D) : ∀ g ∈ transvectionSet k (ZMod 2), Ψ g ∈ D := by
  intro g hg
  rw [← conjugatesOf_transvection hij] at hg
  obtain ⟨c, rfl⟩ := isConj_iff.mp hg
  rw [map_mul, map_mul, map_inv, ← elemTv_eq_transvection hij]
  exact hDc _ _ h

theorem single_add_single_ne_zero {j l : Fin k} (hjl : j ≠ l) :
    (Pi.single j (1 : ZMod 2) + Pi.single l 1 : Fin k → ZMod 2) ≠ 0 := by
  intro h
  have := congrFun h j
  rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hjl, add_zero, Pi.zero_apply] at this
  exact one_ne_zero this

theorem elemTv_mul_elemTv_mem_left {i j l : Fin k} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    elemTv i j * elemTv i l ∈ transvectionSet k (ZMod 2) := by
  rw [elemTv, elemTv, tv_mul_tv_left (single_dotProduct_single_of_ne hij)
    (single_dotProduct_single_of_ne hil)]
  refine tv_mem_transvectionSet (Pi.single_ne_zero_iff.mpr one_ne_zero)
    (single_add_single_ne_zero hjl) ?_
  rw [add_dotProduct, single_dotProduct_single_of_ne hij, single_dotProduct_single_of_ne hil,
    add_zero]

theorem elemTv_mul_elemTv_mem_right {i j l : Fin k} (hij : i ≠ j) (hlj : l ≠ j) (hil : i ≠ l) :
    elemTv i j * elemTv l j ∈ transvectionSet k (ZMod 2) := by
  rw [elemTv, elemTv, tv_mul_tv_right (single_dotProduct_single_of_ne hij)
    (single_dotProduct_single_of_ne hlj)]
  refine tv_mem_transvectionSet (single_add_single_ne_zero hil)
    (Pi.single_ne_zero_iff.mpr one_ne_zero) ?_
  rw [dotProduct_add, single_dotProduct_single_of_ne hij, single_dotProduct_single_of_ne hlj,
    add_zero]

theorem conj_mul_of_commute {w u v : X} (h : Commute w v) :
    w * u * w⁻¹ * v = w * (u * v) * w⁻¹ := by
  calc w * u * w⁻¹ * v = w * u * (w⁻¹ * v) := by group
    _ = w * u * (v * w⁻¹) := by rw [h.inv_left.eq]
    _ = w * (u * v) * w⁻¹ := by group

section Frame

variable {F : Type} [Field F] [CharP F 2] (Ψ : StatedSp k F →* X)

theorem isLeviNode (hDc : ∀ g, ∀ d ∈ D, g * d * g⁻¹ ∈ D)
    (hL : ∀ g ∈ transvectionSet k (ZMod 2), Ψ (levZ g) ∈ D) {p m : Fin k}
    (hp : p.val + 2 = k) (hm : m.val + 1 = k) :
    IsLeviNode D (Ψ.comp levZ) (Ψ (sumPos p m)) (Ψ (sumNeg p m)) where
  map_mem g hg := hL g hg
  mem_left := by
    have hpm : p ≠ m := fin_ne_of_val_ne (by omega)
    rw [← longWeyl_conj_levZ_left hpm, map_mul, map_mul, map_inv]
    exact hDc _ _ (hL _ (elemTv_mem_transvectionSet hpm))
  mem_right := by
    have hpm : p ≠ m := fin_ne_of_val_ne (by omega)
    rw [← longWeyl_conj_levZ_right hpm, map_mul, map_mul, map_inv]
    exact hDc _ _ (hL _ (elemTv_mem_transvectionSet hpm.symm))
  commute_left i j hij :=
    (commute_sumPos_levZ (fin_ne_of_val_ne (by omega)) (fin_ne_of_val_ne (by omega))
      (fun h => Fin.ext (by have := congrArg Fin.val h; omega))
      (fun h => absurd (congrArg Fin.val h) (by have := i.2; omega))).map Ψ
  commute_right i j hij :=
    (commute_sumNeg_levZ (fin_ne_of_val_ne (by omega)) (fin_ne_of_val_ne (by omega))
      (fun h => Fin.ext (by have := congrArg Fin.val h; omega))
      (fun h => absurd (congrArg Fin.val h) (by have := j.2; omega))).map Ψ
  mul_mem_left i j hi hj := by
    obtain rfl : i = p := Fin.ext (by omega)
    have hpm : i ≠ m := fin_ne_of_val_ne (by omega)
    have hij : i ≠ j := fin_ne_of_val_ne (by omega)
    have hjm : j ≠ m := fin_ne_of_val_ne (by omega)
    rw [MonoidHom.comp_apply, ← map_mul, ← longWeyl_conj_levZ_left hpm,
      conj_mul_of_commute (commute_longWeyl_levZ hij hpm hjm), ← map_mul, map_mul, map_mul,
      map_inv]
    exact hDc _ _ (hL _ (elemTv_mul_elemTv_mem_left hpm hij hjm.symm))
  mul_mem_right i j hi hj := by
    obtain rfl : j = p := Fin.ext (by omega)
    have hpm : j ≠ m := fin_ne_of_val_ne (by omega)
    have hij : i ≠ j := fin_ne_of_val_ne (by omega)
    have him : i ≠ m := fin_ne_of_val_ne (by omega)
    rw [MonoidHom.comp_apply, ← map_mul, ← longWeyl_conj_levZ_right hpm,
      conj_mul_of_commute (commute_longWeyl_levZ hij him hpm), ← map_mul, map_mul, map_mul,
      map_inv]
    exact hDc _ _ (hL _ (elemTv_mul_elemTv_mem_right hpm.symm hij him.symm))

theorem dZero_mem (hDc : ∀ g, ∀ d ∈ D, g * d * g⁻¹ ∈ D)
    (hL : ∀ g ∈ transvectionSet k (ZMod 2), Ψ (levZ g) ∈ D) {p m : Fin k} (hpm : p ≠ m) :
    Ψ (dZero p m) ∈ D := by
  rw [dZero, map_mul, map_mul, map_inv]
  exact hDc _ _ (hL _ (elemTv_mem_transvectionSet hpm))

theorem dZero_mul_mem (hDc : ∀ g, ∀ d ∈ D, g * d * g⁻¹ ∈ D)
    (hL : ∀ g ∈ transvectionSet k (ZMod 2), Ψ (levZ g) ∈ D) {p m q : Fin k} (hpm : p ≠ m)
    (hpq : p ≠ q) (hqm : q ≠ m) : Ψ (dZero p m) * Ψ (levZ (elemTv p q)) ∈ D := by
  rw [← map_mul, dZero, conj_mul_of_commute (commute_longPos_levZ hpq hqm), ← map_mul, map_mul,
    map_mul, map_inv]
  exact hDc _ _ (hL _ (elemTv_mul_elemTv_mem_left hpm hpq hqm.symm))

theorem sup_zpowers_eq_top (hF : Nat.card F = 2) (hsurj : Function.Surjective Ψ) {p m : Fin k}
    (hpm : p ≠ m) (hm : m.val + 1 = k) :
    (Ψ.comp levZ).range ⊔ Subgroup.zpowers (Ψ (sumPos p m)) ⊔
        Subgroup.zpowers (Ψ (sumNeg p m)) ⊔ Subgroup.zpowers (Ψ (dZero p m)) = ⊤ := by
  have h := congrArg (Subgroup.map Ψ) (sup_zpowers_dZero_eq_top (F := F) hF hpm hm)
  rwa [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers,
    MonoidHom.map_zpowers, MonoidHom.map_zpowers, ← MonoidHom.range_comp, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.mpr hsurj] at h

theorem map_levZ_tv_swap {v φ : Fin k → ZMod 2} (h : φ ⬝ᵥ v = 0) :
    Ψ (levZ (tv φ v)) = Ψ jElt * Ψ (levZ (tv v φ)) * (Ψ jElt)⁻¹ := by
  rw [← jElt_conj_levZ_tv h, map_mul, map_mul, map_inv]

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (ρ : X →* (V ≃ₗ[ZMod 2] V))

theorem exists_hyperplaneCentre_of_pointCentre {v₀ : Fin k → ZMod 2} (hv₀ : v₀ ≠ 0)
    (h : ∃ P : V, P ≠ 0 ∧ ∀ a ∈ pointGroup v₀, a ≠ 1 → P ∈ commSpace (ρ.comp (Ψ.comp levZ) a)) :
    ∃ P : V, P ≠ 0 ∧ ∀ a ∈ hyperplaneGroup v₀, a ≠ 1 →
      P ∈ commSpace (ρ.comp (Ψ.comp levZ) a) := by
  obtain ⟨P, hP0, hP⟩ := h
  refine ⟨ρ (Ψ jElt) P, fun h0 => hP0 ((LinearEquiv.map_eq_zero_iff _).mp h0), fun a ha ha1 => ?_⟩
  obtain ⟨v, hv, rfl⟩ := mem_hyperplaneGroup.mp ha
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact ha1 (tv_zero_left _)
  have hvv : v ⬝ᵥ v₀ = 0 := by rwa [dotProduct_comm]
  have hmem := apply_mem_commSpace_conj ρ (Ψ jElt)
    (hP (tv v₀ v) (tv_mem_pointGroup v₀ v) (tv_ne_one hv₀ hv0 hvv))
  rwa [MonoidHom.comp_apply, MonoidHom.comp_apply, map_levZ_tv_swap Ψ hvv]

theorem exists_pointCentre_of_hyperplaneCentre {v₀ : Fin k → ZMod 2} (hv₀ : v₀ ≠ 0)
    (h : ∃ P : V, P ≠ 0 ∧ ∀ a ∈ hyperplaneGroup v₀, a ≠ 1 →
      P ∈ commSpace (ρ.comp (Ψ.comp levZ) a)) :
    ∃ P : V, P ≠ 0 ∧ ∀ a ∈ pointGroup v₀, a ≠ 1 → P ∈ commSpace (ρ.comp (Ψ.comp levZ) a) := by
  obtain ⟨P, hP0, hP⟩ := h
  refine ⟨ρ (Ψ jElt) P, fun h0 => hP0 ((LinearEquiv.map_eq_zero_iff _).mp h0), fun a ha ha1 => ?_⟩
  obtain ⟨φ, hφ, rfl⟩ := mem_pointGroup.mp ha
  have hφ0 : φ ≠ 0 := by
    rintro rfl
    exact ha1 (tv_zero_right _)
  have hφφ : v₀ ⬝ᵥ φ = 0 := by rwa [dotProduct_comm]
  have hmem := apply_mem_commSpace_conj ρ (Ψ jElt)
    (hP (tv φ v₀) (tv_mem_hyperplaneGroup φ v₀) (tv_ne_one hφ0 hv₀ hφφ))
  rwa [MonoidHom.comp_apply, MonoidHom.comp_apply, map_levZ_tv_swap Ψ hφφ]

end Frame

section Bounds

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}
  {Ψ : SpecialLinearGroup (Fin k) (ZMod 2) →* X} {a b : X}

theorem finrank_commSpaceOf_le_eight_of_four (hA : A2Action D Q ρ) (h : IsLeviNode D Ψ a b)
    (hk : k = 4) (i : Fin k)
    (hAB : (∃ P : V, P ≠ 0 ∧ ∀ g ∈ pointGroup (Pi.single i 1), g ≠ 1 →
        P ∈ commSpace (ρ.comp Ψ g)) →
      ∃ P : V, P ≠ 0 ∧ ∀ g ∈ hyperplaneGroup (Pi.single i 1), g ≠ 1 →
        P ∈ commSpace (ρ.comp Ψ g))
    (hBA : (∃ P : V, P ≠ 0 ∧ ∀ g ∈ hyperplaneGroup (Pi.single i 1), g ≠ 1 →
        P ∈ commSpace (ρ.comp Ψ g)) →
      ∃ P : V, P ≠ 0 ∧ ∀ g ∈ pointGroup (Pi.single i 1), g ≠ 1 →
        P ∈ commSpace (ρ.comp Ψ g)) :
    finrank (ZMod 2) (commSpaceOf ρ (Ψ.range ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers b)) ≤
      8 := by
  subst hk
  obtain ⟨-, hA'⟩ := hA.comp_sl (by omega) h.map_mem
  have hei : (Pi.single i 1 : Fin 4 → ZMod 2) ≠ 0 := Pi.single_ne_zero_iff.mpr one_ne_zero
  by_cases hc : (∃ P : V, P ≠ 0 ∧ ∀ g ∈ pointGroup (Pi.single i 1), g ≠ 1 →
      P ∈ commSpace (ρ.comp Ψ g)) ∧ ∃ P : V, P ≠ 0 ∧ ∀ g ∈ hyperplaneGroup (Pi.single i 1),
        g ≠ 1 → P ∈ commSpace (ρ.comp Ψ g)
  · obtain ⟨P, Pd, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
      exists_pointMaps_of_concurrent hA' le_rfl hei hei hc.1 hc.2
    have hP : IsPointMaps (ρ.comp Ψ) Q P Pd := ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    have heq : commSpaceOf ρ (Ψ.range ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers b) =
        LinearMap.range P ⊔ LinearMap.range Pd := by
      rw [commSpaceOf_sup_zpowers, commSpaceOf_sup_zpowers, commSpaceOf_range, hP.commSpaceOf_top]
      exact le_antisymm (sup_le (sup_le le_rfl (h.commSpace_left_le_sup hA rfl hP))
        (h.commSpace_right_le_sup hA rfl hP)) (le_sup_left.trans le_sup_left)
    rw [heq, finrank_range_sup_range_eq h1 h2 h6]
  · have hnA := fun hcA => hc ⟨hcA, hAB hcA⟩
    have hnB := fun hcB => hc ⟨hBA hcB, hcB⟩
    have h1 := (hA'.common_point_or_finrank_le_three (A := pointGroup (Pi.single i 1))
      forall_mem_pointGroup_mem_transvectionSet).resolve_left hnA
    have h2 := (hA'.common_point_or_finrank_le_three (A := hyperplaneGroup (Pi.single i 1))
      forall_mem_hyperplaneGroup_mem_transvectionSet).resolve_left hnB
    have h3 := finrank_commSpaceOf_top_le_add (ρ := ρ.comp Ψ) i
    have h21 : (2 : Fin 4) ≠ 1 := by decide
    have ha := hA.finrank_commSpaceOf_sup_zpowers_le_of_collinear (H := Ψ.range) h.mem_left
      (h.map_mem _ (elemTv_mem_transvectionSet h21)) ⟨_, rfl⟩ (h.mul_mem_left 2 1 rfl rfl)
    have hb := hA.finrank_commSpaceOf_sup_zpowers_le_of_collinear
      (H := Ψ.range ⊔ Subgroup.zpowers a) h.mem_right
      (h.map_mem _ (elemTv_mem_transvectionSet h21.symm)) (Subgroup.mem_sup_left ⟨_, rfl⟩)
      (h.mul_mem_right 1 2 rfl rfl)
    rw [commSpaceOf_range] at ha
    omega

theorem finrank_commSpaceOf_le_eight_of_three (hA : A2Action D Q ρ) (h : IsLeviNode D Ψ a b)
    (hk : k = 3) :
    finrank (ZMod 2) (commSpaceOf ρ (Ψ.range ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers b)) ≤
      8 := by
  subst hk
  obtain ⟨-, hA'⟩ := hA.comp_sl le_rfl h.map_mem
  have h0 := finrank_commSpaceOf_top_le hA'
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have ha := hA.finrank_commSpaceOf_sup_zpowers_le_of_collinear (H := Ψ.range) h.mem_left
    (h.map_mem _ (elemTv_mem_transvectionSet h10)) ⟨_, rfl⟩ (h.mul_mem_left 1 0 rfl rfl)
  have hb := hA.finrank_commSpaceOf_sup_zpowers_le_of_collinear
    (H := Ψ.range ⊔ Subgroup.zpowers a) h.mem_right
    (h.map_mem _ (elemTv_mem_transvectionSet h10.symm)) (Subgroup.mem_sup_left ⟨_, rfl⟩)
    (h.mul_mem_right 0 1 rfl rfl)
  rw [commSpaceOf_range] at ha
  have : max 3 3 = 3 := rfl
  omega

end Bounds

end CFSG.LargeExtraspecial.A2Mod.FrC
