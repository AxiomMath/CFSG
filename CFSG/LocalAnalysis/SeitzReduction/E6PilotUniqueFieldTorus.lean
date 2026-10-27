module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotUniqueFieldFix

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

section Monomial

variable {G H : Type*} [CommGroup G] [CommGroup H] {r : ℕ}

theorem monomialHom_mul (M N : Matrix (Fin r) (Fin r) ℤ) (t : Fin r → G) :
    monomialHom M (monomialHom N t) = monomialHom (M * N) t := by
  funext i
  simp only [monomialHom_apply, Matrix.mul_apply]
  calc ∏ j, (∏ k, t k ^ N j k) ^ M i j = ∏ j, ∏ k, t k ^ (M i j * N j k) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [← Finset.prod_zpow]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [← zpow_mul, mul_comm]
    _ = ∏ k, ∏ j, t k ^ (M i j * N j k) := Finset.prod_comm
    _ = ∏ k, t k ^ ∑ j, M i j * N j k := by
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [zpow_finsetSum]

theorem monomialHom_one (t : Fin r → G) : monomialHom (1 : Matrix (Fin r) (Fin r) ℤ) t = t := by
  funext i
  simp only [monomialHom_apply, Matrix.one_apply]
  rw [Finset.prod_eq_single i
    (fun j _ hj => by rw [ite_eq_right_iff.2 (fun h => absurd h (Ne.symm hj)), zpow_zero])
    (fun h => absurd (Finset.mem_univ i) h), ite_eq_left_iff.2 (fun h => absurd rfl h), zpow_one]

theorem monomialHom_diagonal (d : Fin r → ℤ) (t : Fin r → G) (i : Fin r) :
    monomialHom (Matrix.diagonal d) t i = t i ^ d i := by
  simp only [monomialHom_apply, Matrix.diagonal_apply]
  rw [Finset.prod_eq_single i
    (fun j _ hj => by rw [ite_eq_right_iff.2 (fun h => absurd h (Ne.symm hj)), zpow_zero])
    (fun h => absurd (Finset.mem_univ i) h), ite_eq_left_iff.2 (fun h => absurd rfl h)]

theorem map_monomialHom (φ : G →* H) (M : Matrix (Fin r) (Fin r) ℤ) (t : Fin r → G) :
    (fun i => φ (monomialHom M t i)) = monomialHom M (fun i => φ (t i)) := by
  funext i
  simp only [monomialHom_apply, map_prod, map_zpow]

end Monomial

section Cube

variable {K : Type} [Field K]

theorem exists_cube_of_units_map_eq_cube (σ : K ≃+* K) (hσσ : ∀ c, σ (σ c) = c)
    (b : (fixSubfield σ)ˣ) (d : Kˣ)
    (hbd : Units.map (fixSubfield σ).subtype.toMonoidHom b = d ^ 3) :
    ∃ y : (fixSubfield σ)ˣ, b = y ^ 3 := by
  set n : K := (d : K) * σ d with hn
  have hσn : σ n = n := by rw [hn, map_mul, hσσ, mul_comm]
  have hσd : σ (d : K) ≠ 0 := fun h => d.ne_zero ((map_eq_zero σ).1 h)
  have hn0 : n ≠ 0 := mul_ne_zero d.ne_zero hσd
  have hb : ((b : fixSubfield σ) : K) = (d : K) ^ 3 := by
    have := congrArg Units.val hbd
    simpa using this
  have hσb : σ ((b : fixSubfield σ) : K) = (b : fixSubfield σ) :=
    (mem_fixSubfield σ).1 (b : fixSubfield σ).2
  have hb0 : ((b : fixSubfield σ) : K) ≠ 0 := by
    rw [hb]
    exact pow_ne_zero _ d.ne_zero
  have hn3 : n ^ 3 = ((b : fixSubfield σ) : K) ^ 2 := by
    calc n ^ 3 = (d : K) ^ 3 * σ ((d : K) ^ 3) := by rw [hn, mul_pow, map_pow]
      _ = ((b : fixSubfield σ) : K) * σ ((b : fixSubfield σ) : K) := by rw [hb]
      _ = ((b : fixSubfield σ) : K) ^ 2 := by rw [hσb, sq]
  set n' : fixSubfield σ := ⟨n, (mem_fixSubfield σ).2 hσn⟩ with hn'
  have hn'0 : n' ≠ 0 := fun h => hn0 (congrArg Subtype.val h)
  have hn3' : n' ^ 3 = (b : fixSubfield σ) ^ 2 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, SubmonoidClass.coe_pow]
    exact hn3
  have hb0' : (b : fixSubfield σ) ≠ 0 := b.ne_zero
  refine ⟨b * (Units.mk0 n' hn'0)⁻¹, Units.ext ?_⟩
  simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
  rw [mul_pow, inv_pow, hn3']
  field_simp

end Cube

section Descent

open CFSG.Timmesfeld.ExceptionalOrders (smithE6 smithE6P smithE6P' smithE6Q smithE6Q' smithE6D
  smithE6P'_mul smithE6Q_mul)

variable {K : Type} [Field K]

theorem smithE6Q'_mul : smithE6Q' * smithE6Q = 1 := by decide

@[expose] def nodeSixE6 : Fin Tag.E6.rank := ⟨5, by decide⟩

theorem smithE6D_eq : ∀ i : Fin Tag.E6.rank, smithE6D i = if i = nodeSixE6 then 3 else 1 := by
  decide

theorem cartan_transpose_E6 : Tag.E6.cartan.transpose =
    smithE6Q.transpose * Matrix.diagonal (fun i => (smithE6D i : ℤ)) * smithE6P.transpose := by
  rw [smithE6, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.diagonal_transpose,
    Matrix.mul_assoc]

theorem exists_monomial_eq_of_units_map_eq_monomial_E6 (σ : K ≃+* K) (hσσ : ∀ c, σ (σ c) = c)
    (a : Fin Tag.E6.rank → (fixSubfield σ)ˣ) (c : Fin Tag.E6.rank → Kˣ)
    (hac : (fun i => Units.map (fixSubfield σ).subtype.toMonoidHom (a i)) =
      monomialHom Tag.E6.cartan.transpose c) :
    ∃ s : Fin Tag.E6.rank → (fixSubfield σ)ˣ, monomialHom Tag.E6.cartan.transpose s = a := by
  set ι : (fixSubfield σ)ˣ →* Kˣ := Units.map (fixSubfield σ).subtype.toMonoidHom with hι
  set Dm : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
    Matrix.diagonal (fun i => (smithE6D i : ℤ)) with hDm
  have hA := cartan_transpose_E6
  have hQQ : smithE6Q'.transpose * smithE6Q.transpose = 1 := by
    rw [← Matrix.transpose_mul, smithE6Q_mul, Matrix.transpose_one]
  have hQQ' : smithE6Q.transpose * smithE6Q'.transpose = 1 := by
    rw [← Matrix.transpose_mul, smithE6Q'_mul, Matrix.transpose_one]
  have hPP : smithE6P.transpose * smithE6P'.transpose = 1 := by
    rw [← Matrix.transpose_mul, smithE6P'_mul, Matrix.transpose_one]
  set b := monomialHom smithE6Q'.transpose a with hbdef
  have hb : (fun i => ι (b i)) = monomialHom Dm (monomialHom smithE6P.transpose c) := by
    rw [hbdef, map_monomialHom ι, hac, monomialHom_mul, hA, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, hQQ, Matrix.one_mul, ← monomialHom_mul]
  have h5 : ι (b nodeSixE6) = (monomialHom smithE6P.transpose c nodeSixE6) ^ 3 := by
    rw [show ι (b nodeSixE6) = monomialHom Dm (monomialHom smithE6P.transpose c) nodeSixE6 from
      congrFun hb nodeSixE6, hDm, monomialHom_diagonal, smithE6D_eq]
    simp
  obtain ⟨y, hy⟩ := exists_cube_of_units_map_eq_cube σ hσσ (b nodeSixE6) _ h5
  set b' := Function.update b nodeSixE6 y with hb'def
  have hb' : monomialHom Dm b' = b := by
    funext i
    rw [hDm, monomialHom_diagonal, smithE6D_eq]
    by_cases hi : i = nodeSixE6
    · subst hi
      simp [hb'def, hy]
    · simp [hb'def, hi]
  refine ⟨monomialHom smithE6P'.transpose b', ?_⟩
  rw [monomialHom_mul, hA, Matrix.mul_assoc, hPP, Matrix.mul_one, ← monomialHom_mul, hb', hbdef,
    monomialHom_mul, hQQ', monomialHom_one]

end Descent

section Torus

variable {K : Type} [Field K]

theorem torusGroup_le_range_rootDiagUnit_monomial
    (τ : Tag) :
    torusGroup τ K ≤ ((rootDiagUnitHom τ K).comp (monomialHom τ.cartan.transpose)).range := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨⟨i, u⟩, rfl⟩
  refine ⟨Pi.mulSingle i u, ?_⟩
  change rootDiagUnit τ _ = torusElt τ K i u
  rw [torusElt_eq_rootDiagUnit]
  congr 1
  funext l
  rw [monomialHom_apply, Finset.prod_eq_single i
    (fun j _ hj => by rw [Pi.mulSingle_eq_of_ne hj, one_zpow])
    (fun h => absurd (Finset.mem_univ i) h), Pi.mulSingle_eq_same, Matrix.transpose_apply]

theorem entrywiseFixedTorus_le_fixedFieldImage_E6
    (σ : K ≃+* K)
    (hσσ : ∀ c, σ (σ c) = c) :
    entrywiseFixedTorus .E6 σ ≤ fixedFieldImage .E6 σ := by
  set k := fixSubfield σ with hk
  set ι : k →+* K := k.subtype with hι
  rintro h ⟨hT, hΓ⟩
  obtain ⟨c, rfl⟩ := torusGroup_le_range_rootDiagUnit_monomial (K := K) Tag.E6 hT
  set a := monomialHom Tag.E6.cartan.transpose c with ha
  have hh : ((rootDiagUnitHom Tag.E6 K).comp (monomialHom Tag.E6.cartan.transpose)) c =
      rootDiagUnit Tag.E6 a := rfl
  rw [hh] at hΓ ⊢
  have hσa : ∀ i, σ (a i : K) = a i := by
    have hF : Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit Tag.E6 a) =
        rootDiagUnit Tag.E6 a := hΓ.2
    have h0 : Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit Tag.E6 a) =
        rootDiagUnit Tag.E6 (fun i => Units.map σ.toRingHom.toMonoidHom (a i)) :=
      Units.ext (entrywise_rootDiag σ.toRingHom a)
    have h1 := rootDiagUnit_injective (h0.symm.trans hF)
    intro i
    exact congrArg Units.val (congrFun h1 i)
  set a' : Fin Tag.E6.rank → kˣ := fun i =>
    Units.mk0 ⟨a i, hσa i⟩ fun h0 => (a i).ne_zero (congrArg Subtype.val h0) with ha'def
  have ha' : (fun i => Units.map ι.toMonoidHom (a' i)) = a := funext fun i => Units.ext rfl
  obtain ⟨s, hs⟩ := exists_monomial_eq_of_units_map_eq_monomial_E6 σ hσσ a' c ha'
  rw [← ha', ← hs]
  have hprod : rootDiagUnit Tag.E6
      (fun i => Units.map ι.toMonoidHom (monomialHom Tag.E6.cartan.transpose s i)) =
      ((List.finRange Tag.E6.rank).map fun j =>
        torusElt Tag.E6 K j (Units.map ι.toMonoidHom (s j))).prod := by
    rw [list_prod_torusElt_eq_rootDiagUnit]
    congr 1
    funext l
    rw [monomialHom_apply, cartanChar, map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_zpow, Matrix.transpose_apply]
  rw [hprod]
  have hmem : ((List.finRange Tag.E6.rank).map fun j => torusElt Tag.E6 k j (s j)).prod ∈
      adjointGroup Tag.E6 k := Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hg
    exact torusElt_mem_adjointGroup j _
  refine ⟨_, hmem, ?_⟩
  rw [map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun j _ => baseChangeGL_torusElt ι j (s j)

theorem entrywiseFixedGroup_eq_fixedFieldImage_E6 [Finite K] (σ : K ≃+* K)
    (hσσ : ∀ c, σ (σ c) = c) : entrywiseFixedGroup .E6 σ = fixedFieldImage .E6 σ := by
  obtain ⟨-, -, -, hJΓ, hΓ, -⟩ := Chevalley_coordinate_field_fixed_normal_subgroup .E6 K σ
  refine le_antisymm (fun g hg => ?_) hJΓ
  have hg' : g ∈ (entrywiseFixedGroup .E6 σ : Set (ModGL .E6 K)) := hg
  rw [hΓ] at hg'
  obtain ⟨h, hh, j, hj, rfl⟩ := Set.mem_mul.1 hg'
  exact mul_mem (entrywiseFixedTorus_le_fixedFieldImage_E6 σ hσσ hh) hj

theorem fixSubgroup_entrywiseAdjointAut_eq_E6 [Finite K] (σ : K ≃+* K)
    (hσσ : ∀ c, σ (σ c) = c) :
    fixSubgroup (entrywiseAdjointAut .E6 σ) =
      (fixedFieldImage .E6 σ).subgroupOf (adjointGroup .E6 K) := by
  rw [← entrywiseFixedGroup_eq_fixedFieldImage_E6 σ hσσ]
  ext g
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro h
    exact ⟨g.2, congrArg Subtype.val h⟩
  · intro h
    exact Subtype.ext h.2

theorem card_fixSubgroup_entrywiseAdjointAut_E6 {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ (2 * f)) (σ : K ≃+* K) (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1) :
    Nat.card (fixSubgroup (entrywiseAdjointAut .E6 σ)) = ordE6 (2 ^ f) := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  obtain ⟨-, hk⟩ := field_involution_facts_E6 hf hK σ hσ2 hσ1
  have := F4Pilot.finite_of_natCard_eq_two_pow hk
  have hσσ : ∀ c, σ (σ c) = c := fun c => by
    have h := congrArg (fun φ : K ≃+* K => φ c) hσ2
    simpa [sq] using h
  have hJC : fixedFieldImage .E6 σ ≤ adjointGroup .E6 K :=
    (fixedFieldImage_le (τ := .E6) (σ := σ)).trans inf_le_left
  rw [fixSubgroup_entrywiseAdjointAut_eq_E6 σ hσσ, card_subgroupOf_of_le hJC,
    ← Nat.card_congr (fixedFieldImageEquiv σ).toEquiv,
    CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6, hk]

end Torus

end CFSG.SeitzReduction.E6Pilot
