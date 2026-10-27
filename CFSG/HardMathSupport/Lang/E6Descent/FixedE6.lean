module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotUniqueFieldTorus
public import CFSG.RankThree.PartOne.CTP.SeitzField
public import CFSG.RankThree.PartOne.CTP.StrongPClassification

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Lang.E6Descent

open Subgroup CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.SeitzReduction.E6Pilot CFSG.RankThree.PartOne.CTP

section Cube

theorem cube_of_pow_eq {G : Type*} [CommGroup G] {b n : G} {p : ℕ} (hcop : Nat.Coprime p 3)
    (h : n ^ 3 = b ^ p) : ∃ y : G, b = y ^ 3 := by
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * p + v * 3 = 1 := by
    have := Nat.isCoprime_iff_coprime.2 hcop
    obtain ⟨u, v, h⟩ := this
    exact ⟨u, v, h⟩
  refine ⟨n ^ u * b ^ v, ?_⟩
  have e1 : b ^ (u * (p : ℤ)) = (n ^ u) ^ 3 := by
    calc b ^ (u * (p : ℤ)) = (b ^ p) ^ u := by rw [mul_comm, zpow_mul, zpow_natCast]
      _ = (n ^ 3) ^ u := by rw [h]
      _ = (n ^ u) ^ 3 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
  have e2 : b ^ (v * (3 : ℤ)) = (b ^ v) ^ 3 := by
    rw [zpow_mul, zpow_ofNat]
  calc b = b ^ (u * (p : ℤ) + v * 3) := by rw [huv, zpow_one]
    _ = (n ^ u * b ^ v) ^ 3 := by rw [zpow_add, e1, e2, mul_pow]

variable {K : Type} [Field K]

theorem exists_cube_of_pow_eq (σ : K ≃+* K) {p : ℕ} (hσp : σ ^ p = 1) (hcop : Nat.Coprime p 3)
    (b : (fixSubfield σ)ˣ) (d : Kˣ)
    (hbd : Units.map (fixSubfield σ).subtype.toMonoidHom b = d ^ 3) :
    ∃ y : (fixSubfield σ)ˣ, b = y ^ 3 := by
  classical
  have hσ1 : ∀ x : K, σ ((σ ^ p) x) = σ x := fun x => by rw [hσp]; rfl
  set f : ℕ → K := fun i => (σ ^ i) (d : K) with hf
  have hfsucc : ∀ i, σ (f i) = f (i + 1) := fun i => by
    simp only [hf, pow_succ']
    rfl
  have hfp : f p = f 0 := by simp only [hf, hσp, pow_zero]
  set n : K := ∏ i ∈ Finset.range p, f i with hn
  have hd0 : f 0 ≠ 0 := by simp only [hf, pow_zero]; exact d.ne_zero
  have hσn : σ n = n := by
    rw [hn, map_prod]
    simp only [hfsucc]
    have h1 := Finset.prod_range_succ' f p
    have h2 := Finset.prod_range_succ f p
    rw [hfp] at h2
    exact mul_right_cancel₀ hd0 (h1.symm.trans h2)
  have hb : ((b : fixSubfield σ) : K) = (d : K) ^ 3 := by
    have := congrArg Units.val hbd
    simpa using this
  have hσb : σ ((b : fixSubfield σ) : K) = (b : fixSubfield σ) :=
    (mem_fixSubfield σ).1 (b : fixSubfield σ).2
  have hn3 : n ^ 3 = ((b : fixSubfield σ) : K) ^ p := by
    rw [hn, ← Finset.prod_pow]
    have : ∀ i, f i ^ 3 = ((b : fixSubfield σ) : K) := by
      intro i
      induction i with
      | zero => simp only [hf, pow_zero]; exact hb.symm
      | succ i ih => rw [← hfsucc, ← map_pow, ih, hσb]
    simp [this]
  have hn0 : n ≠ 0 := by
    rw [hn]
    exact Finset.prod_ne_zero_iff.2 fun i _ => by
      simp only [hf]
      exact fun h => d.ne_zero ((map_eq_zero _).1 h)
  set n' : fixSubfield σ := ⟨n, (mem_fixSubfield σ).2 hσn⟩ with hn'
  have hn'0 : n' ≠ 0 := fun h => hn0 (congrArg Subtype.val h)
  have hn3' : (Units.mk0 n' hn'0) ^ 3 = b ^ p := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0]
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, SubmonoidClass.coe_pow]
    exact hn3
  exact cube_of_pow_eq hcop hn3'

end Cube

section Descent

open CFSG.Timmesfeld.ExceptionalOrders (smithE6 smithE6P smithE6P' smithE6Q smithE6Q' smithE6D
  smithE6P'_mul smithE6Q_mul)

variable {K : Type} [Field K]

theorem exists_monomial_eq_of_pow (σ : K ≃+* K) {p : ℕ} (hσp : σ ^ p = 1)
    (hcop : Nat.Coprime p 3)
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
  obtain ⟨y, hy⟩ := exists_cube_of_pow_eq σ hσp hcop (b nodeSixE6) _ h5
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


theorem entrywiseFixedTorus_le_fixedFieldImage_E6_of_pow (σ : K ≃+* K) {p : ℕ}
    (hσp : σ ^ p = 1) (hcop : Nat.Coprime p 3) :
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
  obtain ⟨s, hs⟩ := exists_monomial_eq_of_pow σ hσp hcop a' c ha'
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

end Torus

section Fixed

variable {K : Type} [Field K] [Finite K]


theorem entrywiseFixedGroup_eq_fixedFieldImage_E6_of_pow (σ : K ≃+* K) {p : ℕ}
    (hσp : σ ^ p = 1) (hcop : Nat.Coprime p 3) :
    entrywiseFixedGroup .E6 σ = fixedFieldImage .E6 σ := by
  obtain ⟨-, -, -, hJΓ, hΓ, -⟩ := Chevalley_coordinate_field_fixed_normal_subgroup .E6 K σ
  refine le_antisymm (fun g hg => ?_) hJΓ
  have hg' : g ∈ (entrywiseFixedGroup .E6 σ : Set (ModGL .E6 K)) := hg
  rw [hΓ] at hg'
  obtain ⟨h, hh, j, hj, rfl⟩ := Set.mem_mul.1 hg'
  exact mul_mem (entrywiseFixedTorus_le_fixedFieldImage_E6_of_pow σ hσp hcop hh) hj

theorem fixedSubgroup_entrywiseAdjointAut_E6 (σ : K ≃+* K) {p : ℕ}
    (hσp : σ ^ p = 1) (hcop : Nat.Coprime p 3) :
    fixedSubgroup (entrywiseAdjointAut .E6 σ) =
      (fixedFieldImage .E6 σ).subgroupOf (adjointGroup .E6 K) := by
  ext x
  rw [mem_fixedSubgroup, Subgroup.mem_subgroupOf,
    ← entrywiseFixedGroup_eq_fixedFieldImage_E6_of_pow σ hσp hcop, mem_entrywiseFixedGroup]
  constructor
  · intro h
    refine ⟨x.2, ?_⟩
    have := congrArg Subtype.val h
    rwa [coe_entrywiseAdjointAut] at this
  · rintro ⟨-, h⟩
    refine Subtype.ext ?_
    rw [coe_entrywiseAdjointAut]
    exact h

noncomputable def fixedE6Equiv (σ : K ≃+* K) {p : ℕ} (hσp : σ ^ p = 1)
    (hcop : Nat.Coprime p 3) :
    ↥(fixedSubgroup (entrywiseAdjointAut .E6 σ)) ≃* adjointGroup .E6 (fixSubfield σ) :=
  (MulEquiv.subgroupCongr (fixedSubgroup_entrywiseAdjointAut_E6 σ hσp hcop)).trans
    ((Subgroup.subgroupOfEquivOfLe (fun _ hj => (mem_entrywiseFixedGroup.1
      ((Chevalley_coordinate_field_fixed_normal_subgroup .E6 K σ).2.2.2.1 hj)).1)).trans
      (fixedFieldImageEquiv (τ := .E6) σ).symm)

theorem eq_one_of_central_fixed_E6 (σ : K ≃+* K) {p : ℕ} (hσp : σ ^ p = 1)
    (hcop : Nat.Coprime p 3) {x : adjointGroup .E6 K}
    (hx : x ∈ fixedSubgroup (entrywiseAdjointAut .E6 σ))
    (hc : ∀ y ∈ fixedSubgroup (entrywiseAdjointAut .E6 σ), x * y = y * x) : x = 1 := by
  have hz : fixedE6Equiv σ hσp hcop ⟨x, hx⟩ ∈
      Subgroup.center (adjointGroup .E6 (fixSubfield σ)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, hy⟩ : ∃ y : ↥(fixedSubgroup (entrywiseAdjointAut .E6 σ)),
        fixedE6Equiv σ hσp hcop y = g := ⟨(fixedE6Equiv σ hσp hcop).symm g, by simp⟩
    rw [← hy, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc y y.2).symm
  rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hz
  have h1 : (⟨x, hx⟩ : ↥(fixedSubgroup (entrywiseAdjointAut .E6 σ))) = 1 :=
    (fixedE6Equiv σ hσp hcop).injective (by rw [hz, map_one])
  exact congrArg Subtype.val h1

end Fixed

end CFSG.HardMathSupport.Lang.E6Descent
