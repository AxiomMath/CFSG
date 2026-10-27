module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4AmbientFixed
public import CFSG.HardMathSupport.Lang.D4Three.NormalForm
public import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex

public noncomputable section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.D4Three
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)


theorem baseChange_normalForm {K : Type} [Field K] (L : Type) [Field L] (ι : K →+* L)
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (T : K ≃+* K) (ε : ℕ)
    (u : adjointGroup Tag.D4 K) :
    baseChangeGL ι ((MulAut.conj g * (exactNormalAut Tag.D4 K a T 0 * d4Graph K ε)) u :
        ModGL Tag.D4 K) =
      baseChangeGL ι ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) *
        baseChangeGL ι (Subtype.val (twistedEntrywiseAut TwistTag.D4 (ε : ℤ) T u) : ModGL Tag.D4 K) *
          (baseChangeGL ι ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a))⁻¹ := by
  have hP : Units.map (entrywiseHom (τ := Tag.D4) T.toRingHom) (d4P K ^ ε) = d4P K ^ ε := by
    rw [map_pow]
    exact congrArg (· ^ ε) (units_map_entrywiseHom_diagramMap (t := TwistTag.D4) T.toRingHom)
  have h1 : (Subtype.val (twistedEntrywiseAut TwistTag.D4 (ε : ℤ) T u) : ModGL Tag.D4 K) =
      d4P K ^ ε * Units.map (entrywiseHom T.toRingHom) (u : ModGL Tag.D4 K) * (d4P K ^ ε)⁻¹ := by
    have h := coe_twistedEntrywiseAut TwistTag.D4 (ε : ℤ) T u
    rw [zpow_natCast] at h
    exact h
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, coe_exactNormalAut, exactQ_zero, coe_d4Graph, h1]
  simp only [map_mul, map_inv, hP, mul_one, inv_one]
  group

section Inverse

theorem units_map_entrywiseHom_cancel {t : TwistTag} {K : Type} [Field K] (T σ : K ≃+* K)
    (hTσ : ∀ c, T (σ c) = c) (w : ModGL t.tag K) :
    Units.map (entrywiseHom T.toRingHom) (Units.map (entrywiseHom σ.toRingHom) w) = w := by
  rw [units_map_entrywiseHom_comp]
  have h : T.toRingHom.comp σ.toRingHom = RingHom.id K := RingHom.ext hTσ
  rw [h]
  exact Units.ext (entrywise_id (R := K) _)

theorem baseChange_inv_twisted (t : TwistTag) {K L : Type} [Field K] [Field L] (ι : K →+* L)
    (Fr : L →+* L) (T σ : K ≃+* K) (hFrc : Fr.comp ι = ι.comp T.toRingHom)
    (hTσ : ∀ c, T (σ c) = c) (j : ℤ) (x : ModGL t.tag L) (β : MulAut (adjointGroup t.tag K))
    (hβ : ∀ u : adjointGroup t.tag K, baseChangeGL ι (β u : ModGL t.tag K) =
      x * baseChangeGL ι (twistedEntrywiseAut t j σ u : ModGL t.tag K) * x⁻¹)
    (u : adjointGroup t.tag K) :
    baseChangeGL ι ((β⁻¹ u : adjointGroup t.tag K) : ModGL t.tag K) =
      (diagramMap t L ^ (-j) * (Units.map (entrywiseHom Fr) x)⁻¹ * (diagramMap t L ^ (-j))⁻¹) *
        baseChangeGL ι (twistedEntrywiseAut t (-j) T u : ModGL t.tag K) *
        (diagramMap t L ^ (-j) * (Units.map (entrywiseHom Fr) x)⁻¹ *
          (diagramMap t L ^ (-j))⁻¹)⁻¹ := by
  have hFι : ∀ w : ModGL t.tag K, Units.map (entrywiseHom Fr) (baseChangeGL ι w) =
      baseChangeGL ι (Units.map (entrywiseHom T.toRingHom) w) := fun w => by
    rw [units_map_entrywiseHom_eq_baseChangeGL, units_map_entrywiseHom_eq_baseChangeGL,
      baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, hFrc]
  have hQ : ∀ k : ℤ, baseChangeGL ι (diagramMap t K ^ k) = diagramMap t L ^ k := fun k => by
    rw [map_zpow, baseChangeGL_diagramMap]
  set v : adjointGroup t.tag K := β⁻¹ u with hv
  have hβv : β v = u := MulAut.apply_inv_self _ _ u
  have h1 := hβ v
  rw [hβv] at h1
  have h2 := congrArg (Units.map (entrywiseHom Fr)) h1
  rw [map_mul, map_mul, map_inv, hFι, hFι] at h2
  have h3 : Units.map (entrywiseHom T.toRingHom)
      ((twistedEntrywiseAut t j σ v : adjointGroup t.tag K) : ModGL t.tag K) =
        diagramMap t K ^ j * (v : ModGL t.tag K) * (diagramMap t K ^ j)⁻¹ := by
    rw [coe_twistedEntrywiseAut, map_mul, map_mul, map_inv, units_map_entrywiseHom_cancel T σ hTσ,
      units_map_entrywiseHom_diagramMap_zpow]
  rw [h3, map_mul, map_mul, map_inv, hQ] at h2
  have h4 := coe_twistedEntrywiseAut t (-j) T u
  rw [h4, map_mul, map_mul, map_inv, hQ, h2]
  group

end Inverse

theorem exists_frobenius_eq_or_inv_of_orderOf_three {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) (σ : K ≃+* K) (hσ3 : orderOf σ = 3) :
    ∃ (e : ℕ) (T : K ≃+* K), 1 ≤ e ∧ e * 3 = f ∧ (∀ c, T c = c ^ (ℓ ^ e)) ∧
      (σ = T ∨ σ = T⁻¹) := by
  classical
  obtain ⟨fr, hfr, hord, hgen, hcardAut, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality hℓ hf hK
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  have h3f : 3 ∣ f := by
    rw [← hcardAut, ← hσ3]
    exact orderOf_dvd_natCard σ
  obtain ⟨d, hd⟩ := h3f
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hσmem : σ ∈ Subgroup.zpowers fr := by rw [hgen]; exact Subgroup.mem_top σ
  obtain ⟨k, hk, hkσ⟩ := Finset.mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1 hσmem)
  replace hkσ : fr ^ k = σ := hkσ
  rw [Finset.mem_range, hord] at hk
  have hdk : d ∣ k := by
    have h1 : f ∣ k * 3 := by
      rw [← hord]
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [pow_mul, hkσ, ← hσ3, pow_orderOf_eq_one]
    rw [hd, mul_comm k] at h1
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
  obtain ⟨j, rfl⟩ := hdk
  have hjp : j < 3 := by
    by_contra hjp
    have : d * 3 ≤ d * j := Nat.mul_le_mul_left d (not_lt.1 hjp)
    omega
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [mul_zero, pow_zero] at hkσ
    rw [← hkσ, orderOf_one] at hσ3
    omega
  set T := fr ^ d with hTdef
  have hT : ∀ c, T c = c ^ (ℓ ^ d) := ringAut_pow_apply_of_frobenius hfr d
  have hT3 : T ^ 3 = 1 := by
    rw [hTdef, ← pow_mul, show d * 3 = f by omega, ← hord, pow_orderOf_eq_one]
  have hTj : T ^ j = σ := by rw [hTdef, ← pow_mul, hkσ]
  refine ⟨d, T, hd0, by omega, hT, ?_⟩
  have hj : j = 1 ∨ j = 2 := by omega
  rcases hj with rfl | rfl
  · exact Or.inl (by rw [← hTj, pow_one])
  · refine Or.inr ?_
    rw [← hTj]
    exact (inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hT3)).symm

theorem exists_conj_eq_twistedEntrywiseAut_of_normalForm {ℓ f e : ℕ} [Fact ℓ.Prime]
    (K : Type) [Field K] [Finite K] [CharP K ℓ] (hK : Nat.card K = ℓ ^ f)
    (hK4 : 4 ≤ Nat.card K) (he : 1 ≤ e) (hef : e * 3 = f) (T : K ≃+* K)
    (hT : ∀ c, T c = c ^ (ℓ ^ e)) (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1)
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (ε : ℕ)
    (hα : α = MulAut.conj g * (exactNormalAut Tag.D4 K a T 0 * d4Graph K ε)) :
    ∃ ψ : MulAut (adjointGroup Tag.D4 K),
      ψ * α * ψ⁻¹ = twistedEntrywiseAut TwistTag.D4 (ε : ℤ) T := by
  classical
  set L := AlgebraicClosure K with hL
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  set x : ModGL Tag.D4 L :=
    baseChangeGL (algebraMap K L) ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) with hxdef
  have hx : x ∈ adjointGroup Tag.D4 L := by
    rw [hxdef, map_mul, baseChangeGL_rootDiagUnit]
    exact mul_mem (baseChangeGL_mem_adjointGroup _ g.2)
      (exceptional_Lang_adjoint_diagonal_lift Tag.D4 L _).1
  have hβ : ∀ u : adjointGroup Tag.D4 K, baseChangeGL (algebraMap K L) (α u : ModGL Tag.D4 K) =
      x * baseChangeGL (algebraMap K L)
        (Subtype.val (twistedEntrywiseAut TwistTag.D4 (ε : ℤ) T u) : ModGL Tag.D4 K) * x⁻¹ := by
    intro u
    rw [hα, hxdef]
    exact baseChange_normalForm L (algebraMap K L) g a T ε u
  exact exists_conj_eq_twistedEntrywiseAut TwistTag.D4 K hK hK4 he hef T hT (ε : ℤ) L x hx α hβ
    hα3

theorem twentySeven_dvd_card_fixedSubgroup_of_normalForm {ℓ f e : ℕ} [Fact ℓ.Prime]
    (K : Type) [Field K] [Finite K] [CharP K ℓ] (hK : Nat.card K = ℓ ^ f)
    (hK4 : 4 ≤ Nat.card K) (he : 1 ≤ e) (hef : e * 3 = f) (h3 : ¬ 3 ∣ ℓ ^ e) (T : K ≃+* K)
    (hT : ∀ c, T c = c ^ (ℓ ^ e)) (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1)
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (ε : ℕ) (hε : ε = 1 ∨ ε = 2)
    (hα : α = MulAut.conj g * (exactNormalAut Tag.D4 K a T 0 * d4Graph K ε)) :
    27 ∣ Nat.card (fixedSubgroup α) := by
  obtain ⟨ψ, hψ⟩ := exists_conj_eq_twistedEntrywiseAut_of_normalForm K hK hK4 he hef T hT α hα3
    g a ε hα
  have hK' : Nat.card K = (ℓ ^ e) ^ 3 := by rw [hK, ← hef, pow_mul]
  rw [← card_fixedSubgroup_of_conj_eq_mul hψ]
  exact twentySeven_dvd_card_fixedSubgroup_twistedEntrywiseAut_D4 (Fact.out : ℓ.Prime) he h3 K hK'
    T hT (ε : ℤ) (by rcases hε with rfl | rfl <;> simp)

theorem exists_conj_inv_eq_twistedEntrywiseAut_of_normalForm {ℓ f e : ℕ} [Fact ℓ.Prime]
    (K : Type) [Field K] [Finite K] [CharP K ℓ] (hK : Nat.card K = ℓ ^ f)
    (hK4 : 4 ≤ Nat.card K) (he : 1 ≤ e) (hef : e * 3 = f) (T σ : K ≃+* K)
    (hT : ∀ c, T c = c ^ (ℓ ^ e)) (hTσ : T * σ = 1) (α : MulAut (adjointGroup Tag.D4 K))
    (hα3 : α ^ 3 = 1) (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (ε : ℕ)
    (hα : α = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) :
    ∃ ψ : MulAut (adjointGroup Tag.D4 K),
      ψ * α⁻¹ * ψ⁻¹ = twistedEntrywiseAut TwistTag.D4 (-(ε : ℤ)) T := by
  classical
  set L := AlgebraicClosure K with hL
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set x : ModGL Tag.D4 L :=
    baseChangeGL (algebraMap K L) ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) with hxdef
  have hx : x ∈ adjointGroup Tag.D4 L := by
    rw [hxdef, map_mul, baseChangeGL_rootDiagUnit]
    exact mul_mem (baseChangeGL_mem_adjointGroup _ g.2)
      (exceptional_Lang_adjoint_diagonal_lift Tag.D4 L _).1
  have hFrc : (iterateFrobenius L ℓ e).comp (algebraMap K L) =
      (algebraMap K L).comp T.toRingHom := by
    ext c
    simp [iterateFrobenius_def, hT, map_pow]
  have hTσ' : ∀ c, T (σ c) = c := fun c => by
    have := congrArg (fun φ : K ≃+* K => φ c) hTσ
    simpa using this
  have hβ : ∀ u : adjointGroup Tag.D4 K, baseChangeGL (algebraMap K L) (α u : ModGL Tag.D4 K) =
      x * baseChangeGL (algebraMap K L)
        (Subtype.val (twistedEntrywiseAut TwistTag.D4 (ε : ℤ) σ u) : ModGL Tag.D4 K) * x⁻¹ := by
    intro u
    rw [hα, hxdef]
    exact baseChange_normalForm L (algebraMap K L) g a σ ε u
  set y : ModGL TwistTag.D4.tag L := diagramMap TwistTag.D4 L ^ (-(ε : ℤ)) *
    (Units.map (entrywiseHom (τ := TwistTag.D4.tag) (iterateFrobenius L ℓ e))
      (x : ModGL TwistTag.D4.tag L))⁻¹ * (diagramMap TwistTag.D4 L ^ (-(ε : ℤ)))⁻¹ with hydef
  have hy : y ∈ adjointGroup TwistTag.D4.tag L :=
    conj_mem_adjointGroup_of_map_eq (map_conj_diagramMap_zpow TwistTag.D4 L (-(ε : ℤ))) _
      (inv_mem (entrywiseFrobGL_mem ℓ e hx))
  have hβ' : ∀ u : adjointGroup Tag.D4 K,
      baseChangeGL (algebraMap K L) ((α⁻¹ u : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) =
        y * baseChangeGL (algebraMap K L)
          (Subtype.val (twistedEntrywiseAut TwistTag.D4 (-(ε : ℤ)) T u) :
            ModGL TwistTag.D4.tag K) * y⁻¹ :=
    fun u => baseChange_inv_twisted TwistTag.D4 (algebraMap K L) (iterateFrobenius L ℓ e) T σ hFrc
      hTσ' (ε : ℤ) x α hβ u
  have hα3' : α⁻¹ ^ TwistTag.D4.order = 1 := by
    change α⁻¹ ^ 3 = 1
    rw [inv_pow, hα3, inv_one]
  exact exists_conj_eq_twistedEntrywiseAut TwistTag.D4 K hK hK4 he hef T hT (-(ε : ℤ)) L y hy
    α⁻¹ hβ' hα3'

theorem twentySeven_dvd_card_fixedSubgroup_of_normalForm_orient {ℓ f e : ℕ} [Fact ℓ.Prime]
    (K : Type) [Field K] [Finite K] [CharP K ℓ] (hK : Nat.card K = ℓ ^ f)
    (hK4 : 4 ≤ Nat.card K) (he : 1 ≤ e) (hef : e * 3 = f) (h3 : ¬ 3 ∣ ℓ ^ e) (T σ : K ≃+* K)
    (hT : ∀ c, T c = c ^ (ℓ ^ e)) (hσ : σ = T ∨ σ = T⁻¹) (α : MulAut (adjointGroup Tag.D4 K))
    (hα3 : α ^ 3 = 1) (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (ε : ℕ)
    (hε : ε = 1 ∨ ε = 2)
    (hα : α = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) :
    27 ∣ Nat.card (fixedSubgroup α) := by
  rcases hσ with rfl | rfl
  · exact twentySeven_dvd_card_fixedSubgroup_of_normalForm K hK hK4 he hef h3 σ hT α hα3 g a ε hε hα
  · obtain ⟨ψ, hψ⟩ := exists_conj_inv_eq_twistedEntrywiseAut_of_normalForm K hK hK4 he hef T T⁻¹
      hT (mul_inv_cancel T) α hα3 g a ε hα
    have hK' : Nat.card K = (ℓ ^ e) ^ 3 := by rw [hK, ← hef, pow_mul]
    have hshift : twistedEntrywiseAut TwistTag.D4 (-(ε : ℤ)) T =
        twistedEntrywiseAut TwistTag.D4 (3 - (ε : ℤ)) T := by
      have h := twistedEntrywiseAut_add_mul_order TwistTag.D4 (-(ε : ℤ)) 1 T
      rw [show -(ε : ℤ) + 1 * ((TwistTag.D4.order : ℕ) : ℤ) = 3 - (ε : ℤ) by
        change -(ε : ℤ) + 1 * 3 = _
        ring] at h
      exact h.symm
    rw [hshift] at hψ
    rw [← fixedSubgroup_inv_eq, ← card_fixedSubgroup_of_conj_eq_mul hψ]
    exact twentySeven_dvd_card_fixedSubgroup_twistedEntrywiseAut_D4 (Fact.out : ℓ.Prime) he h3 K
      hK' T hT (3 - (ε : ℤ)) (by rcases hε with rfl | rfl <;> simp)

end CFSG.HardMathSupport.Lang.E6Descent
