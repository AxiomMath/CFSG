module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BenderGroupFactsLinear
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Comparator.Defs

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open scoped Pointwise

structure LinearSylowData {X : Type*} [Group X] (J R D : Subgroup X) (q : ℕ) : Prop where
  le : R ≤ J
  torus_le : D ≤ J
  sq : ∀ x ∈ R, x * x = 1
  comm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x
  card : Nat.card R = q
  torus_conj : ∀ d ∈ D, ∀ x ∈ R, d * x * d⁻¹ ∈ R
  normalizer : ∀ g ∈ J, (∀ x ∈ R, g * x * g⁻¹ ∈ R) → ∃ c ∈ R, ∃ d ∈ D, g = c * d
  regular : ∀ x ∈ R, x ≠ 1 → ∀ y ∈ R, y ≠ 1 → ∃! d, d ∈ D ∧ d * x * d⁻¹ = y
  torus_cyclic : IsCyclic D
  torus_card : Nat.card D = q - 1
  inner : ∀ g : X, (∀ y ∈ J, g * y * g⁻¹ ∈ J) → (∀ x ∈ R, g * x = x * g) →
    ∃ j ∈ R, ∀ y ∈ J, g * y * g⁻¹ = j * y * j⁻¹

section Transport

variable {X : Type*} [Group X] [Finite X] {J : Subgroup X} {n : ℕ}

omit [Finite X] in
theorem mem_map_subtype_iff_exists_mem {T : Subgroup J} {x : X} :
    x ∈ T.map J.subtype ↔ ∃ h : x ∈ J, (⟨x, h⟩ : J) ∈ T := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem linearSylowData_of_mulEquiv (hn : 2 ≤ n) (e : J ≃* CFSG.Theory.Comparator.PSL2Model n)
    (T : Sylow 2 J) :
    ∃ D : Subgroup X, LinearSylowData J ((T : Subgroup J).map J.subtype) D (2 ^ n) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have : Finite (GaloisField 2 n) := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  let L := CFSG.Theory.Comparator.PSL2Model n
  have : Finite L := Finite.of_equiv _ e.toEquiv
  have hsurj : Function.Surjective (e.toMonoidHom : J →* L) := e.surjective
  set U : Sylow 2 L := T.mapSurjective hsurj with hUdef
  have hU : (U : Subgroup L) = (T : Subgroup J).map e.toMonoidHom := Sylow.coe_mapSurjective _ _
  have hTU : ∀ y : J, y ∈ (T : Subgroup J) ↔ e y ∈ (U : Subgroup L) := by
    intro y
    rw [hU, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  obtain ⟨hUel, hUcard⟩ := CFSG.Walter.psl2_even_sylow_two hn U
  obtain ⟨D', hD'cyc, hD'card, -, hsup, hreg⟩ := CFSG.Walter.psl2_even_normalizer_sylow_two hn U
  have hD'N : D' ≤ Subgroup.normalizer ((U : Subgroup L) : Set L) := hsup ▸ le_sup_right
  set R := (T : Subgroup J).map J.subtype with hR
  set D := (D'.map e.symm.toMonoidHom).map J.subtype with hD
  have hmemR : ∀ x : X, x ∈ R ↔ ∃ h : x ∈ J, e ⟨x, h⟩ ∈ (U : Subgroup L) := by
    intro x
    rw [hR, mem_map_subtype_iff_exists_mem]
    simp only [hTU]
  have hmemD : ∀ x : X, x ∈ D ↔ ∃ h : x ∈ J, e ⟨x, h⟩ ∈ D' := by
    intro x
    rw [hD, mem_map_subtype_iff_exists_mem]
    simp only [Subgroup.mem_map_equiv, MulEquiv.symm_symm]
  have hUsq : ∀ u ∈ (U : Subgroup L), u * u = 1 := fun u hu => by
    rw [← pow_two]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := (U : Subgroup L)) u hu
  have hUcomm : ∀ u ∈ (U : Subgroup L), ∀ v ∈ (U : Subgroup L), u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hUel.toIsMulCommutative.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  refine ⟨D, ⟨Subgroup.map_subtype_le _, Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩⟩
  ·
    intro x hx
    obtain ⟨hxJ, hxU⟩ := (hmemR x).mp hx
    have h := hUsq _ hxU
    rw [← map_mul, ← map_one e] at h
    exact congrArg Subtype.val (e.injective h)
  ·
    intro x hx y hy
    obtain ⟨hxJ, hxU⟩ := (hmemR x).mp hx
    obtain ⟨hyJ, hyU⟩ := (hmemR y).mp hy
    have h := hUcomm _ hxU _ hyU
    rw [← map_mul, ← map_mul] at h
    exact congrArg Subtype.val (e.injective h)
  ·
    rw [hR, Subgroup.card_map_of_injective J.subtype_injective, ← hUcard, hU,
      Subgroup.card_map_of_injective e.injective]
  ·
    intro d hd x hx
    obtain ⟨hdJ, hdD⟩ := (hmemD d).mp hd
    obtain ⟨hxJ, hxU⟩ := (hmemR x).mp hx
    refine (hmemR _).mpr ⟨J.mul_mem (J.mul_mem hdJ hxJ) (J.inv_mem hdJ), ?_⟩
    have h := (Subgroup.mem_normalizer_iff.mp (hD'N hdD) _).mp hxU
    have heq : (⟨d * x * d⁻¹, J.mul_mem (J.mul_mem hdJ hxJ) (J.inv_mem hdJ)⟩ : J) =
        ⟨d, hdJ⟩ * ⟨x, hxJ⟩ * (⟨d, hdJ⟩ : J)⁻¹ := rfl
    rw [heq, map_mul, map_mul, map_inv]
    exact h
  ·
    intro g hgJ hgR
    have hgU : e ⟨g, hgJ⟩ ∈ Subgroup.normalizer ((U : Subgroup L) : Set L) := by
      refine Subgroup.mem_normalizer_fintype fun u hu => ?_
      obtain ⟨y, rfl⟩ := e.surjective u
      have hyR : (y : X) ∈ R := (hmemR y).mpr ⟨y.2, hu⟩
      obtain ⟨hgyJ, h⟩ := (hmemR _).mp (hgR _ hyR)
      have heq : (⟨g * y * g⁻¹, J.mul_mem (J.mul_mem hgJ y.2) (J.inv_mem hgJ)⟩ : J) =
          ⟨g, hgJ⟩ * y * (⟨g, hgJ⟩ : J)⁻¹ := rfl
      rw [heq, map_mul, map_mul, map_inv] at h
      exact h
    rw [← hsup] at hgU
    have hmul : ((↑((U : Subgroup L) ⊔ D') : Set L)) = (U : Set L) * (D' : Set L) :=
      Subgroup.coe_mul_of_right_le_normalizer_left _ _ hD'N
    have hgU' : e ⟨g, hgJ⟩ ∈ ((U : Set L) * (D' : Set L)) := hmul ▸ hgU
    obtain ⟨u, hu, d', hd', hud⟩ := Set.mem_mul.mp hgU'
    refine ⟨(e.symm u : X), (hmemR _).mpr ⟨(e.symm u).2, ?_⟩,
      (e.symm d' : X), (hmemD _).mpr ⟨(e.symm d').2, ?_⟩, ?_⟩
    · show e (e.symm u) ∈ (U : Subgroup L)
      rw [MulEquiv.apply_symm_apply]
      exact hu
    · show e (e.symm d') ∈ D'
      rw [MulEquiv.apply_symm_apply]
      exact hd'
    have h : (⟨g, hgJ⟩ : J) = e.symm u * e.symm d' := by
      rw [← map_mul, hud, MulEquiv.symm_apply_apply]
    exact congrArg Subtype.val h
  ·
    intro x hx hx1 y hy hy1
    obtain ⟨hxJ, hxU⟩ := (hmemR x).mp hx
    obtain ⟨hyJ, hyU⟩ := (hmemR y).mp hy
    have hex1 : e ⟨x, hxJ⟩ ≠ 1 := fun h =>
      hx1 (congrArg Subtype.val ((map_eq_one_iff e e.injective).mp h))
    have hey1 : e ⟨y, hyJ⟩ ≠ 1 := fun h =>
      hy1 (congrArg Subtype.val ((map_eq_one_iff e e.injective).mp h))
    obtain ⟨δ, hδ, huniq⟩ := hreg _ hxU hex1 _ hyU hey1
    have hconj : ∀ d (hdJ : d ∈ J), e ⟨d, hdJ⟩ * e ⟨x, hxJ⟩ * (e ⟨d, hdJ⟩)⁻¹ = e ⟨y, hyJ⟩ →
        d * x * d⁻¹ = y := by
      intro d hdJ h
      rw [← map_inv, ← map_mul, ← map_mul] at h
      exact congrArg Subtype.val (e.injective h)
    refine ⟨(e.symm δ : X), ⟨(hmemD _).mpr ⟨(e.symm δ).2, by simp⟩, hconj _ (e.symm δ).2 ?_⟩, ?_⟩
    · simpa using hδ
    · rintro d ⟨hd, hdxy⟩
      obtain ⟨hdJ, hdD⟩ := (hmemD d).mp hd
      have h := huniq ⟨_, hdD⟩ (by
        change e ⟨d, hdJ⟩ * e ⟨x, hxJ⟩ * (e ⟨d, hdJ⟩)⁻¹ = e ⟨y, hyJ⟩
        rw [← map_inv, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext hdxy)
      have h' : e ⟨d, hdJ⟩ = (δ : L) := congrArg Subtype.val h
      have h'' : (⟨d, hdJ⟩ : J) = e.symm δ := by rw [← h', MulEquiv.symm_apply_apply]
      exact congrArg Subtype.val h''
  ·
    have e₁ := (D'.equivMapOfInjective e.symm.toMonoidHom e.symm.injective)
    have e₂ := ((D'.map e.symm.toMonoidHom).equivMapOfInjective J.subtype J.subtype_injective)
    exact isCyclic_of_surjective (e₁.trans e₂) (e₁.trans e₂).surjective
  ·
    rw [hD, Subgroup.card_map_of_injective J.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective, hD'card]
  ·
    intro g hgJ hgR
    have hgN : g ∈ Subgroup.normalizer ((J : Subgroup X) : Set X) :=
      Subgroup.mem_normalizer_fintype fun y hy => hgJ y hy
    set α := J.normalizerMonoidHom ⟨g, hgN⟩
    have hα : ∀ y : J, ((α y : J) : X) = g * y * g⁻¹ := fun y => rfl
    have hfix : ∀ r ∈ (T : Subgroup J), α r = r := by
      intro r hr
      apply Subtype.ext
      rw [hα, hgR _ ((hmemR _).mpr ⟨r.2, (hTU r).mp hr⟩), mul_inv_cancel_right]
    obtain ⟨j, hjT, hj⟩ :=
      BenderFacts.exists_mem_eq_conj_of_fixes_sylow_of_mulEquiv_psl2 (K := GaloisField 2 n) hn hK
        e T α hfix
    refine ⟨(j : X), (hmemR _).mpr ⟨j.2, (hTU j).mp hjT⟩, fun y hy => ?_⟩
    have h := congrArg (fun φ : MulAut J => ((φ ⟨y, hy⟩ : J) : X)) hj
    simpa [hα] using h

end Transport

end CFSG.ProperTwoGeneratedCore.Lemma37
