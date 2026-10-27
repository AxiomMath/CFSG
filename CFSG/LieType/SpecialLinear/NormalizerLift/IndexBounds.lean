module

public import CFSG.LieType.SpecialLinear.NormalizerLift.FieldGraph
public import CFSG.LinearAlgebra.LinearGroups.SLConjugationKer
public import CFSG.GroupTheory.ABGDGroups.LinearStructure

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {H : Type*} [Group H]
  (π : SpecialLinearGroup (Fin n) F →* H)

omit [CharP F 2] in
theorem stdData_field_eq_one (hker : π.ker ≤ scalars n F) (hn : 3 ≤ n)
    {d : H} (hdN : d ∈ rangeNormalizer π)
    (h : fieldPart π hker hn ⟨d, hdN⟩ = 1) :
    (stdData π hker hn ⟨d, hdN⟩).2.1 = 1 := h

omit [CharP F 2] in
theorem stdData_eps_eq_zero (hker : π.ker ≤ scalars n F) (hn : 3 ≤ n)
    {d : H} (hdN : d ∈ rangeNormalizer π)
    (h : graphPart π hker hn ⟨d, hdN⟩ = 1) :
    (stdData π hker hn ⟨d, hdN⟩).2.2 = 0 := by
  have hε := stdData_eps_le_one π hker hn ⟨d, hdN⟩
  have hz : ((stdData π hker hn ⟨d, hdN⟩).2.2 : ZMod 2) = 0 := by
    have := congrArg Multiplicative.toAdd h
    simpa [graphPart] using this
  rcases (show (stdData π hker hn ⟨d, hdN⟩).2.2 = 0 ∨
      (stdData π hker hn ⟨d, hdN⟩).2.2 = 1 by omega) with h0 | h1
  · exact h0
  · rw [h1] at hz
    norm_num at hz

omit [CharP F 2] in
theorem stdData_sq_mem_center (hker : π.ker ≤ scalars n F) (hn : 3 ≤ n)
    {d : H} (hdN : d ∈ rangeNormalizer π) (hd2 : d * d = 1)
    (hσ : (stdData π hker hn ⟨d, hdN⟩).2.1 = 1)
    (hε : (stdData π hker hn ⟨d, hdN⟩).2.2 = 0) :
    let A : GL (Fin n) F := (stdData π hker hn ⟨d, hdN⟩).1
    A * A ∈ Subgroup.center (GL (Fin n) F) := by
  let hd : rangeNormalizer π := ⟨d, hdN⟩
  let A : GL (Fin n) F := (stdData π hker hn hd).1
  have hdd : hd * hd = 1 := by
    apply Subtype.ext
    simpa using hd2
  have hliftA : liftAut π hker hn hd = CatalogueBHigherLinearAction.slConjugation n F A := by
    rw [liftAut_eq_stdAut, hσ, hε]
    simp only [CFSG.QuasithinUnique.K1.stdAut, pow_zero, mul_one,
      CatalogueBHigherLinearField.slFieldAut, map_one, mul_one]
    rfl
  have h1 : liftAut π hker hn (hd * hd) = 1 := by rw [hdd, map_one]
  have h2 : liftAut π hker hn (hd * hd) =
      liftAut π hker hn hd * liftAut π hker hn hd := map_mul _ _ _
  have h3 : CatalogueBHigherLinearAction.slConjugation n F (A * A) = 1 := by
    rw [map_mul, ← hliftA, ← h2, h1]
  rw [← MonoidHom.mem_ker, CFSG.LinearGroups.ker_slConjugation] at h3
  exact h3

attribute [local instance] Fintype.ofFinite in
theorem exists_sq_eq_of_finite_field (μ : Fˣ) : ∃ ν : Fˣ, ν ^ 2 = μ := by
  classical
  obtain ⟨m, hprime, hcard⟩ := FiniteField.card F 2
  have hcard' : Nat.card F = 2 ^ (m : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcard]
  have hodd : Odd (Nat.card Fˣ) := by
    rw [Nat.card_units, hcard']
    obtain ⟨k, hk⟩ := Even.pow_of_ne_zero (by norm_num : Even (2 : ℕ)) m.pos.ne'
    have hkpos : 0 < k := by
      have : 0 < 2 ^ (m : ℕ) := pow_pos (by norm_num) _
      omega
    exact ⟨k - 1, by omega⟩
  have hcop : (Nat.card Fˣ).Coprime 2 := Nat.coprime_two_right.mpr hodd
  exact hcop.pow_left_bijective.surjective μ

attribute [local instance] Fintype.ofFinite in
theorem mem_range_of_fieldPart_graphPart_eq_one (hker : π.ker ≤ scalars n F) (hn : 3 ≤ n)
    (hodd : ∀ c ∈ Subgroup.centralizer (π.range : Set H), Odd (orderOf c))
    {d : H} (hdN : d ∈ rangeNormalizer π) (hd2 : d * d = 1)
    (hfield : fieldPart π hker hn ⟨d, hdN⟩ = 1)
    (hgraph : graphPart π hker hn ⟨d, hdN⟩ = 1) :
    d ∈ π.range := by
  classical
  let hd : rangeNormalizer π := ⟨d, hdN⟩
  let A : GL (Fin n) F := (stdData π hker hn hd).1
  have hσ : (stdData π hker hn hd).2.1 = 1 := stdData_field_eq_one π hker hn hdN hfield
  have hε : (stdData π hker hn hd).2.2 = 0 := stdData_eps_eq_zero π hker hn hdN hgraph
  have hliftA : liftAut π hker hn hd = CatalogueBHigherLinearAction.slConjugation n F A := by
    rw [liftAut_eq_stdAut, hσ, hε]
    simp only [CFSG.QuasithinUnique.K1.stdAut, pow_zero, mul_one,
      CatalogueBHigherLinearField.slFieldAut, map_one, mul_one]
    rfl
  have hAAs := stdData_sq_mem_center π hker hn hdN hd2 hσ hε
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hAAs
  obtain ⟨μ, hμ⟩ := MonoidHom.mem_range.mp hAAs
  have hdet_sq : A.det * A.det = μ ^ n := by
    rw [← map_mul, ← hμ, Matrix.GeneralLinearGroup.det_scalar]
    simp
  obtain ⟨ν, hν⟩ := exists_sq_eq_of_finite_field (F := F) μ
  have hνn : (ν ^ n) * (ν ^ n) = μ ^ n := by
    calc (ν ^ n) * (ν ^ n) = ν ^ (n + n) := by rw [pow_add]
      _ = ν ^ (2 * n) := by congr 1; omega
      _ = (ν ^ 2) ^ n := by rw [pow_mul]
      _ = μ ^ n := by rw [hν]
  have hodd_units : Odd (Nat.card Fˣ) := by
    classical
    obtain ⟨m, hprime, hcard⟩ := FiniteField.card F 2
    have hcard' : Nat.card F = 2 ^ (m : ℕ) := by
      rw [Nat.card_eq_fintype_card, hcard]
    rw [Nat.card_units, hcard']
    obtain ⟨k, hk⟩ := Even.pow_of_ne_zero (by norm_num : Even (2 : ℕ)) m.pos.ne'
    have hkpos : 0 < k := by
      have : 0 < 2 ^ (m : ℕ) := pow_pos (by norm_num) _
      omega
    exact ⟨k - 1, by omega⟩
  have hcop : (Nat.card Fˣ).Coprime 2 := Nat.coprime_two_right.mpr hodd_units
  have hdet_eq : A.det = ν ^ n :=
    hcop.pow_left_bijective.injective (by
      simpa only [pow_two] using hdet_sq.trans hνn.symm)
  let B : GL (Fin n) F := (Matrix.GeneralLinearGroup.scalar (Fin n) ν)⁻¹ * A
  have hBdet : B.det = 1 := by
    rw [show B = (Matrix.GeneralLinearGroup.scalar (Fin n) ν)⁻¹ * A from rfl]
    rw [map_mul, map_inv, Matrix.GeneralLinearGroup.det_scalar, hdet_eq]
    simp only [Fintype.card_fin]
    group
  have hBdet' : (B : Matrix (Fin n) (Fin n) F).det = 1 := by
    simpa using congrArg Units.val hBdet
  let x₀ : SpecialLinearGroup (Fin n) F := ⟨B, hBdet'⟩
  have hlift_x₀ : liftAut π hker hn
      ⟨π x₀, Subgroup.le_normalizer (MonoidHom.mem_range.mpr ⟨x₀, rfl⟩)⟩ =
        CatalogueBHigherLinearAction.slConjugation n F A := by
    have hconj : MulAut.conj x₀ =
        CatalogueBHigherLinearAction.slConjugation n F (SpecialLinearGroup.toGL x₀) := by
      apply MulEquiv.ext
      intro g
      rw [MulAut.conj_apply]
      exact (slConjugation_toGL x₀ g).symm
    have hxB : SpecialLinearGroup.toGL x₀ = B := Units.ext rfl
    calc liftAut π hker hn
          ⟨π x₀, Subgroup.le_normalizer (MonoidHom.mem_range.mpr ⟨x₀, rfl⟩)⟩
        = MulAut.conj x₀ := liftAut_range π hker hn x₀
      _ = CatalogueBHigherLinearAction.slConjugation n F (SpecialLinearGroup.toGL x₀) := hconj
      _ = CatalogueBHigherLinearAction.slConjugation n F B := by
          rw [hxB]
      _ = CatalogueBHigherLinearAction.slConjugation n F
            ((Matrix.GeneralLinearGroup.scalar (Fin n) ν)⁻¹ * A) := rfl
      _ = CatalogueBHigherLinearAction.slConjugation n F
            (Matrix.GeneralLinearGroup.scalar (Fin n) ν)⁻¹ *
          CatalogueBHigherLinearAction.slConjugation n F A := map_mul _ _ _
      _ = 1 * CatalogueBHigherLinearAction.slConjugation n F A := by
          rw [show (Matrix.GeneralLinearGroup.scalar (Fin n) ν)⁻¹ =
            Matrix.GeneralLinearGroup.scalar (Fin n) ν⁻¹ from
            (map_inv (Matrix.GeneralLinearGroup.scalar (Fin n)) ν).symm]
          rw [CatalogueBHigherLinearAction.slConjugation_scalar]
      _ = CatalogueBHigherLinearAction.slConjugation n F A := one_mul _
  let hx₀N : rangeNormalizer π :=
    ⟨π x₀, Subgroup.le_normalizer (MonoidHom.mem_range.mpr ⟨x₀, rfl⟩)⟩
  let c : H := (π x₀)⁻¹ * d
  have hcN : c ∈ rangeNormalizer π :=
    (rangeNormalizer π).mul_mem ((rangeNormalizer π).inv_mem hx₀N.2) hd.2
  have hc_lift : liftAut π hker hn ⟨c, hcN⟩ = 1 := by
    have hsub : (⟨c, hcN⟩ : rangeNormalizer π) = hx₀N⁻¹ * hd := by
      apply Subtype.ext
      rfl
    rw [hsub, map_mul, map_inv, hlift_x₀, hliftA, inv_mul_cancel]
  have hc_cent : c ∈ Subgroup.centralizer (π.range : Set H) := by
    have hker_eq := liftAut_ker π hker hn
    have hmem : (⟨c, hcN⟩ : rangeNormalizer π) ∈ (liftAut π hker hn).ker := by
      rw [MonoidHom.mem_ker]
      exact hc_lift
    rwa [hker_eq, Subgroup.mem_subgroupOf] at hmem
  have hc2 : c ^ 2 ∈ π.range := by
    have hcomm : (π x₀) * c = c * (π x₀) :=
      (Subgroup.mem_centralizer_iff.mp hc_cent) (π x₀)
        (MonoidHom.mem_range.mpr ⟨x₀, rfl⟩)
    have hcomm' : c * (π x₀)⁻¹ = (π x₀)⁻¹ * c := by
      calc c * (π x₀)⁻¹ = (π x₀)⁻¹ * ((π x₀) * c) * (π x₀)⁻¹ := by group
        _ = (π x₀)⁻¹ * (c * (π x₀)) * (π x₀)⁻¹ := by rw [hcomm]
        _ = (π x₀)⁻¹ * c := by group
    have hc2_eq : c ^ 2 = (π x₀)⁻¹ * (π x₀)⁻¹ := by
      calc c ^ 2 = c * c := pow_two c
        _ = c * ((π x₀)⁻¹ * d) := rfl
        _ = (c * (π x₀)⁻¹) * d := by group
        _ = ((π x₀)⁻¹ * c) * d := by rw [hcomm']
        _ = (π x₀)⁻¹ * (c * d) := by group
        _ = (π x₀)⁻¹ * (((π x₀)⁻¹ * d) * d) := rfl
        _ = (π x₀)⁻¹ * (π x₀)⁻¹ * (d * d) := by group
        _ = (π x₀)⁻¹ * (π x₀)⁻¹ := by rw [hd2, mul_one]
    rw [hc2_eq]
    exact (π.range).mul_mem ((π.range).inv_mem (MonoidHom.mem_range.mpr ⟨x₀, rfl⟩))
      ((π.range).inv_mem (MonoidHom.mem_range.mpr ⟨x₀, rfl⟩))
  have hc_mem : c ∈ π.range := by
    have hodd_c : Odd (orderOf c) := hodd c hc_cent
    have hc_zpow : c ∈ Subgroup.zpowers (c ^ 2) := by
      rw [Subgroup.mem_zpowers_iff]
      obtain ⟨k, hk⟩ := hodd_c
      refine ⟨(k + 1 : ℕ), ?_⟩
      rw [zpow_natCast, ← pow_mul]
      have hk' : 2 * (k + 1) = orderOf c + 1 := by omega
      rw [hk', pow_succ, pow_orderOf_eq_one, one_mul]
    exact (Subgroup.zpowers_le.mpr hc2) hc_zpow
  have hd_eq : d = (π x₀) * c := by
    rw [show c = (π x₀)⁻¹ * d from rfl]
    group
  rw [hd_eq]
  exact (π.range).mul_mem (MonoidHom.mem_range.mpr ⟨x₀, rfl⟩) hc_mem


@[expose] def normalizerInclusion {D : Subgroup H} (hD : D ≤ rangeNormalizer π) :
    D →* rangeNormalizer π where
  toFun d := ⟨d.1, hD d.2⟩
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

omit [Finite F] [CharP F 2] in
theorem normalizerInclusion_apply {D : Subgroup H} (hD : D ≤ rangeNormalizer π) (d : D) :
    normalizerInclusion π hD d = ⟨d.1, hD d.2⟩ := rfl

attribute [local instance] Fintype.ofFinite in
attribute [local instance] Subgroup.isCyclic in
theorem card_le_two_of_sq_eq_one {G : Type*} [Group G] [Finite G] [IsCyclic G]
    (K : Subgroup G) (hK : ∀ x : K, x ^ 2 = 1) : Nat.card K ≤ 2 := by
  classical
  have hset : (Finset.univ.filter (fun a : K => a ^ 2 = 1)) = Finset.univ := by
    ext a
    simp [hK a]
  have h := IsCyclic.card_pow_eq_one_le (α := K) (n := 2) (by norm_num)
  rw [hset, Finset.card_univ] at h
  simpa only [Nat.card_eq_fintype_card] using h

@[expose] def prodSubtypeEquiv {G N : Type*} [Group G] [Group N] (K : Subgroup G) (L : Subgroup N) :
    ↥(K.prod L) ≃ K × L where
  toFun x := (⟨x.1.1, (Subgroup.mem_prod.mp x.2).1⟩, ⟨x.1.2, (Subgroup.mem_prod.mp x.2).2⟩)
  invFun x := ⟨(x.1.1, x.2.1), Subgroup.mem_prod.mpr ⟨x.1.2, x.2.2⟩⟩
  left_inv x := by ext <;> rfl
  right_inv x := by ext <;> rfl

theorem card_le_four_mul_card_inf (hker : π.ker ≤ scalars n F) (hn : 3 ≤ n)
    (hodd : ∀ c ∈ Subgroup.centralizer (π.range : Set H), Odd (orderOf c))
    (D : Subgroup H) [Finite D] (hD : D ≤ rangeNormalizer π)
    (hD2 : ∀ d ∈ D, d * d = 1) :
    Nat.card D ≤ 4 * Nat.card ↥(D ⊓ π.range) := by
  classical
  let inc : D →* rangeNormalizer π := normalizerInclusion π hD
  let f : D →* (F ≃+* F) := (fieldPart π hker hn).comp inc
  let g : D →* Multiplicative (ZMod 2) := (graphPart π hker hn).comp inc
  let parts : D →* (F ≃+* F) × Multiplicative (ZMod 2) := f.prod g
  have hker_parts : parts.ker = (D ⊓ π.range).subgroupOf D := by
    ext d
    rw [MonoidHom.mem_ker]
    constructor
    · intro hd
      have hf : f d = 1 := by
        simpa [parts, MonoidHom.prod_apply] using congrArg Prod.fst hd
      have hg : g d = 1 := by
        simpa [parts, MonoidHom.prod_apply] using congrArg Prod.snd hd
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      have hf' : (fieldPart π hker hn) ⟨d.1, hD d.2⟩ = 1 := by
        simpa only [f, inc, normalizerInclusion_apply, MonoidHom.comp_apply] using hf
      have hg' : (graphPart π hker hn) ⟨d.1, hD d.2⟩ = 1 := by
        simpa only [g, inc, normalizerInclusion_apply, MonoidHom.comp_apply] using hg
      exact ⟨d.2, mem_range_of_fieldPart_graphPart_eq_one π hker hn hodd (hD d.2)
        (hD2 d.1 d.2) hf' hg'⟩
    · intro hd
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hd
      obtain ⟨x, hx⟩ := hd.2
      have hx' : d.1 = π x := hx.symm
      have hd_eq : (⟨d.1, hD d.2⟩ : rangeNormalizer π) =
          ⟨π x, Subgroup.le_normalizer (MonoidHom.mem_range.mpr ⟨x, rfl⟩)⟩ :=
        Subtype.ext hx'
      have hf : f d = 1 := by
        rw [show f d = (fieldPart π hker hn) (normalizerInclusion π hD d) from rfl,
          normalizerInclusion_apply, hd_eq]
        exact (fieldPart_graphPart_range π hker hn x).1
      have hg : g d = 1 := by
        rw [show g d = (graphPart π hker hn) (normalizerInclusion π hD d) from rfl,
          normalizerInclusion_apply, hd_eq]
        exact (fieldPart_graphPart_range π hker hn x).2
      show (f d, g d) = 1
      rw [show (1 : (F ≃+* F) × Multiplicative (ZMod 2)) = (1, 1) from rfl]
      exact Prod.ext hf hg
  have hcard_ker : Nat.card parts.ker = Nat.card ↥(D ⊓ π.range) := by
    rw [hker_parts]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hfield_range_le : Nat.card f.range ≤ 2 := by
    refine @card_le_two_of_sq_eq_one (F ≃+* F) _ _
      (CFSG.ABGDGroups.isCyclic_ringEquiv F) f.range ?_
    rintro ⟨x, hx⟩
    obtain ⟨d, rfl⟩ := hx
    apply Subtype.ext
    show (f d) ^ 2 = 1
    have hdd : d * d = 1 := by
      apply Subtype.ext
      exact hD2 d.1 d.2
    calc (f d) ^ 2 = f (d * d) := by rw [pow_two, map_mul]
      _ = f 1 := by rw [hdd]
      _ = 1 := map_one f
  have hgraph_range_le : Nat.card g.range ≤ 2 := by
    have hle : Nat.card g.range ≤ Nat.card (Multiplicative (ZMod 2)) :=
      Nat.card_le_card_of_injective (fun x : g.range => (x : Multiplicative (ZMod 2)))
        Subtype.coe_injective
    have hcard : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_eq_fintype_card]
      simp
    rwa [hcard] at hle
  have hparts_range_le : Nat.card parts.range ≤ 4 := by
    have hle : parts.range ≤ f.range.prod g.range := by
      rintro _ ⟨d, rfl⟩
      exact ⟨⟨d, rfl⟩, ⟨d, rfl⟩⟩
    have hcard_le : Nat.card parts.range ≤ Nat.card ↥(f.range.prod g.range) :=
      Subgroup.card_le_of_le hle
    have hprod : Nat.card ↥(f.range.prod g.range) =
        Nat.card f.range * Nat.card g.range := by
      rw [Nat.card_congr (prodSubtypeEquiv f.range g.range), Nat.card_prod]
    rw [hprod] at hcard_le
    calc Nat.card parts.range ≤ Nat.card f.range * Nat.card g.range := hcard_le
      _ ≤ 2 * 2 := Nat.mul_le_mul hfield_range_le hgraph_range_le
      _ = 4 := by norm_num
  have hcardD : Nat.card D = Nat.card parts.range * Nat.card ↥(D ⊓ π.range) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup parts.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange parts).toEquiv, hcard_ker]
  calc Nat.card D = Nat.card parts.range * Nat.card ↥(D ⊓ π.range) := hcardD
    _ ≤ 4 * Nat.card ↥(D ⊓ π.range) := Nat.mul_le_mul_right _ hparts_range_le

theorem card_le_two_mul_card_inf_of_graphPart_eq_one (hker : π.ker ≤ scalars n F) (hn : 3 ≤ n)
    (hodd : ∀ c ∈ Subgroup.centralizer (π.range : Set H), Odd (orderOf c))
    (D : Subgroup H) [Finite D] (hD : D ≤ rangeNormalizer π)
    (hD2 : ∀ d ∈ D, d * d = 1)
    (hgraph : ∀ d (hd : d ∈ D), graphPart π hker hn ⟨d, hD hd⟩ = 1) :
    Nat.card D ≤ 2 * Nat.card ↥(D ⊓ π.range) := by
  classical
  let inc : D →* rangeNormalizer π := normalizerInclusion π hD
  let f : D →* (F ≃+* F) := (fieldPart π hker hn).comp inc
  let g : D →* Multiplicative (ZMod 2) := (graphPart π hker hn).comp inc
  let parts : D →* (F ≃+* F) × Multiplicative (ZMod 2) := f.prod g
  have hker_parts : parts.ker = (D ⊓ π.range).subgroupOf D := by
    ext d
    rw [MonoidHom.mem_ker]
    constructor
    · intro hd
      have hf : f d = 1 := by
        simpa [parts, MonoidHom.prod_apply] using congrArg Prod.fst hd
      have hg : g d = 1 := by
        simpa [parts, MonoidHom.prod_apply] using congrArg Prod.snd hd
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      have hf' : (fieldPart π hker hn) ⟨d.1, hD d.2⟩ = 1 := by
        simpa only [f, inc, normalizerInclusion_apply, MonoidHom.comp_apply] using hf
      have hg' : (graphPart π hker hn) ⟨d.1, hD d.2⟩ = 1 := by
        simpa only [g, inc, normalizerInclusion_apply, MonoidHom.comp_apply] using hg
      exact ⟨d.2, mem_range_of_fieldPart_graphPart_eq_one π hker hn hodd (hD d.2)
        (hD2 d.1 d.2) hf' hg'⟩
    · intro hd
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hd
      obtain ⟨x, hx⟩ := hd.2
      have hx' : d.1 = π x := hx.symm
      have hd_eq : (⟨d.1, hD d.2⟩ : rangeNormalizer π) =
          ⟨π x, Subgroup.le_normalizer (MonoidHom.mem_range.mpr ⟨x, rfl⟩)⟩ :=
        Subtype.ext hx'
      have hf : f d = 1 := by
        rw [show f d = (fieldPart π hker hn) (normalizerInclusion π hD d) from rfl,
          normalizerInclusion_apply, hd_eq]
        exact (fieldPart_graphPart_range π hker hn x).1
      have hg : g d = 1 := by
        rw [show g d = (graphPart π hker hn) (normalizerInclusion π hD d) from rfl,
          normalizerInclusion_apply, hd_eq]
        exact (fieldPart_graphPart_range π hker hn x).2
      show (f d, g d) = 1
      rw [show (1 : (F ≃+* F) × Multiplicative (ZMod 2)) = (1, 1) from rfl]
      exact Prod.ext hf hg
  have hcard_ker : Nat.card parts.ker = Nat.card ↥(D ⊓ π.range) := by
    rw [hker_parts]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hfield_range_le : Nat.card f.range ≤ 2 := by
    refine @card_le_two_of_sq_eq_one (F ≃+* F) _ _
      (CFSG.ABGDGroups.isCyclic_ringEquiv F) f.range ?_
    rintro ⟨x, hx⟩
    obtain ⟨d, rfl⟩ := hx
    apply Subtype.ext
    show (f d) ^ 2 = 1
    have hdd : d * d = 1 := by
      apply Subtype.ext
      exact hD2 d.1 d.2
    calc (f d) ^ 2 = f (d * d) := by rw [pow_two, map_mul]
      _ = f 1 := by rw [hdd]
      _ = 1 := map_one f
  have hparts_range_le : Nat.card parts.range ≤ 2 := by
    have hle : parts.range ≤ f.range.prod (⊥ : Subgroup (Multiplicative (ZMod 2))) := by
      rintro _ ⟨d, rfl⟩
      refine ⟨⟨d, rfl⟩, ?_⟩
      exact hgraph d.1 d.2
    have hcard_le : Nat.card parts.range ≤
        Nat.card ↥(f.range.prod (⊥ : Subgroup (Multiplicative (ZMod 2)))) :=
      Subgroup.card_le_of_le hle
    have hprod : Nat.card ↥(f.range.prod (⊥ : Subgroup (Multiplicative (ZMod 2)))) =
        Nat.card f.range := by
      rw [Nat.card_congr (prodSubtypeEquiv f.range ⊥), Nat.card_prod]
      simp
    rw [hprod] at hcard_le
    exact hcard_le.trans hfield_range_le
  have hcardD : Nat.card D = Nat.card parts.range * Nat.card ↥(D ⊓ π.range) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup parts.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange parts).toEquiv, hcard_ker]
  calc Nat.card D = Nat.card parts.range * Nat.card ↥(D ⊓ π.range) := hcardD
    _ ≤ 2 * Nat.card ↥(D ⊓ π.range) := Nat.mul_le_mul_right _ hparts_range_le

end CFSG.LieType.SpecialLinear
