module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDLinProj

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SD.Lin

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.CALinearPrimary

theorem exists_orderOf_eq_of_dvd_units {E : Type*} [Field E] [Finite E] {m : ℕ} (hm : 2 ≤ m) {p : ℕ}
    (hp : p.Prime) (hpq : p ∣ Nat.card E - 1) :
    ∃ g : Matrix.SpecialLinearGroup (Fin m) E, orderOf g = p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := Eˣ) p (by rw [Nat.card_units]; exact hpq)
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    exact hp.one_lt.ne ht
  have htp : t ^ p = 1 := by
    rw [← ht]
    exact pow_orderOf_eq_one t
  let i₀ : Fin m := ⟨0, by omega⟩
  let i₁ : Fin m := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  let d : Fin m → E := fun i => if i = i₀ then (t : E) else if i = i₁ then ((t⁻¹ : Eˣ) : E) else 1
  have hd₀ : d i₀ = (t : E) := by simp [d]
  have hd₁ : d i₁ = ((t⁻¹ : Eˣ) : E) := by simp [d, Ne.symm h01]
  have hdet : (Matrix.diagonal d).det = 1 := by
    rw [Matrix.det_diagonal, Fintype.prod_eq_mul i₀ i₁ h01 (fun x hx => by simp [d, hx.1, hx.2]),
      hd₀, hd₁, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  let g : Matrix.SpecialLinearGroup (Fin m) E := ⟨Matrix.diagonal d, hdet⟩
  have hd : ∀ i, d i ^ p = 1 := by
    intro i
    simp only [d]
    split_ifs
    · rw [← Units.val_pow_eq_pow_val, htp, Units.val_one]
    · rw [← Units.val_pow_eq_pow_val, inv_pow, htp, inv_one, Units.val_one]
    · exact one_pow p
  have hgp : g ^ p = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow]
    show Matrix.diagonal d ^ p = 1
    rw [Matrix.diagonal_pow]
    have : d ^ p = fun _ => 1 := funext fun i => by simpa using hd i
    rw [this]
    exact Matrix.diagonal_one
  have hg1 : g ≠ 1 := by
    intro h
    have h1 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin m) E =>
      (M : Matrix (Fin m) (Fin m) E) i₀ i₀) h
    simp only [g, Matrix.diagonal_apply_eq, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq,
      hd₀] at h1
    exact ht1 (Units.ext h1)
  exact ⟨g, orderOf_eq_prime hgp hg1⟩

theorem exists_special_of_pow_scalar {E W : Type*} [Field E] [Finite E] [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {p : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ Nat.card E - 1)
    (γ : LinearMap.GeneralLinearGroup E W) (c' : Eˣ)
    (hγp : γ ^ p = Units.map (algebraMap E (Module.End E W)).toMonoidHom c')
    (hns : ¬ ∃ c : E, ∀ w : W, (γ : Module.End E W) w = c • w) :
    ∃ u : _root_.SpecialLinearGroup E W, orderOf u = p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hcop : (Nat.card Eˣ).Coprime p := by
    rw [Nat.card_units]
    exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hpq).symm
  obtain ⟨μ, hμ⟩ := (powCoprime hcop).surjective c'
  have hμp : μ ^ p = c' := hμ
  let sc : Eˣ →* LinearMap.GeneralLinearGroup E W :=
    Units.map (algebraMap E (Module.End E W)).toMonoidHom
  have hsc : ∀ (u : Eˣ) (w : W), ((sc u : LinearMap.GeneralLinearGroup E W) : Module.End E W) w =
      (u : E) • w := fun u w => Module.algebraMap_end_apply E E W _ w
  have hγp' : γ ^ p = sc c' := hγp
  have hcomm : Commute γ (sc μ⁻¹) := by
    refine Units.ext (LinearMap.ext fun w => ?_)
    simp only [Units.val_mul, Module.End.mul_apply, hsc, map_smul]
  set γ' : LinearMap.GeneralLinearGroup E W := γ * sc μ⁻¹ with hγ'
  have hγ'p : γ' ^ p = 1 := by
    rw [hγ', hcomm.mul_pow, hγp', ← map_pow sc, inv_pow, hμp, ← map_mul, mul_inv_cancel, map_one]
  have hd : LinearMap.det (γ' : Module.End E W) ^ p = 1 := by
    have h1 : ((γ' ^ p : LinearMap.GeneralLinearGroup E W) : Module.End E W) = 1 := by
      rw [hγ'p]
      rfl
    have h2 : LinearMap.det (((γ' ^ p : LinearMap.GeneralLinearGroup E W)) : Module.End E W) = 1 := by
      rw [h1, map_one]
    rwa [Units.val_pow_eq_pow_val, map_pow] at h2
  have hd0 : LinearMap.det (γ' : Module.End E W) ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp.ne_zero] at hd
    exact zero_ne_one hd
  haveI := Fintype.ofFinite E
  have hdq : LinearMap.det (γ' : Module.End E W) ^ (Fintype.card E - 1) = 1 :=
    FiniteField.pow_card_sub_one_eq_one _ hd0
  have hgcd : Nat.gcd p (Fintype.card E - 1) = 1 := by
    have := (Nat.Prime.coprime_iff_not_dvd hp).2 hpq
    rwa [Nat.card_eq_fintype_card] at this
  have hd1 : LinearMap.det (γ' : Module.End E W) = 1 := by
    have := pow_gcd_eq_one.2 ⟨hd, hdq⟩
    rwa [hgcd, pow_one] at this
  let u : _root_.SpecialLinearGroup E W :=
    ⟨LinearMap.GeneralLinearGroup.generalLinearEquiv _ _ γ',
      Units.ext (by rw [LinearEquiv.coe_det]; exact hd1)⟩
  refine ⟨u, orderOf_eq_prime ?_ ?_⟩
  · apply Subtype.ext
    show (LinearMap.GeneralLinearGroup.generalLinearEquiv E W γ') ^ p = 1
    rw [← map_pow, hγ'p, map_one]
  · intro hu1
    have h1 : LinearMap.GeneralLinearGroup.generalLinearEquiv E W γ' = 1 := congrArg Subtype.val hu1
    have h2 : γ' = 1 := by
      apply (LinearMap.GeneralLinearGroup.generalLinearEquiv E W).injective
      rw [h1, map_one]
    have h3 : γ = sc μ := by
      have h4 : γ * sc μ⁻¹ = 1 := h2
      rw [mul_eq_one_iff_eq_inv, ← map_inv, inv_inv] at h4
      exact h4
    exact hns ⟨(μ : E), fun w => by rw [h3]; exact hsc μ w⟩

variable {K : Type} [Field K] [Finite K] {n : ℕ}

local notation "𝒱" => (Fin n → K)

theorem nonempty_specialFactor_equiv_block {A : GL (Fin n) K}
    (hsq : Squarefree (minpoly K (glA A : Module.End K 𝒱))) {h : K[X]}
    (hh : h ∈ primaryFactors (glA A : Module.End K 𝒱)) :
    Nonempty (specialFactor A h ≃* linearSpecialBlock (glA A) h) := by
  have hle : linearSpecialBlock (glA A) h ≤ (slGL n K).range := fun _ hg =>
    mem_range_slGL (det_eq_one_of_mem_linearSpecialBlock hsq hh hg)
  have hmap : (specialFactor A h).map (slGL n K) = linearSpecialBlock (glA A) h := by
    rw [specialFactor, Subgroup.map_comap_eq, inf_eq_right]
    exact hle
  exact ⟨(Subgroup.equivMapOfInjective _ (slGL n K) slGL_injective).trans
    (MulEquiv.subgroupCongr hmap)⟩

theorem dvd_card_specialFactor_of_dvd_units {A : GL (Fin n) K}
    (hsq : Squarefree (minpoly K (glA A : Module.End K 𝒱))) {h : K[X]}
    (hh : h ∈ primaryFactors (glA A : Module.End K 𝒱))
    (hm : 2 ≤ primaryMultiplicity (glA A : Module.End K 𝒱) h) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ Nat.card (AdjoinRoot h) - 1) : p ∣ Nat.card (specialFactor A h) := by
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : Finite (AdjoinRoot h) := Module.finite_of_finite K
  obtain ⟨e⟩ := nonempty_mulEquiv_specialFactor hsq hh
  obtain ⟨g, hg⟩ := exists_orderOf_eq_of_dvd_units hm hp hpq
  rw [← Nat.card_congr e.toEquiv, ← hg]
  exact orderOf_dvd_natCard g

theorem glA_scalar_apply (c : Kˣ) (v : 𝒱) :
    ((glA (Matrix.GeneralLinearGroup.scalar (Fin n) c) : LinearMap.GeneralLinearGroup K 𝒱) :
      Module.End K 𝒱) v = (c : K) • v := by
  show Matrix.toLin' (((Matrix.GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K)) :
    Matrix (Fin n) (Fin n) K) v = _
  ext i
  simp [Matrix.toLin'_apply, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply,
    Matrix.mulVec_diagonal]

variable {A : GL (Fin n) K}

local notation "𝒲[" h "]" => primaryComponent (glA A : Module.End K 𝒱) h

theorem dvd_card_specialFactor_of_noncentral {B : GL (Fin n) K}
    (hsq : Squarefree (minpoly K (glA A : Module.End K 𝒱))) {h : K[X]}
    (hh : h ∈ primaryFactors (glA A : Module.End K 𝒱)) {p : ℕ} (hp : p.Prime)
    (hpq : ¬ p ∣ Nat.card (AdjoinRoot h) - 1) (hBc : glA B ∈ gl_centralizer (glA A)) {c₁ : Kˣ}
    (hBp : B ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c₁)
    (hns : ¬ ∃ c : AdjoinRoot h, ∀ v : 𝒲[h],
      (((glA B : LinearMap.GeneralLinearGroup K 𝒱) : Module.End K 𝒱) (v : 𝒱)) = ((c • v : 𝒲[h]) : 𝒱)) :
    p ∣ Nat.card (specialFactor A h) := by
  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : Finite (AdjoinRoot h) := Module.finite_of_finite K
  set γ : blockGL (glA A : Module.End K 𝒱) h := glCentralizerEquivPi hsq ⟨glA B, hBc⟩ ⟨h, hh⟩ with hγ
  let scE : (AdjoinRoot h)ˣ →* blockGL (glA A : Module.End K 𝒱) h :=
    Units.map (algebraMap (AdjoinRoot h) (Module.End (AdjoinRoot h) 𝒲[h])).toMonoidHom
  let c₁' : (AdjoinRoot h)ˣ := Units.map (algebraMap K (AdjoinRoot h) : K →* AdjoinRoot h) c₁
  have hscE : ∀ w : 𝒲[h], ((((scE c₁' : blockGL (glA A : Module.End K 𝒱) h) :
      Module.End (AdjoinRoot h) 𝒲[h]) w : 𝒲[h]) : 𝒱) = (c₁ : K) • (w : 𝒱) := by
    intro w
    change ((algebraMap (AdjoinRoot h) (Module.End (AdjoinRoot h) 𝒲[h])
      (algebraMap K (AdjoinRoot h) (c₁ : K)) w : 𝒲[h]) : 𝒱) = _
    rw [Module.algebraMap_end_apply]
    exact coe_algebraMap_smul_primaryComponent _ _ (c₁ : K) w
  have hγp : γ ^ p = scE c₁' := by
    refine Units.ext (LinearMap.ext fun w => Subtype.ext ?_)
    rw [hscE w]
    have h1 : γ ^ p = glCentralizerEquivPi hsq ((⟨glA B, hBc⟩ : gl_centralizer (glA A)) ^ p) ⟨h, hh⟩ := by
      rw [hγ, map_pow, Pi.pow_apply]
    show blockApply (γ ^ p) (w : 𝒱) w.2 = _
    rw [h1, blockApply_glCentralizerEquivPi]
    change ((((glA B) ^ p : LinearMap.GeneralLinearGroup K 𝒱)) : Module.End K 𝒱) (w : 𝒱) = _
    rw [← map_pow Matrix.GeneralLinearGroup.toLin B p, hBp]
    exact glA_scalar_apply c₁ _
  have hnsγ : ¬ ∃ c : AdjoinRoot h, ∀ w : 𝒲[h],
      (γ : Module.End (AdjoinRoot h) 𝒲[h]) w = c • w :=
    fun ⟨c, hc⟩ => hns ⟨c, fun v => congrArg Subtype.val (hc v)⟩
  obtain ⟨u, hu⟩ := exists_special_of_pow_scalar hp hpq γ c₁' hγp hnsγ
  obtain ⟨g₁, hg₁⟩ := linearSpecialBlockRestrict_surjective hsq hh u
  have hord : orderOf g₁ = p := by
    rw [← hu, ← hg₁]
    exact (orderOf_injective (linearSpecialBlockRestrict (glA A) h)
      (linearSpecialBlockRestrict_injective hsq) g₁).symm
  obtain ⟨e⟩ := nonempty_specialFactor_equiv_block hsq hh
  rw [Nat.card_congr e.toEquiv, ← hord]
  exact orderOf_dvd_natCard g₁

end CFSG.LocalAnalysis.GLTheoremA.T263.SD.Lin

end
