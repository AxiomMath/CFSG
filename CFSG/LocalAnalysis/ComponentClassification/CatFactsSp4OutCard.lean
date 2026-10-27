module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TCClass
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KASp4IStr

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup

variable {K : Type} [Field K]

@[expose] def twistHom (θ : MulAut (StatedSp 2 K)) {α : MulAut (StatedProj (StatedSp 2 K))}
    (hθα : ∀ g, α (proj 2 K g) = proj 2 K (θ g)) :
    (fixOf α).comap (proj 2 K) →* spScalars 2 K where
  toFun g := ⟨θ g * (g : StatedSp 2 K)⁻¹, by
    rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, ← hθα]
    have : α (proj 2 K g) = proj 2 K g := g.2
    rw [this, mul_inv_cancel]⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' g h := by
    apply Subtype.ext
    have hh : θ h * (h : StatedSp 2 K)⁻¹ ∈ spScalars 2 K := by
      rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, ← hθα]
      have : α (proj 2 K h) = proj 2 K h := h.2
      rw [this, mul_inv_cancel]
    have hc := mem_center_iff.mp (mem_center_of_mem_spScalars hh)
    simp only [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev]
    calc θ g * θ h * ((h : StatedSp 2 K)⁻¹ * (g : StatedSp 2 K)⁻¹) =
        θ g * (θ h * (h : StatedSp 2 K)⁻¹) * (g : StatedSp 2 K)⁻¹ := by group
      _ = θ g * ((g : StatedSp 2 K)⁻¹ * (θ h * (h : StatedSp 2 K)⁻¹)) := by
        rw [mul_assoc, ← hc]
      _ = θ g * (g : StatedSp 2 K)⁻¹ * (θ h * (h : StatedSp 2 K)⁻¹) := by group

theorem card_fixOf_dvd [Finite K] (h2 : (2 : K) ≠ 0) (θ : MulAut (StatedSp 2 K))
    {α : MulAut (StatedProj (StatedSp 2 K))} (hθα : ∀ g, α (proj 2 K g) = proj 2 K (θ g)) :
    Nat.card (fixOf α) ∣ Nat.card (fixOf θ) := by
  set F := (fixOf α).comap (proj 2 K) with hF
  have hle : fixOf θ ≤ F := fun g hg => by
    change α (proj 2 K g) = proj 2 K g
    rw [hθα]
    exact congrArg (proj 2 K) hg
  have hker : (twistHom θ hθα).ker = (fixOf θ).subgroupOf F := by
    ext g
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro h
      have h' := congrArg Subtype.val h
      change θ g * (g : StatedSp 2 K)⁻¹ = 1 at h'
      exact mul_inv_eq_one.mp h'
    · intro h
      apply Subtype.ext
      change θ g * (g : StatedSp 2 K)⁻¹ = 1
      exact mul_inv_eq_one.mpr h
  have hkc : Nat.card (twistHom θ hθα).ker = Nat.card (fixOf θ) := by
    rw [hker]
    exact Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv
  have c1 : Nat.card F = Nat.card (fixOf θ) * Nat.card (twistHom θ hθα).range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (twistHom θ hθα).ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange (twistHom θ hθα)).toEquiv, hkc,
      mul_comm]
  have hZle : spScalars 2 K ≤ F := fun z hz => by
    change α (proj 2 K z) = proj 2 K z
    rw [(MonoidHom.mem_ker).mp ((ker_proj (K := K)).symm ▸ hz), map_one]
  have hker2 : ((proj 2 K).subgroupComap (fixOf α)).ker = (spScalars 2 K).subgroupOf F := by
    ext g
    rw [MonoidHom.mem_ker, mem_subgroupOf, ← ker_proj, MonoidHom.mem_ker]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hkc2 : Nat.card ((proj 2 K).subgroupComap (fixOf α)).ker = 2 := by
    rw [hker2, Nat.card_congr (subgroupOfEquivOfLe hZle).toEquiv, card_spScalars h2]
  have c2 : Nat.card F = Nat.card (fixOf α) * 2 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ((proj 2 K).subgroupComap (fixOf α)).ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
        ((proj 2 K).subgroupComap_surjective (fixOf α) proj_surjective)).toEquiv, hkc2]
  have c3 : Nat.card (twistHom θ hθα).range ∣ 2 := by
    have := Subgroup.card_subgroup_dvd_card (twistHom θ hθα).range
    rwa [card_spScalars h2] at this
  have : Nat.card (fixOf α) * 2 ∣ Nat.card (fixOf θ) * 2 := by
    rw [← c2, c1]
    exact Nat.mul_dvd_mul_left _ c3
  exact Nat.dvd_of_mul_dvd_mul_right two_pos this

theorem eq_zero_of_mul_self_qAlg (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0)
    {w : QuadraticAlgebra K a 0} (hw : w * w = 0) : w = 0 := by
  have hre := congrArg QuadraticAlgebra.re hw
  have him := congrArg QuadraticAlgebra.im hw
  simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_zero,
    QuadraticAlgebra.im_zero, zero_mul, add_zero] at hre him
  have hxy : w.re * w.im = 0 := by
    have : (2 : K) * (w.re * w.im) = 0 := by linear_combination him
    exact (mul_eq_zero.mp this).resolve_left h2
  rcases mul_eq_zero.mp hxy with hx | hy
  · have : a * (w.im * w.im) = 0 := by rw [hx] at hre; linear_combination hre
    have hy : w.im = 0 := mul_self_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ha)
    exact QuadraticAlgebra.ext hx hy
  · have : w.re * w.re = 0 := by rw [hy] at hre; linear_combination hre
    exact QuadraticAlgebra.ext (mul_self_eq_zero.mp this) hy

theorem isReduced_qAlg (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) :
    IsReduced (QuadraticAlgebra K a 0) :=
  (isReduced_iff_pow_one_lt 2 one_lt_two).mpr fun w hw =>
    eq_zero_of_mul_self_qAlg h2 ha (by rwa [← pow_two])

theorem eq_one_of_pow_char_qAlg {p : ℕ} [Fact p.Prime] [CharP K p] (h2 : (2 : K) ≠ 0) {a : K}
    (ha : a ≠ 0) {u : (QuadraticAlgebra K a 0)ˣ} (hu : u ^ p = 1) : u = 1 := by
  have : CharP (QuadraticAlgebra K a 0) p :=
    charP_of_injective_algebraMap (algebraMap K (QuadraticAlgebra K a 0)).injective p
  have : IsReduced (QuadraticAlgebra K a 0) := isReduced_qAlg h2 ha
  have h1 : ((u : QuadraticAlgebra K a 0) - 1) ^ p = 0 := by
    rw [sub_pow_char, one_pow, ← Units.val_pow_eq_pow_val, hu, Units.val_one, sub_self]
  have h3 := IsReduced.eq_zero _ ⟨p, h1⟩
  exact Units.ext (sub_eq_zero.mp h3)

variable {a : K}

theorem gI_mem_fixI (ha : a ≠ 0) (k : Matrix.SpecialLinearGroup (Fin 2) K) :
    gI ha k ∈ fixI a ha :=
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.gI_mem_fixI ha k

theorem gI_injective (ha : a ≠ 0) : Function.Injective (gI ha) := by
  intro k k' h
  have h' := congrArg (fun x : StatedSp 2 K => ((x : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) h
  simp only [coe_gI] at h'
  exact Subtype.ext (kron_one_injective (bA_conj_eq_iff ha h'))

theorem detI_gI (ha : a ≠ 0) (k : Matrix.SpecialLinearGroup (Fin 2) K) :
    detI ha ⟨gI ha k, gI_mem_fixI ha k⟩ = 1 :=
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.detI_gI ha k

theorem card_fixI [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (h2 : (2 : K) ≠ 0)
    (ha : a ≠ 0) : ∃ m, ¬ p ∣ m ∧
      Nat.card (fixI a ha) = Nat.card K * (Nat.card K ^ 2 - 1) * m := by
  set φ := (detI ha).toHomUnits with hφ
  have hker : φ.ker = ((gI ha).range).subgroupOf (fixI a ha) := by
    ext g
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro h
      exact mem_range_gI_of_detI ha h2 g (congrArg Units.val h)
    · rintro ⟨k, hk⟩
      apply Units.ext
      change detI ha g = 1
      have : g = ⟨gI ha k, gI_mem_fixI ha k⟩ := Subtype.ext hk.symm
      rw [this, detI_gI]
  have hle : (gI ha).range ≤ fixI a ha := by
    rintro _ ⟨k, rfl⟩
    exact gI_mem_fixI ha k
  refine ⟨Nat.card φ.range, ?_, ?_⟩
  · intro hpd
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := φ.range) p hpd
    have hu1 : (u : (QuadraticAlgebra K a 0)ˣ) ^ p = 1 := by
      rw [← Subgroup.coe_pow, ← hu, pow_orderOf_eq_one, Subgroup.coe_one]
    have := eq_one_of_pow_char_qAlg h2 ha hu1
    have hu' : u = 1 := Subtype.ext this
    rw [hu', orderOf_one] at hu
    exact (Fact.out : p.Prime).one_lt.ne hu
  · have hkc : Nat.card φ.ker = Nat.card K * (Nat.card K ^ 2 - 1) := by
      rw [hker, Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv,
        ← Nat.card_congr (MonoidHom.ofInjective (gI_injective ha)).toEquiv, card_SL2]
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hkc, mul_comm]

theorem conj_inv_conjSp (A B : gsp 2 K) (g : StatedSp 2 K)
    (h : (A : GL (Fin 2 ⊕ Fin 2) K) * (g : GL (Fin 2 ⊕ Fin 2) K) =
      (g : GL (Fin 2 ⊕ Fin 2) K) * (B : GL (Fin 2 ⊕ Fin 2) K)) (x : StatedSp 2 K) :
    (MulAut.conj g)⁻¹ (conjSp 2 K A x) = conjSp 2 K B ((MulAut.conj g)⁻¹ x) := by
  rw [MulAut.conj_inv_apply, MulAut.conj_inv_apply]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_conjSp, coe_conjSp,
    Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  have hA : (A : GL (Fin 2 ⊕ Fin 2) K) =
      (g : GL (Fin 2 ⊕ Fin 2) K) * (B : GL (Fin 2 ⊕ Fin 2) K) * (g : GL (Fin 2 ⊕ Fin 2) K)⁻¹ := by
    rw [← h, mul_inv_cancel_right]
  rw [hA]
  group

theorem mul_self_of_rep (A : gsp 2 K) (d : Kˣ)
    (hd : (A : GL (Fin 2 ⊕ Fin 2) K) *
        CatalogueBHigherLinearField.glFieldEquiv (Fin 2 ⊕ Fin 2) (1 : K ≃+* K)
          (A : GL (Fin 2 ⊕ Fin 2) K) =
      GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) d) :
    ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = (d : K) • 1 := by
  have h1 := congrArg (fun M : GL (Fin 2 ⊕ Fin 2) K =>
    (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hd
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at h1
  have h1' : ((CatalogueBHigherLinearField.glFieldEquiv (Fin 2 ⊕ Fin 2) (1 : K ≃+* K)
      (A : GL (Fin 2 ⊕ Fin 2) K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    ext i j
    rfl
  rw [h1'] at h1
  rw [h1, Matrix.smul_one_eq_diagonal]
  rfl

theorem eq_or_eq_neg_multiplier (A : gsp 2 K) {d : K}
    (hAA : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = d • 1) :
    d = multiplierUnit A ∨ d = -(multiplierUnit A : K) := by
  set Am := ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
  have hμ : Amᵀ * formJ 2 K * Am = (multiplierUnit A : K) • formJ 2 K := multiplierUnit_spec A
  have e1 : (Am * Am)ᵀ * formJ 2 K * (Am * Am) =
      ((multiplierUnit A : K) * multiplierUnit A) • formJ 2 K := by
    rw [transpose_mul, show Amᵀ * Amᵀ * formJ 2 K * (Am * Am) =
      Amᵀ * (Amᵀ * formJ 2 K * Am) * Am by simp only [Matrix.mul_assoc], hμ,
      Matrix.mul_smul, Matrix.smul_mul, hμ, smul_smul]
  rw [hAA, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.one_mul,
    Matrix.mul_smul, Matrix.mul_one, smul_smul] at e1
  exact mul_self_eq_mul_self_iff.mp (smul_formJ_injective 2 e1)

theorem not_sq_dvd_typeI {p f q m : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hq : q = p ^ f)
    (hm : ¬ p ∣ m) : ¬ q ^ 2 ∣ q * (q ^ 2 - 1) * m := by
  intro h
  have hq0 : 0 < q := by rw [hq]; exact pow_pos hp.pos f
  have hpq : p ∣ q := by rw [hq]; exact dvd_pow_self p (by omega)
  have h1 : q ∣ (q ^ 2 - 1) * m := by
    have h' : q * q ∣ q * ((q ^ 2 - 1) * m) := by rw [← sq, ← mul_assoc]; exact h
    exact Nat.dvd_of_mul_dvd_mul_left hq0 h'
  rcases (Nat.Prime.dvd_mul hp).mp (hpq.trans h1) with h2 | h2
  · have h3 : p ∣ q ^ 2 := hpq.trans (dvd_pow_self q two_ne_zero)
    have h4 : p ∣ q ^ 2 - (q ^ 2 - 1) := Nat.dvd_sub h3 h2
    have h5 : q ^ 2 - (q ^ 2 - 1) = 1 := by
      have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq0
      omega
    rw [h5] at h4
    exact hp.one_lt.ne' (Nat.dvd_one.mp h4)
  · exact hm h2

theorem not_dvd_field {k : ℕ} (hk : Odd k) (hk3 : 3 ≤ k) :
    ¬ (k ^ 2) ^ 2 * (((k ^ 2) ^ 2) ^ 2 - 1) / 2 ∣ k ^ 4 * ((k ^ 2 - 1) * (k ^ 4 - 1)) := by
  intro h
  have e1 : ((k ^ 2) ^ 2) ^ 2 = k ^ 8 := by ring
  have e2 : (k ^ 2) ^ 2 = k ^ 4 := by ring
  rw [e1, e2] at h
  have hk0 : 0 < k := by omega
  obtain ⟨j, hj⟩ : ∃ j, k ^ 4 + 1 = 2 * j := by
    obtain ⟨r, rfl⟩ := hk
    have : Odd ((2 * r + 1) ^ 4) := (odd_two_mul_add_one r).pow
    obtain ⟨s, hs⟩ := this
    exact ⟨s + 1, by omega⟩
  have h41 : 1 ≤ k ^ 4 := Nat.one_le_pow 4 k hk0
  have h81 : 1 ≤ k ^ 8 := Nat.one_le_pow 8 k hk0
  have h8 : k ^ 8 - 1 = (k ^ 4 - 1) * (k ^ 4 + 1) := by
    zify [h41, h81]
    ring
  have e : k ^ 4 * (k ^ 8 - 1) / 2 = (k ^ 4 * (k ^ 4 - 1)) * j := by
    rw [h8, hj, show k ^ 4 * ((k ^ 4 - 1) * (2 * j)) = (k ^ 4 * (k ^ 4 - 1) * j) * 2 by ring,
      Nat.mul_div_cancel _ two_pos]
  rw [e, show k ^ 4 * ((k ^ 2 - 1) * (k ^ 4 - 1)) = (k ^ 4 * (k ^ 4 - 1)) * (k ^ 2 - 1) by ring]
    at h
  have hk4 : 1 < k ^ 4 := Nat.one_lt_pow (by norm_num) (by omega)
  have hpos : 0 < k ^ 4 * (k ^ 4 - 1) := Nat.mul_pos (by positivity) (by omega)
  have h2 := Nat.dvd_of_mul_dvd_mul_left hpos h
  have hk2 : 1 < k ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
  have h3 := Nat.le_of_dvd (by omega) h2
  set t := k ^ 2 with ht
  have htt : k ^ 4 = t * t := by rw [ht]; ring
  rw [htt] at hj
  have h5 : j + 1 ≤ t := by omega
  have h6 : (t : ℤ) * t + 1 = 2 * j := by exact_mod_cast hj
  have h7 : (j : ℤ) + 1 ≤ t := by exact_mod_cast h5
  nlinarith [sq_nonneg ((t : ℤ) - 1)]

theorem exists_typeII_of_admissible {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    [Finite K] (hK : Nat.card K = p ^ f) (α : MulAut (StatedProj (StatedSp 2 K)))
    (hα2 : α * α = 1) (hout : α ∉ (MulAut.conj : StatedProj (StatedSp 2 K) →* _).range)
    (hdvd : (p ^ f) ^ 2 * (((p ^ f) ^ 2) ^ 2 - 1) / 2 ∣ Nat.card (fixOf α)) :
    ∃ A : gsp 2 K, α = conjAut 2 K A ∧ ∃ d : K, d ≠ 0 ∧ (∀ l : K, l ^ 2 ≠ d) ∧
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = d • 1 ∧
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * formJ 2 K *
        ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
          d • formJ 2 K := by
  have hodd : Odd (Nat.card K) := odd_card_of_card_eq hp hp2 hK
  have hqodd : Odd (p ^ f) := hK ▸ hodd
  have h2 := two_ne_zero_of_odd_card hodd
  have : Fact p.Prime := ⟨hp⟩
  have hchar : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hrc : ringChar K ≠ 2 := by
    intro h
    apply h2
    have := ringChar.Nat.cast_ringChar (R := K)
    rw [h] at this
    exact_mod_cast this
  have hα1 : α ≠ 1 := fun h => hout ⟨1, by rw [h, map_one]⟩
  have hq2 : (p ^ f) ^ 2 ∣ (p ^ f) ^ 2 * (((p ^ f) ^ 2) ^ 2 - 1) / 2 := by
    obtain ⟨j, hj⟩ : 2 ∣ ((p ^ f) ^ 2) ^ 2 - 1 := by
      have h4 : Odd (((p ^ f) ^ 2) ^ 2) := (hqodd.pow).pow
      obtain ⟨r, hr⟩ := h4
      exact ⟨r, by omega⟩
    rw [hj, show (p ^ f) ^ 2 * (2 * j) = ((p ^ f) ^ 2 * j) * 2 by ring,
      Nat.mul_div_cancel _ two_pos]
    exact dvd_mul_right _ _
  obtain ⟨A, σ, hα, hσ2, ⟨d, hd⟩, -, hfield⟩ :=
    (CatalogueBSymplecticRepresentation.odd_symplectic_automorphism_semilinear_representation
      hrc le_rfl).2.2 α hα2 hα1
  by_cases hσ : σ = 1
  · subst hσ
    have hα' : α = conjAut 2 K A := by rw [hα, map_one, mul_one]
    have hAA := mul_self_of_rep A d hd
    have hμ := multiplierUnit_spec A
    by_cases hsq : ∃ l : K, l ^ 2 = (multiplierUnit A : K)
    · exfalso
      obtain ⟨l, hl⟩ := hsq
      have hl0 : l ≠ 0 := by
        rintro rfl
        rw [zero_pow two_ne_zero] at hl
        exact (multiplierUnit A).ne_zero hl.symm
      set Am := ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
      have hA'sp : (l⁻¹ • Am)ᵀ * formJ 2 K * (l⁻¹ • Am) = formJ 2 K := by
        rw [transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, hμ, smul_smul,
          smul_smul, ← hl]
        rw [show l⁻¹ * l⁻¹ * l ^ 2 = 1 by field_simp, one_smul]
      set A' : StatedSp 2 K := toSp (l⁻¹ • Am) hA'sp with hA'def
      have hAz : (A : GL (Fin 2 ⊕ Fin 2) K) =
          GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) (Units.mk0 l hl0) *
            (A' : GL (Fin 2 ⊕ Fin 2) K) := by
        apply Units.ext
        rw [Units.val_mul, GeneralLinearGroup.coe_scalar, hA'def, coe_toSp, Units.val_mk0,
          Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
          Matrix.one_mul, smul_smul, mul_inv_cancel₀ hl0, one_smul]
      exact hout ⟨proj 2 K A', (hα'.trans (conjAut_eq_conj_of_scalar_mul A _ A' hAz)).symm⟩
    · push Not at hsq
      rcases eq_or_eq_neg_multiplier A hAA with hdm | hdm
      · refine ⟨A, hα', d, d.ne_zero, fun l => by rw [hdm]; exact hsq l, hAA, ?_⟩
        rw [hdm]
        exact hμ
      · exfalso
        have ha : (d : K) ≠ 0 := d.ne_zero
        have hA : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ *
            formJ 2 K * ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
              (-(d : K)) • formJ 2 K := by
          rw [hμ, hdm, neg_neg]
        obtain ⟨g, hg⟩ := exists_frame_typeI h2 ha hA hAA
        have hGL : (A : GL (Fin 2 ⊕ Fin 2) K) * (g : GL (Fin 2 ⊕ Fin 2) K) =
            (g : GL (Fin 2 ⊕ Fin 2) K) * ((aIgsp ha : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) := by
          apply Units.ext
          rw [Units.val_mul, Units.val_mul, coe_aIgsp]
          exact hg
        have hfixmap := map_fixOf_of_comm (conj_inv_conjSp A (aIgsp ha) g hGL)
        have hcardA : Nat.card (fixOf (conjSp 2 K A)) = Nat.card (fixI (d : K) ha) := by
          rw [Nat.card_congr ((fixOf (conjSp 2 K A)).equivMapOfInjective
            ((MulAut.conj g)⁻¹ : MulAut (StatedSp 2 K)).toMonoidHom
            ((MulAut.conj g)⁻¹ : MulAut (StatedSp 2 K)).injective).toEquiv, hfixmap]
        have hθα : ∀ g, α (proj 2 K g) = proj 2 K (conjSp 2 K A g) := fun g => by
          rw [hα', conjAut_proj]
        have hdv := card_fixOf_dvd h2 (conjSp 2 K A) hθα
        obtain ⟨m, hm, hcm⟩ := card_fixI (p := p) h2 ha
        rw [hcardA, hcm, hK] at hdv
        exact not_sq_dvd_typeI hp hf rfl hm ((hq2.trans hdvd).trans hdv)
  · exfalso
    have hθα : ∀ g, α (proj 2 K g) = proj 2 K ((conjSp 2 K A * fieldSp 2 K σ) g) := fun g => by
      rw [hα]
      rfl
    have hdv := card_fixOf_dvd h2 (conjSp 2 K A * fieldSp 2 K σ) hθα
    obtain ⟨-, hcard⟩ := fixOf_conjSp_fieldSp hodd A σ hσ2 hσ d hd
    rw [hcard] at hdv
    obtain ⟨hKk, -⟩ := hfield hσ
    have hk : Nat.card {c : K // σ c = c} =
        Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun c =>
        (CatalogueBLinearTwoDescent.mem_fixedSubfield K σ c).symm)
    rw [hk, hK] at hKk
    set k := Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ)
    have hkodd : Odd k := (Nat.odd_mul.mp (by rw [← sq, ← hKk]; exact hqodd)).1
    have hk3 : 3 ≤ k := by
      have hq3 : 3 ≤ p ^ f := by
        have := hp.two_le
        have h3 : 3 ≤ p := by omega
        exact h3.trans (Nat.le_self_pow (by omega) p)
      by_contra hlt
      push Not at hlt
      interval_cases k <;> simp_all
    rw [hKk] at hdvd
    exact not_dvd_field hkodd hk3 (hdvd.trans hdv)

end CFSG.ComponentClassification.CatFactsSp4
