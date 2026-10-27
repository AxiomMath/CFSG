module

public import CFSG.RankThree.PartTwo.KFacts.AutKindsCentral
import CFSG.RankThree.PartTwo.KFacts.AutPSUScalar
import CFSG.RankThree.PartTwo.KFacts.AutPSUDet

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitary

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartTwo.KFacts

variable {p f : ℕ} {K : Type} [Field K]

theorem norm_eq_one_of_pow_three (h : UnitaryFieldData p f K) (h3 : 3 ∣ p ^ f + 1) (c : Kˣ)
    (hc : h.norm ((c ^ 3 : Kˣ) : K) = 1) : h.norm (c : K) = 1 := by
  have := h.finite
  have hq : 1 < p ^ f := h.one_lt_pow
  have hn : ∀ x : Kˣ, h.norm (x : K) = 1 ↔ x ^ (p ^ f + 1) = 1 := fun x => by
    rw [h.norm_eq_pow, ← Units.val_pow_eq_pow_val, Units.val_eq_one]
  rw [hn] at hc ⊢
  have h1 : (c ^ (p ^ f + 1)) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact hc
  have h2 : (c ^ (p ^ f + 1)) ^ (p ^ f - 1) = 1 := by
    have hc1 : c ^ Nat.card Kˣ = 1 := pow_card_eq_one'
    rw [Nat.card_units, h.card_eq_sq] at hc1
    have hmul : (p ^ f + 1) * (p ^ f - 1) = (p ^ f) ^ 2 - 1 := by
      have := Nat.mul_self_sub_mul_self_eq (p ^ f) 1
      simpa [sq] using this.symm
    rw [← pow_mul, hmul]
    exact hc1
  have hcop : Nat.Coprime 3 (p ^ f - 1) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)
  have h4 : (c ^ (p ^ f + 1)) ^ Nat.gcd 3 (p ^ f - 1) = 1 := pow_gcd_eq_one.2 ⟨h1, h2⟩
  rwa [hcop.gcd_eq_one, pow_one] at h4

theorem scalar_mem_unitaryIsom3 (h : UnitaryFieldData p f K) {c : Kˣ} (hc : h.norm (c : K) = 1) :
    GeneralLinearGroup.scalar (Fin 3) c ∈ unitaryIsom3 h :=
  CFSG.RankThree.PartTwo.KFacts.scalar_mem_unitaryIsom3_of_norm hc

theorem norm_det_eq_one (h : UnitaryFieldData p f K) {B : GL (Fin 3) K} (hB : B ∈ unitaryIsom3 h) :
    h.norm (B : Matrix (Fin 3) (Fin 3) K).det = 1 :=
  CFSG.RankThree.PartTwo.KFacts.norm_det_of_mem_unitaryIsom3 hB

theorem exists_scalar_of_suConj_eq_one (h : UnitaryFieldData p f K) {B : unitaryIsom3 h}
    (hB : suConj h B = 1) :
    ∃ c : Kˣ, h.norm (c : K) = 1 ∧ (B : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) c := by
  have h1 : psuConj h B * psuField h 1 = 1 := by
    rw [map_one, mul_one]
    ext x
    induction x using QuotientGroup.induction_on with
    | H g => rw [psuConj_mk, hB]; rfl
  exact (eq_one_of_psuConj_mul_psuField_eq_one B 1 h1).2

theorem coe_scalar_eq_smul (c : Kˣ) :
    ((GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (c : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem suConj_scalar (h : UnitaryFieldData p f K) {c : Kˣ} (hc : h.norm (c : K) = 1) :
    suConj h ⟨GeneralLinearGroup.scalar (Fin 3) c, scalar_mem_unitaryIsom3 h hc⟩ = 1 := by
  refine MulEquiv.ext fun t => ?_
  apply Subtype.ext
  rw [coe_suConj]
  change GeneralLinearGroup.scalar (Fin 3) c * (t : GL (Fin 3) K) *
    (GeneralLinearGroup.scalar (Fin 3) c)⁻¹ = t
  rw [← (commute_scalar c (t : GL (Fin 3) K)).eq, mul_inv_cancel_right]

theorem exists_suConj_of_pow_three_eq_one (h : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    (hσ : ∀ σ : K ≃+* K, σ ^ 3 = 1 → σ = 1) {θ : MulAut (unitarySU p f K 3)} (hθ : θ ^ 3 = 1) :
    ∃ B : unitaryIsom3 h, θ = suConj h B := by
  set α : MulAut (unitaryPSU h 3) :=
    MulAut.congr (suCenterEquiv h hq) (centerDescend _ θ) with hα
  have hα3 : α ^ 3 = 1 := by rw [hα, ← map_pow, ← map_pow, hθ, map_one, map_one]
  have hD : α ∈ (psuConj h).range := by
    by_contra hD
    obtain ⟨σ, hσ3, -⟩ := unitary_order_three_field_descent hq α hα3 hD
    have h1 : σ ^ 3 = 1 := by rw [← hσ3]; exact pow_orderOf_eq_one σ
    rw [hσ σ h1, orderOf_one] at hσ3
    omega
  obtain ⟨B, hB⟩ := hD
  refine ⟨B, ?_⟩
  have hdesc : MulAut.congr (suCenterEquiv h hq) (centerDescend _ (suConj h B)) = psuConj h B := by
    ext y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    rfl
  have hdesc' : centerDescend _ θ = centerDescend _ (suConj h B) :=
    (MulAut.congr (suCenterEquiv h hq)).injective (by rw [← hα, hdesc, hB])
  have : Group.IsPerfect (unitarySU p f K 3) := isPerfect_unitarySU_three h hq
  have hτ : θ * (suConj h B)⁻¹ = 1 := by
    apply eq_one_of_forall_mul_inv_mem_center
    intro s
    have h1 := congrArg (fun τ : MulAut (unitarySU p f K 3 ⧸ Subgroup.center _) =>
      τ (((suConj h B)⁻¹ s : unitarySU p f K 3) : unitarySU p f K 3 ⧸ Subgroup.center _)) hdesc'
    simp only [centerDescend_mk] at h1
    rw [MulAut.apply_inv_self] at h1
    exact QuotientGroup.eq.1 h1.symm
  exact mul_inv_eq_one.1 hτ

theorem exists_scalar_pow_three (h : UnitaryFieldData p f K) {B : unitaryIsom3 h}
    (hB : suConj h B ^ 3 = 1) :
    ∃ c : Kˣ, h.norm (c : K) = 1 ∧
      (B : GL (Fin 3) K) ^ 3 = GeneralLinearGroup.scalar (Fin 3) c := by
  have h1 : suConj h (B ^ 3) = 1 := by rw [map_pow]; exact hB
  obtain ⟨c, hc, hcB⟩ := exists_scalar_of_suConj_eq_one h h1
  exact ⟨c, hc, by simpa using hcB⟩

theorem card_units_quotient_cubes_dvd_three [Finite K] :
    Nat.card (Kˣ ⧸ (powMonoidHom 3 : Kˣ →* Kˣ).range) ∣ 3 := by
  have : IsCyclic (Kˣ ⧸ (powMonoidHom 3 : Kˣ →* Kˣ).range) :=
    isCyclic_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  rw [← IsCyclic.exponent_eq_card]
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
  induction x using QuotientGroup.induction_on with
  | H u =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨u, rfl⟩

theorem exists_inner_of_index (h : UnitaryFieldData p f K) (h3 : 3 ∣ p ^ f + 1)
    {A : Type} [Group A] [Finite A] (φ : A →* MulAut (unitarySU p f K 3))
    (hφ : ∀ a, ∃ B : unitaryIsom3 h, φ a = suConj h B)
    (hcard : 3 * Nat.card φ.ker < Nat.card A) :
    ∃ a : A, a ∉ φ.ker ∧ ∃ s : unitarySU p f K 3, ∀ t, φ a t = s * t * s⁻¹ := by
  classical
  have := h.finite
  choose g hg using hφ
  set H : Subgroup Kˣ := (powMonoidHom 3 : Kˣ →* Kˣ).range with hH
  let D : unitaryIsom3 h →* Kˣ ⧸ H :=
    (QuotientGroup.mk' H).comp (GeneralLinearGroup.det.comp (unitaryIsom3 h).subtype)
  have hD : ∀ B₁ B₂ : unitaryIsom3 h, suConj h B₁ = suConj h B₂ → D B₁ = D B₂ := by
    intro B₁ B₂ hB
    have h1 : suConj h (B₁⁻¹ * B₂) = 1 := by rw [map_mul, map_inv, hB, inv_mul_cancel]
    obtain ⟨c, -, hcB⟩ := exists_scalar_of_suConj_eq_one h h1
    have hc1 : D (B₁⁻¹ * B₂) = 1 := by
      simp only [D, MonoidHom.comp_apply, Subgroup.coe_subtype, hcB,
        GeneralLinearGroup.det_scalar, QuotientGroup.mk'_apply]
      rw [QuotientGroup.eq_one_iff]
      exact ⟨c, by simp⟩
    have hB₂ : B₂ = B₁ * (B₁⁻¹ * B₂) := by group
    rw [hB₂, map_mul, hc1, mul_one]
  let Δ : A →* Kˣ ⧸ H :=
    { toFun := fun a => D (g a)
      map_one' := by
        rw [hD (g 1) 1 (by rw [← hg 1, map_one, map_one]), map_one]
      map_mul' := by
        intro a b
        rw [← map_mul]
        apply hD
        rw [← hg (a * b), map_mul, hg a, hg b, map_mul] }
  have hindex : Nat.card A ≤ 3 * Nat.card Δ.ker := by
    have h1 : Nat.card Δ.ker * Δ.ker.index = Nat.card A := Subgroup.card_mul_index _
    have h2 : Δ.ker.index = Nat.card Δ.range := Subgroup.index_ker Δ
    have h3 : Nat.card Δ.range ≤ Nat.card (Kˣ ⧸ H) :=
      Nat.card_le_card_of_injective _ Subtype.val_injective
    have h4 : Nat.card (Kˣ ⧸ H) ≤ 3 :=
      Nat.le_of_dvd (by norm_num) card_units_quotient_cubes_dvd_three
    calc Nat.card A = Nat.card Δ.ker * Δ.ker.index := h1.symm
      _ ≤ Nat.card Δ.ker * 3 := Nat.mul_le_mul_left _ (h2 ▸ h3.trans h4)
      _ = 3 * Nat.card Δ.ker := mul_comm _ _
  have hex : ∃ a ∈ Δ.ker, a ∉ φ.ker := by
    by_contra hne
    have hle : Δ.ker ≤ φ.ker := fun a ha => by
      by_contra ha'
      exact hne ⟨a, ha, ha'⟩
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨a, haΔ, haφ⟩ := hex
  refine ⟨a, haφ, ?_⟩
  have hdet : GeneralLinearGroup.det ((g a : unitaryIsom3 h) : GL (Fin 3) K) ∈ H := by
    have h0 : D (g a) = 1 := haΔ
    simpa [D, QuotientGroup.eq_one_iff] using h0
  obtain ⟨u, hu⟩ := hdet
  have hu3 : u ^ 3 = GeneralLinearGroup.det ((g a : unitaryIsom3 h) : GL (Fin 3) K) := hu
  have hNu : h.norm (u : K) = 1 := by
    refine norm_eq_one_of_pow_three h h3 u ?_
    rw [hu3, Matrix.GeneralLinearGroup.val_det_apply]
    exact norm_det_eq_one h (g a).2
  have hNinv : h.norm ((u⁻¹ : Kˣ) : K) = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv_eq h, hNu, inv_one]
  set sc : GL (Fin 3) K := GeneralLinearGroup.scalar (Fin 3) u⁻¹ with hsc
  have hB'mem : sc * ((g a : unitaryIsom3 h) : GL (Fin 3) K) ∈ unitaryIsom3 h :=
    mul_mem (scalar_mem_unitaryIsom3 h hNinv) (g a).2
  have hB'det : GeneralLinearGroup.det (sc * ((g a : unitaryIsom3 h) : GL (Fin 3) K)) = 1 := by
    rw [map_mul, hsc, GeneralLinearGroup.det_scalar, ← hu3]
    simp
  have hB'det' : (((sc * ((g a : unitaryIsom3 h) : GL (Fin 3) K)) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).det = 1 := by
    have := congrArg (fun x : Kˣ => (x : K)) hB'det
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
  refine ⟨⟨sc * ((g a : unitaryIsom3 h) : GL (Fin 3) K),
    (mem_unitarySU_iff h).2 ⟨hB'det', mem_unitaryIsom3.1 hB'mem⟩⟩, fun t => ?_⟩
  have hcomm : ∀ x : GL (Fin 3) K, sc * x = x * sc := fun x => ((commute_scalar u⁻¹ x).eq).symm
  rw [hg a]
  apply Subtype.ext
  rw [coe_suConj]
  change ((g a : unitaryIsom3 h) : GL (Fin 3) K) * (t : GL (Fin 3) K) *
      ((g a : unitaryIsom3 h) : GL (Fin 3) K)⁻¹ =
    (sc * ((g a : unitaryIsom3 h) : GL (Fin 3) K)) * (t : GL (Fin 3) K) *
      (sc * ((g a : unitaryIsom3 h) : GL (Fin 3) K))⁻¹
  calc ((g a : unitaryIsom3 h) : GL (Fin 3) K) * (t : GL (Fin 3) K) *
        ((g a : unitaryIsom3 h) : GL (Fin 3) K)⁻¹
      = sc * (((g a : unitaryIsom3 h) : GL (Fin 3) K) * (t : GL (Fin 3) K) *
        ((g a : unitaryIsom3 h) : GL (Fin 3) K)⁻¹) * sc⁻¹ := by
        rw [hcomm (((g a : unitaryIsom3 h) : GL (Fin 3) K) * (t : GL (Fin 3) K) *
          ((g a : unitaryIsom3 h) : GL (Fin 3) K)⁻¹)]
        group
    _ = _ := by group

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitary
