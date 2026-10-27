module

public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryHermitian

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {E : Type} [Field E] {V : Type*} [AddCommGroup V] [Module E V]

section Scalars

variable (h : UnitaryFieldData p f E) (B : V →ₛₗ[h.bar] V →ₗ[E] E)

theorem norm_mul_eq' (a b : E) : h.norm (a * b) = h.norm a * h.norm b := by
  simp only [UnitaryFieldData.norm, map_mul]
  ring

theorem ne_zero_of_norm_eq_one {c : E} (hc : h.norm c = 1) : c ≠ 0 := fun h0 => by
  rw [h0, UnitaryFieldData.norm, zero_mul] at hc
  exact zero_ne_one hc

@[expose] def sesqNormOneScalars : Subgroup (sesqUnitaryGroup B) where
  carrier := {g | ∃ c : E, h.norm c = 1 ∧
    ((g : LinearMap.GeneralLinearGroup E V) : Module.End E V) = c • 1}
  one_mem' := ⟨1, by rw [UnitaryFieldData.norm, map_one, one_mul], by rw [one_smul]; rfl⟩
  mul_mem' := by
    rintro g g' ⟨c, hc, hg⟩ ⟨c', hc', hg'⟩
    refine ⟨c * c', by rw [norm_mul_eq', hc, hc', one_mul], ?_⟩
    change ((g : LinearMap.GeneralLinearGroup E V) : Module.End E V) *
      ((g' : LinearMap.GeneralLinearGroup E V) : Module.End E V) = _
    rw [hg, hg', smul_mul_smul_comm, one_mul]
  inv_mem' := by
    rintro g ⟨c, hc, hg⟩
    have hc0 := ne_zero_of_norm_eq_one h hc
    have hci : h.norm c⁻¹ = (h.norm c)⁻¹ := by
      simp only [UnitaryFieldData.norm, map_inv₀, mul_inv]
    refine ⟨c⁻¹, by rw [hci, hc, inv_one], ?_⟩
    change ((g⁻¹ : LinearMap.GeneralLinearGroup E V) : Module.End E V) = _
    calc ((g⁻¹ : LinearMap.GeneralLinearGroup E V) : Module.End E V) =
          (c⁻¹ • 1) * (((g : LinearMap.GeneralLinearGroup E V) : Module.End E V) *
            ((g⁻¹ : LinearMap.GeneralLinearGroup E V) : Module.End E V)) := by
          rw [hg, ← mul_assoc, smul_mul_smul_comm, inv_mul_cancel₀ hc0, one_mul, one_smul,
            one_mul]
      _ = c⁻¹ • 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

variable {h B} in
theorem mem_sesqNormOneScalars {g : sesqUnitaryGroup B} :
    g ∈ sesqNormOneScalars h B ↔ ∃ c : E, h.norm c = 1 ∧
      ((g : LinearMap.GeneralLinearGroup E V) : Module.End E V) = c • 1 :=
  Iff.rfl

instance sesqNormOneScalars_normal : (sesqNormOneScalars h B).Normal where
  conj_mem g hg x := by
    obtain ⟨c, hc, hg⟩ := hg
    refine ⟨c, hc, ?_⟩
    change ((x : LinearMap.GeneralLinearGroup E V) : Module.End E V) *
      ((g : LinearMap.GeneralLinearGroup E V) : Module.End E V) *
        ((x⁻¹ : LinearMap.GeneralLinearGroup E V) : Module.End E V) = _
    rw [hg, mul_smul_comm, mul_one, smul_mul_assoc, ← Units.val_mul, mul_inv_cancel,
      Units.val_one]

abbrev sesqProjUnitary : Type _ :=
  sesqUnitaryGroup B ⧸ sesqNormOneScalars h B

end Scalars

theorem exists_sq_eq_of_norm_eq_one (h : UnitaryFieldData p f E) (hp : p ≠ 2) {d : E}
    (hd : h.norm d = 1) : ∃ l : E, l ≠ 0 ∧ l ^ 2 = d := by
  obtain ⟨r, hr, hrd⟩ := h.exists_div_bar_eq hd
  obtain ⟨m, hm⟩ : Odd (p ^ f) := (h.prime.odd_of_ne_two hp).pow
  refine ⟨(r ^ m)⁻¹, inv_ne_zero (pow_ne_zero _ hr), ?_⟩
  rw [← hrd, UnitaryFieldData.bar_apply, hm]
  field_simp
  ring

theorem isCompl_ker_sub_one_ker_add_one (h2 : (2 : E) ≠ 0) {T : Module.End E V}
    (hT : T * T = 1) : IsCompl (LinearMap.ker (T - 1)) (LinearMap.ker (T + 1)) := by
  have hTT : ∀ v, T (T v) = v := fun v => by
    rw [← Module.End.mul_apply, hT, Module.End.one_apply]
  refine ⟨Submodule.disjoint_def.mpr fun v hv hv' => ?_,
    Submodule.codisjoint_iff_exists_add_eq.mpr fun v => ?_⟩
  · rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, hv] at hv'
    have h3 : (2 : E) • v = 0 := by rw [two_smul]; exact hv'
    exact (smul_eq_zero.mp h3).resolve_left h2
  · refine ⟨(2 : E)⁻¹ • (v + T v), (2 : E)⁻¹ • (v - T v), ?_, ?_, ?_⟩
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, map_smul, map_add, hTT,
        add_comm (T v), sub_self]
    · rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, map_smul, map_sub, hTT,
        ← smul_add, sub_add_sub_cancel', sub_self, smul_zero]
    · rw [← smul_add, add_add_sub_cancel, ← two_smul E v, smul_smul, inv_mul_cancel₀ h2,
        one_smul]

theorem apply_eq_of_mem_ker_sub_one {T : Module.End E V} {v : V}
    (hv : v ∈ LinearMap.ker (T - 1)) : T v = v := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
  exact hv

theorem apply_eq_neg_of_mem_ker_add_one {T : Module.End E V} {v : V}
    (hv : v ∈ LinearMap.ker (T + 1)) : T v = -v := by
  rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply] at hv
  exact eq_neg_of_add_eq_zero_left hv

section Lift

variable {h : UnitaryFieldData p f E} {B : V →ₛₗ[h.bar] V →ₗ[E] E}

theorem sesq_smul_smul (c : E) (v w : V) : B (c • v) (c • w) = h.norm c * B v w := by
  simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul,
    UnitaryFieldData.norm]
  ring

theorem norm_eq_one_of_scalar_mem [Nontrivial V] (hBl : B.SeparatingLeft) {g : sesqUnitaryGroup B}
    {c : E} (hg : ((g : LinearMap.GeneralLinearGroup E V) : Module.End E V) = c • 1) :
    h.norm c = 1 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨w, hw⟩ : ∃ w, B v w ≠ 0 := by
    by_contra! h0
    exact hv (hBl v h0)
  have h1 := g.2 v w
  rw [hg] at h1
  simp only [LinearMap.smul_apply, Module.End.one_apply] at h1
  rw [sesq_smul_smul] at h1
  have h2 : (h.norm c - 1) * B v w = 0 := by linear_combination h1
  exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hw)

theorem involution_lift_sq (hp : p ≠ 2) [Nontrivial V] (hBl : B.SeparatingLeft)
    {A : sesqUnitaryGroup B} (hA : orderOf (QuotientGroup.mk A : sesqProjUnitary h B) = 2) :
    (∃ l : E, l ≠ 0 ∧
      ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V) *
        ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V) = (l ^ 2) • 1 ∧
      (h.norm l = 1 ∨ h.norm l = -1)) ∧
    ∀ c : E, ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V) ≠ c • 1 := by
  have hsq : (QuotientGroup.mk (A * A) : sesqProjUnitary h B) = 1 := by
    rw [QuotientGroup.mk_mul, ← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hA])
  obtain ⟨d, hd, hAA⟩ := (QuotientGroup.eq_one_iff _).mp hsq
  obtain ⟨l, hl0, hld⟩ := exists_sq_eq_of_norm_eq_one h hp hd
  refine ⟨⟨l, hl0, ?_, ?_⟩, fun c hc => ?_⟩
  · rw [hld]
    exact hAA
  · have h1 : h.norm l * h.norm l = 1 := by
      rw [← norm_mul_eq', ← pow_two, hld, hd]
    exact mul_self_eq_one_iff.mp h1
  · have hcN := norm_eq_one_of_scalar_mem hBl hc
    have h1 : (QuotientGroup.mk A : sesqProjUnitary h B) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨c, hcN, hc⟩
    rw [h1, orderOf_one] at hA
    exact absurd hA (by norm_num)

end Lift

section Eigen

variable {h : UnitaryFieldData p f E} {B : V →ₛₗ[h.bar] V →ₗ[E] E}

theorem two_ne_zero_of_odd (h : UnitaryFieldData p f E) (hp : p ≠ 2) : (2 : E) ≠ 0 := by
  have := h.charP
  intro h2
  have h3 : ((2 : ℕ) : E) = 0 := by exact_mod_cast h2
  rw [CharP.cast_eq_zero_iff E p] at h3
  exact hp ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).mp h3)

@[expose] def invSMulOp (l : E) (A : Module.End E V) : Module.End E V :=
  l⁻¹ • A

theorem invSMulOp_mul_self {l : E} (hl0 : l ≠ 0) {A : Module.End E V}
    (hAA : A * A = (l ^ 2) • 1) : invSMulOp l A * invSMulOp l A = 1 := by
  rw [invSMulOp, smul_mul_smul_comm, hAA, smul_smul,
    show l⁻¹ * l⁻¹ * l ^ 2 = 1 by field_simp, one_smul]

theorem sesq_invSMulOp (l : E) (A : sesqUnitaryGroup B) (v w : V) :
    B (invSMulOp l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V) v)
      (invSMulOp l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V) w) =
      (h.norm l)⁻¹ * B v w := by
  rw [invSMulOp, LinearMap.smul_apply, LinearMap.smul_apply, sesq_smul_smul, A.2 v w]
  congr 1
  simp only [UnitaryFieldData.norm, map_inv₀, mul_inv]

theorem sesq_eq_zero_of_eigen_one (h2 : (2 : E) ≠ 0) {T : Module.End E V}
    (hT : ∀ v w, B (T v) (T w) = B v w) {v w : V} (hv : v ∈ LinearMap.ker (T - 1))
    (hw : w ∈ LinearMap.ker (T + 1)) : B v w = 0 := by
  have h1 := hT v w
  rw [apply_eq_of_mem_ker_sub_one hv, apply_eq_neg_of_mem_ker_add_one hw, map_neg] at h1
  have h3 : (2 : E) * B v w = 0 := by linear_combination -h1
  exact (mul_eq_zero.mp h3).resolve_left h2

theorem sesq_eq_zero_of_eigen_neg_plus (h2 : (2 : E) ≠ 0) {T : Module.End E V}
    (hT : ∀ v w, B (T v) (T w) = -B v w) {v w : V} (hv : v ∈ LinearMap.ker (T - 1))
    (hw : w ∈ LinearMap.ker (T - 1)) : B v w = 0 := by
  have h1 := hT v w
  rw [apply_eq_of_mem_ker_sub_one hv, apply_eq_of_mem_ker_sub_one hw] at h1
  have h3 : (2 : E) * B v w = 0 := by linear_combination h1
  exact (mul_eq_zero.mp h3).resolve_left h2

theorem sesq_eq_zero_of_eigen_neg_minus (h2 : (2 : E) ≠ 0) {T : Module.End E V}
    (hT : ∀ v w, B (T v) (T w) = -B v w) {v w : V} (hv : v ∈ LinearMap.ker (T + 1))
    (hw : w ∈ LinearMap.ker (T + 1)) : B v w = 0 := by
  have h1 := hT v w
  rw [apply_eq_neg_of_mem_ker_add_one hv, apply_eq_neg_of_mem_ker_add_one hw] at h1
  simp only [map_neg, LinearMap.neg_apply, neg_neg] at h1
  have h3 : (2 : E) * B v w = 0 := by linear_combination h1
  exact (mul_eq_zero.mp h3).resolve_left h2

theorem eigen_ne_bot (h2 : (2 : E) ≠ 0) {l : E} (hl0 : l ≠ 0) {A : Module.End E V}
    (hAA : A * A = (l ^ 2) • 1) (hA : ∀ c : E, A ≠ c • 1) :
    LinearMap.ker (invSMulOp l A - 1) ≠ ⊥ ∧ LinearMap.ker (invSMulOp l A + 1) ≠ ⊥ := by
  have hc := isCompl_ker_sub_one_ker_add_one h2 (invSMulOp_mul_self hl0 hAA)
  have hAT : ∀ v, A v = l • invSMulOp l A v := fun v => by
    rw [invSMulOp, LinearMap.smul_apply, smul_smul, mul_inv_cancel₀ hl0, one_smul]
  constructor
  · intro h0
    have htop : LinearMap.ker (invSMulOp l A + 1) = ⊤ := by
      have := hc.sup_eq_top
      rwa [h0, bot_sup_eq] at this
    refine hA (-l) (LinearMap.ext fun v => ?_)
    have hv : v ∈ LinearMap.ker (invSMulOp l A + 1) := by rw [htop]; exact Submodule.mem_top
    rw [hAT, apply_eq_neg_of_mem_ker_add_one hv, LinearMap.smul_apply, Module.End.one_apply,
      smul_neg, neg_smul]
  · intro h0
    have htop : LinearMap.ker (invSMulOp l A - 1) = ⊤ := by
      have := hc.sup_eq_top
      rwa [h0, sup_bot_eq] at this
    refine hA l (LinearMap.ext fun v => ?_)
    have hv : v ∈ LinearMap.ker (invSMulOp l A - 1) := by rw [htop]; exact Submodule.mem_top
    rw [hAT, apply_eq_of_mem_ker_sub_one hv, LinearMap.smul_apply, Module.End.one_apply]

theorem mapsTo_eigen_of_commute {l : E} {A g : Module.End E V} (hg : g * A = A * g)
    {s : E} {v : V} (hv : v ∈ LinearMap.ker (invSMulOp l A - s • 1)) :
    g v ∈ LinearMap.ker (invSMulOp l A - s • 1) := by
  rw [LinearMap.mem_ker] at hv ⊢
  have h1 : (invSMulOp l A - s • 1) * g = g * (invSMulOp l A - s • 1) := by
    rw [invSMulOp, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, hg, smul_mul_assoc,
      mul_smul_comm, one_mul, mul_one]
  rw [← Module.End.mul_apply, h1, Module.End.mul_apply, hv, map_zero]

theorem commute_of_mapsTo_eigen (h2 : (2 : E) ≠ 0) {l : E} (hl0 : l ≠ 0) {A g : Module.End E V}
    (hAA : A * A = (l ^ 2) • 1)
    (hp : ∀ v ∈ LinearMap.ker (invSMulOp l A - 1), g v ∈ LinearMap.ker (invSMulOp l A - 1))
    (hm : ∀ v ∈ LinearMap.ker (invSMulOp l A + 1), g v ∈ LinearMap.ker (invSMulOp l A + 1)) :
    g * A = A * g := by
  have hc := isCompl_ker_sub_one_ker_add_one h2 (invSMulOp_mul_self hl0 hAA)
  have hAT : A = l • invSMulOp l A := by
    rw [invSMulOp, smul_smul, mul_inv_cancel₀ hl0, one_smul]
  have hT : g * invSMulOp l A = invSMulOp l A * g := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, y, hx, hy, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hc.codisjoint v
    simp only [Module.End.mul_apply, map_add, apply_eq_of_mem_ker_sub_one hx,
      apply_eq_neg_of_mem_ker_add_one hy, apply_eq_of_mem_ker_sub_one (hp x hx),
      apply_eq_neg_of_mem_ker_add_one (hm y hy), map_neg]
  rw [hAT, mul_smul_comm, smul_mul_assoc, hT]

end Eigen

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
