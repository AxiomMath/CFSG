module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4Gen4
public import CFSG.GH74.Generic.BProg.B2.GenLocL4Gen4U
public import CFSG.GH74.Generic.BProg.B2.T4OutCore

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.LocalAnalysis.ComponentInitial Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace GenLocL4Refl

theorem exists_pow_four_or_mul {Γ : Type*} [CommGroup Γ] [Finite Γ] [IsCyclic Γ]
    (hΓ : Nat.card Γ % 8 = 4) (ε : Γ) (hε1 : ε ≠ 1) (hε2 : ε * ε = 1) (c : Γ) :
    ∃ y : Γ, c ^ 2 = y ^ 4 ∨ ε * c ^ 2 = y ^ 4 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Γ)
  have hord : orderOf g = Nat.card Γ := orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨m, hm, hm2⟩ : ∃ m : ℕ, Nat.card Γ = 4 * m ∧ m % 2 = 1 :=
    ⟨Nat.card Γ / 4, by omega, by omega⟩
  have hg4 : g ^ (4 * m) = 1 := by rw [← hm, ← hord]; exact pow_orderOf_eq_one g
  have hg4' : g ^ ((4 * m : ℕ) : ℤ) = 1 := by rw [zpow_natCast]; exact hg4
  have hε : ε = g ^ (2 * m) := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ε)
    have h2 : g ^ (k + k) = 1 := by rw [zpow_add, hk]; exact hε2
    have h3 : ((orderOf g : ℕ) : ℤ) ∣ k + k := orderOf_dvd_iff_zpow_eq_one.2 h2
    rw [hord, hm] at h3
    obtain ⟨r, hr⟩ := h3
    have hk' : k = 2 * ((m : ℤ) * r) := by push_cast at hr; linarith
    obtain ⟨u, r', hr', hr'0⟩ : ∃ u r' : ℤ, r = 2 * u + r' ∧ (r' = 0 ∨ r' = 1) :=
      ⟨r / 2, r % 2, by omega, by omega⟩
    have hkk : k = ((4 * m : ℕ) : ℤ) * u + ((2 * m : ℕ) : ℤ) * r' := by
      rw [hk', hr']; push_cast; ring
    have hε' : ε = g ^ (((2 * m : ℕ) : ℤ) * r') := by
      rw [← hk, hkk, zpow_add, zpow_mul, hg4', one_zpow, one_mul]
    rcases hr'0 with h0 | h1
    · exfalso; apply hε1; rw [hε', h0, mul_zero, zpow_zero]
    · rw [hε', h1, mul_one, zpow_natCast]
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hg c)
  obtain ⟨a, hja⟩ : ∃ a : ℤ, j = 2 * a ∨ j = 2 * a + 1 := ⟨j / 2, by omega⟩
  rcases hja with h | h
  · refine ⟨g ^ a, Or.inl ?_⟩
    rw [← hj, ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, h]
    push_cast; ring_nf
  · obtain ⟨b, hb⟩ : ∃ b : ℕ, m = 2 * b + 1 := ⟨m / 2, by omega⟩
    refine ⟨g ^ (a + b + 1), Or.inr ?_⟩
    rw [← hj, hε]
    simp only [← zpow_natCast, ← zpow_mul, ← zpow_add]
    congr 1
    rw [h, hb]; push_cast; ring

theorem exists_fourth_power_of_sq_eq {K : Type*} [Field K] [Finite K] (Γ : Subgroup Kˣ)
    (hΓ : Nat.card Γ % 8 = 4) (hneg : (-1 : Kˣ) ∈ Γ) (h2 : (2 : K) ≠ 0) {c d : Kˣ}
    (hc : c ∈ Γ) (hdc : d ^ 2 = c ^ 4) :
    ∃ y : Kˣ, y ∈ Γ ∧ (d = y ^ 4 ∨ d = -y ^ 4) := by
  have hne : (-1 : Kˣ) ≠ 1 := by
    intro h
    have h2' := congrArg (fun u : Kˣ => (u : K)) h
    simp at h2'
    exact h2 (by linear_combination -h2')
  obtain ⟨y, hy⟩ := exists_pow_four_or_mul hΓ (⟨-1, hneg⟩ : Γ)
    (fun h => hne (congrArg Subtype.val h)) (Subtype.ext (by simp)) (⟨c, hc⟩ : Γ)
  have hy' : (c ^ 2 = (y : Kˣ) ^ 4) ∨ (-1 * c ^ 2 = (y : Kˣ) ^ 4) := by
    rcases hy with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  have hd2 : (d * (c ^ 2)⁻¹) ^ 2 = 1 := by
    rw [mul_pow, hdc, inv_pow, ← pow_mul]; simp
  have hd3 : d * (c ^ 2)⁻¹ = 1 ∨ d * (c ^ 2)⁻¹ = -1 := by
    have h5 : ((d * (c ^ 2)⁻¹ : Kˣ) : K) * ((d * (c ^ 2)⁻¹ : Kˣ) : K) = 1 := by
      have := congrArg (fun u : Kˣ => (u : K)) hd2
      simpa [sq] using this
    rcases mul_self_eq_one_iff.1 h5 with h6 | h6
    · exact Or.inl (Units.ext h6)
    · exact Or.inr (Units.ext (by simpa using h6))
  have hdc' : d = c ^ 2 ∨ d = -c ^ 2 := by
    rcases hd3 with h | h
    · left; calc d = d * (c ^ 2)⁻¹ * c ^ 2 := by simp
        _ = c ^ 2 := by rw [h, one_mul]
    · right; calc d = d * (c ^ 2)⁻¹ * c ^ 2 := by simp
        _ = -c ^ 2 := by rw [h]; simp
  refine ⟨(y : Kˣ), y.2, ?_⟩
  rcases hdc' with h | h <;> rcases hy' with h' | h'
  · left; rw [h, h']
  · right
    have h3 : c ^ 2 = -(y : Kˣ) ^ 4 := by rw [← h']; simp
    rw [h, h3]
  · right; rw [h, h']
  · left; rw [h, ← h']; simp

theorem sectionalTwoRankLE_of_le_range {N X : Type*} [Group N] [Group X] (φ : N →* X)
    (hφ : Function.Injective φ) {Y : Subgroup X} (hY : Y ≤ φ.range) {r : ℕ}
    (hN : SectionalTwoRankLE N r) : SectionalTwoRankLE ↥Y r := by
  let e : N ≃* φ.range := MonoidHom.ofInjective hφ
  refine SectionalTwoRankLE.of_injective ((e.symm : φ.range →* N).comp (Subgroup.inclusion hY)) ?_ hN
  exact e.symm.injective.comp (Subgroup.inclusion_injective hY)

theorem injective_congr_conjNormal {N : Type*} [Group N] {H : Subgroup N} [H.Normal]
    (hfaith : ∀ n : N, (∀ h ∈ H, n * h = h * n) → n = 1) {P : Type*} [Group P] (e : ↥H ≃* P) :
    Function.Injective ((MulAut.congr e).toMonoidHom.comp
      (MulAut.conjNormal : N →* MulAut ↥H)) := by
  intro a b hab
  have h1 : (MulAut.conjNormal a : MulAut ↥H) = MulAut.conjNormal b :=
    (MulAut.congr e).injective hab
  have h2 : a⁻¹ * b = 1 := by
    apply hfaith
    intro x hx
    have h3 := congrArg (fun φ : MulAut ↥H => ((φ ⟨x, hx⟩ : ↥H) : N)) h1
    simp only [MulAut.conjNormal_apply] at h3
    calc a⁻¹ * b * x = a⁻¹ * (b * x * b⁻¹) * b := by group
      _ = a⁻¹ * (a * x * a⁻¹) * b := by rw [← h3]
      _ = x * (a⁻¹ * b) := by group
  exact (inv_mul_eq_one.mp h2)

theorem innJoin_le_range {N : Type*} [Group N] {H : Subgroup N} [H.Normal] {P : Type*} [Group P]
    (e : ↥H ≃* P) (t : N) :
    (MulAut.conj : P →* MulAut P).range ⊔
        zpowers (MulAut.congr e (MulAut.conjNormal t : MulAut ↥H)) ≤
      ((MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : N →* MulAut ↥H)).range := by
  refine sup_le ?_ ((Subgroup.zpowers_le).2 ⟨t, rfl⟩)
  rintro _ ⟨p, rfl⟩
  refine ⟨((e.symm p : ↥H) : N), ?_⟩
  ext x
  apply e.symm.injective
  apply Subtype.ext
  simp [MulAut.congr_apply, MulAut.conj_apply, MulAut.conjNormal_apply]

theorem sectionalTwoRankLE_innJoin {N : Type*} [Group N] {H : Subgroup N} [H.Normal]
    (hfaith : ∀ n : N, (∀ h ∈ H, n * h = h * n) → n = 1) {P : Type*} [Group P] (e : ↥H ≃* P)
    (t : N) {r : ℕ} (hN : SectionalTwoRankLE N r) :
    SectionalTwoRankLE ↥((MulAut.conj : P →* MulAut P).range ⊔
      zpowers (MulAut.congr e (MulAut.conjNormal t : MulAut ↥H))) r :=
  sectionalTwoRankLE_of_le_range _ (injective_congr_conjNormal hfaith e) (innJoin_le_range e t) hN

theorem mem_of_congr_conjNormal_mem_inner {N : Type*} [Group N] {H : Subgroup N} [H.Normal]
    (hfaith : ∀ n : N, (∀ h ∈ H, n * h = h * n) → n = 1) {P : Type*} [Group P] (e : ↥H ≃* P)
    {t : N} (ht : MulAut.congr e (MulAut.conjNormal t : MulAut ↥H) ∈
      (MulAut.conj : P →* MulAut P).range) : t ∈ H := by
  have h1 : MulAut.congr e (MulAut.conjNormal t : MulAut ↥H) ∈
      (inner ↥H).map (MulAut.congr e).toMonoidHom := by
    rw [CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr]
    exact ht
  obtain ⟨y, hy, hyeq⟩ := h1
  have h3 : y = (MulAut.conjNormal t : MulAut ↥H) := (MulAut.congr e).injective hyeq
  exact T4.T4OutCore.mem_of_conjNormal_mem_inner hfaith (h3 ▸ hy)


section Linear

theorem det_refl4 (F : Type) [Field F] :
    Matrix.GeneralLinearGroup.det (GenLocL4Gen4.refl4 F) = -1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, GenLocL4Gen4.coe_refl4, Matrix.det_diagonal]
  simp [Fin.prod_univ_four]

theorem det_pow_four_or_neg {F : Type} [Field F] [Finite F] (hF : Nat.card F % 8 = 5)
    (A : GL (Fin 4) F) (hA2 : LinearFlag.conjAut 4 F A ^ 2 = 1) :
    ∃ y : Fˣ, Matrix.GeneralLinearGroup.det A = y ^ 4 ∨
      Matrix.GeneralLinearGroup.det A = -y ^ 4 := by
  have h1 : LinearFlag.conjAut 4 F (A * A) * LinearFlag.fieldAut 4 F 1 = 1 := by
    rw [map_mul, map_one, mul_one, ← pow_two]; exact hA2
  obtain ⟨-, c, hc⟩ :=
    LinearFlag.eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num : 3 ≤ 4) (A * A) 1 h1
  have hd : Matrix.GeneralLinearGroup.det A ^ 2 = c ^ 4 := by
    have := congrArg Matrix.GeneralLinearGroup.det hc
    rw [Matrix.GeneralLinearGroup.det_scalar, map_mul] at this
    simpa [sq] using this.symm
  have h2 : (2 : F) ≠ 0 := T4.T4OutCore.two_ne_zero_of_odd_card (Nat.odd_iff.mpr (by omega))
  have hcard : Nat.card (⊤ : Subgroup Fˣ) % 8 = 4 := by
    rw [Subgroup.card_top, Nat.card_units]; omega
  obtain ⟨y, -, hy⟩ := exists_fourth_power_of_sq_eq (⊤ : Subgroup Fˣ) hcard (Subgroup.mem_top _) h2
    (Subgroup.mem_top c) hd
  exact ⟨y, hy⟩

theorem not_sectional_of_outerDiag {F : Type} [Field F] [Finite F] (hF : Nat.card F % 8 = 5)
    (A : GL (Fin 4) F) (hA2 : LinearFlag.conjAut 4 F A ^ 2 = 1)
    (hA : LinearFlag.conjAut 4 F A ∉
      (MulAut.conj : LinearFlag.projectiveSL 4 F →* MulAut (LinearFlag.projectiveSL 4 F)).range) :
    ¬ SectionalTwoRankLE ↥((MulAut.conj : LinearFlag.projectiveSL 4 F →*
      MulAut (LinearFlag.projectiveSL 4 F)).range ⊔ zpowers (LinearFlag.conjAut 4 F A)) 4 := by
  intro hY
  obtain ⟨y, hy | hy⟩ := det_pow_four_or_neg hF A hA2
  · exact hA (T4.T4OutCore.conjAut_mem_inner_of_det hy)
  · set t1 := GenLocL4Gen4.refl4 F with ht1
    have hC : Matrix.GeneralLinearGroup.det (t1⁻¹ * A) = y ^ 4 := by
      rw [map_mul, map_inv, det_refl4, hy]; simp
    have hin : LinearFlag.conjAut 4 F (t1⁻¹ * A) ∈
        (MulAut.conj : LinearFlag.projectiveSL 4 F →* MulAut (LinearFlag.projectiveSL 4 F)).range :=
      T4.T4OutCore.conjAut_mem_inner_of_det hC
    have hmem : LinearFlag.conjAut 4 F t1 ∈
        (MulAut.conj : LinearFlag.projectiveSL 4 F →* MulAut (LinearFlag.projectiveSL 4 F)).range ⊔
          zpowers (LinearFlag.conjAut 4 F A) := by
      have h3 : LinearFlag.conjAut 4 F t1 =
          LinearFlag.conjAut 4 F A * (LinearFlag.conjAut 4 F (t1⁻¹ * A))⁻¹ := by
        rw [map_mul, map_inv, mul_inv_rev, inv_inv, mul_inv_cancel_left]
      rw [h3]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
        (Subgroup.inv_mem _ (Subgroup.mem_sup_left hin))
    have hle : (MulAut.conj : LinearFlag.projectiveSL 4 F →*
        MulAut (LinearFlag.projectiveSL 4 F)).range ⊔ zpowers (LinearFlag.conjAut 4 F t1) ≤
        (MulAut.conj : LinearFlag.projectiveSL 4 F →*
          MulAut (LinearFlag.projectiveSL 4 F)).range ⊔ zpowers (LinearFlag.conjAut 4 F A) :=
      sup_le le_sup_left ((Subgroup.zpowers_le).2 hmem)
    exact not_sectional_l4_t1 hF t1 (GenLocL4Gen4.coe_refl4 F)
      (SectionalTwoRankLE.of_injective (Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle) hY)

theorem false_of_outerDiag_linear {N : Type} [Group N] {H : Subgroup N} [H.Normal]
    (hfaith : ∀ n : N, (∀ h ∈ H, n * h = h * n) → n = 1) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F % 8 = 5) (e : ↥H ≃* LinearFlag.projectiveSL 4 F) {t : N} (ht : t ∉ H)
    (ht2 : t ^ 2 = 1) (A : GL (Fin 4) F)
    (hA : MulAut.congr e (MulAut.conjNormal t : MulAut ↥H) = LinearFlag.conjAut 4 F A)
    (hN : SectionalTwoRankLE N 4) : False := by
  have hA2 : LinearFlag.conjAut 4 F A ^ 2 = 1 := by
    rw [← hA, ← map_pow, ← map_pow, ht2, map_one, map_one]
  have hAout : LinearFlag.conjAut 4 F A ∉
      (MulAut.conj : LinearFlag.projectiveSL 4 F →* MulAut (LinearFlag.projectiveSL 4 F)).range := by
    intro hin
    rw [← hA] at hin
    exact ht (mem_of_congr_conjNormal_mem_inner hfaith e hin)
  have hY := sectionalTwoRankLE_innJoin hfaith e t hN
  rw [hA] at hY
  exact not_sectional_of_outerDiag hF A hA2 hAout hY

end Linear


section Unitary

open Matrix CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  GenLocL4Gen4U

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem ne_two_of_pow_mod_eight {q : ℕ} (hq : q % 8 = 3) (hqp : q = p ^ f) (hf : 1 ≤ f) :
    p ≠ 2 := by
  rintro rfl
  have : 2 ^ f % 2 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega))
  omega

theorem det_pow_four_or_neg_unitary (hq : p ^ f % 8 = 3)
    (A : primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
    (hA2 : primeFormConjHom h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) A ^ 2 = 1) :
    ∃ v : Kˣ, h.norm (v : K) = 1 ∧
      (GeneralLinearGroup.det (A : GL (Fin 4) K) = v ^ 4 ∨
        GeneralLinearGroup.det (A : GL (Fin 4) K) = -v ^ 4) := by
  have hfin : Finite K := h.finite
  have hp2 : p ≠ 2 := ne_two_of_pow_mod_eight hq rfl h.one_le
  have h2 : (2 : K) ≠ 0 := by
    have := h.charP
    exact T4.T4OutCore.two_ne_zero_of_charP h.prime hp2
  have hC : IsPrimeFormGram (1 : GL (Fin 4) K) := GenLocL4Gen4U.isPrimeFormGram_one
  have h1 : primeFormConjHom h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) (A * A) = 1 := by
    rw [map_mul, ← pow_two]; exact hA2
  have key := (primeFormPsi_eq_one_iff h hC (by norm_num : 3 ≤ 4) ⟨A * A, 1⟩).1
    (by rw [primeFormPsi_apply, map_one, mul_one]; exact h1)
  obtain ⟨-, c, hcn, hc⟩ := key
  have hd : GeneralLinearGroup.det (A : GL (Fin 4) K) ^ 2 = c ^ 4 := by
    have := congrArg GeneralLinearGroup.det hc
    rw [GeneralLinearGroup.det_scalar] at this
    simpa [sq] using this
  have hcard : Nat.card (Units.map h.normHom).ker % 8 = 4 := by
    rw [h.card_ker_normUnits_and_surjective.1]; omega
  have hneg : (-1 : Kˣ) ∈ (Units.map h.normHom).ker := by
    rw [UnitaryFieldData.mem_ker_normUnits]
    simp [UnitaryFieldData.norm]
  obtain ⟨y, hy, hy4⟩ := exists_fourth_power_of_sq_eq (Units.map h.normHom).ker hcard hneg h2
    ((UnitaryFieldData.mem_ker_normUnits h).2 hcn) hd
  exact ⟨y, (UnitaryFieldData.mem_ker_normUnits h).1 hy, hy4⟩


theorem det_refl4U :
    GeneralLinearGroup.det ((refl4U h : primeFormUnitary h ((1 : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K)) : GL (Fin 4) K) = -1 := det_refl4 K

theorem not_sectional_of_outerDiag_unitary (hq : p ^ f % 8 = 3)
    (A : primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
    (hA2 : primeFormConjHom h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) A ^ 2 = 1)
    (hA : primeFormConjHom h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) A ∉
      (MulAut.conj : primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) →*
        MulAut (primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))).range) :
    ¬ SectionalTwoRankLE ↥((MulAut.conj : primeFormP h ((1 : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) →* MulAut (primeFormP h ((1 : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K))).range ⊔
      zpowers (primeFormConjHom h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) A)) 4 := by
  intro hY
  obtain ⟨v, hv, hd | hd⟩ := det_pow_four_or_neg_unitary h hq A hA2
  · exact hA (T4.T4OutCore.primeFormConjHom_mem_inner_of_det h A hv hd)
  · set t1 := refl4U h with ht1
    have hC : GeneralLinearGroup.det ((t1⁻¹ * A : primeFormUnitary h ((1 : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K)) : GL (Fin 4) K) = v ^ 4 := by
      rw [Subgroup.coe_mul, map_mul, Subgroup.coe_inv, map_inv, det_refl4U, hd]; simp
    have hin : primeFormConjHom h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) (t1⁻¹ * A) ∈
        (MulAut.conj : primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) →*
          MulAut (primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))).range :=
      T4.T4OutCore.primeFormConjHom_mem_inner_of_det h (t1⁻¹ * A) hv hC
    have hmem : primeFormConjHom h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) t1 ∈
        (MulAut.conj : primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) →*
          MulAut (primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))).range ⊔
          zpowers (primeFormConjHom h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) A) := by
      have h3 : primeFormConjHom h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) t1 =
          primeFormConjHom h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) A *
            (primeFormConjHom h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) (t1⁻¹ * A))⁻¹ := by
        rw [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, mul_inv_cancel_left]
      rw [h3]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
        (Subgroup.inv_mem _ (Subgroup.mem_sup_left hin))
    have hle : (MulAut.conj : primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) →*
        MulAut (primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))).range ⊔
        zpowers (primeFormConjHom h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) t1) ≤
        (MulAut.conj : primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) →*
          MulAut (primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))).range ⊔
        zpowers (primeFormConjHom h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) A) :=
      sup_le le_sup_left ((Subgroup.zpowers_le).2 hmem)
    exact not_sectional_u4_t1 h hq t1 (coe_refl4U h)
      (SectionalTwoRankLE.of_injective (Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle) hY)

theorem false_of_outerDiag_unitary {N : Type} [Group N] {H : Subgroup N} [H.Normal]
    (hfaith : ∀ n : N, (∀ h ∈ H, n * h = h * n) → n = 1) (hq : p ^ f % 8 = 3)
    (e : ↥H ≃* primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) {t : N} (ht : t ∉ H)
    (ht2 : t ^ 2 = 1) (A : primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
    (hA : MulAut.congr e (MulAut.conjNormal t : MulAut ↥H) =
      primeFormConjHom h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) A)
    (hN : SectionalTwoRankLE N 4) : False := by
  have hA2 : primeFormConjHom h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) A ^ 2 = 1 := by
    rw [← hA, ← map_pow, ← map_pow, ht2, map_one, map_one]
  have hAout : primeFormConjHom h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) A ∉
      (MulAut.conj : primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) →*
        MulAut (primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))).range := by
    intro hin
    rw [← hA] at hin
    exact ht (mem_of_congr_conjNormal_mem_inner hfaith e hin)
  have hY := sectionalTwoRankLE_innJoin hfaith e t hN
  rw [hA] at hY
  exact not_sectional_of_outerDiag_unitary h hq A hA2 hAout hY

end Unitary

end GenLocL4Refl

end CFSG.GH74.Generic.BProg.B2
