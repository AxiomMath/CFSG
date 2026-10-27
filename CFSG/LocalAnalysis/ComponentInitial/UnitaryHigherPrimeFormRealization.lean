module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormTransport

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

theorem IsPrimeFormGram.barTranspose {C : GL (Fin n) K} (hC : IsPrimeFormGram C)
    (h : UnitaryFieldData p f K) : ((C : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ = C := by
  rw [hC.map_eq h.bar, hC.symm]

theorem primeFormGram_det_ne_zero (C : GL (Fin n) K) : (C : Matrix (Fin n) (Fin n) K).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp C.isUnit).ne_zero

theorem scalar_barTranspose_mul_mul (h : UnitaryFieldData p f K) {ι : Type} [Fintype ι]
    [DecidableEq ι] (G : Matrix ι ι K) (c : K) :
    ((Matrix.scalar ι c).map h.bar)ᵀ * G * Matrix.scalar ι c = h.norm c • G := by
  rw [scalar_apply, diagonal_map (map_zero h.bar), diagonal_transpose]
  ext a b
  rw [mul_diagonal, diagonal_mul, Matrix.smul_apply, smul_eq_mul, UnitaryFieldData.norm]
  ring

theorem norm_eq_one_of_scalar_mem_primeFormUnitary (h : UnitaryFieldData p f K) (hn : 1 ≤ n)
    (C : GL (Fin n) K) {c : Kˣ}
    (hc : GeneralLinearGroup.scalar (Fin n) c ∈ primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) :
    h.norm (c : K) = 1 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h1 := mem_primeFormUnitary.mp hc
  rw [GeneralLinearGroup.coe_scalar, scalar_barTranspose_mul_mul] at h1
  have h2 : (h.norm (c : K) - 1) • (C : Matrix (Fin n) (Fin n) K) = 0 := by
    rw [sub_smul, h1, one_smul, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact sub_eq_zero.mp h3
  · exact absurd h3 C.ne_zero

section Hyp

variable (h : UnitaryFieldData p f K) {r ε : ℕ} {C : GL (Fin (2 * r + ε)) K}
  (hC : IsPrimeFormGram C)

theorem primeFormPsi_surjective_hyp (hr : 1 ≤ r) (hε : ε ≤ 1) (hn : 3 ≤ 2 * r + ε)
    (hq : ¬(2 * r + ε = 3 ∧ p ^ f = 2)) : Function.Surjective (primeFormPsi h hC) := by
  obtain ⟨W, hW⟩ := exists_isGramHypTransport h (C : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K)
    (hC.barTranspose h) (primeFormGram_det_ne_zero C)
  intro α
  obtain ⟨x₀, hx₀⟩ := semilinearAutHom_surjective_of_admissible h hr hε hn hq
    (MulAut.congr (gramHypProjEquiv h _ hW) α)
  obtain ⟨x, hx, -, hxu⟩ := exists_unitary_rep h hr hε hn x₀
  obtain ⟨A, hA⟩ : ∃ A : primeFormUnitary h (C : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K),
      (A : GL (Fin (2 * r + ε)) K) = gramOfHypSemiGL hW (x : SemiGL (HypIndex r ε) K).left
        (x : SemiGL (HypIndex r ε) K).right :=
    ⟨⟨_, gramOfHypSemiGL_mem hC.map_eq_ringEquiv hW hxu _⟩, rfl⟩
  have hxA : (((x : SemiGL (HypIndex r ε) K).left : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) =
        gramHypInv h (C : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) W *
          ((A : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *
            W.map (x : SemiGL (HypIndex r ε) K).right := by
    rw [hA]
    exact (gramToHyp_gramOfHypSemi hW _ _).symm
  refine ⟨⟨A, (x : SemiGL (HypIndex r ε) K).right⟩,
    MulEquiv.ext fun y => (gramHypProjEquiv h _ hW).injective ?_⟩
  rw [gramHypProjEquiv_psi hC hW hr hε A x hxA y, hx, hx₀, MulAut.congr_apply,
    MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

theorem primeFormPsi_eq_one_iff_hyp (hr : 1 ≤ r) (hε : ε ≤ 1) (hn : 3 ≤ 2 * r + ε)
    (x : primeFormUnitary h (C : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K)
      ⋊[primeFormFieldU h hC] (K ≃+* K)) :
    primeFormPsi h hC x = 1 ↔ x.right = RingEquiv.refl K ∧ ∃ c : Kˣ, h.norm (c : K) = 1 ∧
      (x.left : GL (Fin (2 * r + ε)) K) = GeneralLinearGroup.scalar (Fin (2 * r + ε)) c := by
  constructor
  · intro h1
    obtain ⟨W, hW⟩ := exists_isGramHypTransport h
      (C : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) (hC.barTranspose h)
      (primeFormGram_det_ne_zero C)
    have hB := gramToHypSemiGL_mem hC.map_eq_ringEquiv hW x.left.2 x.right
    obtain ⟨y, hy⟩ : ∃ y : semilinearSimilitudes h r ε, (y : SemiGL (HypIndex r ε) K) =
        ⟨gramToHypSemiGL hW x.left x.right, x.right⟩ :=
      ⟨⟨⟨gramToHypSemiGL hW x.left x.right, x.right⟩, 1, one_ne_zero, map_one _,
        by rw [one_smul]; exact hB⟩, rfl⟩
    have hyr : (y : SemiGL (HypIndex r ε) K).right = x.right := by rw [hy]
    have hyl : (((y : SemiGL (HypIndex r ε) K).left : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) =
          gramHypInv h (C : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) W *
            ((x.left : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *
              W.map (y : SemiGL (HypIndex r ε) K).right := by
      rw [hy]
      rfl
    have hy1 : semilinearAutHom h hr hε y = 1 := by
      refine MulEquiv.ext fun z => ?_
      obtain ⟨w, rfl⟩ := (gramHypProjEquiv h _ hW).surjective z
      rw [← gramHypProjEquiv_psi hC hW hr hε x.left y hyl w, hyr]
      change gramHypProjEquiv h _ hW (primeFormPsi h hC x w) = _
      rw [h1]
      rfl
    obtain ⟨hσ, c, hc⟩ := (semilinearAutHom_eq_one_iff h hr hε hn y).mp hy1
    rw [hyr] at hσ
    have hBc := congrArg (fun g : GL (HypIndex r ε) K => (g : Matrix (HypIndex r ε)
      (HypIndex r ε) K)) hc
    rw [hyl, hyr, hσ, GeneralLinearGroup.coe_scalar] at hBc
    have hWr : W.map (RingEquiv.refl K) = W := Matrix.ext fun _ _ => rfl
    rw [hWr] at hBc
    have hxc : (x.left : GL (Fin (2 * r + ε)) K) =
        GeneralLinearGroup.scalar (Fin (2 * r + ε)) c := by
      refine Units.ext ?_
      rw [GeneralLinearGroup.coe_scalar, ← gramOfHyp_gramToHyp hW
        ((x.left : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K), hBc,
        gramOfHyp_scalar hW]
    refine ⟨hσ, c, norm_eq_one_of_scalar_mem_primeFormUnitary h (by omega) C ?_, hxc⟩
    rw [← hxc]
    exact x.left.2
  · rintro ⟨hσ, c, -, hA⟩
    obtain ⟨A, φ⟩ := x
    change φ = RingEquiv.refl K at hσ
    subst hσ
    rw [primeFormPsi_apply]
    refine MulEquiv.ext fun y => QuotientGroup.induction_on y fun g => ?_
    rw [MulAut.mul_apply]
    change primeFormConjHom h _ A (primeFormFieldAut h hC (RingEquiv.refl K)
      (g : primeFormP h _)) = (g : primeFormP h _)
    rw [primeFormFieldAut_mk, primeFormConjHom_mk]
    congr 1
    refine Subtype.ext ?_
    change (A : GL (Fin (2 * r + ε)) K) * glAut (RingEquiv.refl K) (g : GL (Fin (2 * r + ε)) K) *
      (A : GL (Fin (2 * r + ε)) K)⁻¹ = g
    have hg1 : glAut (RingEquiv.refl K) (g : GL (Fin (2 * r + ε)) K) = g := by
      rw [show RingEquiv.refl K = (1 : K ≃+* K) from rfl, map_one, MulAut.one_apply]
    change A.1 = _ at hA
    rw [hg1, hA, ← (commute_scalar c _).eq, mul_inv_cancel_right]

end Hyp

section General

variable (h : UnitaryFieldData p f K) {C : GL (Fin n) K} (hC : IsPrimeFormGram C)

theorem primeFormPsi_surjective (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ p ^ f = 2)) :
    Function.Surjective (primeFormPsi h hC) := by
  obtain ⟨r, ε, rfl, hr, hε⟩ : ∃ r ε, n = 2 * r + ε ∧ 1 ≤ r ∧ ε ≤ 1 :=
    ⟨n / 2, n % 2, by omega, by omega, by omega⟩
  exact primeFormPsi_surjective_hyp h hC hr hε hn hq

theorem primeFormPsi_eq_one_iff (hn : 3 ≤ n)
    (x : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) ⋊[primeFormFieldU h hC] (K ≃+* K)) :
    primeFormPsi h hC x = 1 ↔ x.right = RingEquiv.refl K ∧ ∃ c : Kˣ, h.norm (c : K) = 1 ∧
      (x.left : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) c := by
  obtain ⟨r, ε, rfl, hr, hε⟩ : ∃ r ε, n = 2 * r + ε ∧ 1 ≤ r ∧ ε ≤ 1 :=
    ⟨n / 2, n % 2, by omega, by omega, by omega⟩
  exact primeFormPsi_eq_one_iff_hyp h hC hr hε hn x

theorem primeFormPsi_ker_le (hn : 3 ≤ n) :
    (primeFormPsi h hC).ker ≤ (SemidirectProduct.rightHom :
      primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) ⋊[primeFormFieldU h hC] (K ≃+* K) →*
        (K ≃+* K)).ker := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx ⊢
  rw [SemidirectProduct.rightHom_eq_right]
  exact ((primeFormPsi_eq_one_iff h hC hn x).mp hx).1

@[expose] noncomputable def primeFormFieldFactor (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ p ^ f = 2)) :
    MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K)) →* (K ≃+* K) :=
  (QuotientGroup.lift _ SemidirectProduct.rightHom (primeFormPsi_ker_le h hC hn)).comp
    (QuotientGroup.quotientKerEquivOfSurjective _
      (primeFormPsi_surjective h hC hn hq)).symm.toMonoidHom

variable (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ p ^ f = 2))

theorem primeFormFieldFactor_psi
    (x : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) ⋊[primeFormFieldU h hC] (K ≃+* K)) :
    primeFormFieldFactor h hC hn hq (primeFormPsi h hC x) = x.right := by
  have e : (QuotientGroup.quotientKerEquivOfSurjective _
      (primeFormPsi_surjective h hC hn hq)).symm (primeFormPsi h hC x) =
        (x : _ ⧸ (primeFormPsi h hC).ker) :=
    (MulEquiv.symm_apply_eq _).mpr rfl
  change QuotientGroup.lift _ SemidirectProduct.rightHom (primeFormPsi_ker_le h hC hn)
    ((QuotientGroup.quotientKerEquivOfSurjective _ (primeFormPsi_surjective h hC hn hq)).symm
      (primeFormPsi h hC x)) = _
  rw [e, QuotientGroup.lift_mk, SemidirectProduct.rightHom_eq_right]

theorem primeFormFieldFactor_apply (A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K))
    (φ : K ≃+* K) :
    primeFormFieldFactor h hC hn hq (primeFormConjHom h _ A * primeFormFieldHom h hC φ) = φ := by
  rw [← primeFormPsi_apply, primeFormFieldFactor_psi]

theorem primeFormFieldFactor_surjective : Function.Surjective (primeFormFieldFactor h hC hn hq) :=
  fun φ => ⟨_, primeFormFieldFactor_apply h hC hn hq 1 φ⟩

theorem ker_primeFormFieldFactor :
    (primeFormFieldFactor h hC hn hq).ker = primeFormD h (C : Matrix (Fin n) (Fin n) K) := by
  ext α
  rw [MonoidHom.mem_ker]
  constructor
  · intro hα
    obtain ⟨⟨A, φ⟩, rfl⟩ := primeFormPsi_surjective h hC hn hq α
    rw [primeFormFieldFactor_psi] at hα
    change φ = 1 at hα
    subst hα
    refine ⟨A, ?_⟩
    rw [primeFormPsi_apply, map_one, mul_one]
  · rintro ⟨A, rfl⟩
    have e := primeFormFieldFactor_apply h hC hn hq A 1
    rwa [map_one, mul_one] at e

include hn hq in
theorem existsUnique_primeFormFieldFactor
    (α : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))) :
    ∃! φ : K ≃+* K, ∃ A, α = primeFormConjHom h _ A * primeFormFieldHom h hC φ := by
  obtain ⟨⟨A, φ⟩, rfl⟩ := primeFormPsi_surjective h hC hn hq α
  refine ⟨φ, ⟨A, primeFormPsi_apply h hC A φ⟩, ?_⟩
  rintro ψ ⟨B, hB⟩
  rw [← primeFormFieldFactor_apply h hC hn hq B ψ, ← hB, primeFormFieldFactor_psi]

end General

section Inner

variable (h : UnitaryFieldData p f K)

theorem primeFormConjHom_eq_conj (C : Matrix (Fin n) (Fin n) K) (s : gramSU h C) :
    primeFormConjHom h C ⟨s, s.2.1⟩ = MulAut.conj (s : primeFormP h C) := by
  refine MulEquiv.ext fun y => QuotientGroup.induction_on y fun g => ?_
  rw [primeFormConjHom_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  rfl

theorem mem_inner_primeFormP (C : Matrix (Fin n) (Fin n) K) (α : MulAut (primeFormP h C)) :
    α ∈ inner (primeFormP h C) ↔ ∃ s : gramSU h C, α = primeFormConjHom h C ⟨s, s.2.1⟩ := by
  change α ∈ (MulAut.conj : primeFormP h C →* MulAut (primeFormP h C)).range ↔ _
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨s, (primeFormConjHom_eq_conj h C s).symm⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s, (primeFormConjHom_eq_conj h C s).symm⟩

theorem norm_det_eq_one (C : GL (Fin n) K) {A : GL (Fin n) K}
    (hA : A ∈ primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) :
    h.norm (A : Matrix (Fin n) (Fin n) K).det = 1 := by
  have hdet := congrArg Matrix.det (mem_primeFormUnitary.mp hA)
  rw [det_mul, det_mul, det_transpose, show (A : Matrix (Fin n) (Fin n) K).map h.bar =
    h.bar.mapMatrix (A : Matrix (Fin n) (Fin n) K) from rfl, ← RingHom.map_det] at hdet
  rw [UnitaryFieldData.norm]
  apply mul_right_cancel₀ (primeFormGram_det_ne_zero C)
  linear_combination hdet

theorem card_primeFormD_quotient_dvd (C : GL (Fin n) K) :
    Nat.card (primeFormD h (C : Matrix (Fin n) (Fin n) K) ⧸
      (inner (primeFormP h (C : Matrix (Fin n) (Fin n) K))).subgroupOf
        (primeFormD h (C : Matrix (Fin n) (Fin n) K))) ∣ p ^ f + 1 := by
  obtain ⟨c, hc⟩ : ∃ c : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) →*
      primeFormD h (C : Matrix (Fin n) (Fin n) K),
        ∀ A, (c A : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))) =
          primeFormConjHom h _ A :=
    ⟨(primeFormConjHom h _).rangeRestrict, fun _ => rfl⟩
  have hcs : Function.Surjective c := by
    rintro ⟨α, A, rfl⟩
    exact ⟨A, Subtype.ext (hc A)⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) →* Kˣ,
      ∀ A, (δ A : K) = ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det :=
    ⟨GeneralLinearGroup.det.comp (primeFormUnitary h _).subtype, fun _ => rfl⟩
  have hS : (gramSU h (C : Matrix (Fin n) (Fin n) K)).subgroupOf
      (primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) = δ.ker := by
    ext A
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, mem_gramSU_iff_unitary, Units.ext_iff, hδ,
      Units.val_one]
    exact ⟨fun hA => hA.2, fun hA => ⟨A.2, hA⟩⟩
  have hle : (gramSU h (C : Matrix (Fin n) (Fin n) K)).subgroupOf
      (primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) ≤
        ((inner (primeFormP h (C : Matrix (Fin n) (Fin n) K))).subgroupOf
          (primeFormD h (C : Matrix (Fin n) (Fin n) K))).comap c := by
    intro A hA
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, hc, mem_inner_primeFormP]
    exact ⟨⟨A, hA⟩, rfl⟩
  have hrange : δ.range ≤ (Units.map h.normHom).ker := by
    rintro _ ⟨A, rfl⟩
    rw [h.mem_ker_normUnits, hδ]
    exact norm_det_eq_one h C A.2
  calc Nat.card (primeFormD h (C : Matrix (Fin n) (Fin n) K) ⧸
        (inner (primeFormP h (C : Matrix (Fin n) (Fin n) K))).subgroupOf
          (primeFormD h (C : Matrix (Fin n) (Fin n) K)))
      = (((inner (primeFormP h (C : Matrix (Fin n) (Fin n) K))).subgroupOf
          (primeFormD h (C : Matrix (Fin n) (Fin n) K))).comap c).index :=
        (Subgroup.index_comap_of_surjective _ hcs).symm
    _ ∣ ((gramSU h (C : Matrix (Fin n) (Fin n) K)).subgroupOf
          (primeFormUnitary h (C : Matrix (Fin n) (Fin n) K))).index :=
        Subgroup.index_dvd_of_le hle
    _ = Nat.card δ.range := by rw [hS, Subgroup.index_ker]
    _ ∣ Nat.card (Units.map h.normHom).ker := Subgroup.card_dvd_of_le hrange
    _ = p ^ f + 1 := (unitary_field_norm h).2.2.1

end Inner

theorem nonempty_primeFormP_mulEquiv (h : UnitaryFieldData p f K) {C : GL (Fin n) K}
    (hC : IsPrimeFormGram C) :
    Nonempty (primeFormP h (C : Matrix (Fin n) (Fin n) K) ≃* unitaryPSU h n) := by
  obtain ⟨r, ε, rfl⟩ : ∃ r ε, n = 2 * r + ε := ⟨n / 2, n % 2, by omega⟩
  obtain ⟨W, hW⟩ := exists_isGramHypTransport h (C : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K)
    (hC.barTranspose h) (primeFormGram_det_ne_zero C)
  obtain ⟨R, hR⟩ := exists_isHypTransport h (r := r) (ε := ε)
  exact ⟨(gramHypProjEquiv h _ hW).trans (hypProjTransport h hR)⟩


theorem unitary_prime_form_full_semilinear_realization (h : UnitaryFieldData p f K)
    {C : GL (Fin n) K} (hC : IsPrimeFormGram C) (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ p ^ f = 2)) :
    Nonempty (primeFormP h (C : Matrix (Fin n) (Fin n) K) ≃* unitaryPSU h n) ∧
    Function.Surjective (primeFormPsi h hC) ∧
    (∀ x : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) ⋊[primeFormFieldU h hC] (K ≃+* K),
      primeFormPsi h hC x = 1 ↔ x.right = RingEquiv.refl K ∧ ∃ c : Kˣ, h.norm (c : K) = 1 ∧
        (x.left : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) c) ∧
    primeFormE h hC = ⊤ ∧
    (∀ α : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K)), ∃! φ : K ≃+* K,
      ∃ A, α = primeFormConjHom h _ A * primeFormFieldHom h hC φ) ∧
    (∀ (A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) (φ : K ≃+* K),
      primeFormFieldFactor h hC hn hq (primeFormConjHom h _ A * primeFormFieldHom h hC φ) = φ) ∧
    Function.Surjective (primeFormFieldFactor h hC hn hq) ∧
    (primeFormFieldFactor h hC hn hq).ker = primeFormD h (C : Matrix (Fin n) (Fin n) K) ∧
    (primeFormD h (C : Matrix (Fin n) (Fin n) K)).Normal ∧
    (∀ α : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K)),
      α ∈ inner (primeFormP h (C : Matrix (Fin n) (Fin n) K)) ↔
        ∃ s : gramSU h (C : Matrix (Fin n) (Fin n) K),
          α = primeFormConjHom h (C : Matrix (Fin n) (Fin n) K) ⟨s, s.2.1⟩) ∧
    Nat.card (primeFormD h (C : Matrix (Fin n) (Fin n) K) ⧸
      (inner (primeFormP h (C : Matrix (Fin n) (Fin n) K))).subgroupOf
        (primeFormD h (C : Matrix (Fin n) (Fin n) K))) ∣ p ^ f + 1 := by
  have hker := ker_primeFormFieldFactor h hC hn hq
  refine ⟨nonempty_primeFormP_mulEquiv h hC, primeFormPsi_surjective h hC hn hq,
    primeFormPsi_eq_one_iff h hC hn, ?_, existsUnique_primeFormFieldFactor h hC hn hq,
    primeFormFieldFactor_apply h hC hn hq, primeFormFieldFactor_surjective h hC hn hq, hker, ?_,
    mem_inner_primeFormP h _, card_primeFormD_quotient_dvd h C⟩
  · rw [← range_primeFormPsi h hC, MonoidHom.range_eq_top]
    exact primeFormPsi_surjective h hC hn hq
  · rw [← hker]
    infer_instance

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
