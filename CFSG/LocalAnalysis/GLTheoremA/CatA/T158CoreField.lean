module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158CoreTri
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighDiagField

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158Core

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived inner mem_innAutDerived_congr
  inner_le_innAutDerived congr_mem_inner_iff)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)

section FieldModel

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.LieType.Chevalley

variable {K : Type} [Field K]

theorem t158Core_glAut_scalar (σ : K ≃+* K) (c : Kˣ) :
    glAut σ (GeneralLinearGroup.scalar (Fin 3) c) =
      GeneralLinearGroup.scalar (Fin 3) (Units.map σ.toMonoidHom c) := by
  refine Units.ext ?_
  rw [coe_glAut, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.scalar_apply, Matrix.diagonal_apply]
  · simp [Matrix.scalar_apply, Matrix.diagonal_apply, hij]

theorem t158Core_eq_one_of_scalar_eq_one {c : Kˣ} (h : GeneralLinearGroup.scalar (Fin 3) c = 1) :
    c = 1 := by
  have h1 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h
  simp only [GeneralLinearGroup.coe_scalar, Units.val_one, Matrix.scalar_apply,
    Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h1
  exact Units.ext h1

theorem t158Core_subfield_restrict (h : UnitaryFieldData 2 9 K) {σ : K ≃+* K} (hσ : orderOf σ = 3)
    {γ : MulAut (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))} (hγ3 : γ ^ 3 = 1)
    (hγc : primeFormFieldHom h (isPrimeFormGram_one (n := 3)) σ * γ =
      γ * primeFormFieldHom h (isPrimeFormGram_one (n := 3)) σ) :
    ∃ x₀ : MulAut (primeFormP (fixSubfield_unitaryFieldData h Nat.prime_three (by decide) hσ)
        ((1 : GL (Fin 3) (fixSubfield σ)) : Matrix (Fin 3) (Fin 3) (fixSubfield σ))),
      x₀ ∈ innAutDerived _ ∧
      ∀ y, γ (primeSubfieldPSU h Nat.prime_three (by decide) hσ 3 y) =
        primeSubfieldPSU h Nat.prime_three (by decide) hσ 3 (x₀ y) := by
  classical
  haveI : Finite K := h.finite
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one
  have hn : 3 ≤ 3 := le_rfl
  have hne : ¬(3 = 3 ∧ 2 ^ 9 = 2) := by norm_num
  set h₀ := fixSubfield_unitaryFieldData h Nat.prime_three (by decide) hσ with hh₀
  set hbar := fixSubfield_unitaryFieldData_bar h Nat.prime_three (by decide) hσ with hhbar
  set fσ := primeFormFieldHom h hC σ with hfσ
  have hΘσ : primeFormFieldFactor h hC hn hne fσ = σ := by
    have := primeFormFieldFactor_apply h hC hn hne 1 σ
    rwa [map_one, one_mul] at this
  have hσ3 : σ ^ 3 = 1 := by
    rw [← hσ]
    exact pow_orderOf_eq_one σ
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    norm_num at hσ
  haveI : IsCyclic (K ≃+* K) :=
    CFSG.RankThree.PartOne.CTP.isCyclic_ringEquiv_of_card h.prime (by norm_num) h.card
  haveI : Finite (K ≃+* K) := Finite.of_injective _ DFunLike.coe_injective
  obtain ⟨k, -, hk⟩ := t158Core_pow_of_cyclic hσ3 hσ1
    (b := primeFormFieldFactor h hC hn hne γ) (by rw [← map_pow, hγ3, map_one])
  have hdD : γ * (fσ ^ k)⁻¹ ∈ primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [← ker_primeFormFieldFactor h hC hn hne, MonoidHom.mem_ker, map_mul, map_inv, map_pow, hΘσ,
      ← hk, mul_inv_cancel]
  obtain ⟨z, hz⟩ := hdD
  have hγf : Commute fσ γ := hγc
  have hcomm : Commute γ (fσ ^ k)⁻¹ := ((hγf.symm).pow_right k).inv_right
  have hdc : fσ * primeFormConjHom h _ z = primeFormConjHom h _ z * fσ := by
    rw [hz]
    exact (hγf.mul_right ((Commute.self_pow fσ k).inv_right)).eq
  have hfσ3 : fσ ^ 3 = 1 := by rw [hfσ, ← map_pow, hσ3, map_one]
  have hd3 : (primeFormConjHom h _ z) ^ 3 = 1 := by
    rw [hz, hcomm.mul_pow, hγ3, one_mul, inv_pow, ← pow_mul, mul_comm, pow_mul, hfσ3, one_pow,
      inv_one]
  obtain ⟨c, hc⟩ := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh2.exists_glAut_eq_mul_scalar
    h hn hdc
  have hzU : (z : GL (Fin 3) K) ∈ primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := z.2
  have hcU : GeneralLinearGroup.scalar (Fin 3) c ∈
      primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    have e1 : GeneralLinearGroup.scalar (Fin 3) c = (z : GL (Fin 3) K)⁻¹ * glAut σ (z : GL (Fin 3) K) := by
      rw [hc]
      group
    rw [e1]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hzU) (glAut_mem_primeFormUnitary h hC σ hzU)
  have hcN : h.norm (c : K) = 1 :=
    norm_eq_one_of_scalar_mem_primeFormUnitary h (by norm_num) 1 hcU
  have hN3 : c * Units.map σ.toMonoidHom c * Units.map σ.toMonoidHom (Units.map σ.toMonoidHom c) = 1 := by
    have h3 : glAut (σ ^ 3) (z : GL (Fin 3) K) = z := by
      rw [hσ3, map_one]
      rfl
    have e2 : glAut (σ ^ 3) (z : GL (Fin 3) K) =
        glAut σ (glAut σ (glAut σ (z : GL (Fin 3) K))) := by
      rw [pow_succ, pow_succ, pow_one, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply]
    rw [e2, hc, map_mul, hc, t158Core_glAut_scalar, map_mul, map_mul, hc, t158Core_glAut_scalar,
      t158Core_glAut_scalar] at h3
    have h4 : GeneralLinearGroup.scalar (Fin 3)
        (c * Units.map σ.toMonoidHom c * Units.map σ.toMonoidHom (Units.map σ.toMonoidHom c)) = 1 := by
      rw [map_mul, map_mul]
      calc GeneralLinearGroup.scalar (Fin 3) c *
            GeneralLinearGroup.scalar (Fin 3) (Units.map σ.toMonoidHom c) *
            GeneralLinearGroup.scalar (Fin 3) (Units.map σ.toMonoidHom (Units.map σ.toMonoidHom c))
          = (z : GL (Fin 3) K)⁻¹ * ((z : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) c *
            GeneralLinearGroup.scalar (Fin 3) (Units.map σ.toMonoidHom c) *
            GeneralLinearGroup.scalar (Fin 3) (Units.map σ.toMonoidHom (Units.map σ.toMonoidHom c))) := by
            group
        _ = 1 := by rw [h3, inv_mul_cancel]
    exact t158Core_eq_one_of_scalar_eq_one h4
  have hKq : Nat.card K = (2 ^ 9) ^ 2 := by rw [h.card]; norm_num
  have hcq : ((c⁻¹ : Kˣ) : K) ^ (2 ^ 9 + 1) = 1 := by
    have h1 : (c : K) ^ (2 ^ 9 + 1) = 1 := by
      rw [← CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.norm_eq_pow h]
      exact hcN
    rw [Units.val_inv_eq_inv_val, inv_pow, h1, inv_one]
  have hN3K : (c : K) * σ (c : K) * σ (σ (c : K)) = 1 := by
    have h1 := congrArg (fun u : Kˣ => (u : K)) hN3
    simpa using h1
  have hcPN : CFSG.StandardType.TableBUF.partNorm σ ((c⁻¹ : Kˣ) : K) 3 = 1 := by
    simp only [CFSG.StandardType.TableBUF.partNorm, Finset.prod_range_succ, Finset.prod_range_zero,
      one_mul]
    rw [pow_zero, pow_one, pow_two]
    change ((c⁻¹ : Kˣ) : K) * σ ((c⁻¹ : Kˣ) : K) * σ (σ ((c⁻¹ : Kˣ) : K)) = 1
    rw [Units.val_inv_eq_inv_val, map_inv₀, map_inv₀, ← mul_inv, ← mul_inv, hN3K, inv_one]
  obtain ⟨μ, hμq, hσμ⟩ := CFSG.StandardType.TableBUF.exists_hilbert90_unitary hKq
    (by decide) (by norm_num) Nat.prime_three hσ3 hσ1 hcq hcPN
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hμq
    exact zero_ne_one hμq
  set μ' : Kˣ := Units.mk0 μ hμ0 with hμ'
  have hμN : h.norm (μ' : K) = 1 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.norm_eq_pow h]
    exact hμq
  have hμU : GeneralLinearGroup.scalar (Fin 3) μ' ∈
      primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    scalar_mem_primeFormUnitary_one h hμN
  set z' : primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := z * ⟨_, hμU⟩ with hz'
  have hσμ' : Units.map σ.toMonoidHom μ' = c⁻¹ * μ' := Units.ext (by
    rw [Units.coe_map, Units.val_mul, hμ', Units.val_mk0]
    exact hσμ)
  have hz'σ : glAut σ (z' : GL (Fin 3) K) = z' := by
    change glAut σ ((z : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) μ') =
      (z : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) μ'
    rw [map_mul, hc, t158Core_glAut_scalar, hσμ', map_mul, map_inv]
    group
  have hcz' : primeFormConjHom h _ z' = primeFormConjHom h _ z := by
    rw [hz', map_mul, primeFormConjHom_scalar h 3 μ' hμU, mul_one]
  obtain ⟨z₀, hz₀⟩ := exists_subfieldGL_eq_of_fixed 3 hz'σ
  have hz₀U : z₀ ∈ primeFormUnitary h₀
      ((1 : GL (Fin 3) (fixSubfield σ)) : Matrix (Fin 3) (Fin 3) (fixSubfield σ)) := by
    have h1 : (z' : GL (Fin 3) K) ∈ primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
      z'.2
    rw [mem_primeFormUnitary, ← hz₀, Units.val_one, Matrix.mul_one, coe_subfieldGL,
      map_subtype_map_bar h h₀ hbar, ← Matrix.transpose_map, ← Matrix.map_mul] at h1
    rw [mem_primeFormUnitary, Units.val_one, Matrix.mul_one]
    refine Matrix.map_injective (f := ((fixSubfield σ).subtype : fixSubfield σ → K))
      Subtype.val_injective ?_
    change (((z₀ : Matrix (Fin 3) (Fin 3) (fixSubfield σ)).map h₀.bar)ᵀ * z₀).map (fixSubfield σ).subtype =
      (1 : Matrix (Fin 3) (Fin 3) (fixSubfield σ)).map (fixSubfield σ).subtype
    rw [h1, Matrix.map_one _ (map_zero _) (map_one _)]
  set x₀ := primeFormConjHom h₀ _ ⟨z₀, hz₀U⟩ with hx₀
  set j := primeSubfieldPSU h Nat.prime_three (by decide) hσ 3 with hj
  have hint : ∀ y, j (x₀ y) = primeFormConjHom h _ z' (j y) := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H g =>
      rw [hx₀, primeFormConjHom_mk]
      change subfieldPSU h h₀ hbar 3 _ = primeFormConjHom h _ z' (subfieldPSU h h₀ hbar 3 _)
      rw [subfieldPSU_mk, subfieldPSU_mk, primeFormConjHom_mk]
      congr 1
      apply Subtype.ext
      change subfieldGL (fixSubfield σ) 3 (z₀ * (g : GL (Fin 3) (fixSubfield σ)) * z₀⁻¹) =
        (z' : GL (Fin 3) K) * subfieldGL (fixSubfield σ) 3 g * (z' : GL (Fin 3) K)⁻¹
      rw [map_mul, map_mul, map_inv, hz₀]
  have hfix : ∀ y, fσ (j y) = j y := fun y => range_subfieldPSU_le h 3 h₀ hbar ⟨y, rfl⟩
  have hfixk : ∀ (m : ℕ) y, (fσ ^ m) (j y) = j y := by
    intro m y
    induction m with
    | zero => rfl
    | succ m ih => rw [pow_succ, MulAut.mul_apply, hfix, ih]
  have hγeq : γ = primeFormConjHom h _ z * fσ ^ k := by
    rw [hz]
    group
  have hact : ∀ y, γ (j y) = j (x₀ y) := by
    intro y
    rw [hγeq, MulAut.mul_apply, hfixk, hint, hcz']
  have hjinj : Function.Injective j := subfieldPSU_injective h h₀ hbar 3 (by norm_num)
  have hintm : ∀ (m : ℕ) y, j ((x₀ ^ m) y) = ((primeFormConjHom h _ z) ^ m) (j y) := by
    intro m y
    induction m generalizing y with
    | zero => rfl
    | succ m ih => rw [pow_succ, MulAut.mul_apply, ih, hint, hcz', pow_succ, MulAut.mul_apply]
  have hx₀3 : x₀ ^ 3 = 1 := by
    ext y
    apply hjinj
    rw [hintm, hd3, MulAut.one_apply, MulAut.one_apply]
  exact ⟨x₀, CFSG.LocalAnalysis.GLTheoremA.KD264Lie.mem_innAutDerived_of_mem_primeFormD h₀ Nat.prime_three
    (by norm_num) ⟨_, rfl⟩ hx₀3, hact⟩

end FieldModel

theorem t158Core_congr_apply_apply {G H : Type} [Group G] [Group H] (e : G ≃* H) (α : MulAut G) (g : G) :
    MulAut.congr e α (e g) = e (α g) := by
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

theorem t158Core_eq_commutator_of_glaPComponent {G : Type} [Group G] [Finite G] {X T : Subgroup G}
    (hT : GLAPComponent 3 X T) (hs : IsSimpleGroup ↥(⁅X, X⁆ : Subgroup G)) (hne : T ≠ ⊥) :
    T = ⁅X, X⁆ := by
  have hperf : ⁅T, T⁆ = T := glaPComponent_perfect hT
  have hTX : T ≤ X := hT.1
  have hTXX : T ≤ ⁅X, X⁆ := by
    rw [← hperf]
    exact Subgroup.commutator_mono hTX hTX
  have hXX : (⁅X, X⁆ : Subgroup G) ≤ X := Subgroup.commutator_le.mpr fun a ha b hb =>
    X.mul_mem (X.mul_mem (X.mul_mem ha hb) (X.inv_mem ha)) (X.inv_mem hb)
  have hsub : CFSG.Assembly.IsSubnormal T X := CFSG.Assembly.isSubnormal_iff_open.2 hT.2.1
  exact CFSG.StandardType.ggEq_of_isSubnormal_of_isSimpleGroup
    (CFSG.StandardType.ggIsSubnormal_of_le_of_le hsub hTXX hXX) hs hne

section FieldCore

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.LieType.Chevalley

theorem t158FieldCoreU_holds : T158Inn.T158FieldCoreU := by
  intro Ω _ _ S x₁ x₂ L₁ L₂ hSn hq hcore hx1 hx2 hc hx1N hmk hL1 hU1 _ _ _ hF21
  classical
  have hSc : GLAPComponent 3 S S :=
    CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_self_of_quasisimple hq hcore
  have hN : ∀ y : Ω, y ∈ Subgroup.normalizer (S : Set Ω) := fun y => by
    rw [Subgroup.normalizer_eq_top_iff.2 hSn]
    exact Subgroup.mem_top y
  set β := MI.indAut 3 S x₁ (hN x₁) with hβdef
  set x := MI.indAut 3 S x₂ (hN x₂) with hxdef
  have hβx : β * x = x * β := by
    rw [hβdef, hxdef, MI.indAut, MI.indAut, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change x₁⁻¹ * x₂⁻¹ = x₂⁻¹ * x₁⁻¹
    rw [← _root_.mul_inv_rev, ← _root_.mul_inv_rev, hc]
  have hx3 : x ^ 3 = 1 := by
    rw [hxdef, t158Core_indAut_eq_inv (hN x₂), inv_pow, chevAut_pow_eq_one 3 S (hN x₂) hx2, inv_one]
  obtain ⟨-, lab, -, hraw⟩ := hmk
  obtain ⟨R, _, I, F, -, -, θ, hlab9, -⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  subst hlab9
  dsimp only [CFSG.Assembly.LargeEvenRawDatum, CFSG.Assembly.LargeEvenRecipeUnitary] at hraw
  obtain ⟨K, hKf, hKfin, hKcard, -, -, θ, -, -, f, hf, u, hu, hord, hind⟩ := hraw
  letI := hKf
  letI := hKfin
  have e1 : u * f * u⁻¹ = MulAut.congr θ (MI.indAut 3 S x₁ hx1N) := (MI.induces_indRel_iff hx1N θ).1 hind
  have hKcard' : Nat.card K = 2 ^ (2 * 9) := by rw [hKcard]; norm_num
  let h : UnitaryFieldData 2 9 K := ⟨Nat.prime_two, by norm_num, hKcard'⟩
  have hd1 : 1 ≤ 2 + 1 := by norm_num
  have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one
  let ψ := CFSG.StandardType.InndiagSU.projEquiv h hd1
  have huD : MulAut.congr ψ u ∈ primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    CFSG.StandardType.InndiagSU.congr_mem_primeFormD h hd1 hKcard hu
  obtain ⟨σ, hσf⟩ := CFSG.StandardType.RecipeFieldSU.congr_field_eq h hd1 hf
  set fσ := primeFormFieldHom h hC σ with hfσ
  have hn : 3 ≤ 3 := le_rfl
  have hne : ¬(3 = 3 ∧ 2 ^ 9 = 2) := by norm_num
  have hΘσ : ∀ τ : K ≃+* K, primeFormFieldFactor h hC hn hne (primeFormFieldHom h hC τ) = τ := by
    intro τ
    have := primeFormFieldFactor_apply h hC hn hne 1 τ
    rwa [map_one, one_mul] at this
  have hfinj : Function.Injective (primeFormFieldHom h hC) := fun a b hab => by
    rw [← hΘσ a, ← hΘσ b, hab]
  have hσ : orderOf σ = 3 := by
    rw [← orderOf_injective _ hfinj σ, ← hfσ, ← hσf, MulEquiv.orderOf_eq]
    exact hord
  obtain ⟨A, hA⟩ := huD
  set u' := MulAut.congr ψ u with hu'
  let Φ : PSimple 3 S ≃* primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    (θ.trans ψ).trans (u'⁻¹ : MulAut _)
  have hcongrΦ : ∀ α : MulAut (PSimple 3 S),
      MulAut.congr Φ α = u'⁻¹ * MulAut.congr ψ (MulAut.congr θ α) * u' := by
    intro α
    ext y
    rfl
  have hΦβ : MulAut.congr Φ β = fσ := by
    rw [hcongrΦ, hβdef, ← e1, map_mul, map_mul, map_inv, ← hu', hσf]
    group
  set γ := MulAut.congr Φ x with hγdef
  have hγ3 : γ ^ 3 = 1 := by rw [hγdef, ← map_pow, hx3, map_one]
  have hγc : fσ * γ = γ * fσ := by
    rw [← hΦβ, hγdef, ← map_mul, ← map_mul, hβx]
  set h₀ := fixSubfield_unitaryFieldData h Nat.prime_three (by decide) hσ with hh₀
  set hbar := fixSubfield_unitaryFieldData_bar h Nat.prime_three (by decide) hσ with hhbar
  set j := primeSubfieldPSU h Nat.prime_three (by decide) hσ 3 with hj
  have hjinj : Function.Injective j := subfieldPSU_injective h h₀ hbar 3 (by norm_num)
  obtain ⟨x₀, hx₀, hact⟩ := t158Core_subfield_restrict h hσ hγ3 hγc
  have hact' : ∀ y, γ (j y) = j (x₀ y) := hact
  have hq₀ : ¬(3 = 3 ∧ 2 ^ (9 / 3) = 2) := by norm_num
  have hP₀simple : IsSimpleGroup (primeFormP h₀
      ((1 : GL (Fin 3) (fixSubfield σ)) : Matrix (Fin 3) (Fin 3) (fixSubfield σ))) :=
    isSimpleGroup_primeFormP_one h₀ (by norm_num) hq₀
  have hP₀perf : Group.IsPerfect (primeFormP h₀
      ((1 : GL (Fin 3) (fixSubfield σ)) : Matrix (Fin 3) (Fin 3) (fixSubfield σ))) := by
    haveI := isPerfect_gramSU_one h₀ (by norm_num) hq₀
    exact Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have hJC : j.range ≤ fixSubgroup fσ := fun y hy => by
    rw [mem_fixSubgroup]
    exact range_subfieldPSU_le h 3 h₀ hbar hy
  have hCJ : ⁅fixSubgroup fσ, fixSubgroup fσ⁆ ≤ j.range :=
    CFSG.HardMathSupport.Dickson.Sec6.I923.commutator_fixed_le_range h hσ
  have hJperf : ⁅j.range, j.range⁆ = j.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
      hP₀perf.commutator_eq_top]
  have hCC : ⁅fixSubgroup fσ, fixSubgroup fσ⁆ = j.range :=
    le_antisymm hCJ (hJperf ▸ Subgroup.commutator_mono hJC hJC)
  have hfixΦ : (fixSubgroup β).map (Φ : PSimple 3 S →* _) = fixSubgroup fσ := by
    rw [← hΦβ, CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr]
  have hCCmap : (⁅fixSubgroup β, fixSubgroup β⁆ : Subgroup (PSimple 3 S)).map (Φ : PSimple 3 S →* _) =
      j.range := by
    rw [Subgroup.map_commutator, hfixΦ, hCC]
  let eCC : ↥(⁅fixSubgroup β, fixSubgroup β⁆ : Subgroup (PSimple 3 S)) ≃*
      primeFormP h₀ ((1 : GL (Fin 3) (fixSubfield σ)) : Matrix (Fin 3) (Fin 3) (fixSubfield σ)) :=
    ((Subgroup.equivMapOfInjective _ (Φ : PSimple 3 S →* _) Φ.injective).trans
      (MulEquiv.subgroupCongr hCCmap)).trans (MonoidHom.ofInjective hjinj).symm
  haveI hsCC : IsSimpleGroup ↥(⁅fixSubgroup β, fixSubgroup β⁆ : Subgroup (PSimple 3 S)) :=
    (MulEquiv.isSimpleGroup_congr eCC).2 hP₀simple
  obtain ⟨hT1, -, hcT1⟩ := t158Core_transfer (hN x₁) hx1 hL1 hU1
  have hfixβ : fixSubgroup (chevAut 3 S ⟨x₁, hN x₁⟩) = fixSubgroup β := by
    rw [hβdef, t158Core_indAut_eq_inv (hN x₁),
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.fixSubgroup_inv_eq]
  rw [hfixβ] at hT1
  have hT1ne : chevTransfer 3 S L₁ ≠ ⊥ := by
    intro hbot
    have h19 : 19 ∣ Nat.card ↥(chevTransfer 3 S L₁) := by
      have h0 : 19 ∣ Nat.card (PSimple 3 (chevTransfer 3 S L₁)) := by rw [hcT1]; norm_num
      exact h0.trans (t158Core_card_pSimple_dvd _)
    rw [hbot, Subgroup.card_bot] at h19
    norm_num at h19
  have hT1eq : chevTransfer 3 S L₁ = ⁅fixSubgroup β, fixSubgroup β⁆ :=
    t158Core_eq_commutator_of_glaPComponent hT1 hsCC hT1ne
  let ε : ↥(chevTransfer 3 S L₁) ≃*
      primeFormP h₀ ((1 : GL (Fin 3) (fixSubfield σ)) : Matrix (Fin 3) (Fin 3) (fixSubfield σ)) :=
    (MulEquiv.subgroupCongr hT1eq).trans eCC
  have hεj : ∀ t : ↥(chevTransfer 3 S L₁), j (ε t) = Φ (t : PSimple 3 S) := by
    intro t
    change j ((MonoidHom.ofInjective hjinj).symm _) = _
    rw [← MonoidHom.ofInjective_apply hjinj, MulEquiv.apply_symm_apply]
    rfl
  have hTq : CFSG.Open.IsQuasisimple ↥(chevTransfer 3 S L₁) := by
    haveI hsT : IsSimpleGroup ↥(chevTransfer 3 S L₁) := (MulEquiv.isSimpleGroup_congr ε).2 hP₀simple
    haveI : Group.IsPerfect ↥(chevTransfer 3 S L₁) :=
      Group.IsPerfect.ofSurjective (f := ε.symm.toMonoidHom) ε.symm.surjective
    have hZ : Subgroup.center ↥(chevTransfer 3 S L₁) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(chevTransfer 3 S L₁)) with hZ | hZ
      · exact hZ
      · exfalso
        apply not_commute_primeFormP_one h₀ (by norm_num) hq₀
        intro a b
        apply ε.symm.injective
        rw [map_mul, map_mul]
        have hb : ε.symm b ∈ Subgroup.center ↥(chevTransfer 3 S L₁) := hZ ▸ Subgroup.mem_top _
        exact (Subgroup.mem_center_iff.1 hb (ε.symm a))
    refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
    exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup
  refine t158Core_false_of_restrict (hN x₁) (hN x₂) hx1 hL1 hU1 hF21 hTq (fun hstab => ?_)
  have hres : MulAut.congr ε (CFSG.GroupActions.subgroupStabRestrict (chevTransfer 3 S L₁)
      ⟨x, hstab⟩) = x₀ := by
    ext y
    obtain ⟨t, rfl⟩ := ε.surjective y
    apply hjinj
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      hεj, CFSG.GroupActions.subgroupStabRestrict_apply, ← hact', hεj]
    exact (t158Core_congr_apply_apply Φ x t).symm
  have hmem : CFSG.GroupActions.subgroupStabRestrict (chevTransfer 3 S L₁) ⟨x, hstab⟩ ∈
      innAutDerived ↥(chevTransfer 3 S L₁) := by
    rw [← mem_innAutDerived_congr ε, hres]
    exact hx₀
  exact CFSG.ComponentClassification.PerfectCentralQuotient.centerQuotientHom_mem_innAutDerived hmem

end FieldCore

end CFSG.LocalAnalysis.GLTheoremA.T158Core

end
