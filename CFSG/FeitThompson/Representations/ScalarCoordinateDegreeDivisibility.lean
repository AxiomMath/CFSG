module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.SemidirectProduct
public import CFSG.FeitThompson.Representations.NormalRestrictionSingleConstituentOrbit
public import CFSG.FeitThompson.Representations.InducedIrreducibleNormOrbitFormula
public import CFSG.FeitThompson.Definitions.KernelFilteredIrreducibleCharacters
import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
import CFSG.FeitThompson.Foundations.CoprimeActionFittingFaithful
import CFSG.FeitThompson.Representations.AbelianGroupIrreducibleCharacters
import CFSG.FeitThompson.OddOrder.ScalarLinesCoordinateEmbedding
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module SemidirectProduct

open NormalInduction (conjClassFun conjClassFun_apply)

variable {p q : ℕ} [Fact p.Prime] {V U : Type*} [AddCommGroup V] [Module (ZMod p) V] [Group U]

structure ScalarCoordinateSystem (p q : ℕ) [Fact p.Prime] (V U : Type*) [AddCommGroup V]
    [Module (ZMod p) V] [Group U] where
  two_le_q : 2 ≤ q
  line : Fin q → Submodule (ZMod p) V
  finrank_line : ∀ i, finrank (ZMod p) (line i) = 1
  indep_line : iSupIndep line
  iSup_line : ⨆ i, line i = ⊤
  act : U →* (V ≃ₗ[ZMod p] V)
  map_line : ∀ (u : U) (i : Fin q), ∀ v ∈ line i, act u v ∈ line i
  coprime_card : Nat.Coprime p (Nat.card U)

namespace ScalarCoordinateSystem

variable (S : ScalarCoordinateSystem p q V U)

noncomputable def lineScalar (i : Fin q) (u : U) : (ZMod p)ˣ :=
  (existsUnique_units_forall_apply_eq_smul (S.finrank_line i) (S.act u) (S.map_line u i)).choose

theorem act_apply_eq_lineScalar_smul (i : Fin q) (u : U) {v : V} (hv : v ∈ S.line i) :
    S.act u v = (S.lineScalar i u : ZMod p) • v :=
  (existsUnique_units_forall_apply_eq_smul (S.finrank_line i) (S.act u)
    (S.map_line u i)).choose_spec.1 v hv

theorem eq_lineScalar (i : Fin q) (u : U) {c : (ZMod p)ˣ}
    (hc : ∀ v ∈ S.line i, S.act u v = (c : ZMod p) • v) : c = S.lineScalar i u :=
  (existsUnique_units_forall_apply_eq_smul (S.finrank_line i) (S.act u)
    (S.map_line u i)).choose_spec.2 c hc

theorem lineScalar_one (i : Fin q) : S.lineScalar i 1 = 1 :=
  (S.eq_lineScalar i 1 fun v _ => by simp).symm

theorem lineScalar_mul (i : Fin q) (u u' : U) :
    S.lineScalar i (u * u') = S.lineScalar i u * S.lineScalar i u' := by
  refine (S.eq_lineScalar i (u * u') ?_).symm
  intro v hv
  rw [map_mul]
  have h : (S.act u * S.act u') v = S.act u (S.act u' v) := by simp
  rw [h, S.act_apply_eq_lineScalar_smul i u' hv, map_smul,
    S.act_apply_eq_lineScalar_smul i u hv]
  simp [smul_smul, mul_comm]

noncomputable def lineScalarHom (i : Fin q) : U →* (ZMod p)ˣ where
  toFun := S.lineScalar i
  map_one' := S.lineScalar_one i
  map_mul' := S.lineScalar_mul i

@[simp] theorem lineScalarHom_apply (i : Fin q) (u : U) :
    S.lineScalarHom i u = S.lineScalar i u := (rfl)

noncomputable def lineCentralizer (i : Fin q) : Subgroup U := (S.lineScalarHom i).ker

theorem lineCentralizer_eq_ker (i : Fin q) :
    S.lineCentralizer i = (S.lineScalarHom i).ker := (rfl)

theorem mem_lineCentralizer {i : Fin q} {u : U} :
    u ∈ S.lineCentralizer i ↔ ∀ v ∈ S.line i, S.act u v = v := by
  constructor
  · intro h v hv
    have h1 : S.lineScalar i u = 1 := h
    rw [S.act_apply_eq_lineScalar_smul i u hv, h1]
    simp
  · intro h
    exact (S.eq_lineScalar i u fun v hv => by rw [h v hv]; simp).symm

noncomputable def totalCentralizer : Subgroup U := S.act.ker

instance totalCentralizer_normal : (S.totalCentralizer).Normal := MonoidHom.normal_ker _

theorem mem_totalCentralizer {u : U} : u ∈ S.totalCentralizer ↔ ∀ v : V, S.act u v = v := by
  constructor
  · intro h v
    have h1 : S.act u = 1 := h
    rw [h1]; rfl
  · intro h
    exact LinearEquiv.ext h

theorem totalCentralizer_eq_iInf : S.totalCentralizer = ⨅ i, S.lineCentralizer i := by
  refine le_antisymm (le_iInf fun i => ?_) ?_
  · intro u hu
    exact S.mem_lineCentralizer.2 fun v _ => (S.mem_totalCentralizer.1 hu) v
  · intro u hu
    rw [Subgroup.mem_iInf] at hu
    refine S.mem_totalCentralizer.2 fun v => ?_
    have hle : (⊤ : Submodule (ZMod p) V) ≤
        LinearMap.eqLocus (S.act u : V →ₗ[ZMod p] V) LinearMap.id := by
      rw [← S.iSup_line]
      exact iSup_le fun i => fun w hw => (S.mem_lineCentralizer.1 (hu i)) w hw
    exact hle (Submodule.mem_top) (x := v)

theorem totalCentralizer_le_lineCentralizer (i : Fin q) :
    S.totalCentralizer ≤ S.lineCentralizer i := by
  rw [S.totalCentralizer_eq_iInf]
  exact iInf_le _ i

theorem index_lineCentralizer_dvd_sub_one (i : Fin q) :
    (S.lineCentralizer i).index ∣ p - 1 := by
  rw [S.lineCentralizer_eq_ker i, Subgroup.index_ker]
  have h := Subgroup.card_subgroup_dvd_card (S.lineScalarHom i).range
  rwa [Nat.card_eq_fintype_card (α := (ZMod p)ˣ), ZMod.card_units p] at h

theorem commutator_le_totalCentralizer : commutator U ≤ S.totalCentralizer := by
  rw [S.totalCentralizer_eq_iInf]
  refine le_iInf fun i => ?_
  rw [S.lineCentralizer_eq_ker i]
  exact Abelianization.commutator_subset_ker (S.lineScalarHom i)

theorem closure_setOf_inv_mul_inv_mul_mul_le_totalCentralizer :
    Subgroup.closure {g : U | ∃ x ∈ (⊤ : Subgroup U), ∃ y ∈ (⊤ : Subgroup U),
      x⁻¹ * y⁻¹ * x * y = g} ≤ S.totalCentralizer := by
  rw [closure_setOf_inv_mul_inv_mul_mul]
  exact S.commutator_le_totalCentralizer

theorem isMulCommutative_quotient_totalCentralizer :
    IsMulCommutative (U ⧸ S.totalCentralizer) :=
  Subgroup.Normal.quotient_commutative_iff_commutator_le.2 S.commutator_le_totalCentralizer

theorem index_lineCentralizer_dvd_index_totalCentralizer (i : Fin q) :
    (S.lineCentralizer i).index ∣ (S.totalCentralizer).index :=
  Subgroup.index_dvd_of_le (S.totalCentralizer_le_lineCentralizer i)

def mulAutHom : U →* MulAut (Multiplicative V) where
  toFun u := AddEquiv.toMultiplicative (S.act u).toAddEquiv
  map_one' := by ext x; simp
  map_mul' u u' := by ext x; simp

@[simp] theorem mulAutHom_apply (u : U) (v : V) :
    S.mulAutHom u (Multiplicative.ofAdd v) = Multiplicative.ofAdd (S.act u v) := (rfl)

abbrev grp : Type _ := Multiplicative V ⋊[S.mulAutHom] U

def base : Subgroup S.grp := (SemidirectProduct.inl : Multiplicative V →* S.grp).range

theorem inl_mem_base (x : Multiplicative V) : (inl x : S.grp) ∈ S.base := ⟨x, rfl⟩

instance base_normal : (S.base).Normal := range_inl_normal

instance base_isMulCommutative : IsMulCommutative (S.base) := by
  refine ⟨⟨?_⟩⟩
  rintro ⟨a, x, rfl⟩ ⟨b, y, rfl⟩
  refine Subtype.ext ?_
  change (inl x : S.grp) * inl y = inl y * inl x
  rw [← map_mul, ← map_mul, mul_comm]

def baseHom : Multiplicative V →* S.base :=
  (SemidirectProduct.inl : Multiplicative V →* S.grp).codRestrict S.base S.inl_mem_base

@[simp] theorem coe_baseHom_apply (x : Multiplicative V) :
    (S.baseHom x : S.grp) = inl x := (rfl)

noncomputable def baseEquiv : Multiplicative V ≃* S.base :=
  MonoidHom.ofInjective (f := (SemidirectProduct.inl : Multiplicative V →* S.grp)) inl_injective

theorem baseEquiv_apply (x : Multiplicative V) : S.baseEquiv x = S.baseHom x := Subtype.ext rfl

theorem comp_baseEquiv_mem_Irr {lam : S.base → ℂ} (h : lam ∈ Irr S.base) :
    lam ∘ S.baseEquiv ∈ Irr (Multiplicative V) := by
  rw [← normalInduction_irrChars_eq_Irr] at h ⊢
  exact NormalInduction.mem_irrChars_comp_mulEquiv h S.baseEquiv

theorem apply_one_eq_one_of_mem_Irr_base {lam : S.base → ℂ} (h : lam ∈ Irr S.base) :
    lam 1 = 1 := by
  have := Irr.apply_one_eq_one (S.comp_baseEquiv_mem_Irr h)
  simpa using this

theorem exists_monoidHom_units_eq_of_mem_Irr_base {lam : S.base → ℂ} (h : lam ∈ Irr S.base) :
    ∃ ψ : Multiplicative V →* ℂˣ, ∀ y : Multiplicative V, (ψ y : ℂ) = lam (S.baseHom y) := by
  obtain ⟨ψ, hψ⟩ := exists_linearCharFun_eq_of_mem_Irr (S.comp_baseEquiv_mem_Irr h)
  refine ⟨ψ, fun y => ?_⟩
  have hy := congrFun hψ y
  rw [linearCharFun_apply] at hy
  rw [hy]
  exact congrArg lam (S.baseEquiv_apply y)

include S in
theorem finite_of_finite_line : Finite V := by
  have h1 : ∀ i, FiniteDimensional (ZMod p) (S.line i) := fun i =>
    Module.finite_of_finrank_eq_succ (n := 0) (S.finrank_line i)
  have h2 : FiniteDimensional (ZMod p) (⨆ i, S.line i : Submodule (ZMod p) V) :=
    Submodule.finiteDimensional_iSup _
  rw [S.iSup_line] at h2
  have : FiniteDimensional (ZMod p) V := Module.Finite.equiv Submodule.topEquiv
  exact Module.finite_of_finite (ZMod p)

theorem forall_apply_eq_one (χ : Multiplicative V →* ℂˣ)
    (h : ∀ i, ∀ v ∈ S.line i, χ (Multiplicative.ofAdd v) = 1) (v : V) :
    χ (Multiplicative.ofAdd v) = 1 := by
  have hmem : v ∈ ⨆ i, S.line i := by rw [S.iSup_line]; exact Submodule.mem_top
  refine Submodule.iSup_induction S.line (motive := fun w => χ (Multiplicative.ofAdd w) = 1)
    hmem (fun i x hx => h i x hx) (by simp) ?_
  intro x y hx hy
  rw [ofAdd_add, map_mul, hx, hy, one_mul]

theorem mem_lineCentralizer_of_apply_eq (χ : Multiplicative V →* ℂˣ) {i : Fin q} {v : V}
    (hv : v ∈ S.line i) (hne : χ (Multiplicative.ofAdd v) ≠ 1) {u : U}
    (h : χ (Multiplicative.ofAdd (S.act u v)) = χ (Multiplicative.ofAdd v)) :
    u ∈ S.lineCentralizer i := by
  have hp0 : (p : ℕ) • v = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod p)]
    simp
  have hζp : χ (Multiplicative.ofAdd v) ^ p = 1 := by
    have hpow : χ (Multiplicative.ofAdd ((p : ℕ) • v)) = χ (Multiplicative.ofAdd v) ^ p := by
      rw [ofAdd_nsmul, map_pow]
    rw [hp0] at hpow
    simpa using hpow.symm
  have hord : orderOf (χ (Multiplicative.ofAdd v)) = p := orderOf_eq_prime hζp hne
  have hc : S.act u v = ((S.lineScalar i u : ZMod p)) • v :=
    S.act_apply_eq_lineScalar_smul i u hv
  have hcast : (((S.lineScalar i u : ZMod p).val : ℕ) : ZMod p) = (S.lineScalar i u : ZMod p) := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  have hn : ((S.lineScalar i u : ZMod p)) • v = ((S.lineScalar i u : ZMod p).val : ℕ) • v := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod p), hcast]
  rw [hc, hn, ofAdd_nsmul, map_pow] at h
  have h1 : χ (Multiplicative.ofAdd v) ^ ((S.lineScalar i u : ZMod p).val : ℕ)
      = χ (Multiplicative.ofAdd v) ^ 1 := by rw [pow_one]; exact h
  have hmod : ((S.lineScalar i u : ZMod p).val : ℕ) ≡ 1
      [MOD orderOf (χ (Multiplicative.ofAdd v))] := pow_eq_pow_iff_modEq.1 h1
  rw [hord] at hmod
  have hval : (S.lineScalar i u : ZMod p) = 1 := by
    have h2 := (ZMod.natCast_eq_natCast_iff ((S.lineScalar i u : ZMod p).val) 1 p).2 hmod
    rw [hcast] at h2
    simpa using h2
  rw [S.lineCentralizer_eq_ker i, MonoidHom.mem_ker, S.lineScalarHom_apply]
  exact Units.ext hval

theorem conjClassFun_inr_apply (lam : S.base → ℂ) (u : U) (x : Multiplicative V) :
    conjClassFun S.base (inr u) lam (S.baseHom x) = lam (S.baseHom (S.mulAutHom u⁻¹ x)) := by
  rw [conjClassFun_apply]
  congr 1
  refine Subtype.ext ?_
  have haut := inl_aut (φ := S.mulAutHom) u⁻¹ x
  rw [MulAut.conjNormal_apply, coe_baseHom_apply, coe_baseHom_apply, haut, map_inv]
  group

theorem natCard_quotient_inertiaGroup_eq_card {K : Type*} [Group K] [Finite K] {N : Subgroup K}
    [N.Normal] [Fintype N] {θ : K → ℂ} (hθ : θ ∈ Irr K) {lam : N → ℂ}
    (hlam : lam ∈ resConstituents N θ) :
    Nat.card (K ⧸ inertiaGroup N lam) = (resConstituents N θ).card := by
  classical
  have hwd : ∀ s t : K, (QuotientGroup.leftRel (inertiaGroup N lam)).r s t →
      conjClassFun N s lam = conjClassFun N t lam := by
    intro s t hst
    have h : conjClassFun N (s⁻¹ * t) lam = lam :=
      mem_inertiaGroup.1 (QuotientGroup.leftRel_apply.mp hst)
    calc conjClassFun N s lam = conjClassFun N s (conjClassFun N (s⁻¹ * t) lam) := by rw [h]
      _ = conjClassFun N (s * (s⁻¹ * t)) lam := (conjClassFun_mul N s _ lam).symm
      _ = conjClassFun N t lam := by rw [mul_inv_cancel_left]
  set f : K ⧸ inertiaGroup N lam → (N → ℂ) := fun z => Quotient.liftOn z
    (fun t => conjClassFun N t lam) hwd with hf
  have hfmk : ∀ t : K, f (t : K ⧸ inertiaGroup N lam) = conjClassFun N t lam := fun _ => rfl
  have hmem : ∀ z, f z ∈ (resConstituents N θ : Set (N → ℂ)) := by
    intro z
    induction z using QuotientGroup.induction_on with
    | _ t =>
      rw [hfmk]
      exact (mem_resConstituents_iff_exists_conjClassFun hθ hlam).2 ⟨t, rfl⟩
  have hbij : Function.Bijective
      (fun z => (⟨f z, hmem z⟩ : ↥(resConstituents N θ : Set (N → ℂ)))) := by
    constructor
    · intro z z' hzz'
      have h := congrArg Subtype.val hzz'
      simp only at h
      induction z using QuotientGroup.induction_on with
      | _ s =>
      induction z' using QuotientGroup.induction_on with
      | _ t =>
      rw [hfmk, hfmk] at h
      refine QuotientGroup.eq.mpr (mem_inertiaGroup.2 ?_)
      rw [conjClassFun_mul, ← h, ← conjClassFun_mul, inv_mul_cancel, conjClassFun_one]
    · rintro ⟨mu, hmu⟩
      obtain ⟨t, ht⟩ := (mem_resConstituents_iff_exists_conjClassFun hθ hlam).1 hmu
      exact ⟨(t : K ⧸ inertiaGroup N lam), Subtype.ext (by simp only; rw [hfmk, ht])⟩
  rw [Nat.card_eq_of_bijective _ hbij, Nat.card_coe_set_eq, Set.ncard_coe_finset]

theorem exists_degree_dvd [Finite U] {a : ℕ} (ha : ∀ i, (S.lineCentralizer i).index = a)
    {θ : S.grp → ℂ} (hθ : θ ∈ Irr S.grp)
    (hker : ¬ (S.base : Set S.grp) ⊆ charValueKernel θ) :
    ∃ n : ℕ, θ 1 = (n : ℂ) ∧ a ∣ n := by
  classical
  have : Finite V := S.finite_of_finite_line
  have : Finite S.grp := inferInstance
  have : Fintype S.base := Fintype.ofFinite _
  obtain ⟨e, -, -, hres⟩ := exists_pos_resClassFun_eq_nsmul_sum (N := S.base) hθ
  set T := resConstituents S.base θ with hT
  have hval : ∀ x : S.base, θ (x : S.grp) = (e : ℂ) * ∑ lam ∈ T, lam x := by
    intro x
    have h := congrFun hres x
    rw [resClassFun_apply] at h
    rw [h]
    simp [Finset.sum_apply]
  have hone : ∀ lam ∈ T, lam (1 : S.base) = 1 := fun lam hl =>
    S.apply_one_eq_one_of_mem_Irr_base (resConstituents_subset_Irr (Finset.mem_coe.2 hl))
  have hdeg : θ 1 = ((e * T.card : ℕ) : ℂ) := by
    have h := hval 1
    rw [Subgroup.coe_one, Finset.sum_congr rfl hone] at h
    rw [h]
    push_cast
    simp
  by_cases hprinc : ∀ lam ∈ T, ∀ x : S.base, lam x = 1
  · refine absurd (fun g hg => ?_) hker
    have hconst : ∀ x : S.base, θ (x : S.grp) = (e : ℂ) * (T.card : ℂ) := by
      intro x
      rw [hval x, Finset.sum_congr rfl fun lam hl => hprinc lam hl x]
      simp
    rw [mem_charValueKernel]
    calc θ g = θ ((⟨g, hg⟩ : S.base) : S.grp) := rfl
      _ = (e : ℂ) * (T.card : ℂ) := hconst _
      _ = θ ((1 : S.base) : S.grp) := (hconst 1).symm
      _ = θ 1 := by rw [Subgroup.coe_one]
  · obtain ⟨lam, hlamT, x₀, hx₀⟩ : ∃ lam ∈ T, ∃ x : S.base, lam x ≠ 1 := by
      obtain ⟨lam, h1⟩ := not_forall.1 hprinc
      obtain ⟨hlamT, h2⟩ := Classical.not_imp.1 h1
      obtain ⟨x, hx⟩ := not_forall.1 h2
      exact ⟨lam, hlamT, x, hx⟩
    have hlamIrr : lam ∈ Irr S.base := (mem_resConstituents.1 hlamT).1
    obtain ⟨χ, hχval⟩ := S.exists_monoidHom_units_eq_of_mem_Irr_base hlamIrr
    have hexne : ∃ y : Multiplicative V, χ y ≠ 1 := by
      obtain ⟨y, hy⟩ := x₀.2
      refine ⟨y, fun hcon => hx₀ ?_⟩
      have h := hχval y
      rw [hcon] at h
      have hxy : S.baseHom y = x₀ := Subtype.ext hy
      rw [hxy] at h
      simpa using h.symm
    obtain ⟨i, v, hvline, hvne⟩ : ∃ i, ∃ v ∈ S.line i, χ (Multiplicative.ofAdd v) ≠ 1 := by
      by_cases hall : ∀ i, ∀ v ∈ S.line i, χ (Multiplicative.ofAdd v) = 1
      · obtain ⟨y, hy⟩ := hexne
        exact absurd (S.forall_apply_eq_one χ hall (Multiplicative.toAdd y)) hy
      · obtain ⟨i, h1⟩ := not_forall.1 hall
        obtain ⟨v, h2⟩ := not_forall.1 h1
        obtain ⟨hvline, hvne⟩ := Classical.not_imp.1 h2
        exact ⟨i, v, hvline, hvne⟩
    set I := inertiaGroup S.base lam with hI
    have hbaseI : S.base ≤ I := le_inertiaGroup S.base (Irr_subset_classFun hlamIrr)
    have hWle : I.map (rightHom : S.grp →* U) ≤ S.lineCentralizer i := by
      rintro w ⟨g, hgI, rfl⟩
      have hinr : (inr (rightHom g) : S.grp) ∈ I := by
        have hg : (inl g.left : S.grp) * inr g.right = g := inl_left_mul_inr_right g
        have h1 : (inl g.left : S.grp) ∈ I := hbaseI (S.inl_mem_base _)
        have h2 : (inr g.right : S.grp) = (inl g.left)⁻¹ * g := eq_inv_mul_of_mul_eq hg
        rw [rightHom_eq_right, h2]
        exact I.mul_mem (I.inv_mem h1) hgI
      have hfix : conjClassFun S.base (inr (rightHom g)) lam = lam := mem_inertiaGroup.1 hinr
      have hkey : χ (Multiplicative.ofAdd (S.act (rightHom g)⁻¹ v))
          = χ (Multiplicative.ofAdd v) := by
        refine Units.ext ?_
        have h := congrFun hfix (S.baseHom (Multiplicative.ofAdd v))
        rw [S.conjClassFun_inr_apply lam (rightHom g) (Multiplicative.ofAdd v),
          S.mulAutHom_apply] at h
        rw [hχval, hχval, h]
      have hinv : (rightHom g)⁻¹ ∈ S.lineCentralizer i :=
        S.mem_lineCentralizer_of_apply_eq χ hvline hvne hkey
      simpa using (S.lineCentralizer i).inv_mem hinv
    have hindex : (I.map (rightHom : S.grp →* U)).index = I.index := by
      refine Subgroup.index_map_eq I rightHom_surjective ?_
      rw [← range_inl_eq_ker_rightHom]
      exact hbaseI
    have hdvd1 : a ∣ I.index := by
      rw [← ha i, ← hindex]
      exact Subgroup.index_dvd_of_le hWle
    have hcard : I.index = T.card := by
      rw [Subgroup.index_eq_card, hI]
      exact natCard_quotient_inertiaGroup_eq_card hθ hlamT
    refine ⟨e * T.card, hdeg, ?_⟩
    rw [hcard] at hdvd1
    exact hdvd1.trans (Dvd.intro_left e rfl)

end ScalarCoordinateSystem

end CFSG.FeitThompson
