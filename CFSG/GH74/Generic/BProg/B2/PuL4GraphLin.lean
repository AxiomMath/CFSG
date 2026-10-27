module

public import CFSG.GH74.Generic.BProg.B2.PumpupTableOmega3
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorRowO
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4ESplit
public import CFSG.GH74.GLS.Stage2.Final.ModelType
public import CFSG.GH74.Generic.BProg.B2.GenLocL4Refl
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearHigherBFixed

public section

namespace CFSG.GH74.Generic.BProg.B2

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.ComponentClassification
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.OutcomeLocal
  CFSG.ComponentClassification.OddSelector CFSG CFSG.GH74 CFSG.GH74.GLS
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace PuL4GraphLin

theorem eq_one_of_mul_self_of_mod_eight {F : Type} [Field F] [Finite F] (hF : Nat.card F % 8 = 5)
    (σ : F ≃+* F) (hσ : σ * σ = 1) : σ = 1 := by
  by_contra h1
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hσ) h1
  have hcard := CFSG.GH74.GLS.IVK.fixedField_card_pow σ
  rw [hord] at hcard
  set r := Nat.card ↥(CFSG.GH74.GLS.IVK.fixedField σ) with hr
  have hodd : r % 2 = 1 := by
    by_contra h
    have : r % 2 = 0 := by omega
    obtain ⟨k, hk⟩ : 2 ∣ r := Nat.dvd_of_mod_eq_zero this
    have : r ^ 2 % 8 = 0 ∨ r ^ 2 % 8 = 4 := by
      rw [hk]; ring_nf; omega
    omega
  have : r ^ 2 % 8 = 1 := by
    obtain ⟨k, hk⟩ : ∃ k, r = 2 * k + 1 := ⟨r / 2, by omega⟩
    rw [hk]
    have : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
    rw [this]
    have h2 : 2 ∣ k * (k + 1) := by
      rcases Nat.even_or_odd k with he | ho
      · exact Dvd.dvd.mul_right (even_iff_two_dvd.mp he) _
      · exact Dvd.dvd.mul_left (even_iff_two_dvd.mp (Odd.add_one ho)) _
    obtain ⟨m, hm⟩ := h2
    rw [hm]; omega
  omega

open Matrix in
theorem graph_form_of_not_diag {F : Type} [Field F] [Finite F] (hF : Nat.card F % 8 = 5)
    (τ : MulAut (LinearFlag.projectiveSL 4 F)) (hτ : τ ^ 2 = 1)
    (hnd : ∀ A : GL (Fin 4) F, τ ≠ LinearFlag.conjAut 4 F A) :
    ∃ A : GL (Fin 4) F, τ = LinearFlag.conjAut 4 F A * LinearFlag.dualAut 4 F ∧
      (((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ = (A : Matrix (Fin 4) (Fin 4) F) ∨
        ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ = -(A : Matrix (Fin 4) (Fin 4) F)) := by
  obtain ⟨-, hgen⟩ := LinearFlag.automorphism_generation (K := F) (n := 4) (by norm_num)
  obtain ⟨A, σ, ε, hε, hτA⟩ := hgen τ
  obtain ⟨-, -, hfc, hδδ, hδc, hδf, -⟩ := LinearFlag.standard_automorphism_transport (K := F) (n := 4)
  have hsq : τ * τ = 1 := by rw [← pow_two]; exact hτ
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  ·
    rw [pow_zero, mul_one] at hτA
    rw [hτA, LinearFlag.conjAut_mul_fieldAut_mul] at hsq
    obtain ⟨hσ, -⟩ := LinearFlag.eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num : 3 ≤ 4) _ _ hsq
    have hσ1 : σ = 1 := eq_one_of_mul_self_of_mod_eight hF σ hσ
    exact (hnd A (by rw [hτA, hσ1, map_one, mul_one])).elim
  ·
    rw [pow_one] at hτA
    set A' := GeneralLinearGroup.inverseTranspose A with hA'
    have hδ : LinearFlag.dualAut 4 F * (LinearFlag.conjAut 4 F A * LinearFlag.fieldAut 4 F σ) *
        LinearFlag.dualAut 4 F = LinearFlag.conjAut 4 F A' * LinearFlag.fieldAut 4 F σ := by
      have := hδc A
      have h2 := hδf σ
      calc LinearFlag.dualAut 4 F * (LinearFlag.conjAut 4 F A * LinearFlag.fieldAut 4 F σ) *
          LinearFlag.dualAut 4 F
          = (LinearFlag.dualAut 4 F * LinearFlag.conjAut 4 F A * LinearFlag.dualAut 4 F) *
            (LinearFlag.dualAut 4 F * LinearFlag.fieldAut 4 F σ * LinearFlag.dualAut 4 F) := by
            calc _ = LinearFlag.dualAut 4 F * LinearFlag.conjAut 4 F A *
                  (LinearFlag.dualAut 4 F * LinearFlag.dualAut 4 F) * LinearFlag.fieldAut 4 F σ *
                  LinearFlag.dualAut 4 F := by rw [hδδ]; group
              _ = _ := by group
        _ = _ := by rw [this, h2]
    have h1 : τ * τ = LinearFlag.conjAut 4 F (A * GeneralLinearGroup.map (σ : F →+* F) A') *
        LinearFlag.fieldAut 4 F (σ * σ) := by
      rw [hτA, ← LinearFlag.conjAut_mul_fieldAut_mul, ← hδ]
      group
    rw [h1] at hsq
    obtain ⟨hσ, c, hc⟩ := LinearFlag.eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num : 3 ≤ 4) _ _ hsq
    have hσ1 : σ = 1 := eq_one_of_mul_self_of_mod_eight hF σ hσ
    subst hσ1
    refine ⟨A, by rw [hτA, map_one, mul_one], ?_⟩
    have hAc : ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        (c : F) • ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ := by
      have h3 : (A * GeneralLinearGroup.map ((1 : F ≃+* F) : F →+* F) A' : GL (Fin 4) F) =
          GeneralLinearGroup.scalar (Fin 4) c := hc.symm
      have h4 : ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
          (((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ) = (c : F) • (1 : Matrix (Fin 4) (Fin 4) F) := by
        have := congrArg (fun u : GL (Fin 4) F => (u : Matrix (Fin 4) (Fin 4) F)) h3
        simpa [hA', GeneralLinearGroup.coe_inverseTranspose, Matrix.smul_eq_diagonal_mul,
          GeneralLinearGroup.coe_scalar] using this
      have h5 : ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ *
          ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ = 1 := by
        rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
      calc ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
          = ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
              (((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ *
                ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ) := by rw [h5, Matrix.mul_one]
        _ = ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
              (((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ) *
                ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ := by rw [Matrix.mul_assoc]
        _ = (c : F) • ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ := by
          rw [h4, Matrix.smul_mul, Matrix.one_mul]
    have hAT : ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ =
        (c : F) • ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
      have := congrArg Matrix.transpose hAc
      rwa [Matrix.transpose_smul, Matrix.transpose_transpose] at this
    have hc2 : (c : F) * c = 1 := by
      have h6 : ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
          ((c : F) * c) • ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
        calc ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
            = (c : F) • ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ := hAc
          _ = (c : F) • ((c : F) • ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) := by rw [hAT]
          _ = ((c : F) * c) • ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := smul_smul _ _ _
      have hA0 : ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) ≠ 0 := by
        intro h0
        have h7 := Units.mul_inv A
        rw [h0, Matrix.zero_mul] at h7
        exact zero_ne_one h7
      by_contra hne
      apply hA0
      have h8 : ((c : F) * c - 1) • ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 0 := by
        rw [sub_smul, one_smul, ← h6, sub_self]
      exact (smul_eq_zero.1 h8).resolve_left (sub_ne_zero.2 hne)
    rcases mul_self_eq_one_iff.1 hc2 with h | h
    · left; rw [hAT, h, one_smul]
    · right; rw [hAT, h, neg_smul, one_smul]

section Cover

variable {k : Type} [Field k] [Finite k] {m : ℕ}
variable {A : Type} [Group A] {a : A} {L : Subgroup A}

theorem exists_sp_cover (hm : 4 ≤ m) (hk2 : ringChar k ≠ 2) (hodd : Odd (Nat.card k))
    {ρ : A →* MulAut (projectiveSL m k)} (hinj : Function.Injective ρ)
    (hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ)
      (OuterAutomorphisms.inner (projectiveSL m k) ⊓ centralizer {ρ a}))
    {B : GL (Fin m) k} (hρa : ρ a = conjAut m k B * dualAut m k)
    (hB : (B : Matrix (Fin m) (Fin m) k)ᵀ = -B) :
    ∃ r : ℕ, m = 2 * r ∧ ∃ σ : StatedSp r k →* L, σ.ker ≤ center (StatedSp r k) := by
  classical
  have hm3 : 3 ≤ m := by omega
  rw [hρa] at hL₁
  obtain ⟨hXh, hmap, -⟩ := graph_component_lift hm3 B hL₁
  set Xh := ⁅(L.map ρ).comap (conjAut m k), (L.map ρ).comap (conjAut m k)⁆ with hXhdef
  set R : GL (Fin m) k := B⁻¹ with hRdef
  set O := CatalogueBGraphForm.isometryGroup m k R with hOdef
  have hR : (R : Matrix (Fin m) (Fin m) k)ᵀ = -R := by
    have hBR : (B : Matrix (Fin m) (Fin m) k) * R = 1 := by
      rw [hRdef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hRB : (R : Matrix (Fin m) (Fin m) k) * B = 1 := by
      rw [hRdef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hRt : (R : Matrix (Fin m) (Fin m) k)ᵀ * (B : Matrix (Fin m) (Fin m) k)ᵀ = 1 := by
      rw [← transpose_mul, hBR, transpose_one]
    calc (R : Matrix (Fin m) (Fin m) k)ᵀ = (R : Matrix (Fin m) (Fin m) k)ᵀ * (B * R) := by
          rw [hBR, Matrix.mul_one]
      _ = -(((R : Matrix (Fin m) (Fin m) k)ᵀ * (B : Matrix (Fin m) (Fin m) k)ᵀ) * R) := by
          rw [hB, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, neg_neg]
      _ = -R := by rw [hRt, Matrix.one_mul]
  have eI := CatalogueBLinearHigherB.isometryGroupEquiv R
  obtain ⟨r, hdim, ⟨eS⟩⟩ := CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic
    (CatalogueBLinearHigherB.matrixForm R) (CatalogueBLinearHigherB.matrixForm_isAlt hk2 R hR)
    (CatalogueBLinearHigherB.matrixForm_nondegenerate R)
  have hmr : m = 2 * r := by simpa using hdim
  have hr2 : 2 ≤ r := by omega
  have heq := CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := r) (K := k)
  set ι : StatedSp r k ≃* O := (MulEquiv.subgroupCongr heq).trans (eS.symm.trans eI) with hι
  have hqO : CFSG.IsQuasisimple O := by
    have hq := CatalogueBAlternatingIsometry.symplectic_quasisimple k r (by omega) hodd
      (Or.inl (by omega))
    exact (isQuasisimple_congr (eS.symm.trans eI)).1 hq
  have hXO : Xh = O := by
    have hcomp := (isComponentOf_iff_isComponent_subgroupOf hXh.1).mp hXh
    have htop := eq_top_of_isComponent_quasisimple hqO hcomp
    exact le_antisymm hXh.1 fun x hx => by
      have : (⟨x, hx⟩ : O) ∈ Xh.subgroupOf O := htop ▸ mem_top _
      exact this
  have hσL : ∀ x : StatedSp r k, conjAut m k (ι x : GL (Fin m) k) ∈ L.map ρ := by
    intro x
    rw [← hmap]
    exact ⟨ι x, by rw [hXO]; exact (ι x).2, rfl⟩
  set σ : StatedSp r k →* L := (L.equivMapOfInjective ρ hinj).symm.toMonoidHom.comp
    (((conjAut m k).comp (O.subtype.comp ι.toMonoidHom)).codRestrict (L.map ρ) hσL) with hσ
  have hker : σ.ker ≤ center (StatedSp r k) := by
    intro x hx
    have h1 : conjAut m k (ι x : GL (Fin m) k) = 1 := by
      have : (L.equivMapOfInjective ρ hinj).symm
          ((((conjAut m k).comp (O.subtype.comp ι.toMonoidHom)).codRestrict (L.map ρ) hσL) x) =
            1 := hx
      rw [MulEquiv.map_eq_one_iff] at this
      exact congrArg Subtype.val this
    have h2 := ker_conjAut_le_center hm3 h1
    have hιx : ι x ∈ center O := by
      rw [mem_center_iff]
      intro y
      exact Subtype.ext (mem_center_iff.mp h2 y)
    rw [mem_center_iff]
    intro y
    apply ι.injective
    rw [map_mul, map_mul]
    exact mem_center_iff.mp hιx (ι y)
  exact ⟨r, hmr, σ, hker⟩

end Cover

def signHom : Multiplicative (ZMod 2) →* ℤˣ where
  toFun x := if x = 1 then 1 else -1
  map_one' := by simp
  map_mul' x y := by
    revert x y
    decide

def chi1 : QuaternionGroup 2 →* ℤˣ where
  toFun x := match x with
    | QuaternionGroup.a i => if i.val % 2 = 0 then 1 else -1
    | QuaternionGroup.xa i => if i.val % 2 = 0 then 1 else -1
  map_one' := by decide
  map_mul' x y := by
    revert x y
    decide

def chi2 : QuaternionGroup 2 →* ℤˣ where
  toFun x := match x with
    | QuaternionGroup.a _ => 1
    | QuaternionGroup.xa _ => -1
  map_one' := by decide
  map_mul' x y := by
    revert x y
    decide

theorem two_pow_le_card_of_mulSingle_mem {n : ℕ} (R : Subgroup (Fin n → ℤˣ))
    (h : ∀ l, (Pi.mulSingle l (-1 : ℤˣ) : Fin n → ℤˣ) ∈ R) : 2 ^ n ≤ Nat.card R := by
  classical
  let v : (Fin n → Bool) → (Fin n → ℤˣ) := fun b l => if b l then -1 else 1
  have hv : ∀ b, v b ∈ R := by
    intro b
    have : v b = ∏ l, Pi.mulSingle l (v b l) := (Finset.univ_prod_mulSingle _).symm
    rw [this]
    refine Subgroup.prod_mem _ fun l _ => ?_
    by_cases hb : b l
    · have h1 : v b l = -1 := by simp [v, hb]
      rw [h1]
      exact h l
    · have h1 : v b l = 1 := by simp [v, hb]
      rw [h1, Pi.mulSingle_one]
      exact one_mem R
  have hinj : Function.Injective (fun b => (⟨v b, hv b⟩ : R)) := by
    intro b b' hbb
    funext l
    have h1 := congrFun (congrArg Subtype.val hbb) l
    simp only [v] at h1
    cases hb : b l <;> cases hb' : b' l
    · rfl
    · rw [hb, hb'] at h1
      revert h1
      decide
    · rw [hb, hb'] at h1
      revert h1
      decide
    · rfl
  have h2 := Nat.card_le_card_of_injective _ hinj
  simpa using h2

def psi5 : (QuaternionGroup 2 × QuaternionGroup 2) × Multiplicative (ZMod 2) →* (Fin 5 → ℤˣ) where
  toFun k := fun i => match i with
    | 0 => chi1 k.1.1
    | 1 => chi2 k.1.1
    | 2 => chi1 k.1.2
    | 3 => chi2 k.1.2
    | 4 => signHom k.2
  map_one' := by
    funext i
    fin_cases i <;> simp
  map_mul' x y := by
    funext i
    fin_cases i <;> simp

theorem psi5_sq (k : (QuaternionGroup 2 × QuaternionGroup 2) × Multiplicative (ZMod 2)) :
    psi5 k ^ 2 = 1 := by
  funext i
  rw [Pi.pow_apply, Pi.one_apply]
  exact Int.units_sq _

theorem two_pow_le_card_psi5 : 2 ^ 5 ≤ Nat.card psi5.range := by
  refine two_pow_le_card_of_mulSingle_mem _ fun l => ?_
  fin_cases l
  · refine ⟨((QuaternionGroup.a 1, 1), 1), ?_⟩
    funext i; fin_cases i <;> decide
  · refine ⟨((QuaternionGroup.xa 0, 1), 1), ?_⟩
    funext i; fin_cases i <;> decide
  · refine ⟨((1, QuaternionGroup.a 1), 1), ?_⟩
    funext i; fin_cases i <;> decide
  · refine ⟨((1, QuaternionGroup.xa 0), 1), ?_⟩
    funext i; fin_cases i <;> decide
  · refine ⟨((1, 1), Multiplicative.ofAdd 1), ?_⟩
    funext i; fin_cases i <;> decide

theorem psi5_eq_one_of {a b : QuaternionGroup 2} {ε : Multiplicative (ZMod 2)}
    (ha : a = 1 ∨ a = QuaternionGroup.a 2) (hb : b = 1 ∨ b = QuaternionGroup.a 2) (hε : ε = 1) :
    psi5 ((a, b), ε) = 1 := by
  subst hε
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    (funext i; fin_cases i <;> decide)

section SpQ8

open CFSG.GH74.GLS.Stage2.Final.ModelSp CFSG.GH74.GLS.Stage2.Final.ModelBlock CFSG.GH74.L5U5

theorem exists_q8q8_sp {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0) :
    ∃ φ : QuaternionGroup 2 × QuaternionGroup 2 →* StatedSp 2 F,
      ∀ k, φ k ∈ center (StatedSp 2 F) →
        k = (1, 1) ∨ k = (QuaternionGroup.a 2, QuaternionGroup.a 2) := by
  obtain ⟨φ, hφK, hφinj, hφz, -⟩ := exists_q8q8_swap_sp h2
  refine ⟨(spMulEquiv (F := F)).symm.toMonoidHom.comp (φ.codRestrict _ hφK), fun k hk => ?_⟩
  obtain ⟨c, hc⟩ := exists_scalar_of_mem_center_statedSp hk
  have hφk : φ k = GeneralLinearGroup.scalar (Fin 4) c := by
    have h1 : ((spMulEquiv (F := F) ((spMulEquiv (F := F)).symm.toMonoidHom (φ.codRestrict _ hφK k)) :
        ↥(ModelData.sp F).K4) : GL (Fin 4) F) = φ k := by
      simp
    rw [← h1, coe_spMulEquiv]
    have hc' : ((spMulEquiv (F := F)).symm (φ.codRestrict _ hφK k) : GL (Fin 2 ⊕ Fin 2) F) =
        GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c := hc
    simp only [MulEquiv.coe_toMonoidHom]
    rw [hc', glSigma_scalar]
  have hcc : c * c = 1 := by
    have := mem_K4_sp.1 (hφK k)
    rw [hφk] at this
    exact scalar_mem_isoGL_J c this
  rcases units_sq_eq_one hcc with rfl | rfl
  · left
    apply hφinj
    rw [hφk, map_one, Prod.mk_one_one, map_one]
  · right
    apply hφinj
    rw [hφk, hφz, xGL_eq_neg_one, CFSG.GH74.L5U5.scalar_neg_one_eq]

end SpQ8

noncomputable def rhoOf {N : Type*} [Group N] {H : Subgroup N} [H.Normal] {P : Type*} [Group P]
    (e : ↥H ≃* P) : N →* MulAut P :=
  (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : N →* MulAut ↥H)

theorem rhoOf_injective {N : Type*} [Group N] {H : Subgroup N} [H.Normal]
    (hfaith : ∀ n : N, (∀ h ∈ H, n * h = h * n) → n = 1) {P : Type*} [Group P] (e : ↥H ≃* P) :
    Function.Injective (rhoOf e) :=
  GenLocL4Refl.injective_congr_conjNormal hfaith e

theorem rhoOf_mem {N : Type*} [Group N] {H : Subgroup N} [H.Normal] {P : Type*} [Group P]
    (e : ↥H ≃* P) (h : ↥H) : rhoOf e (h : N) = MulAut.conj (e h) := by
  ext x
  apply e.symm.injective
  apply Subtype.ext
  simp [rhoOf, MulAut.congr_apply, MulAut.conj_apply, MulAut.conjNormal_apply]

theorem map_centralizer_rho {N : Type*} [Group N] {H : Subgroup N} [H.Normal]
    (hfaith : ∀ n : N, (∀ h ∈ H, n * h = h * n) → n = 1) {P : Type*} [Group P] (e : ↥H ≃* P)
    (t : N) :
    (centralizer ({t} : Set N)).map (rhoOf e) =
      (rhoOf e).range ⊓ centralizer ({rhoOf e t} : Set (MulAut P)) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨y, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 hy
    rw [← map_mul, ← map_mul, h1]
  · rintro ⟨⟨y, rfl⟩, hx⟩
    refine ⟨y, Subgroup.mem_centralizer_singleton_iff.2 ?_, rfl⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 hx
    apply rhoOf_injective hfaith e
    rw [map_mul, map_mul]
    exact h1

theorem map_inf_centralizer_rho {N : Type*} [Group N] {H : Subgroup N} [H.Normal]
    (hfaith : ∀ n : N, (∀ h ∈ H, n * h = h * n) → n = 1) {P : Type*} [Group P] (e : ↥H ≃* P)
    (t : N) :
    (H ⊓ centralizer ({t} : Set N)).map (rhoOf e) =
      inner P ⊓ centralizer ({rhoOf e t} : Set (MulAut P)) := by
  ext x
  constructor
  · rintro ⟨y, ⟨hyH, hyc⟩, rfl⟩
    refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    · have := rhoOf_mem e ⟨y, hyH⟩
      exact ⟨e ⟨y, hyH⟩, this.symm⟩
    · have h1 := Subgroup.mem_centralizer_singleton_iff.1 hyc
      rw [← map_mul, ← map_mul, h1]
  · rintro ⟨hxi, hxc⟩
    obtain ⟨p, rfl⟩ := hxi
    refine ⟨((e.symm p : ↥H) : N), ⟨(e.symm p).2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩, ?_⟩
    · apply rhoOf_injective hfaith e
      have h1 := Subgroup.mem_centralizer_singleton_iff.1 hxc
      rw [map_mul, map_mul, rhoOf_mem, MulEquiv.apply_symm_apply]
      exact h1
    · rw [rhoOf_mem, MulEquiv.apply_symm_apply]

theorem isCompIn_map_of_injective {A B : Type*} [Group A] [Group B] (ρ : A →* B)
    (hρ : Function.Injective ρ) {C S : Subgroup A} (h : IsCompIn C S) :
    IsCompIn (C.map ρ) (S.map ρ) := by
  refine ⟨Subgroup.map_mono h.1, ?_⟩
  let ψ : ↥C ≃* ↥(C.map ρ) := C.equivMapOfInjective ρ hρ
  have h1 := CFSG.LocalCores.isComponent_map_mulEquiv ψ h.2
  convert h1 using 1
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hx)
    obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.1 x.2
    have hsc : s = c := hρ (hsx.trans hcx.symm)
    subst hsc
    refine Subgroup.mem_map.2 ⟨⟨s, hc⟩, Subgroup.mem_subgroupOf.2 hs, Subtype.ext ?_⟩
    exact hsx
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
    refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨(y : A), Subgroup.mem_subgroupOf.1 hy, ?_⟩)
    have := congrArg Subtype.val hyx
    exact this

theorem isComponentOf_map_rho {N : Type} [Group N] [Finite N] {H : Subgroup N} [H.Normal] {t : N}
    {L : Subgroup N} (hs : ShapeInCent H t L) {P : Type} [Group P] (e : ↥H ≃* P) :
    CFSG.Assembly.IsComponentOf (L.map (rhoOf e))
      (inner P ⊓ centralizer ({rhoOf e t} : Set (MulAut P))) := by
  have h1 := isCompIn_map_of_injective (rhoOf e) (rhoOf_injective hs.faithful e) hs.comp
  rw [map_inf_centralizer_rho hs.faithful e t] at h1
  exact (isComponentOf_iff_isComponent_subgroupOf h1.1).2 h1.2

section Alt

open CFSG.GH74.Generic.BProg.B2.GenLocL4Gen4

theorem false_of_graph_alt {N : Type} [Group N] [Finite N] (H : Subgroup N) [H.Normal] {t : N}
    {L : Subgroup N} (hs : ShapeInCent H t L) (htH : t ∉ H) {F : Type} [Field F] [Finite F]
    (hF8 : Nat.card F % 8 = 5) (e : ↥H ≃* LinearFlag.projectiveSL 4 F) (A : GL (Fin 4) F)
    (hA : ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ = -(A : Matrix (Fin 4) (Fin 4) F))
    (hτ : MulAut.congr e (MulAut.conjNormal t : MulAut ↥H) =
      LinearFlag.conjAut 4 F A * LinearFlag.dualAut 4 F) (hN : SectionalTwoRankLE N 4) : False := by
  have hodd : Odd (Nat.card F) := Nat.odd_iff.mpr (by omega)
  have hk2 : ringChar F ≠ 2 :=
    CFSG.ComponentClassification.CatalogueBOddQuadratic.char_ne_two_of_odd_card hodd
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hk2
  obtain ⟨r, hmr, σ, hker⟩ := exists_sp_cover (A := N) (a := t) (L := L) (m := 4) le_rfl hk2 hodd
    (rhoOf_injective hs.faithful e) (isComponentOf_map_rho hs e) (B := A) hτ hA
  have hr : r = 2 := by omega
  subst hr
  obtain ⟨φ, hφc⟩ := exists_q8q8_sp h2
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hs.inv, pow_two] at this
  have hLC : L ≤ H ⊓ centralizer ({t} : Set N) := hs.comp.1
  let g₁ : QuaternionGroup 2 × QuaternionGroup 2 →* N := L.subtype.comp (σ.comp φ)
  let g₂ : Multiplicative (ZMod 2) →* N :=
    { toFun := fun x => if x = 1 then 1 else t
      map_one' := by simp
      map_mul' := by
        have hc : ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x = Multiplicative.ofAdd 1 := by decide
        have hs11 : Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1 := by decide
        have hne : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide
        intro x y
        rcases hc x with rfl | rfl <;> rcases hc y with rfl | rfl
        · simp
        · simp
        · simp
        · simp [hs11, hne, ht2] }
  have hcomm : ∀ m n, Commute (g₁ m) (g₂ n) := by
    intro m n
    have hm : ((σ (φ m) : L) : N) * t = t * ((σ (φ m) : L) : N) :=
      Subgroup.mem_centralizer_singleton_iff.1 (hLC (σ (φ m)).2).2
    by_cases hn : n = 1
    · simp [g₂, hn]
    · simp only [g₂, MonoidHom.coe_mk, OneHom.coe_mk, hn, ite_false]
      exact hm
  let f := g₁.noncommCoprod g₂ hcomm
  have hT : SectionalTwoRankLE ↥(⊤ : Subgroup N) 4 := SectionalTwoRankLE.subgroup ⊤ hN
  refine not_sectionalTwoRankLE_of_char (⊤ : Subgroup N) f (fun _ => Subgroup.mem_top _) psi5
    psi5_sq ?_ (r := 4) (by have := two_pow_le_card_psi5; omega) hT
  rintro ⟨⟨a, b⟩, ε⟩ hk
  have hc : ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x = Multiplicative.ofAdd 1 := by decide
  have hfk : f ((a, b), ε) = g₁ (a, b) * g₂ ε := by
    simp only [f, MonoidHom.noncommCoprod_apply]
  rcases hc ε with rfl | rfl
  · have h1 : ((σ (φ (a, b)) : L) : N) = 1 := by
      have h0 : g₂ 1 = 1 := map_one g₂
      rw [hfk, h0, mul_one] at hk
      exact hk
    have h2 : σ (φ (a, b)) = 1 := Subtype.ext h1
    have h4 := hker (show φ (a, b) ∈ σ.ker from h2)
    rcases hφc _ h4 with h5 | h5
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h5
      exact psi5_eq_one_of (Or.inl rfl) (Or.inl rfl) rfl
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h5
      exact psi5_eq_one_of (Or.inr rfl) (Or.inr rfl) rfl
  · exfalso
    have hne : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide
    have h0 : g₂ (Multiplicative.ofAdd 1) = t := by simp [g₂, hne]
    rw [hfk, h0] at hk
    have ht' : t = (g₁ (a, b))⁻¹ := eq_inv_of_mul_eq_one_right hk
    have hmem : t ∈ L := by
      rw [ht']
      exact L.inv_mem (σ (φ (a, b))).2
    exact htH (hLC hmem).1

end Alt

section Certified

theorem false_of_graph_nonsplit {N : Type} [Group N] [Finite N] (H : Subgroup N) [H.Normal] {t : N}
    {L : Subgroup N} (hs : ShapeInCent H t L) {F : Type} [Field F] [Finite F]
    (hF8 : Nat.card F % 8 = 5) (e : ↥H ≃* LinearFlag.projectiveSL 4 F) (A : GL (Fin 4) F)
    (hA : ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ = (A : Matrix (Fin 4) (Fin 4) F))
    (hns : ¬ ∃ S : Submodule F (Fin 4 → F), Module.finrank F S = 2 ∧
      ∀ x ∈ S, CFSG.ComponentClassification.CatalogueBLinearHigherB.matrixQuadraticForm
        (A⁻¹ : GL (Fin 4) F) x = 0)
    (hτ : MulAut.congr e (MulAut.conjNormal t : MulAut ↥H) =
      LinearFlag.conjAut 4 F A * LinearFlag.dualAut 4 F) : False := by
  have hodd : Odd (Nat.card F) := Nat.odd_iff.mpr (by omega)
  have hchar : ringChar F ≠ 2 := CFSG.ComponentClassification.CatalogueBOddQuadratic.char_ne_two_of_odd_card hodd
  obtain ⟨-, E, _, _, hE, ⟨eL⟩⟩ := CFSG.ComponentClassification.OddSelector.selectorRowO_of_nonsplit
    (W := H) (a := t) (L := L) hodd (rhoOf_injective hs.faithful e)
    (map_centralizer_rho hs.faithful e t) (map_inf_centralizer_rho hs.faithful e t)
    (isComponentOf_map_rho hs e) (B := A) hτ hA hns
  obtain ⟨p, f, hp, hpodd, hf, hF⟩ :=
    CFSG.ComponentClassification.CatalogueBLinearHigherB.exists_odd_prime_pow_card F hchar
  have hp2 : p ≠ 2 := by rintro rfl; exact (Nat.not_odd_iff_even.mpr even_two) hpodd
  have hE' : Nat.card E = p ^ (2 * f) := by rw [hE, hF, ← pow_mul, mul_comm]
  have h4 : 4 ≤ p ^ (2 * f) := by
    have h5 : 5 ≤ p ^ f := by rw [← hF]; omega
    calc 4 ≤ 5 * 5 := by norm_num
      _ ≤ p ^ f * p ^ f := Nat.mul_le_mul h5 h5
      _ = p ^ (2 * f) := by rw [← pow_add]; ring_nf
  exact PumpupTableOmega3.false_of_psl2_component hs hp hp2
    (PumpupTableOmega3.lieModel_psl2_of_equiv hp (by omega) h4 hE'
      (eL.trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 E).symm))

theorem false_of_graph_split {N : Type} [Group N] [Finite N] (H : Subgroup N) [H.Normal] {t : N}
    {L : Subgroup N} (hs : ShapeInCent H t L) {F : Type} [Field F] [Finite F]
    (hF8 : Nat.card F % 8 = 5) (e : ↥H ≃* LinearFlag.projectiveSL 4 F) (A : GL (Fin 4) F)
    (hA : ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ = (A : Matrix (Fin 4) (Fin 4) F))
    (hsp : ∃ S : Submodule F (Fin 4 → F), Module.finrank F S = 2 ∧
      ∀ x ∈ S, CFSG.ComponentClassification.CatalogueBLinearHigherB.matrixQuadraticForm
        (A⁻¹ : GL (Fin 4) F) x = 0)
    (hτ : MulAut.congr e (MulAut.conjNormal t : MulAut ↥H) =
      LinearFlag.conjAut 4 F A * LinearFlag.dualAut 4 F) : False := by
  have hodd : Odd (Nat.card F) := Nat.odd_iff.mpr (by omega)
  have hchar : ringChar F ≠ 2 := CFSG.ComponentClassification.CatalogueBOddQuadratic.char_ne_two_of_odd_card hodd
  obtain ⟨p, f, hp, hpodd, hf, hF⟩ :=
    CFSG.ComponentClassification.CatalogueBLinearHigherB.exists_odd_prime_pow_card F hchar
  have hp2 : p ≠ 2 := by rintro rfl; exact (Nat.not_odd_iff_even.mpr even_two) hpodd
  obtain ⟨-, ⟨eL⟩⟩ := CFSG.ComponentClassification.OddSelector.Catalog7L4E.split_component_iso
    (A := N) (a := t) (L := L) hp hp2 hf hF (rhoOf_injective hs.faithful e)
    (isComponentOf_map_rho hs e) (B := A) hτ hA hsp
  have h4 : 4 ≤ p ^ f := by rw [← hF]; omega
  exact PumpupTableOmega3.false_of_psl2_component hs hp hp2
    (PumpupTableOmega3.lieModel_psl2_of_equiv hp hf h4 hF eL)

end Certified

section Final

theorem outGraph_lin {N : Type} [Group N] [Finite N] (H : Subgroup N) [H.Normal] {t : N}
    {L : Subgroup N} {F : Type} [Field F] [Finite F] (hs : ShapeInCent H t L)
    (hF8 : Nat.card F % 8 = 5) (e : ↥H ≃* LinearFlag.projectiveSL 4 F)
    (hnd : ∀ A : GL (Fin 4) F, MulAut.congr e (MulAut.conjNormal t : MulAut ↥H) ≠
      LinearFlag.conjAut 4 F A) (h4 : SectionalTwoRankLE N 4) : False := by
  have htH : t ∉ H := by
    intro ht
    obtain ⟨g, hg⟩ := LinearFlag.proj_surjective 4 F (e ⟨t, ht⟩)
    apply hnd (Matrix.SpecialLinearGroup.toGL g)
    rw [LinearFlag.conjAut_toGL, hg]
    exact rhoOf_mem e ⟨t, ht⟩
  have ht2 : t ^ 2 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hs.inv] at this
  have hτ2 : (MulAut.congr e (MulAut.conjNormal t : MulAut ↥H)) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, ht2, map_one, map_one]
  obtain ⟨A, hτA, hform⟩ := graph_form_of_not_diag hF8 _ hτ2 hnd
  rcases hform with hsym | halt
  · by_cases hsp : ∃ S : Submodule F (Fin 4 → F), Module.finrank F S = 2 ∧
        ∀ x ∈ S, CFSG.ComponentClassification.CatalogueBLinearHigherB.matrixQuadraticForm
          (A⁻¹ : GL (Fin 4) F) x = 0
    · exact false_of_graph_split H hs hF8 e A hsym hsp hτA
    · exact false_of_graph_nonsplit H hs hF8 e A hsym hsp hτA
  · exact false_of_graph_alt H hs htH hF8 e A halt hτA h4

end Final

end PuL4GraphLin

end CFSG.GH74.Generic.BProg.B2
