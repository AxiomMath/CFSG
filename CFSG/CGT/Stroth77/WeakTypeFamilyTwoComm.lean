module

public import CFSG.CGT.Stroth77.Section225FamilyTwoComm

public section

namespace CFSG.CGT.Stroth77

open Matrix
open scoped commutatorElement

section Rho

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {τ : StrothTypeIndex}

private theorem weak_phi_rho_sq_sub_ofInt
    (hrel : τ.m + 2 = τ.n) (v : Fin 3 → ℤ) :
    τ.action.φρ (τ.action.φρ (Torus.ofInt τ.k v)) - Torus.ofInt τ.k v =
      Torus.ofInt τ.k
        (fun i => (Type200.ρM *ᵥ (Type200.ρM *ᵥ v) - v) i) := by
  rw [show τ.action.φρ =
      matAct τ.k τ.action.ρ τ.action.compat_ρ from rfl]
  rw [matAct_ofInt, matAct_ofInt]
  rw [show τ.action.ρ = Type200.ρM from action_rho_eq_type200 τ hrel]
  rw [← Torus.ofInt_sub]

omit [Finite G] in
private theorem weak_e_commutator_rho (dD : StrothWeakTypeData D τ) (x : D) :
    dD.e (Additive.ofMul
        (conjBy (Subgroup.inv_mem (Subgroup.normalizer (D : Set G))
      dD.ρ_mem) x * x⁻¹)) =
      (τ.action.φρ - AddMonoidHom.id (Torus τ.k))
        (-(τ.action.φρ (τ.action.φρ (dD.e (Additive.ofMul x))))) := by
  let hρinv : dD.ρ⁻¹ ∈ Subgroup.normalizer (D : Set G) :=
    Subgroup.inv_mem (Subgroup.normalizer (D : Set G)) dD.ρ_mem
  have hconj : conjBy dD.ρ_mem (conjBy hρinv x) = x := by
    apply Subtype.ext
    simp only [conjBy, Subtype.coe_mk]
    group
  have h1 : τ.action.φρ (dD.e (Additive.ofMul
        (conjBy hρinv x))) =
      dD.e (Additive.ofMul x) := by
    rw [← dD.ρ_conj]
    rw [hconj]
  have h2 : dD.e (Additive.ofMul
        (conjBy hρinv x)) =
      τ.action.φρ (τ.action.φρ (dD.e (Additive.ofMul x))) := by
    have h3 : τ.action.φρ (τ.action.φρ (τ.action.φρ
          (dD.e (Additive.ofMul
            (conjBy hρinv x))))) =
        dD.e (Additive.ofMul
          (conjBy hρinv x)) := by
      have := DFunLike.congr_fun τ.action.rels.rho_cube
        (dD.e (Additive.ofMul
          (conjBy hρinv x)))
      simpa using this
    calc dD.e (Additive.ofMul
          (conjBy hρinv x))
        = τ.action.φρ (τ.action.φρ (τ.action.φρ
            (dD.e (Additive.ofMul
              (conjBy hρinv x))))) := h3.symm
      _ = τ.action.φρ (τ.action.φρ (dD.e (Additive.ofMul x))) := by rw [h1]
  rw [ofMul_mul, map_add, h2, ofMul_inv, map_neg]
  rw [sub_eq_add_neg]
  rw [show τ.action.φρ (τ.action.φρ (dD.e (Additive.ofMul x))) +
      -dD.e (Additive.ofMul x) =
      (τ.action.φρ + -AddMonoidHom.id (Torus τ.k))
        (-(τ.action.φρ (τ.action.φρ (dD.e (Additive.ofMul x))))) from by
    rw [AddMonoidHom.add_apply, AddMonoidHom.neg_apply, AddMonoidHom.id_apply, map_neg]
    have hcube := DFunLike.congr_fun τ.action.rels.rho_cube
      (dD.e (Additive.ofMul x))
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at hcube
    rw [hcube]
    abel]

private theorem weak_phi_rho_sq_sub_two_torsion
    (hrel : τ.m + 2 = τ.n) (ε : Fin 3 → ℤ) :
    τ.action.φρ (τ.action.φρ
        (Torus.ofInt τ.k (fun i => ε i * 2 ^ (τ.k i - 1)))) -
        Torus.ofInt τ.k (fun i => ε i * 2 ^ (τ.k i - 1)) =
      Torus.ofInt τ.k
        ![-ε 1 * (2 : ℤ) ^ (τ.m + 1),
          (ε 2 - 2 * ε 1) * (2 : ℤ) ^ (τ.m + 1),
          -(ε 1 + ε 2) * (2 : ℤ) ^ (τ.m + 1)] := by
  have hk1 : τ.k 1 = τ.m + 2 := by
    rw [StrothTypeIndex.k_eq]
    simp [hrel]
  have hk2 : τ.k 2 = τ.m + 2 := by
    rw [StrothTypeIndex.k_two, hrel]
  set v : Fin 3 → ℤ := fun i => ε i * 2 ^ (τ.k i - 1) with hv
  rw [weak_phi_rho_sq_sub_ofInt hrel v]
  have hvec : (fun i => (Type200.ρM *ᵥ (Type200.ρM *ᵥ v) - v) i) =
      ![-ε 1 * (2 : ℤ) ^ (τ.m + 1),
        (ε 2 - 2 * ε 1) * (2 : ℤ) ^ (τ.m + 1),
        -(ε 1 + ε 2) * (2 : ℤ) ^ (τ.m + 1)] := by
    funext i
    fin_cases i <;>
      simp [v, hk1, hk2, type200_rhoM_mulVec] <;> ring
  rw [hvec]

omit [Finite G] in
private theorem weak_e_commutator_rho_ofInt (dD : StrothWeakTypeData D τ)
    (hrel : τ.m + 2 = τ.n)
    (v : Fin 3 → ℤ) (y : D)
    (hy : dD.e (Additive.ofMul y) = Torus.ofInt τ.k v) :
    dD.e (Additive.ofMul
        (conjBy (Subgroup.inv_mem (Subgroup.normalizer (D : Set G))
          dD.ρ_mem) y * y⁻¹)) =
      Torus.ofInt τ.k
        (fun i => (Type200.ρM *ᵥ (Type200.ρM *ᵥ v) - v) i) := by
  have hcube := DFunLike.congr_fun τ.action.rels.rho_cube
    (dD.e (Additive.ofMul y))
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at hcube
  rw [weak_e_commutator_rho]
  rw [show (τ.action.φρ - AddMonoidHom.id (Torus τ.k))
      (-(τ.action.φρ (τ.action.φρ (dD.e (Additive.ofMul y))))) =
      (τ.action.φρ (τ.action.φρ (dD.e (Additive.ofMul y))) -
        dD.e (Additive.ofMul y)) from by
    rw [AddMonoidHom.sub_apply, AddMonoidHom.id_apply, map_neg]
    rw [hcube]
    abel]
  rw [hy, weak_phi_rho_sq_sub_ofInt hrel v]

private theorem weak_rho_commutator_mem_closure (dD : StrothWeakTypeData D τ)
    (hk : ∀ i, 2 ≤ τ.k i) (hrel : τ.m + 2 = τ.n)
    {x : G} (hx : x ∈ omegaIn 1 D) :
    ⁅(dD.ρ : G), x⁆ ∈
      Subgroup.closure ({(dD.a : G) ^ (2 ^ (τ.m + 1)),
        (dD.b : G) ^ (2 ^ (τ.m + 1))} : Set G) := by
  classical
  let H : Subgroup G :=
    Subgroup.closure ({(dD.a : G) ^ (2 ^ (τ.m + 1)),
      (dD.b : G) ^ (2 ^ (τ.m + 1))} : Set G)
  let W : AddSubgroup (Torus τ.k) :=
    AddSubgroup.closure ({(2 : ℤ) ^ (τ.m + 1) • (Torus.a : Torus τ.k),
      (2 : ℤ) ^ (τ.m + 1) • (Torus.b : Torus τ.k)} : Set (Torus τ.k))
  have hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (dD.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨hxD, hx2⟩ := (mem_omegaIn_iff_of_comm hcomm).mp hx
  let d : D := ⟨x, hxD⟩
  have hd2 : d * d = 1 := by
    apply Subtype.ext
    simpa [d, pow_two] using hx2
  have h2 : (2 : ℤ) • dD.e (Additive.ofMul d) = 0 := by
    rw [show (2 : ℤ) • dD.e (Additive.ofMul d) =
        dD.e (Additive.ofMul (d * d)) from by
      rw [ofMul_mul, map_add, two_zsmul]]
    rw [hd2, ofMul_one, map_zero]
  have hk1all : ∀ i, 1 ≤ τ.k i := fun i => by have := hk i; omega
  obtain ⟨ε, hε, hεd⟩ := (Torus.two_zsmul_eq_zero_iff hk1all _).mp h2
  let hρinv : dD.ρ⁻¹ ∈ Subgroup.normalizer (D : Set G) :=
    Subgroup.inv_mem (Subgroup.normalizer (D : Set G)) dD.ρ_mem
  have hρinv_val : ((conjBy hρinv d * d⁻¹ : D) : G) = ⁅(dD.ρ : G), x⁆ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjBy,
      commutatorElement_def]
    simp only [d]
    group
  have hcube := DFunLike.congr_fun τ.action.rels.rho_cube
    (dD.e (Additive.ofMul d))
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at hcube
  have heq : dD.e (Additive.ofMul (conjBy hρinv d * d⁻¹)) =
      Torus.ofInt τ.k
        ![-ε 1 * (2 : ℤ) ^ (τ.m + 1),
          (ε 2 - 2 * ε 1) * (2 : ℤ) ^ (τ.m + 1),
          -(ε 1 + ε 2) * (2 : ℤ) ^ (τ.m + 1)] := by
    rw [weak_e_commutator_rho]
    rw [show (τ.action.φρ - AddMonoidHom.id (Torus τ.k))
        (-(τ.action.φρ (τ.action.φρ (dD.e (Additive.ofMul d))))) =
        (τ.action.φρ (τ.action.φρ (dD.e (Additive.ofMul d))) -
          dD.e (Additive.ofMul d)) from by
      rw [AddMonoidHom.sub_apply, AddMonoidHom.id_apply, map_neg]
      rw [hcube]
      abel]
    rw [hεd]
    exact weak_phi_rho_sq_sub_two_torsion hrel ε
  have hczero : (-ε 1 * (2 : ℤ) ^ (τ.m + 1)) • (Torus.c : Torus τ.k) = 0 := by
    rw [← addOrderOf_dvd_iff_zsmul_eq_zero, addOrderOf_c]
    have hdm : (2 : ℤ) ^ τ.m ∣ -ε 1 * (2 : ℤ) ^ (τ.m + 1) := by
      rw [show (2 : ℤ) ^ (τ.m + 1) = (2 : ℤ) ^ τ.m * 2 by rw [pow_succ]]
      exact dvd_mul_of_dvd_right (dvd_mul_right ((2 : ℤ) ^ τ.m) 2) (-ε 1)
    simpa [StrothTypeIndex.m] using hdm
  have hW : dD.e (Additive.ofMul (conjBy hρinv d * d⁻¹)) ∈ W := by
    rw [heq]
    refine AddSubgroup.mem_closure_pair.mpr
      ⟨ε 2 - 2 * ε 1, -(ε 1 + ε 2), ?_⟩
    rw [Torus.ofInt_eq_zsmul_gens]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    rw [hczero, zero_add]
    rw [show (ε 2 - 2 * ε 1) •
        ((2 : ℤ) ^ (τ.m + 1) • (Torus.a : Torus τ.k)) =
        ((ε 2 - 2 * ε 1) * (2 : ℤ) ^ (τ.m + 1)) • Torus.a from by
      rw [← mul_zsmul']; ring]
    rw [show (-(ε 1 + ε 2)) •
        ((2 : ℤ) ^ (τ.m + 1) • (Torus.b : Torus τ.k)) =
        (-(ε 1 + ε 2) * (2 : ℤ) ^ (τ.m + 1)) • Torus.b from by
      rw [← mul_zsmul']; ring]
  have hmem : ⁅(dD.ρ : G), x⁆ ∈ H := by
    rw [← hρinv_val]
    obtain ⟨p, q, hpq⟩ := AddSubgroup.mem_closure_pair.mp hW
    set g : D := ((⟨dD.a, dD.a.2⟩ : D) ^ ((2 : ℕ) ^ (τ.m + 1))) ^ p *
        ((⟨dD.b, dD.b.2⟩ : D) ^ ((2 : ℕ) ^ (τ.m + 1))) ^ q with hg_def
    have hg_e : dD.e (Additive.ofMul g) =
        p • ((2 : ℤ) ^ (τ.m + 1) • (Torus.a : Torus τ.k)) +
          q • ((2 : ℤ) ^ (τ.m + 1) • (Torus.b : Torus τ.k)) := by
      rw [hg_def, ofMul_mul, map_add, ofMul_zpow, ofMul_zpow, map_zsmul, map_zsmul]
      rw [dD.e_pow, dD.e_pow, dD.e_a, dD.e_b]
      rw [show ((2 : ℕ) ^ (τ.m + 1)) • (Torus.a : Torus τ.k) =
          ((2 : ℤ) ^ (τ.m + 1)) • Torus.a from by
        rw [← natCast_zsmul]; push_cast; ring]
      rw [show ((2 : ℕ) ^ (τ.m + 1)) • (Torus.b : Torus τ.k) =
          ((2 : ℤ) ^ (τ.m + 1)) • Torus.b from by
        rw [← natCast_zsmul]; push_cast; ring]
    have heq_g : dD.e (Additive.ofMul (conjBy hρinv d * d⁻¹)) =
        dD.e (Additive.ofMul g) := by rw [hg_e, hpq]
    have hg_eq : (conjBy hρinv d * d⁻¹ : D) = g :=
      Additive.ofMul.injective (dD.e.injective heq_g)
    rw [hg_eq]
    show (((dD.a : G) ^ ((2 : ℕ) ^ (τ.m + 1))) ^ p *
        ((dD.b : G) ^ ((2 : ℕ) ^ (τ.m + 1))) ^ q) ∈ H
    exact H.mul_mem
      (H.zpow_mem (Subgroup.subset_closure (Set.mem_insert _ _)) p)
      (H.zpow_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) q)
  exact hmem

private theorem weak_commutator_zpowers_rho_le (dD : StrothWeakTypeData D τ)
    (hk : ∀ i, 2 ≤ τ.k i) (hrel : τ.m + 2 = τ.n) :
    ⁅Subgroup.zpowers (dD.ρ : G), omegaIn 1 D⁆ ≤
      Subgroup.closure ({(dD.a : G) ^ (2 ^ (τ.m + 1)),
        (dD.b : G) ^ (2 ^ (τ.m + 1))} : Set G) := by
  apply commutator_zpowers_le_of_pow_three_central
  · intro x hx
    simpa only [inv_inv] using conj_mem_omegaIn_one (inv_mem dD.ρ_mem) hx
  · exact Subgroup.centralizer_le (omegaIn_le 1 D) dD.rho_cube_mem
  · intro x hx
    exact weak_rho_commutator_mem_closure dD hk hrel hx

omit [Finite G] in
private theorem weak_rho_commutator_a_pow (dD : StrothWeakTypeData D τ)
    (hrel : τ.m + 2 = τ.n) :
    ⁅(dD.ρ : G), (dD.a : G) ^ (2 ^ (τ.m + 1))⁆ =
      ((dD.b : G)⁻¹) ^ (2 ^ (τ.m + 1)) := by
  classical
  let ya : D := ⟨(dD.a : G) ^ (2 ^ (τ.m + 1)),
    D.pow_mem dD.a.2 _⟩
  let bb : D := ((⟨dD.b, dD.b.2⟩ : D)⁻¹) ^ ((2 : ℕ) ^ (τ.m + 1))
  let hρinv : dD.ρ⁻¹ ∈ Subgroup.normalizer (D : Set G) :=
    Subgroup.inv_mem (Subgroup.normalizer (D : Set G)) dD.ρ_mem
  have hval : ((conjBy hρinv ya * ya⁻¹ : D) : G) =
      ⁅(dD.ρ : G), (dD.a : G) ^ (2 ^ (τ.m + 1))⁆ := by
    simp only [conjBy, ya, Subgroup.coe_mul, Subgroup.coe_inv,
      commutatorElement_def]
    group
  have hk1 : τ.k 1 = τ.m + 2 := by
    rw [StrothTypeIndex.k_eq]; simp [hrel]
  have hk1sub : τ.k 1 - 1 = τ.m + 1 := by
    rw [hk1]; omega
  have hya : dD.e (Additive.ofMul ya) =
      Torus.ofInt τ.k (fun i => (![0, 1, 0] : Fin 3 → ℤ) i * 2 ^ (τ.k i - 1)) := by
    have hya_eq : ya = (⟨dD.a, dD.a.2⟩ : D) ^ ((2 : ℕ) ^ (τ.m + 1)) := by
      apply Subtype.ext
      rfl
    rw [hya_eq, dD.e_pow, dD.e_a]
    rw [Torus.ofInt_eq_zsmul_gens]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, one_mul,
      hk1sub, Torus.a, gen]
    module
  have hbb : dD.e (Additive.ofMul bb) =
      Torus.ofInt τ.k ![0, 0, -(2 : ℤ) ^ (τ.m + 1)] := by
    have hbb_eq : bb = ((⟨dD.b, dD.b.2⟩ : D)⁻¹) ^ ((2 : ℕ) ^ (τ.m + 1)) := by
      apply Subtype.ext
      rfl
    rw [hbb_eq, dD.e_pow, ofMul_inv, map_neg, dD.e_b]
    rw [Torus.ofInt_eq_zsmul_gens]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, zero_smul, zero_add,
      Torus.b, gen]
    module
  have heq : dD.e (Additive.ofMul (conjBy hρinv ya * ya⁻¹)) =
      dD.e (Additive.ofMul bb) := by
    rw [weak_e_commutator_rho_ofInt dD hrel
      (fun i => (![0, 1, 0] : Fin 3 → ℤ) i * 2 ^ (τ.k i - 1)) ya hya, hbb]
    apply Torus.ofInt_eq_ofInt_iff.mpr
    intro i
    fin_cases i
    · simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, type200_rhoM_mulVec, hk1]
      rw [Int.modEq_zero_iff_dvd]
      exact dvd_neg.mpr (pow_dvd_pow (2 : ℤ) (by omega : τ.m ≤ τ.m + 1))
    · simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, type200_rhoM_mulVec, hk1]
      rw [Int.modEq_zero_iff_dvd]
      refine ⟨-1, ?_⟩
      rw [show (2 : ℤ) ^ (τ.m + 2) =
          (2 : ℤ) ^ (τ.m + 1) + (2 : ℤ) ^ (τ.m + 1) by
        rw [show τ.m + 2 = (τ.m + 1) + 1 by omega, pow_succ]; ring]
      ring
    · simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, type200_rhoM_mulVec, hk1]
  have hEqD : (conjBy hρinv ya * ya⁻¹ : D) = bb :=
    Additive.ofMul.injective (dD.e.injective heq)
  rw [← hval, hEqD]
  rfl

omit [Finite G] in
private theorem weak_rho_commutator_ab_pow (dD : StrothWeakTypeData D τ)
    (hrel : τ.m + 2 = τ.n) :
    ⁅(dD.ρ : G),
        (dD.a : G) ^ (2 ^ (τ.m + 1)) *
          (dD.b : G) ^ (2 ^ (τ.m + 1))⁆ =
      ((dD.a : G)⁻¹) ^ (2 ^ (τ.m + 1)) := by
  classical
  let ya : D := ⟨(dD.a : G) ^ (2 ^ (τ.m + 1)),
    D.pow_mem dD.a.2 _⟩
  let yb : D := ⟨(dD.b : G) ^ (2 ^ (τ.m + 1)),
    D.pow_mem dD.b.2 _⟩
  let y2 : D := ya * yb
  let aa : D := ((⟨dD.a, dD.a.2⟩ : D)⁻¹) ^ ((2 : ℕ) ^ (τ.m + 1))
  let hρinv : dD.ρ⁻¹ ∈ Subgroup.normalizer (D : Set G) :=
    Subgroup.inv_mem (Subgroup.normalizer (D : Set G)) dD.ρ_mem
  have hval : ((conjBy hρinv y2 * y2⁻¹ : D) : G) =
      ⁅(dD.ρ : G),
        (dD.a : G) ^ (2 ^ (τ.m + 1)) *
          (dD.b : G) ^ (2 ^ (τ.m + 1))⁆ := by
    simp only [conjBy, y2, ya, yb, Subgroup.coe_mul, Subgroup.coe_inv,
      commutatorElement_def]
    group
  have hk1 : τ.k 1 = τ.m + 2 := by
    rw [StrothTypeIndex.k_eq]; simp [hrel]
  have hk2 : τ.k 2 = τ.m + 2 := by
    rw [StrothTypeIndex.k_two, hrel]
  have hk1sub : τ.k 1 - 1 = τ.m + 1 := by
    rw [hk1]; omega
  have hk2sub : τ.k 2 - 1 = τ.m + 1 := by
    rw [hk2]; omega
  have hy2 : dD.e (Additive.ofMul y2) =
      Torus.ofInt τ.k (fun i => (![0, 1, 1] : Fin 3 → ℤ) i * 2 ^ (τ.k i - 1)) := by
    have hya_eq : ya = (⟨dD.a, dD.a.2⟩ : D) ^ ((2 : ℕ) ^ (τ.m + 1)) := by
      apply Subtype.ext
      rfl
    have hyb_eq : yb = (⟨dD.b, dD.b.2⟩ : D) ^ ((2 : ℕ) ^ (τ.m + 1)) := by
      apply Subtype.ext
      rfl
    rw [show y2 = ya * yb from rfl, ofMul_mul, map_add,
      hya_eq, hyb_eq, dD.e_pow, dD.e_pow, dD.e_a, dD.e_b]
    rw [Torus.ofInt_eq_zsmul_gens]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, one_mul,
      hk1sub, hk2sub, Torus.a, Torus.b, gen]
    module
  have haa : dD.e (Additive.ofMul aa) =
      Torus.ofInt τ.k ![0, -(2 : ℤ) ^ (τ.m + 1), 0] := by
    have haa_eq : aa = ((⟨dD.a, dD.a.2⟩ : D)⁻¹) ^
        ((2 : ℕ) ^ (τ.m + 1)) := by
      apply Subtype.ext
      rfl
    rw [haa_eq, dD.e_pow, ofMul_inv, map_neg, dD.e_a]
    rw [Torus.ofInt_eq_zsmul_gens]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, zero_smul, zero_add,
      Torus.a, gen]
    module
  have heq : dD.e (Additive.ofMul (conjBy hρinv y2 * y2⁻¹)) =
      dD.e (Additive.ofMul aa) := by
    rw [weak_e_commutator_rho_ofInt dD hrel
      (fun i => (![0, 1, 1] : Fin 3 → ℤ) i * 2 ^ (τ.k i - 1)) y2 hy2, haa]
    apply Torus.ofInt_eq_ofInt_iff.mpr
    intro i
    fin_cases i
    · simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, type200_rhoM_mulVec, hk1, hk2]
      rw [Int.modEq_zero_iff_dvd]
      exact dvd_neg.mpr (pow_dvd_pow (2 : ℤ) (by omega : τ.m ≤ τ.m + 1))
    · simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, type200_rhoM_mulVec, hk1, hk2]
    · simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, type200_rhoM_mulVec, hk1, hk2]
      rw [Int.modEq_zero_iff_dvd]
      refine ⟨-1, ?_⟩
      rw [show (2 : ℤ) ^ (τ.m + 2) =
          (2 : ℤ) ^ (τ.m + 1) + (2 : ℤ) ^ (τ.m + 1) by
        rw [show τ.m + 2 = (τ.m + 1) + 1 by omega, pow_succ]; ring]
      ring
  have hEqD : (conjBy hρinv y2 * y2⁻¹ : D) = aa :=
    Additive.ofMul.injective (dD.e.injective heq)
  rw [← hval, hEqD]
  rfl

private theorem weak_omegaIn_pow (hrel : τ.m + 2 = τ.n) {x : D} (hx : orderOf x = 2 ^ τ.n) :
    (x : G) ^ (2 ^ (τ.m + 1)) ∈ omegaIn 1 D := by
  refine mem_omegaIn_one_of_mul_self (D.pow_mem x.2 _) ?_
  have h : (x : G) ^ (2 ^ τ.n) = 1 := by
    rw [← hx, ← Subgroup.coe_pow, pow_orderOf_eq_one, Subgroup.coe_one]
  rw [← pow_add, ← h]
  congr 1
  rw [← hrel]
  ring

private theorem weak_omegaIn_ab_pow (dD : StrothWeakTypeData D τ) (hrel : τ.m + 2 = τ.n) :
    ((dD.a : G) ^ (2 ^ (τ.m + 1)) *
      (dD.b : G) ^ (2 ^ (τ.m + 1))) ∈ omegaIn 1 D :=
  (omegaIn 1 D).mul_mem (weak_omegaIn_pow hrel dD.orderOf_a) (weak_omegaIn_pow hrel dD.orderOf_b)

private theorem weak_commutator_zpowers_rho_ge (dD : StrothWeakTypeData D τ)
    (hrel : τ.m + 2 = τ.n) :
    Subgroup.closure ({(dD.a : G) ^ (2 ^ (τ.m + 1)),
        (dD.b : G) ^ (2 ^ (τ.m + 1))} : Set G) ≤
      ⁅Subgroup.zpowers (dD.ρ : G), omegaIn 1 D⁆ := by
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · have h := Subgroup.commutator_mem_commutator
      (Subgroup.mem_zpowers (dD.ρ : G)) (weak_omegaIn_ab_pow dD hrel)
    rw [weak_rho_commutator_ab_pow dD hrel] at h
    have hinv := Subgroup.inv_mem _ h
    simpa [inv_pow] using hinv
  · have h := Subgroup.commutator_mem_commutator
      (Subgroup.mem_zpowers (dD.ρ : G)) (weak_omegaIn_pow hrel dD.orderOf_a)
    rw [weak_rho_commutator_a_pow dD hrel] at h
    have hinv := Subgroup.inv_mem _ h
    simpa [inv_pow] using hinv

end Rho

theorem StrothWeakTypeData.commutator_zpowers_rho_omegaIn_one_familyTwo
    {G : Type} [Group G] [Finite G] {D : Subgroup G} {τ : StrothTypeIndex}
    (dD : StrothWeakTypeData D τ) (hk : ∀ i, 2 ≤ τ.k i) (hrel : τ.m + 2 = τ.n) :
    ⁅Subgroup.zpowers dD.ρ, omegaIn 1 D⁆ =
      Subgroup.closure ({(dD.a : G) ^ (2 ^ (τ.m + 1)), (dD.b : G) ^ (2 ^ (τ.m + 1))} : Set G) :=
  le_antisymm (weak_commutator_zpowers_rho_le dD hk hrel) (weak_commutator_zpowers_rho_ge dD hrel)

theorem StrothWeakTypeData.commutator_zpowers_eq_of_commutator_familyTwo
    {G : Type} [Group G] [Finite G] {D : Subgroup G} {τ : StrothTypeIndex}
    (dD : StrothWeakTypeData D τ) {s : G} (hsN : s ∈ Subgroup.normalizer (D : Set G))
    (hsC : s ∈ Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G))
    (hc : s * (dD.c : G) * s⁻¹ * (dD.c : G)⁻¹ = 1)
    (ha : s * (dD.a : G) * s⁻¹ * (dD.a : G)⁻¹ = (dD.a : G) ^ (2 ^ (τ.m + 1)))
    (hb : s * (dD.b : G) * s⁻¹ * (dD.b : G)⁻¹ = (dD.b : G) ^ (2 ^ (τ.m + 1))) :
    ⁅Subgroup.zpowers s, D⁆ =
      Subgroup.closure ({(dD.a : G) ^ (2 ^ (τ.m + 1)), (dD.b : G) ^ (2 ^ (τ.m + 1))} : Set G) := by
  set H : Subgroup G :=
    Subgroup.closure ({(dD.a : G) ^ (2 ^ (τ.m + 1)), (dD.b : G) ^ (2 ^ (τ.m + 1))} : Set G)
    with hH
  have hcommD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (dD.isMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hconj : ∀ x ∈ D, s * x * s⁻¹ ∈ D := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hsN x).mp hx
  let f : D →* G :=
    { toFun := fun d => ⁅s, (d : G)⁆
      map_one' := by simp
      map_mul' := fun x y => by
        have e1 : (x : G)⁻¹ * (s * (y : G) * s⁻¹) = (s * (y : G) * s⁻¹) * (x : G)⁻¹ :=
          hcommD _ (inv_mem x.2) _ (hconj _ y.2)
        have e2 : (y : G)⁻¹ * (x : G)⁻¹ = (x : G)⁻¹ * (y : G)⁻¹ :=
          hcommD _ (inv_mem y.2) _ (inv_mem x.2)
        simp only [Subgroup.coe_mul, commutatorElement_def]
        calc s * ((x : G) * (y : G)) * s⁻¹ * ((x : G) * (y : G))⁻¹
            = s * (x : G) * s⁻¹ * ((s * (y : G) * s⁻¹) * ((y : G)⁻¹ * (x : G)⁻¹)) := by group
          _ = s * (x : G) * s⁻¹ * (((x : G)⁻¹ * (s * (y : G) * s⁻¹)) * (y : G)⁻¹) := by
            rw [e2, e1]; group
          _ = s * (x : G) * s⁻¹ * (x : G)⁻¹ * (s * (y : G) * s⁻¹ * (y : G)⁻¹) := by group }
  have hf : ∀ d : D, f d = ⁅s, (d : G)⁆ := fun _ => rfl
  have haH : (dD.a : G) ^ (2 ^ (τ.m + 1)) ∈ H := Subgroup.subset_closure (by simp)
  have hbH : (dD.b : G) ^ (2 ^ (τ.m + 1)) ∈ H := Subgroup.subset_closure (by simp)
  have himg : ∀ d ∈ D, ⁅s, d⁆ ∈ H := by
    intro d hd
    obtain ⟨i, j, l, hdl⟩ := dD.exists_zpow_c_a_b ⟨d, hd⟩
    have e : ⁅s, d⁆ = f ⟨d, hd⟩ := rfl
    rw [e, hdl, map_mul, map_mul, map_zpow, map_zpow, map_zpow, hf, hf, hf,
      commutatorElement_def, commutatorElement_def, commutatorElement_def, hc, ha, hb,
      _root_.one_zpow, one_mul]
    exact H.mul_mem (H.zpow_mem haH j) (H.zpow_mem hbH l)
  have hpow : ∀ x ∈ D, x ^ (2 ^ (τ.m + 1)) ∈ mhoOne D := fun x hx => by
    rw [pow_succ, pow_mul]
    exact CFSG.GroupTheory.HuppertProduct.pow_mem_mho (D.pow_mem hx _)
  have hHmho : H ≤ mhoOne D := by
    rw [hH, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hpow _ dD.a.2
    · exact hpow _ dD.b.2
  have hcomm : ∀ d ∈ D, Commute s ⁅s, d⁆ := fun d hd =>
    (Subgroup.mem_centralizer_iff.mp hsC _ (hHmho (himg d hd))).symm
  refine le_antisymm (commutator_zpowers_le_of_image himg hcomm) ?_
  rw [hH, Subgroup.closure_le]
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl
  · have h := Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers s) dD.a.2
    rwa [commutatorElement_def, ha] at h
  · have h := Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers s) dD.b.2
    rwa [commutatorElement_def, hb] at h

end CFSG.CGT.Stroth77
