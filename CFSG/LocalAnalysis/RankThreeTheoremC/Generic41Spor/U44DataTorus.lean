module

public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.KF.R9Perm
public import CFSG.RankThree.PartOne.KF.SymTorus
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

open Matrix CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.U44Data

abbrev F16 : Type := GaloisField 2 (2 * 2)

theorem card_F16 : Nat.card F16 = (2 ^ 2) ^ 2 := by
  rw [GaloisField.card 2 (2 * 2) (by norm_num)]
  norm_num

theorem unitaryFieldData : UnitaryFieldData 2 2 F16 := ⟨Nat.prime_two, by norm_num, by
  rw [GaloisField.card 2 (2 * 2) (by norm_num)]⟩

theorem exists_zeta : ∃ ζ : F16ˣ, IsPrimitiveRoot ζ 5 := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot unitaryFieldData Nat.prime_five (by norm_num)
  exact ⟨hζ.isUnit (by norm_num) |>.unit, by
    rw [← IsPrimitiveRoot.coe_units_iff]; simpa using hζ⟩

@[expose] noncomputable def zeta : F16ˣ := exists_zeta.choose

theorem zeta_prim : IsPrimitiveRoot zeta 5 := exists_zeta.choose_spec

theorem zeta_pow_five : zeta ^ 5 = 1 := zeta_prim.pow_eq_one

@[expose] noncomputable def pw (a : ZMod 5) : F16ˣ := zeta ^ a.val

theorem pw_add (a b : ZMod 5) : pw (a + b) = pw a * pw b := by
  unfold pw
  rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ zeta_pow_five]

theorem pw_zero : pw 0 = 1 := by simp [pw]

theorem pw_pow_five (a : ZMod 5) : pw a ^ 5 = 1 := by
  unfold pw
  rw [← pow_mul, Nat.mul_comm a.val 5, pow_mul, zeta_pow_five, one_pow]

theorem pw_injective : Function.Injective pw := by
  intro a b h
  exact ZMod.val_injective 5 (zeta_prim.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h)

theorem exists_pw {u : F16ˣ} (hu : u ^ 5 = 1) : ∃ a, pw a = u := by
  have hpr : IsPrimitiveRoot (zeta : F16) 5 := IsPrimitiveRoot.coe_units_iff.mpr zeta_prim
  have hu' : (u : F16) ^ 5 = 1 := by
    have := congrArg (fun w : F16ˣ => (w : F16)) hu
    simpa using this
  obtain ⟨i, hi, hiu⟩ := hpr.eq_pow_of_pow_eq_one hu'
  refine ⟨(i : ZMod 5), ?_⟩
  unfold pw
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hi]
  apply Units.ext
  simpa using hiu

@[expose] noncomputable def dv (n : Fin 4 → ZMod 5) : Fin 4 → F16ˣ := fun i => pw (n i)

@[expose] noncomputable def ldg (n : Fin 4 → ZMod 5) : GL (Fin 4) F16 := diagU (dv n)

theorem dv_add (n m : Fin 4 → ZMod 5) : dv (n + m) = dv n * dv m :=
  funext fun i => pw_add _ _

theorem ldg_mul (n m : Fin 4 → ZMod 5) : ldg n * ldg m = ldg (n + m) := by
  unfold ldg
  rw [diagU_mul, dv_add]

theorem ldg_zero : ldg 0 = 1 := by
  unfold ldg
  have : dv 0 = 1 := funext fun i => pw_zero
  rw [this, diagU_one]

theorem ldg_injective : Function.Injective ldg := fun n m h =>
  funext fun i => pw_injective (congrFun (diagU_injective h) i)

theorem prod_dv (n : Fin 4 → ZMod 5) : ∏ i, dv n i = pw (∑ i, n i) := by
  simp only [dv, Fin.prod_univ_four, Fin.sum_univ_four, pw_add]

theorem ldg_mem_torus {n : Fin 4 → ZMod 5} (h : ∑ i, n i = 0) : ldg n ∈ torusSU 5 4 F16 :=
  mem_torusSU_iff.mpr ⟨dv n, fun i => pw_pow_five _, by rw [prod_dv, h, pw_zero], rfl⟩

theorem exists_ldg_of_mem_torus {g : GL (Fin 4) F16} (hg : g ∈ torusSU 5 4 F16) :
    ∃ n : Fin 4 → ZMod 5, ∑ i, n i = 0 ∧ ldg n = g := by
  obtain ⟨d, hd5, hd, rfl⟩ := mem_torusSU_iff.mp hg
  choose n hn using fun i => exists_pw (hd5 i)
  have hdn : dv n = d := funext hn
  refine ⟨n, ?_, by rw [ldg, hdn]⟩
  apply pw_injective
  rw [← prod_dv, hdn, hd, pw_zero]

theorem ldg_mem_unitarySU {n : Fin 4 → ZMod 5} (h : ∑ i, n i = 0) :
    ldg n ∈ unitarySU 2 2 F16 4 :=
  torusSU_le_unitarySU unitaryFieldData (by norm_num) (ldg_mem_torus h)

theorem permGL_conj_ldg (σ : Equiv.Perm (Fin 4)) (n : Fin 4 → ZMod 5) :
    (permGL σ : GL (Fin 4) F16) * ldg n * (permGL σ)⁻¹ = ldg (n ∘ σ.symm) := by
  unfold ldg
  rw [permGL_conj_diagU]
  rfl

theorem exists_perm_of_card_fiber_eq {ι α : Type*} [Fintype ι] [DecidableEq α] (d e : ι → α)
    (h : ∀ v, Fintype.card {i // d i = v} = Fintype.card {i // e i = v}) :
    ∃ π : Equiv.Perm ι, ∀ i, e (π i) = d i := by
  classical
  have eqv : ∀ v, {i // d i = v} ≃ {i // e i = v} := fun v => Fintype.equivOfCardEq (h v)
  let π : ι ≃ ι := ((Equiv.sigmaFiberEquiv d).symm.trans (Equiv.sigmaCongrRight eqv)).trans
    (Equiv.sigmaFiberEquiv e)
  refine ⟨π, fun i => ?_⟩
  have h1 : π i = (eqv (d i) ⟨i, rfl⟩).1 := rfl
  rw [h1]
  exact (eqv (d i) ⟨i, rfl⟩).2

theorem exists_perm_of_conj_diagU {K : Type} [Field K] {n : ℕ} (d e : Fin n → Kˣ)
    (g : GL (Fin n) K) (h : g * diagU d * g⁻¹ = diagU e) :
    ∃ π : Equiv.Perm (Fin n), ∀ i, e (π i) = d i := by
  classical
  have hcp : (diagU e : Matrix (Fin n) (Fin n) K).charpoly =
      (diagU d : Matrix (Fin n) (Fin n) K).charpoly := by
    rw [← h, Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
    exact Matrix.charpoly_units_conj g _
  rw [diagU_val, diagU_val, Matrix.charpoly_diagonal, Matrix.charpoly_diagonal] at hcp
  have hroots : ∀ f : Fin n → Kˣ,
      (∏ i, (Polynomial.X - Polynomial.C (f i : K))).roots =
        Multiset.map (fun i => (f i : K)) Finset.univ.val := by
    intro f
    rw [Finset.prod_eq_multiset_prod]
    have := Polynomial.roots_multiset_prod_X_sub_C
      (Multiset.map (fun i => (f i : K)) Finset.univ.val)
    rw [Multiset.map_map] at this
    exact this
  have hms : Multiset.map (fun i => (e i : K)) Finset.univ.val =
      Multiset.map (fun i => (d i : K)) Finset.univ.val := by
    rw [← hroots e, ← hroots d, hcp]
  refine exists_perm_of_card_fiber_eq d e fun v => ?_
  have hc := congrArg (Multiset.count (v : K)) hms
  simp only [Multiset.count_map] at hc
  rw [Fintype.card_subtype, Fintype.card_subtype]
  have key : ∀ f : Fin n → Kˣ, (Finset.univ.filter (fun x => f x = v)).card =
      (Multiset.filter (fun a => (v : K) = (f a : K)) Finset.univ.val).card := by
    intro f
    rw [Finset.card_def, Finset.filter_val]
    have hf : Multiset.filter (fun x => f x = v) Finset.univ.val =
        Multiset.filter (fun a => (v : K) = (f a : K)) Finset.univ.val := by
      refine Multiset.filter_congr fun x _ => ?_
      constructor
      · intro h
        rw [h]
      · intro h
        exact Units.ext h.symm
    rw [hf]
  exact (key d).trans (hc.symm.trans (key e).symm)

@[expose] noncomputable def ldgHom : Multiplicative (Fin 4 → ZMod 5) →* GL (Fin 4) F16 where
  toFun n := ldg n.toAdd
  map_one' := ldg_zero
  map_mul' a b := (ldg_mul a.toAdd b.toAdd).symm

theorem ldg_zpow (n : Fin 4 → ZMod 5) (k : ℤ) : ldg n ^ k = ldg (k • n) := by
  have := map_zpow ldgHom (Multiplicative.ofAdd n) k
  simpa [ldgHom] using this.symm

@[expose] noncomputable def Ln (n : Fin 4 → ZMod 5) : Subgroup (GL (Fin 4) F16) :=
  Subgroup.zpowers (ldg n)

theorem ldg_mem_Ln_iff {n m : Fin 4 → ZMod 5} :
    ldg m ∈ Ln n ↔ ∃ c : ZMod 5, ∀ i, m i = c * n i := by
  unfold Ln
  rw [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    rw [ldg_zpow] at hk
    refine ⟨(k : ZMod 5), fun i => ?_⟩
    have := congrFun (ldg_injective hk) i
    simpa using this.symm
  · rintro ⟨c, hc⟩
    refine ⟨(c.val : ℤ), ?_⟩
    rw [ldg_zpow]
    congr 1
    funext i
    simp [hc i]

@[expose] def v1 : Fin 4 → ZMod 5 := ![1, 1, -1, -1]
@[expose] def v2 : Fin 4 → ZMod 5 := ![1, -1, 1, -1]
@[expose] def v3 : Fin 4 → ZMod 5 := ![1, -1, -1, 1]

abbrev NoSingle (n : Fin 4 → ZMod 5) : Prop := ∀ i, ∃ j, j ≠ i ∧ n j = n i

theorem cls : ∀ n : Fin 4 → ZMod 5, ∑ i, n i = 0 → n ≠ 0 → NoSingle n →
    ∃ (σ : Equiv.Perm (Fin 4)) (s : ZMod 5), s ≠ 0 ∧ ∀ i, n i = s * v1 (σ i) := by
  decide +kernel

theorem pairing_perm : ∀ σ τ : Equiv.Perm (Fin 4),
    (∃ i j, i ≠ j ∧ v1 (σ i) = v1 (σ j) ∧ v1 (τ i) = v1 (τ j)) →
    ∃ c : ZMod 5, c ≠ 0 ∧ ∀ i, v1 (τ i) = c * v1 (σ i) := by
  decide +kernel

theorem lines_cases : ∀ σ : Equiv.Perm (Fin 4), ∃ c : ZMod 5, c ≠ 0 ∧
    ((∀ i, v1 (σ i) = c * v1 i) ∨ (∀ i, v1 (σ i) = c * v2 i) ∨ (∀ i, v1 (σ i) = c * v3 i)) := by
  decide

theorem lines_ne : ∀ c : ZMod 5,
    ¬ (∀ i, v2 i = c * v1 i) ∧ ¬ (∀ i, v3 i = c * v1 i) ∧ ¬ (∀ i, v3 i = c * v2 i) := by
  decide

theorem v2_eq : ∀ i, v2 i = v1 (Equiv.swap (1 : Fin 4) 2 i) := by decide

theorem v3_eq : ∀ i, v3 i = v1 (Equiv.swap (1 : Fin 4) 3 i) := by decide

theorem mul_ne_zero_zmod5 : ∀ a b : ZMod 5, a ≠ 0 → b ≠ 0 → a * b ≠ 0 := by decide

theorem cancel_zmod5 : ∀ s a b : ZMod 5, s ≠ 0 → s * a = s * b → a = b := by decide

theorem exists_inv_zmod5 : ∀ s : ZMod 5, s ≠ 0 → ∃ s' : ZMod 5, s * s' = 1 ∧ s' ≠ 0 := by decide

theorem sum_v1 : ∑ i, v1 i = 0 := by decide
theorem sum_v2 : ∑ i, v2 i = 0 := by decide
theorem sum_v3 : ∑ i, v3 i = 0 := by decide

theorem noSingle_or : ∀ n : Fin 4 → ZMod 5, ¬ NoSingle n ↔ ∃ i, ∀ j, j ≠ i → n j ≠ n i := by
  intro n
  simp [NoSingle]

theorem card_torus : Nat.card (torusSU 5 4 F16) = 5 ^ 3 := by
  have h := card_torusVec_eq (K := F16) (p := 5) (by norm_num) ⟨zeta, zeta_prim⟩ 3
  rw [torusSU, Subgroup.card_map_of_injective (f := diagUHom) diagU_injective]
  exact h

theorem torus_pow_five {g : GL (Fin 4) F16} (hg : g ∈ torusSU 5 4 F16) : g ^ 5 = 1 := by
  obtain ⟨d, hd, -, rfl⟩ := mem_torusSU_iff.mp hg
  rw [diagU_pow]
  have : d ^ 5 = 1 := funext hd
  rw [this, diagU_one]

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.U44Data
