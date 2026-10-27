module

public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceLinear

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance.Linear

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

@[expose] def ScalarsSquare (k : Type) [Field k] (n : ℕ) : Prop :=
  ∀ ζ : k, ζ ^ n = 1 → IsSquare ζ

theorem scalarsSquare_of_odd {k : Type} [Field k] {n : ℕ} (hn : Odd n) : ScalarsSquare k n := by
  intro ζ hζ
  obtain ⟨m, rfl⟩ := hn
  refine ⟨ζ ^ (m + 1), ?_⟩
  rw [← pow_add, show m + 1 + (m + 1) = (2 * m + 1) + 1 by ring, pow_succ, hζ, one_mul]

section Square

variable {n : ℕ} {k : Type} [Field k] {X : Type} [Group X]

theorem mul_self_mem_center_of_lift (hperf : Group.IsPerfect SL(n, k)) (ψ : SL(n, k) →* X)
    (hker : ψ.ker ≤ Subgroup.center SL(n, k)) {f : X} (hf : f * f = 1) {x : SL(n, k)}
    (hx : ∀ y, f * ψ y * f⁻¹ = ψ (x * y * x⁻¹)) : x * x ∈ Subgroup.center SL(n, k) := by
  have hcomm : ∀ y : SL(n, k), (x * x) * y * (x * x)⁻¹ * y⁻¹ ∈ Subgroup.center SL(n, k) := by
    intro y
    refine hker ?_
    have h1 : ψ ((x * x) * y * (x * x)⁻¹) = ψ y := by
      have e : (x * x) * y * (x * x)⁻¹ = x * (x * y * x⁻¹) * x⁻¹ := by group
      rw [e, ← hx, ← hx]
      calc f * (f * ψ y * f⁻¹) * f⁻¹ = (f * f) * ψ y * (f * f)⁻¹ := by group
        _ = ψ y := by rw [hf]; group
    simp only [MonoidHom.mem_ker, map_mul, map_inv] at h1 ⊢
    rw [h1]
    group
  have hR : (⊤ : Subgroup SL(n, k)) ≤ ⁅(⊤ : Subgroup SL(n, k)), ⊤⁆ := by
    have := hperf.commutator_eq_top
    rw [commutator_def] at this
    exact this.ge
  refine Subgroup.mem_center_iff.mpr fun y => ?_
  exact (CFSG.ClassicalInvolution.Balance.StrongBalance.commute_of_perfect_of_commutator_mem_center
    hR (fun s _ => hcomm s) y (Subgroup.mem_top y)).symm

end Square

section Toral

variable {X : Type} [Group X] [Finite X]

theorem isPerfect_specialLinear {n : ℕ} {k : Type} [Field k] [Finite k] (hn : 2 ≤ n)
    (h4 : 4 ≤ Nat.card k) : Group.IsPerfect SL(n, k) :=
  ⟨((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
    (CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple n k hn
      (Or.inr (by omega)) (Or.inr (by omega)))).1⟩

theorem strongConclusion_gf_toral {p e n : ℕ} [Fact p.Prime] (hn : 3 ≤ n) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ e) (hsq : ScalarsSquare (GaloisField p e) n)
    (ψ : SL(n, GaloisField p e) →* X) (hker : ψ.ker ≤ Subgroup.center SL(n, GaloisField p e))
    (hnorm : ψ.range.Normal) {F : Subgroup X} (hcard : Nat.card F = 4)
    (hF2 : ∀ f ∈ F, f * f = 1) (htoral : ToralAction ψ F) : StrongConclusion ψ.range F := by
  obtain ⟨P, hP, hact⟩ := htoral
  have he : e ≠ 0 := by
    rintro rfl
    simp at h5
  have h4 : 4 ≤ Nat.card (GaloisField p e) := by
    rw [GaloisField.card p e he]
    omega
  have hperf := isPerfect_specialLinear (n := n) (k := GaloisField p e) (by omega) h4
  refine strongConclusion_gf_split hn hp2 h5 ψ hker hnorm hcard hF2 P hP fun f hf => ?_
  obtain ⟨x, hxP, hxa⟩ := hact f hf
  refine ⟨x, hxP, hxa, ?_⟩
  obtain ⟨r, hr, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp
    (mul_self_mem_center_of_lift hperf ψ hker (hF2 f hf) hxa)
  obtain ⟨s, hs⟩ := hsq r (by simpa using hr)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [Fintype.card_fin, zero_pow (by omega)] at hr
    exact zero_ne_one hr
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hr0 (by simpa using hs)
  refine ⟨s, hs0, ?_⟩
  have hxx : ((x * x : SL(n, GaloisField p e)) : Matrix (Fin n) (Fin n) (GaloisField p e)) =
      (x : Matrix (Fin n) (Fin n) (GaloisField p e)) * x := Matrix.SpecialLinearGroup.coe_mul _ _
  rw [← hxx, ← hrx, hs, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  simp only [pow_two]

end Toral

section RankOne

theorem coe_sq_eq_neg_one_of_sq_central {k : Type} [Field k] {x : SL(2, k)}
    (hx : x ∉ Subgroup.center SL(2, k)) (hx2 : x * x ∈ Subgroup.center SL(2, k)) :
    (x : Matrix (Fin 2) (Fin 2) k) * x = (-1 : k) • (1 : Matrix (Fin 2) (Fin 2) k) := by
  obtain ⟨r, -, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hx2
  have hM : (x : Matrix (Fin 2) (Fin 2) k) * x = r • (1 : Matrix (Fin 2) (Fin 2) k) := by
    have h1 : ((x * x : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) =
        (x : Matrix (Fin 2) (Fin 2) k) * x := Matrix.SpecialLinearGroup.coe_mul _ _
    rw [← h1, ← hrx, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hdet : (x : Matrix (Fin 2) (Fin 2) k).det = 1 := x.2
  rw [Matrix.det_fin_two] at hdet
  have e00 := congrFun (congrFun hM 0) 0
  have e01 := congrFun (congrFun hM 0) 1
  have e10 := congrFun (congrFun hM 1) 0
  have e11 := congrFun (congrFun hM 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne, ne_eq, Fin.zero_eq_one_iff, not_false_eq_true, Fin.one_eq_zero_iff,
    OfNat.ofNat_ne_one, smul_eq_mul, mul_one, mul_zero]
    at e00 e01 e10 e11
  set a := (x : Matrix (Fin 2) (Fin 2) k) 0 0
  set b := (x : Matrix (Fin 2) (Fin 2) k) 0 1
  set c := (x : Matrix (Fin 2) (Fin 2) k) 1 0
  set d := (x : Matrix (Fin 2) (Fin 2) k) 1 1
  by_cases hsum : a + d = 0
  · have hd : d = -a := by linear_combination hsum
    rw [hd] at hdet
    have hr : r = -1 := by linear_combination (-1 : k) * e00 + (-1 : k) * hdet
    rw [hM, hr]
  · exfalso
    have hb : b = 0 := by
      have : b * (a + d) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right hsum
    have hc : c = 0 := by
      have : c * (a + d) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right hsum
    have had : a = d := by
      have : (a - d) * (a + d) = 0 := by rw [hb, hc] at e00 e11; linear_combination e00 - e11
      have := (mul_eq_zero.mp this).resolve_right hsum
      linear_combination this
    have hxs : (x : Matrix (Fin 2) (Fin 2) k) = a • (1 : Matrix (Fin 2) (Fin 2) k) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [a, b, c, d, hb, hc, had]
    refine hx (Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hxs, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

variable {X : Type} [Group X] [Finite X]

theorem false_of_toral_two {k : Type} [Field k] [Finite k] (h2 : (2 : k) ≠ 0)
    (h4 : 4 ≤ Nat.card k) (ψ : SL(2, k) →* X) (hker : ψ.ker ≤ Subgroup.center SL(2, k))
    {F : Subgroup X} (hcard : Nat.card F = 4) (hF2 : ∀ f ∈ F, f * f = 1)
    (hfaith : ∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ ψ.range, f * x = x * f) (htoral : ToralAction ψ F) :
    False := by
  obtain ⟨P, hP, hact⟩ := htoral
  obtain ⟨a, haF, b, hbF, ha1, hb1, hab1⟩ := exists_pair_of_card_four hcard hF2
  have hperf := isPerfect_specialLinear (n := 2) (k := k) le_rfl h4
  obtain ⟨xa, hxaP, hxa⟩ := hact a haF
  obtain ⟨xb, hxbP, hxb⟩ := hact b hbF
  have hnc : ∀ (f : X) (x : SL(2, k)), f ∈ F → f ≠ 1 →
      (∀ y, f * ψ y * f⁻¹ = ψ (x * y * x⁻¹)) → x ∉ Subgroup.center SL(2, k) := by
    intro f x hf hf1 hfa hcen
    refine hfaith f hf hf1 ?_
    rintro _ ⟨y, rfl⟩
    have := hfa y
    rw [conj_eq_of_mem_center hcen y] at this
    exact mul_inv_eq_iff_eq_mul.mp this
  have hxa2 := coe_sq_eq_neg_one_of_sq_central (hnc a xa haF ha1 hxa)
    (mul_self_mem_center_of_lift hperf ψ hker (hF2 a haF) hxa)
  have hxb2 := coe_sq_eq_neg_one_of_sq_central (hnc b xb hbF hb1 hxb)
    (mul_self_mem_center_of_lift hperf ψ hker (hF2 b hbF) hxb)
  have hcomm : xa * xb = xb * xa := hP xa hxaP xb hxbP
  have hcomm' : (xa : Matrix (Fin 2) (Fin 2) k) * xb = xb * xa := by
    have := congrArg (fun z : SL(2, k) => (z : Matrix (Fin 2) (Fin 2) k)) hcomm
    simpa only [Matrix.SpecialLinearGroup.coe_mul] using this
  have hsq : (xa * xb) * (xa * xb) = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_one]
    calc ((xa : Matrix (Fin 2) (Fin 2) k) * xb) * ((xa : Matrix (Fin 2) (Fin 2) k) * xb)
        = (xa : Matrix (Fin 2) (Fin 2) k) * (xb * xa) * xb := by simp only [Matrix.mul_assoc]
      _ = (xa : Matrix (Fin 2) (Fin 2) k) * (xa * xb) * xb := by rw [hcomm']
      _ = ((xa : Matrix (Fin 2) (Fin 2) k) * xa) * (xb * xb) := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hxa2, hxb2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul]
        norm_num
  have hcen := sl2_involution_central h2 hsq
  refine hfaith (a * b) (F.mul_mem haF hbF) hab1 ?_
  rintro _ ⟨y, rfl⟩
  have hab : (a * b) * ψ y * (a * b)⁻¹ = ψ ((xa * xb) * y * (xa * xb)⁻¹) := by
    calc (a * b) * ψ y * (a * b)⁻¹ = a * (b * ψ y * b⁻¹) * a⁻¹ := by group
      _ = ψ (xa * (xb * y * xb⁻¹) * xa⁻¹) := by rw [hxb, hxa]
      _ = ψ ((xa * xb) * y * (xa * xb)⁻¹) := by congr 1; group
  rw [conj_eq_of_mem_center hcen y] at hab
  exact mul_inv_eq_iff_eq_mul.mp hab

end RankOne

section Tag

open CFSG.ClassicalInvolution.Balance.StrongBalance

@[expose] def PSLScalarsSquare (n p e : ℕ) : Prop :=
  ∀ _ : Fact p.Prime, ScalarsSquare (GaloisField p e) n

theorem strongLocalTwoBalanceToralOn_PSL_scalarsSquare :
    StrongLocalTwoBalanceToralOn .PSL PSLScalarsSquare := by
  intro n p e hp hq hfund hadm hp2 h5 X _ _ ψ hker hnorm F hcard hF2 hfaith htoral
  have : Fact p.Prime := ⟨hp⟩
  have hsq := hq this
  have hn : 2 ≤ n := hadm.2.2.1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  by_cases h3 : 3 ≤ m + 1
  · exact strongConclusion_gf_toral h3 hp2 h5 hsq ψ hker hnorm hcard hF2 htoral
  · exfalso
    obtain rfl : m = 1 := by omega
    have he : e ≠ 0 := by
      rintro rfl
      simp at h5
    have h4 : 4 ≤ Nat.card (GaloisField p e) := by
      rw [GaloisField.card p e he]
      omega
    exact false_of_toral_two (CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2) h4
      ψ hker hcard hF2 hfaith htoral

theorem strongLocalTwoBalanceToralOn_PSL_odd :
    StrongLocalTwoBalanceToralOn .PSL fun n _ _ => Odd n :=
  strongLocalTwoBalanceToralOn_PSL_scalarsSquare.mono fun _ _ _ hn _ => scalarsSquare_of_odd hn

end Tag

end CFSG.ClassicalInvolution.Balance.StrongBalance.Linear
