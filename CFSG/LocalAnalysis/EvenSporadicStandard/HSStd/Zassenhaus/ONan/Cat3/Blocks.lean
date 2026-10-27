module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3.Basic
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3

open Subgroup CFSG.Open Matrix
open CFSG.Open.StatedAPI
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

section MatrixGeneric

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

private theorem det_pairMat {a b : ι} (hab : a ≠ b) (g : Matrix (Fin 2) (Fin 2) K) :
    (pairMat a b g).det = g.det := by
  let U : Matrix ι (Fin 2) K := Matrix.of fun x c =>
    if c = 0 then (if x = a then (1 : K) else 0) else (if x = b then (1 : K) else 0)
  let V : Matrix (Fin 2) ι K := Matrix.of fun c y =>
    if c = 0 then (if y = a then g 0 0 - 1 else if y = b then g 0 1 else 0)
    else (if y = a then g 1 0 else if y = b then g 1 1 - 1 else 0)
  have hUV : pairMat a b g = U * V + 1 := by
    ext x y
    rw [Matrix.add_apply, mul_apply, Fin.sum_univ_two]
    by_cases hxa : x = a
    · rw [hxa]
      by_cases hya : y = a
      · rw [hya]; simp [U, V, pairMat, hab, Ne.symm hab, sub_add_cancel]
      by_cases hyb : y = b
      · rw [hyb]; simp [U, V, pairMat, hab, Ne.symm hab]
      · simp [U, V, pairMat, hya, hyb, Ne.symm hya, Ne.symm hyb, hab, Ne.symm hab]
    by_cases hxb : x = b
    · rw [hxb]
      by_cases hya : y = a
      · rw [hya]; simp [U, V, pairMat, hab, Ne.symm hab]
      by_cases hyb : y = b
      · rw [hyb]; simp [U, V, pairMat, hab, Ne.symm hab, sub_add_cancel]
      · simp [U, V, pairMat, hya, hyb, Ne.symm hya, Ne.symm hyb, hab, Ne.symm hab]
    · simp [U, V, pairMat, hxa, hxb, Ne.symm hxa, Ne.symm hxb, hab, Ne.symm hab]
  have hVU : g = V * U + 1 := by
    ext i j
    rw [Matrix.add_apply, mul_apply,
      Fintype.sum_eq_add a b hab (fun z hz => by simp [U, hz.1, hz.2])]
    fin_cases i <;> fin_cases j <;> simp [U, V, hab, Ne.symm hab, sub_add_cancel]
  rw [hUV, det_mul_add_one_comm U V, ← hVU]

private theorem pairMat_mul_pairMat_entries {a b c d : ι}
    (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (g h : Matrix (Fin 2) (Fin 2) K) (u : K)
    (heq : pairMat a b g * pairMat c d h = u • (1 : Matrix ι ι K)) :
    g 0 0 = u ∧ g 0 1 = 0 ∧ g 1 0 = 0 ∧ g 1 1 = u ∧ h 0 0 = u ∧ h 0 1 = 0 := by
  have hdisj : Disjoint ({a, b} : Set ι) ({c, d} : Set ι) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hx'
    rcases hx with rfl | rfl
    · rcases hx' with h | h
      · exact hac h
      · exact had h
    · rcases hx' with h | h
      · exact hbc h
      · exact hbd h
  have hc : c ∉ ({a, b} : Set ι) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hac.symm, hbc.symm⟩
  have hd : d ∉ ({a, b} : Set ι) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨had.symm, hbd.symm⟩
  have h00 : g 0 0 = u := by
    have h' := congrFun (congrFun heq a) a
    rw [IsSupp.mul_apply_of_mem (isSupp_pairMat (a := a) (b := b) g)
      (isSupp_pairMat (a := c) (b := d) h) hdisj (by simp), (pairMat_apply_pair hab g).1] at h'
    simpa using h'
  have h01 : g 0 1 = 0 := by
    have h' := congrFun (congrFun heq a) b
    rw [IsSupp.mul_apply_of_mem (isSupp_pairMat (a := a) (b := b) g)
      (isSupp_pairMat (a := c) (b := d) h) hdisj (by simp), (pairMat_apply_pair hab g).2.1] at h'
    simpa [hab, Ne.symm hab] using h'
  have h10 : g 1 0 = 0 := by
    have h' := congrFun (congrFun heq b) a
    rw [IsSupp.mul_apply_of_mem (isSupp_pairMat (a := a) (b := b) g)
      (isSupp_pairMat (a := c) (b := d) h) hdisj (by simp), (pairMat_apply_pair hab g).2.2.1] at h'
    simpa [hab, Ne.symm hab] using h'
  have h11 : g 1 1 = u := by
    have h' := congrFun (congrFun heq b) b
    rw [IsSupp.mul_apply_of_mem (isSupp_pairMat (a := a) (b := b) g)
      (isSupp_pairMat (a := c) (b := d) h) hdisj (by simp), (pairMat_apply_pair hab g).2.2.2] at h'
    simpa using h'
  have hh00 : h 0 0 = u := by
    have h' := congrFun (congrFun heq c) c
    rw [IsSupp.mul_apply_of_notMem (isSupp_pairMat (a := a) (b := b) g) hc
      (pairMat c d h) c, (pairMat_apply_pair hcd h).1] at h'
    simpa using h'
  have hh01 : h 0 1 = 0 := by
    have h' := congrFun (congrFun heq c) d
    rw [IsSupp.mul_apply_of_notMem (isSupp_pairMat (a := a) (b := b) g) hc
      (pairMat c d h) d, (pairMat_apply_pair hcd h).2.1] at h'
    simpa [hcd, Ne.symm hcd] using h'
  exact ⟨h00, h01, h10, h11, hh00, hh01⟩

end MatrixGeneric

section SL2

variable {K : Type} [Field K]

private def X : SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, -1; 1, -1], by simp [Matrix.det_fin_two_of]⟩

private theorem coe_X :
    ((X : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, -1; 1, -1] := rfl

private theorem X_mul_self_mul_self : (X : SpecialLinearGroup (Fin 2) K) * X * X = 1 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [X, mul_apply, Fin.sum_univ_two]

private theorem X_ne_one : (X : SpecialLinearGroup (Fin 2) K) ≠ 1 := by
  intro h
  have h1 := congrArg
    (fun g : SpecialLinearGroup (Fin 2) K => ((g : Matrix (Fin 2) (Fin 2) K)) 0 1) h
  simp [X] at h1

private theorem X_cubed : (X : SpecialLinearGroup (Fin 2) K) ^ 3 = 1 := by
  rw [show (X : SpecialLinearGroup (Fin 2) K) ^ 3 = X * X * X by
      rw [pow_succ, pow_succ, pow_one]]
  exact X_mul_self_mul_self

private theorem orderOf_X : orderOf (X : SpecialLinearGroup (Fin 2) K) = 3 := by
  apply orderOf_eq_prime
  · exact X_cubed
  · exact X_ne_one

private theorem smul_one_pow (μ : K) (k : ℕ) :
    (μ • (1 : Matrix (Fin 2) (Fin 2) K)) ^ k = μ ^ k • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [Matrix.smul_one_eq_diagonal, Matrix.smul_one_eq_diagonal, Matrix.diagonal_pow]
  simp

private def Usl (b : K) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, b; 0, 1], by simp [Matrix.det_fin_two_of]⟩

private theorem Usl_mul (p q : K) : Usl p * Usl q = Usl (p + q) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [Usl, mul_apply, Fin.sum_univ_two, add_comm]

private def hU : Multiplicative K →* SpecialLinearGroup (Fin 2) K where
  toFun b := Usl b.toAdd
  map_one' := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Usl]
  map_mul' b b' := by
    rw [toAdd_mul, Usl_mul]

private theorem coe_hU (b : Multiplicative K) :
    ((hU b : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![1, b.toAdd; 0, 1] := rfl

private def hS : ℤˣ →* SpecialLinearGroup (Fin 2) K :=
  sl2Diag.comp (Units.map (Int.castRingHom K).toMonoidHom)

private theorem intUnits_inv_eq_self (ε : ℤˣ) : ε⁻¹ = ε := by
  rcases Int.units_eq_one_or ε with h | h <;> simp [h]

private theorem coe_hS (ε : ℤˣ) :
    ((hS ε : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![(((ε : ℤ) : K)), 0; 0, (((ε : ℤ) : K))] := by
  rw [hS, MonoidHom.comp_apply, coe_sl2Diag, ← map_inv, intUnits_inv_eq_self]
  simp

private theorem commute_hU_hS (b : Multiplicative K) (ε : ℤˣ) : Commute (hU b) (hS ε) := by
  show hU b * hS ε = hS ε * hU b
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_hU, coe_hS]
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two, mul_comm]

private def hUS : Multiplicative K × ℤˣ →* SpecialLinearGroup (Fin 2) K :=
  hU.noncommCoprod hS commute_hU_hS

private theorem coe_hUS (b : Multiplicative K) (ε : ℤˣ) :
    ((hUS (b, ε) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![(((ε : ℤ) : K)), b.toAdd * (((ε : ℤ) : K)); 0, (((ε : ℤ) : K))] := by
  rw [hUS, MonoidHom.noncommCoprod_apply, Matrix.SpecialLinearGroup.coe_mul, coe_hU, coe_hS]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]

end SL2

private theorem card_eq_two_or_four_of_bounds {K : Type} [Field K] [Finite K]
    (h3 : ringChar K ≠ 3) (h3q : 3 * Nat.card K ≤ 18)
    (hor : ringChar K = 2 ∨ 6 * Nat.card K ≤ 18) :
    Nat.card K = 2 ∨ Nat.card K = 4 := by
  have : Fintype K := Fintype.ofFinite K
  haveI := ringChar.charP K
  obtain ⟨n, hpn, hn⟩ := FiniteField.card K (ringChar K)
  have hq : Nat.card K = ringChar K ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card, hn]
  rcases hor with h2 | h6
  · have hqle : Nat.card K ≤ 6 := by omega
    rw [h2] at hq
    have hnle : (n : ℕ) ≤ 2 := by
      by_contra h
      have h3n : 3 ≤ (n : ℕ) := by have := n.pos; omega
      have h8 : 2 ^ 3 ≤ 2 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) h3n
      omega
    have hn1 : (n : ℕ) = 1 ∨ (n : ℕ) = 2 := by have := n.pos; omega
    rcases hn1 with h1 | h1
    · left; rw [hq, h1]; norm_num
    · right; rw [hq, h1]; norm_num
  · have hqle : Nat.card K ≤ 3 := by omega
    have hpq : ringChar K ≤ Nat.card K := by
      have hp1 : 1 ≤ ringChar K := by have := hpn.two_le; omega
      have hn1' : 1 ≤ (n : ℕ) := by have := n.pos; omega
      rw [hq]
      calc ringChar K = ringChar K ^ 1 := (pow_one _).symm
        _ ≤ ringChar K ^ (n : ℕ) := Nat.pow_le_pow_right hp1 hn1'
    have hp2 : ringChar K = 2 := by
      have := hpn.two_le
      omega
    have hq2 : 2 ^ (n : ℕ) ≤ 3 := by
      rw [hq, hp2] at hqle
      exact hqle
    have hn1 : (n : ℕ) = 1 := by
      by_contra h
      have h2n : 2 ≤ (n : ℕ) := by have := n.pos; omega
      have h4 : 4 ≤ 2 ^ (n : ℕ) := by
        calc (4 : ℕ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) h2n
      omega
    left
    rw [hq, hp2, hn1]
    norm_num

section PSL

variable {K : Type} [Field K] [Finite K]

local notation "SL2" => Matrix.SpecialLinearGroup (Fin 2)

private theorem psl_aux {n : ℕ} (hn : 4 ≤ n) (h3 : ringChar K ≠ 3)
    (hC : CentHyp (StatedProj (StatedSL n K))) : Nat.card K = 2 ∨ Nat.card K = 4 := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let c : Fin n := ⟨2, by omega⟩
  let d : Fin n := ⟨3, by omega⟩
  have hab : a ≠ b := by intro h; have := congrArg Fin.val h; simp [a, b] at this
  have hcd : c ≠ d := by intro h; have := congrArg Fin.val h; simp [c, d] at this
  have hac : a ≠ c := by intro h; have := congrArg Fin.val h; simp [a, c] at this
  have had : a ≠ d := by intro h; have := congrArg Fin.val h; simp [a, d] at this
  have hbc : b ≠ c := by intro h; have := congrArg Fin.val h; simp [b, c] at this
  have hbd : b ≠ d := by intro h; have := congrArg Fin.val h; simp [b, d] at this
  have hdisj : Disjoint ({a, b} : Set (Fin n)) ({c, d} : Set (Fin n)) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hx'
    rcases hx with rfl | rfl
    · rcases hx' with h | h
      · exact hac h
      · exact had h
    · rcases hx' with h | h
      · exact hbc h
      · exact hbd h
  have hmem1 : ∀ g : SpecialLinearGroup (Fin 2) K, pairGL hab g ∈ StatedSL n K := fun g => by
    rw [mem_statedSL_iff, coe_pairGL, det_pairMat hab]; exact g.2
  have hmem2 : ∀ g : SpecialLinearGroup (Fin 2) K, pairGL hcd g ∈ StatedSL n K := fun g => by
    rw [mem_statedSL_iff, coe_pairGL, det_pairMat hcd]; exact g.2
  let pairSL1 : SpecialLinearGroup (Fin 2) K →* StatedSL n K := (pairGL hab).codRestrict _ hmem1
  let pairSL2 : SpecialLinearGroup (Fin 2) K →* StatedSL n K := (pairGL hcd).codRestrict _ hmem2
  let uX : ↥(Subgroup.zpowers (X : SpecialLinearGroup (Fin 2) K)) :=
    ⟨X, Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩⟩
  let α : ↥(Subgroup.zpowers (X : SpecialLinearGroup (Fin 2) K)) →* StatedSL n K :=
    pairSL1.comp (Subgroup.zpowers (X : SpecialLinearGroup (Fin 2) K)).subtype
  let Γ₁ : Multiplicative K × ℤˣ →* StatedSL n K := pairSL2.comp hUS
  let Γ₀ : Multiplicative K →* StatedSL n K := pairSL2.comp hU
  have hΓ₀_eq : ∀ b : Multiplicative K, Γ₀ b = Γ₁ (b, 1) := by
    intro b
    simp [Γ₀, Γ₁, hUS, MonoidHom.noncommCoprod_apply]
  have hcomm : ∀ u w, Commute (α u) (Γ₁ w) := by
    intro u w
    have hGL : Commute ((α u : StatedSL n K) : GL (Fin n) K)
        ((Γ₁ w : StatedSL n K) : GL (Fin n) K) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul]
      rw [show ((α u : StatedSL n K) : GL (Fin n) K) = pairGL hab (u : SL2 K) from rfl,
        show ((Γ₁ w : StatedSL n K) : GL (Fin n) K) = pairGL hcd (hUS w) from rfl,
        coe_pairGL, coe_pairGL]
      exact (isSupp_pairMat (a := a) (b := b) ((u : SL2 K) : Matrix (Fin 2) (Fin 2) K)).commute
        (isSupp_pairMat (a := c) (b := d) ((hUS w : SL2 K) : Matrix (Fin 2) (Fin 2) K)) hdisj
    exact Subtype.ext hGL.eq
  have hcomm₀ : ∀ u b, Commute (α u) (Γ₀ b) := by
    intro u b
    rw [hΓ₀_eq b]
    exact hcomm u (b, 1)
  let Φ₁ : (↥(Subgroup.zpowers (X : SpecialLinearGroup (Fin 2) K))) ×
      (Multiplicative K × ℤˣ) →* StatedSL n K := α.noncommCoprod Γ₁ hcomm
  let Φ₀ : (↥(Subgroup.zpowers (X : SpecialLinearGroup (Fin 2) K))) ×
      Multiplicative K →* StatedSL n K := α.noncommCoprod Γ₀ hcomm₀
  let A₁ : Subgroup (StatedSL n K) := Φ₁.range
  let A₀ : Subgroup (StatedSL n K) := Φ₀.range
  let x : StatedSL n K := α uX
  have coe_Φ₁ : ∀ v : (↥(Subgroup.zpowers (X : SpecialLinearGroup (Fin 2) K))) ×
      (Multiplicative K × ℤˣ),
      (((Φ₁ v : StatedSL n K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        pairMat a b ((v.1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) *
        pairMat c d ((hUS v.2 : SL2 K) : Matrix (Fin 2) (Fin 2) K) := by
    intro v
    change ((((α v.1) * (Γ₁ v.2) : StatedSL n K) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = _
    rw [Subgroup.coe_mul, Units.val_mul,
      show ((α v.1 : StatedSL n K) : GL (Fin n) K) = pairGL hab (v.1 : SL2 K) from rfl,
      show ((Γ₁ v.2 : StatedSL n K) : GL (Fin n) K) = pairGL hcd (hUS v.2) from rfl,
      coe_pairGL, coe_pairGL]
  have coe_Φ₀ : ∀ v : (↥(Subgroup.zpowers (X : SpecialLinearGroup (Fin 2) K))) ×
      Multiplicative K,
      (((Φ₀ v : StatedSL n K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        pairMat a b ((v.1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) *
        pairMat c d ((hU v.2 : SL2 K) : Matrix (Fin 2) (Fin 2) K) := by
    intro v
    change ((((α v.1) * (Γ₀ v.2) : StatedSL n K) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = _
    rw [Subgroup.coe_mul, Units.val_mul,
      show ((α v.1 : StatedSL n K) : GL (Fin n) K) = pairGL hab (v.1 : SL2 K) from rfl,
      show ((Γ₀ v.2 : StatedSL n K) : GL (Fin n) K) = pairGL hcd (hU v.2) from rfl,
      coe_pairGL, coe_pairGL]
  have hkey₀ : ∀ v : (↥(Subgroup.zpowers (X : SpecialLinearGroup (Fin 2) K))) ×
      Multiplicative K,
      ((Φ₀ v : StatedSL n K) : GL (Fin n) K) ∈ StatedScalars (Fin n) K → v = 1 := by
    intro v hv
    obtain ⟨μ, hμ⟩ := MonoidHom.mem_range.mp hv
    have hmat : (((Φ₀ v : StatedSL n K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (μ : K) • 1 := by
      rw [← hμ, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal]
    have heq : pairMat a b ((v.1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) *
        pairMat c d ((hU v.2 : SL2 K) : Matrix (Fin 2) (Fin 2) K) = (μ : K) • 1 := by
      rw [← coe_Φ₀ v]; exact hmat
    obtain ⟨hg00, hg01, hg10, hg11, hh00, hh01⟩ :=
      pairMat_mul_pairMat_entries hab hcd hac had hbc hbd _ _ (μ : K) heq
    have hh00' : ((hU v.2 : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 0 = (1 : K) := by
      rw [coe_hU]; simp
    have hμ1 : (μ : K) = 1 := by rw [← hh00]; exact hh00'
    have hg1 : ((v.1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.one_apply, hg00, hg01, hg10, hg11, hμ1]
    have hv1sl2 : (v.1 : SL2 K) = 1 := Subtype.ext hg1
    have hv1 : v.1 = 1 := Subtype.ext (by simpa using hv1sl2)
    have hh01' : ((hU v.2 : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 1 = v.2.toAdd := by
      rw [coe_hU]; simp
    have hb : v.2.toAdd = 0 := by rw [← hh01']; exact hh01
    have hv2 : v.2 = 1 := Multiplicative.toAdd.injective (by simpa using hb)
    exact Prod.ext hv1 hv2
  have hkey₁ : (ringChar K ≠ 2) → ∀ v :
      (↥(Subgroup.zpowers (X : SpecialLinearGroup (Fin 2) K))) ×
      (Multiplicative K × ℤˣ),
      ((Φ₁ v : StatedSL n K) : GL (Fin n) K) ∈ StatedScalars (Fin n) K → v = 1 := by
    intro h2 v hv
    obtain ⟨μ, hμ⟩ := MonoidHom.mem_range.mp hv
    have hmat : (((Φ₁ v : StatedSL n K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (μ : K) • 1 := by
      rw [← hμ, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal]
    have heq : pairMat a b ((v.1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) *
        pairMat c d ((hUS v.2 : SL2 K) : Matrix (Fin 2) (Fin 2) K) = (μ : K) • 1 := by
      rw [← coe_Φ₁ v]; exact hmat
    obtain ⟨hg00, hg01, hg10, hg11, hh00, hh01⟩ :=
      pairMat_mul_pairMat_entries hab hcd hac had hbc hbd _ _ (μ : K) heq
    have hg : ((v.1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) = (μ : K) • 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.smul_apply, Matrix.one_apply, hg00, hg01, hg10, hg11]
    have hμ2 : (μ : K) ^ 2 = 1 := by
      have hdet := (v.1 : SL2 K).2
      rw [hg, Matrix.det_smul, Matrix.det_one, mul_one] at hdet
      simpa using hdet
    have hv1pow : (v.1 : SL2 K) ^ 3 = 1 := by
      have h := orderOf_dvd_of_mem_zpowers (v.1).2
      rw [orderOf_X] at h
      exact (orderOf_dvd_iff_pow_eq_one).mp h
    have hg3 : (((v.1 : SL2 K) : Matrix (Fin 2) (Fin 2) K)) ^ 3 = 1 := by
      have h := congrArg (fun z : SL2 K => ((z : Matrix (Fin 2) (Fin 2) K))) hv1pow
      simpa using h
    have hμ3 : (μ : K) ^ 3 = 1 := by
      have h := hg3
      rw [hg, smul_one_pow] at h
      have h00 := congrFun (congrFun h 0) 0
      simpa [Matrix.smul_apply, Matrix.one_apply] using h00
    have hμ1 : (μ : K) = 1 := by
      have h3 : (μ : K) ^ 3 = (μ : K) := by
        rw [show (μ : K) ^ 3 = (μ : K) ^ 2 * (μ : K) by rw [pow_succ], hμ2, one_mul]
      rw [← h3]; exact hμ3
    have hg1 : ((v.1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) = 1 := by rw [hg, hμ1, one_smul]
    have hv1sl2 : (v.1 : SL2 K) = 1 := Subtype.ext hg1
    have hv1 : v.1 = 1 := Subtype.ext (by simpa using hv1sl2)
    have hh00' : ((hUS v.2 : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 0 = (((v.2.2 : ℤ) : K)) := by
      rw [coe_hUS]; simp
    have hεK : (((v.2.2 : ℤ) : K)) = 1 := by rw [← hh00', hh00, hμ1]
    have hh01' : ((hUS v.2 : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 1 =
        v.2.1.toAdd * (((v.2.2 : ℤ) : K)) := by
      rw [coe_hUS]; simp
    have hb : v.2.1.toAdd = 0 := by
      have hbK : v.2.1.toAdd * (((v.2.2 : ℤ) : K)) = 0 := by rw [← hh01']; exact hh01
      rwa [hεK, mul_one] at hbK
    have hv21 : v.2.1 = 1 := Multiplicative.toAdd.injective (by simpa using hb)
    have hε : v.2.2 = 1 := by
      rcases Int.units_eq_one_or v.2.2 with h | h
      · exact h
      · exfalso
        rw [h] at hεK
        exact (Ring.neg_one_ne_one_of_char_ne_two h2) (by simpa using hεK)
    exact Prod.ext hv1 (Prod.ext hv21 hε)
  have hinj₀ : Function.Injective Φ₀ := by
    intro v w hvw
    have h1 : v * w⁻¹ = 1 := by
      apply hkey₀ (v * w⁻¹)
      have : Φ₀ (v * w⁻¹) = 1 := by rw [map_mul, map_inv, hvw, mul_inv_cancel]
      rw [this]; exact Subgroup.one_mem _
    exact mul_inv_eq_one.mp h1
  have hcard₀ : Nat.card A₀ = 3 * Nat.card K := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj₀).toEquiv]
    rw [Nat.card_prod, Nat.card_zpowers, orderOf_X, Nat.card_congr Multiplicative.toAdd]
  have habel : ∀ a ∈ A₁, ∀ b ∈ A₁, a * b = b * a := by
    rintro a ⟨v, rfl⟩ b ⟨w, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    refine Prod.ext ?_ ?_
    · exact mul_comm' v.1 w.1
    · exact Prod.ext (mul_comm _ _) (mul_comm _ _)
  have hxA₀ : x ∈ A₀ := by
    refine ⟨(uX, 1), ?_⟩
    change Φ₀ (uX, 1) = α uX
    simp [Φ₀, MonoidHom.noncommCoprod_apply]
  have hxA₁ : x ∈ A₁ := by
    refine ⟨(uX, 1), ?_⟩
    change Φ₁ (uX, 1) = α uX
    simp [Φ₁, MonoidHom.noncommCoprod_apply]
  have hA₀le : A₀ ≤ A₁ := by
    rintro a ⟨v, rfl⟩
    exact ⟨(v.1, (v.2, 1)), by
      change Φ₁ (v.1, (v.2, 1)) = Φ₀ v
      simp [Φ₀, Φ₁, MonoidHom.noncommCoprod_apply, hΓ₀_eq]⟩
  have habel₀ : ∀ a ∈ A₀, ∀ b ∈ A₀, a * b = b * a :=
    fun a ha b hb => habel a (hA₀le ha) b (hA₀le hb)
  have hAx₀ : ∀ a ∈ A₀, a * x = x * a := fun a ha => habel a (hA₀le ha) x hxA₁
  have hAz₀ : ∀ a ∈ A₀, (a : GL (Fin n) K) ∈ StatedScalars (Fin n) K → a = 1 := by
    rintro a ⟨v, rfl⟩ hv
    simp [hkey₀ v hv]
  have hx : orderOf (QuotientGroup.mk x : StatedProj (StatedSL n K)) = 3 := by
    apply orderOf_mk_eq_prime (p := 3) x
    · have hx3 : (x : GL (Fin n) K) ^ 3 = 1 := by
        rw [show (x : GL (Fin n) K) = pairGL hab (X : SL2 K) from rfl, ← map_pow, X_cubed,
          map_one]
      rw [hx3]; exact Subgroup.one_mem _
    · intro hmem
      obtain ⟨μ, hμ⟩ := MonoidHom.mem_range.mp hmem
      have hmat : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (μ : K) • 1 := by
        rw [← hμ, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
          ← Matrix.smul_one_eq_diagonal]
      have h1 : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b = 0 := by
        rw [hmat]; simp [Matrix.smul_apply, Matrix.one_apply_ne hab]
      have h2 : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b = -1 := by
        show (pairMat a b ((X : SL2 K) : Matrix (Fin 2) (Fin 2) K)) a b = -1
        rw [(pairMat_apply_pair hab _).2.1, coe_X]; simp
      rw [h1] at h2; norm_num at h2
  have h3q : 3 * Nat.card K ≤ 18 := by
    have h := CentHyp.card_le_of_proj hC hx hAx₀ habel₀ hAz₀
    rwa [hcard₀] at h
  rcases eq_or_ne (ringChar K) 2 with h2 | h2
  · exact card_eq_two_or_four_of_bounds h3 h3q (Or.inl h2)
  · have hinj₁ : Function.Injective Φ₁ := by
      intro v w hvw
      have h1 : v * w⁻¹ = 1 := by
        apply hkey₁ h2 (v * w⁻¹)
        have : Φ₁ (v * w⁻¹) = 1 := by rw [map_mul, map_inv, hvw, mul_inv_cancel]
        rw [this]; exact Subgroup.one_mem _
      exact mul_inv_eq_one.mp h1
    have hAx₁ : ∀ a ∈ A₁, a * x = x * a := fun a ha => habel a ha x hxA₁
    have hAz₁ : ∀ a ∈ A₁, (a : GL (Fin n) K) ∈ StatedScalars (Fin n) K → a = 1 := by
      rintro a ⟨v, rfl⟩ hv
      simp [hkey₁ h2 v hv]
    have hunits : Nat.card ℤˣ = 2 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
    have hcard₁ : Nat.card A₁ = 3 * (Nat.card K * 2) := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hinj₁).toEquiv]
      rw [Nat.card_prod, Nat.card_prod, Nat.card_zpowers, orderOf_X,
        Nat.card_congr Multiplicative.toAdd, hunits]
    have h6q : 6 * Nat.card K ≤ 18 := by
      have h := CentHyp.card_le_of_proj hC hx hAx₁ habel hAz₁
      rw [hcard₁] at h
      omega
    exact card_eq_two_or_four_of_bounds h3 h3q (Or.inr h6q)

theorem card_eq_two_or_four_of_psl_four (h3 : ringChar K ≠ 3)
    (hC : CentHyp (StatedProj (StatedSL 4 K))) : Nat.card K = 2 ∨ Nat.card K = 4 :=
  psl_aux (by norm_num) h3 hC

theorem card_eq_two_or_four_of_psl_five (h3 : ringChar K ≠ 3)
    (hC : CentHyp (StatedProj (StatedSL 5 K))) : Nat.card K = 2 ∨ Nat.card K = 4 :=
  psl_aux (by norm_num) h3 hC

end PSL

section PSP

variable {K : Type} [Field K] [Finite K]

local notation "SL2" => Matrix.SpecialLinearGroup (Fin 2)

private theorem psp_aux (h3 : ringChar K ≠ 3)
    (hC : CentHyp (StatedProj (StatedSp 2 K))) : Nat.card K = 2 ∨ Nat.card K = 4 := by
  let a : Fin 2 ⊕ Fin 2 := Sum.inl 0
  let b : Fin 2 ⊕ Fin 2 := Sum.inr 0
  let c : Fin 2 ⊕ Fin 2 := Sum.inl 1
  let d : Fin 2 ⊕ Fin 2 := Sum.inr 1
  have hab : a ≠ b := Sum.inl_ne_inr
  have hcd : c ≠ d := Sum.inl_ne_inr
  have hac : a ≠ c := by decide
  have had : a ≠ d := by decide
  have hbc : b ≠ c := by decide
  have hbd : b ≠ d := by decide
  have hdisj : Disjoint ({a, b} : Set (Fin 2 ⊕ Fin 2)) ({c, d} : Set (Fin 2 ⊕ Fin 2)) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hx'
    rcases hx with rfl | rfl
    · rcases hx' with h | h
      · exact hac h
      · exact had h
    · rcases hx' with h | h
      · exact hbc h
      · exact hbd h
  let uX : ↥(Subgroup.zpowers (X : SL2 K)) :=
    ⟨X, Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩⟩
  let α : ↥(Subgroup.zpowers (X : SL2 K)) →* StatedSp 2 K :=
    (lam (0 : Fin 2)).comp (Subgroup.zpowers (X : SL2 K)).subtype
  let Γ₁ : Multiplicative K × ℤˣ →* StatedSp 2 K := (lam (1 : Fin 2)).comp hUS
  let Γ₀ : Multiplicative K →* StatedSp 2 K := (lam (1 : Fin 2)).comp hU
  have hΓ₀_eq : ∀ b : Multiplicative K, Γ₀ b = Γ₁ (b, 1) := by
    intro b
    simp [Γ₀, Γ₁, hUS, MonoidHom.noncommCoprod_apply]
  have hcomm : ∀ u w, Commute (α u) (Γ₁ w) := by
    intro u w
    show Commute (lam (0 : Fin 2) (u : SL2 K)) (lam (1 : Fin 2) (hUS w))
    exact commute_lam_lam (by decide) (u : SL2 K) (hUS w)
  have hcomm₀ : ∀ u b, Commute (α u) (Γ₀ b) := by
    intro u b
    rw [hΓ₀_eq b]
    exact hcomm u (b, 1)
  let Φ₁ : (↥(Subgroup.zpowers (X : SL2 K))) × (Multiplicative K × ℤˣ) →* StatedSp 2 K :=
    α.noncommCoprod Γ₁ hcomm
  let Φ₀ : (↥(Subgroup.zpowers (X : SL2 K))) × Multiplicative K →* StatedSp 2 K :=
    α.noncommCoprod Γ₀ hcomm₀
  let A₁ : Subgroup (StatedSp 2 K) := Φ₁.range
  let A₀ : Subgroup (StatedSp 2 K) := Φ₀.range
  let x : StatedSp 2 K := α uX
  have coe_Φ₁ : ∀ v : (↥(Subgroup.zpowers (X : SL2 K))) × (Multiplicative K × ℤˣ),
      (((Φ₁ v : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        pairMat a b ((v.1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) *
        pairMat c d ((hUS v.2 : SL2 K) : Matrix (Fin 2) (Fin 2) K) := by
    intro v
    change ((((α v.1) * (Γ₁ v.2) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = _
    rw [Subgroup.coe_mul, Units.val_mul,
      show ((α v.1 : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) =
        lam (0 : Fin 2) (v.1 : SL2 K) from rfl,
      show ((Γ₁ v.2 : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) =
        lam (1 : Fin 2) (hUS v.2) from rfl,
      coe_lam, coe_lam]
  have coe_Φ₀ : ∀ v : (↥(Subgroup.zpowers (X : SL2 K))) × Multiplicative K,
      (((Φ₀ v : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        pairMat a b ((v.1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) *
        pairMat c d ((hU v.2 : SL2 K) : Matrix (Fin 2) (Fin 2) K) := by
    intro v
    change ((((α v.1) * (Γ₀ v.2) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = _
    rw [Subgroup.coe_mul, Units.val_mul,
      show ((α v.1 : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) =
        lam (0 : Fin 2) (v.1 : SL2 K) from rfl,
      show ((Γ₀ v.2 : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) =
        lam (1 : Fin 2) (hU v.2) from rfl,
      coe_lam, coe_lam]
  have hkey₀ : ∀ v : (↥(Subgroup.zpowers (X : SL2 K))) × Multiplicative K,
      ((Φ₀ v : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) ∈
        StatedScalars (Fin 2 ⊕ Fin 2) K → v = 1 := by
    intro v hv
    obtain ⟨μ, hμ⟩ := MonoidHom.mem_range.mp hv
    have hmat : (((Φ₀ v : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = (μ : K) • 1 := by
      rw [← hμ, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal]
    have heq : pairMat a b ((v.1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) *
        pairMat c d ((hU v.2 : SL2 K) : Matrix (Fin 2) (Fin 2) K) = (μ : K) • 1 := by
      rw [← coe_Φ₀ v]; exact hmat
    obtain ⟨hg00, hg01, hg10, hg11, hh00, hh01⟩ :=
      pairMat_mul_pairMat_entries hab hcd hac had hbc hbd _ _ (μ : K) heq
    have hh00' : ((hU v.2 : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 0 = (1 : K) := by
      rw [coe_hU]; simp
    have hμ1 : (μ : K) = 1 := by rw [← hh00]; exact hh00'
    have hg1 : ((v.1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.one_apply, hg00, hg01, hg10, hg11, hμ1]
    have hv1sl2 : (v.1 : SL2 K) = 1 := Subtype.ext hg1
    have hv1 : v.1 = 1 := Subtype.ext (by simpa using hv1sl2)
    have hh01' : ((hU v.2 : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 1 = v.2.toAdd := by
      rw [coe_hU]; simp
    have hb : v.2.toAdd = 0 := by rw [← hh01']; exact hh01
    have hv2 : v.2 = 1 := Multiplicative.toAdd.injective (by simpa using hb)
    exact Prod.ext hv1 hv2
  have hkey₁ : (ringChar K ≠ 2) → ∀ v : (↥(Subgroup.zpowers (X : SL2 K))) ×
      (Multiplicative K × ℤˣ),
      ((Φ₁ v : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) ∈
        StatedScalars (Fin 2 ⊕ Fin 2) K → v = 1 := by
    intro h2 v hv
    obtain ⟨μ, hμ⟩ := MonoidHom.mem_range.mp hv
    have hmat : (((Φ₁ v : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = (μ : K) • 1 := by
      rw [← hμ, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal]
    have heq : pairMat a b ((v.1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) *
        pairMat c d ((hUS v.2 : SL2 K) : Matrix (Fin 2) (Fin 2) K) = (μ : K) • 1 := by
      rw [← coe_Φ₁ v]; exact hmat
    obtain ⟨hg00, hg01, hg10, hg11, hh00, hh01⟩ :=
      pairMat_mul_pairMat_entries hab hcd hac had hbc hbd _ _ (μ : K) heq
    have hg : ((v.1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) = (μ : K) • 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.smul_apply, Matrix.one_apply, hg00, hg01, hg10, hg11]
    have hμ2 : (μ : K) ^ 2 = 1 := by
      have hdet := (v.1 : SL2 K).2
      rw [hg, Matrix.det_smul, Matrix.det_one, mul_one] at hdet
      simpa using hdet
    have hv1pow : (v.1 : SL2 K) ^ 3 = 1 := by
      have h := orderOf_dvd_of_mem_zpowers (v.1).2
      rw [orderOf_X] at h
      exact (orderOf_dvd_iff_pow_eq_one).mp h
    have hg3 : (((v.1 : SL2 K) : Matrix (Fin 2) (Fin 2) K)) ^ 3 = 1 := by
      have h := congrArg (fun z : SL2 K => ((z : Matrix (Fin 2) (Fin 2) K))) hv1pow
      simpa using h
    have hμ3 : (μ : K) ^ 3 = 1 := by
      have h := hg3
      rw [hg, smul_one_pow] at h
      have h00 := congrFun (congrFun h 0) 0
      simpa [Matrix.smul_apply, Matrix.one_apply] using h00
    have hμ1 : (μ : K) = 1 := by
      have h3 : (μ : K) ^ 3 = (μ : K) := by
        rw [show (μ : K) ^ 3 = (μ : K) ^ 2 * (μ : K) by rw [pow_succ], hμ2, one_mul]
      rw [← h3]; exact hμ3
    have hg1 : ((v.1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) = 1 := by rw [hg, hμ1, one_smul]
    have hv1sl2 : (v.1 : SL2 K) = 1 := Subtype.ext hg1
    have hv1 : v.1 = 1 := Subtype.ext (by simpa using hv1sl2)
    have hh00' : ((hUS v.2 : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 0 =
        (((v.2.2 : ℤ) : K)) := by
      rw [coe_hUS]; simp
    have hεK : (((v.2.2 : ℤ) : K)) = 1 := by rw [← hh00', hh00, hμ1]
    have hh01' : ((hUS v.2 : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 1 =
        v.2.1.toAdd * (((v.2.2 : ℤ) : K)) := by
      rw [coe_hUS]; simp
    have hb : v.2.1.toAdd = 0 := by
      have hbK : v.2.1.toAdd * (((v.2.2 : ℤ) : K)) = 0 := by rw [← hh01']; exact hh01
      rwa [hεK, mul_one] at hbK
    have hv21 : v.2.1 = 1 := Multiplicative.toAdd.injective (by simpa using hb)
    have hε : v.2.2 = 1 := by
      rcases Int.units_eq_one_or v.2.2 with h | h
      · exact h
      · exfalso
        rw [h] at hεK
        exact (Ring.neg_one_ne_one_of_char_ne_two h2) (by simpa using hεK)
    exact Prod.ext hv1 (Prod.ext hv21 hε)
  have hinj₀ : Function.Injective Φ₀ := by
    intro v w hvw
    have h1 : v * w⁻¹ = 1 := by
      apply hkey₀ (v * w⁻¹)
      have : Φ₀ (v * w⁻¹) = 1 := by rw [map_mul, map_inv, hvw, mul_inv_cancel]
      rw [this]; exact Subgroup.one_mem _
    exact mul_inv_eq_one.mp h1
  have hcard₀ : Nat.card A₀ = 3 * Nat.card K := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj₀).toEquiv]
    rw [Nat.card_prod, Nat.card_zpowers, orderOf_X, Nat.card_congr Multiplicative.toAdd]
  have habel : ∀ a ∈ A₁, ∀ b ∈ A₁, a * b = b * a := by
    rintro a ⟨v, rfl⟩ b ⟨w, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    refine Prod.ext ?_ ?_
    · exact mul_comm' v.1 w.1
    · exact Prod.ext (mul_comm _ _) (mul_comm _ _)
  have hxA₀ : x ∈ A₀ := by
    refine ⟨(uX, 1), ?_⟩
    change Φ₀ (uX, 1) = α uX
    simp [Φ₀, MonoidHom.noncommCoprod_apply]
  have hxA₁ : x ∈ A₁ := by
    refine ⟨(uX, 1), ?_⟩
    change Φ₁ (uX, 1) = α uX
    simp [Φ₁, MonoidHom.noncommCoprod_apply]
  have hA₀le : A₀ ≤ A₁ := by
    rintro a ⟨v, rfl⟩
    exact ⟨(v.1, (v.2, 1)), by
      change Φ₁ (v.1, (v.2, 1)) = Φ₀ v
      simp [Φ₀, Φ₁, MonoidHom.noncommCoprod_apply, hΓ₀_eq]⟩
  have habel₀ : ∀ a ∈ A₀, ∀ b ∈ A₀, a * b = b * a :=
    fun a ha b hb => habel a (hA₀le ha) b (hA₀le hb)
  have hAx₀ : ∀ a ∈ A₀, a * x = x * a := fun a ha => habel a (hA₀le ha) x hxA₁
  have hAz₀ : ∀ a ∈ A₀, (a : GL (Fin 2 ⊕ Fin 2) K) ∈
      StatedScalars (Fin 2 ⊕ Fin 2) K → a = 1 := by
    rintro a ⟨v, rfl⟩ hv
    simp [hkey₀ v hv]
  have hx : orderOf (QuotientGroup.mk x : StatedProj (StatedSp 2 K)) = 3 := by
    apply orderOf_mk_eq_prime (p := 3) x
    · have hx3sp : x ^ 3 = 1 := by
        rw [show x = lam (0 : Fin 2) (X : SL2 K) from rfl, ← map_pow, X_cubed, map_one]
      have hx3 : (x : GL (Fin 2 ⊕ Fin 2) K) ^ 3 = 1 := by
        rw [← Subgroup.coe_pow, hx3sp, Subgroup.coe_one]
      rw [hx3]; exact Subgroup.one_mem _
    · intro hmem
      obtain ⟨μ, hμ⟩ := MonoidHom.mem_range.mp hmem
      have hmat : ((x : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = (μ : K) • 1 := by
        rw [← hμ, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
          ← Matrix.smul_one_eq_diagonal]
      have h1 : ((x : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) a b = 0 := by
        rw [hmat]; simp [Matrix.smul_apply, Matrix.one_apply_ne hab]
      have h2 : ((x : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) a b = -1 := by
        show (pairMat a b ((X : SL2 K) : Matrix (Fin 2) (Fin 2) K)) a b = -1
        rw [(pairMat_apply_pair hab _).2.1, coe_X]; simp
      rw [h1] at h2; norm_num at h2
  have h3q : 3 * Nat.card K ≤ 18 := by
    have h := CentHyp.card_le_of_proj hC hx hAx₀ habel₀ hAz₀
    rwa [hcard₀] at h
  rcases eq_or_ne (ringChar K) 2 with h2 | h2
  · exact card_eq_two_or_four_of_bounds h3 h3q (Or.inl h2)
  · have hinj₁ : Function.Injective Φ₁ := by
      intro v w hvw
      have h1 : v * w⁻¹ = 1 := by
        apply hkey₁ h2 (v * w⁻¹)
        have : Φ₁ (v * w⁻¹) = 1 := by rw [map_mul, map_inv, hvw, mul_inv_cancel]
        rw [this]; exact Subgroup.one_mem _
      exact mul_inv_eq_one.mp h1
    have hAx₁ : ∀ a ∈ A₁, a * x = x * a := fun a ha => habel a ha x hxA₁
    have hAz₁ : ∀ a ∈ A₁, (a : GL (Fin 2 ⊕ Fin 2) K) ∈
        StatedScalars (Fin 2 ⊕ Fin 2) K → a = 1 := by
      rintro a ⟨v, rfl⟩ hv
      simp [hkey₁ h2 v hv]
    have hunits : Nat.card ℤˣ = 2 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
    have hcard₁ : Nat.card A₁ = 3 * (Nat.card K * 2) := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hinj₁).toEquiv]
      rw [Nat.card_prod, Nat.card_prod, Nat.card_zpowers, orderOf_X,
        Nat.card_congr Multiplicative.toAdd, hunits]
    have h6q : 6 * Nat.card K ≤ 18 := by
      have h := CentHyp.card_le_of_proj hC hx hAx₁ habel hAz₁
      rw [hcard₁] at h
      omega
    exact card_eq_two_or_four_of_bounds h3 h3q (Or.inr h6q)

end PSP

theorem card_eq_two_or_four_of_psp_four {K : Type} [Field K] [Finite K] (h3 : ringChar K ≠ 3)
    (hC : CentHyp (StatedProj (StatedSp 2 K))) : Nat.card K = 2 ∨ Nat.card K = 4 :=
  psp_aux h3 hC

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3
