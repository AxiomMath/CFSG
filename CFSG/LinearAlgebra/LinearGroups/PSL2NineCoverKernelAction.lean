module

public import CFSG.LocalAnalysis.SectionRank.OddCover.PSL2

public section

namespace CFSG.LinearGroups

open Matrix CFSG.SectionRank.OddCover
open scoped commutatorElement

section NineField

variable {F : Type*} [Field F] [Finite F]

theorem charP_three_of_card_nine (hF : Nat.card F = 9) : CharP F 3 := by
  have := Fintype.ofFinite F
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact charP_of_card_eq_prime_pow (p := 3) (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hF]; norm_num)

theorem exists_sq_eq_neg_one_of_card_nine (hF : Nat.card F = 9) : ∃ ω : F, ω ^ 2 = -1 := by
  have := Fintype.ofFinite F
  obtain ⟨ω, hω⟩ := (FiniteField.isSquare_neg_one_iff (F := F)).mpr
    (by rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  exact ⟨ω, by rw [sq, ← hω]⟩

omit [Finite F] in
theorem intCast_pow_three [CharP F 3] (m : ℤ) : (m : F) ^ 3 = m := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h := map_intCast (frobenius F 3) m
  rwa [frobenius_def] at h

theorem exists_coords_of_card_nine (hF : Nat.card F = 9) [CharP F 3] {ω : F}
    (hω : ω ^ 2 = -1) (x : F) : ∃ m n : ℤ, x = m + n * ω := by
  classical
  have := Fintype.ofFinite F
  obtain ⟨ι, hιdef⟩ : ∃ ι : ZMod 3 →+* F, ι = ZMod.castHom (dvd_refl 3) F := ⟨_, rfl⟩
  have hι : Function.Injective ι := ι.injective
  let φ : ZMod 3 × ZMod 3 → F := fun mn => ι mn.1 + ι mn.2 * ω
  have hinj : Function.Injective φ := by
    rintro ⟨m, n⟩ ⟨m', n'⟩ h
    have h' : ι (n - n') * ω = ι (m' - m) := by
      simp only [φ] at h
      rw [map_sub, map_sub]
      linear_combination h
    by_cases hv : n - n' = 0
    · rw [hv, map_zero, zero_mul, eq_comm, map_eq_zero_iff ι hι, sub_eq_zero] at h'
      exact Prod.ext h'.symm (sub_eq_zero.mp hv)
    · exfalso
      have hv' : ι (n - n') ≠ 0 := (map_ne_zero_iff ι hι).mpr hv
      obtain ⟨w, hw⟩ : ∃ w : ZMod 3, w = (m' - m) / (n - n') := ⟨_, rfl⟩
      have hωι : ω = ι w := by
        rw [hw, map_div₀, eq_div_iff hv', mul_comm]
        exact h'
      have hsq : ι (w * w + 1) = 0 := by
        rw [map_add, map_mul, ← hωι, map_one, ← sq, hω, neg_add_cancel]
      have h0 := (map_eq_zero_iff ι hι).mp hsq
      clear hw hsq hωι
      revert w
      decide
  have hbij : Function.Bijective φ := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [Fintype.card_prod, ZMod.card, ← Nat.card_eq_fintype_card, hF]
  obtain ⟨⟨m, n⟩, hmn⟩ := hbij.2 x
  refine ⟨m.val, n.val, ?_⟩
  rw [← hmn]
  simp only [φ, hιdef, ZMod.castHom_apply, ZMod.cast_eq_val, Int.cast_natCast]

end NineField

section Semilinear

variable {F : Type*} [Field F]

theorem det_map_ringEquiv (σ : F ≃+* F) (M : Matrix (Fin 2) (Fin 2) F) :
    (M.map σ).det = σ M.det :=
  (RingHom.map_det σ.toRingHom M).symm

@[expose] noncomputable def slSemilinearAut (A : GL (Fin 2) F) (σ : F ≃+* F) :
    SpecialLinearGroup (Fin 2) F ≃* SpecialLinearGroup (Fin 2) F where
  toFun X := ⟨(A : Matrix (Fin 2) (Fin 2) F) * (X : Matrix (Fin 2) (Fin 2) F).map σ *
      ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), by
    rw [det_mul, det_mul, det_map_ringEquiv, X.2, map_one, mul_one, ← det_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, det_one]⟩
  invFun X := ⟨(((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (X : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F)).map σ.symm, by
    rw [det_map_ringEquiv, det_mul, det_mul, X.2, mul_one, ← det_mul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, det_one, map_one]⟩
  left_inv X := by
    apply Subtype.ext
    change (((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      ((A : Matrix (Fin 2) (Fin 2) F) * (X : Matrix (Fin 2) (Fin 2) F).map σ *
        ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
      (A : Matrix (Fin 2) (Fin 2) F)).map σ.symm = X
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.mul_one, Matrix.map_map]
    ext i j
    simp
  right_inv X := by
    apply Subtype.ext
    change (A : Matrix (Fin 2) (Fin 2) F) * ((((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (X : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F)).map σ.symm).map σ *
        ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = X
    have hmm : ((((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        (X : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F)).map σ.symm).map σ =
        ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (X : Matrix (Fin 2) (Fin 2) F) *
          (A : Matrix (Fin 2) (Fin 2) F) := by
      rw [Matrix.map_map]
      ext i j
      simp
    rw [hmm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.mul_one]
  map_mul' X Y := by
    apply Subtype.ext
    change (A : Matrix (Fin 2) (Fin 2) F) * ((X : Matrix (Fin 2) (Fin 2) F) *
      (Y : Matrix (Fin 2) (Fin 2) F)).map σ * ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (A : Matrix (Fin 2) (Fin 2) F) * (X : Matrix (Fin 2) (Fin 2) F).map σ *
        ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      ((A : Matrix (Fin 2) (Fin 2) F) * (Y : Matrix (Fin 2) (Fin 2) F).map σ *
        ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
    rw [Matrix.map_mul]
    simp only [Matrix.mul_assoc]
    congr 2
    rw [← Matrix.mul_assoc ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mul]

theorem coe_slSemilinearAut (A : GL (Fin 2) F) (σ : F ≃+* F) (X : SpecialLinearGroup (Fin 2) F) :
    ((slSemilinearAut A σ X : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (A : Matrix (Fin 2) (Fin 2) F) * (X : Matrix (Fin 2) (Fin 2) F).map σ *
        ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) :=
  rfl

@[expose] noncomputable def pslSemilinearAut (A : GL (Fin 2) F) (σ : F ≃+* F) :
    ProjectiveSpecialLinearGroup (Fin 2) F ≃* ProjectiveSpecialLinearGroup (Fin 2) F :=
  QuotientGroup.congr _ _ (slSemilinearAut A σ) (Subgroup.map_center_eq _)

theorem pslSemilinearAut_pslMk (A : GL (Fin 2) F) (σ : F ≃+* F)
    (X : SpecialLinearGroup (Fin 2) F) :
    pslSemilinearAut A σ (pslMk X) = pslMk (slSemilinearAut A σ X) :=
  QuotientGroup.congr_mk _ _ _ _ X

theorem center_specialLinearGroup_two :
    ((Subgroup.center (SpecialLinearGroup (Fin 2) F) : Set (SpecialLinearGroup (Fin 2) F)) =
      {1, -1}) := by
  ext A
  rw [SetLike.mem_coe, Matrix.SpecialLinearGroup.mem_center_iff, Fintype.card_fin,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨r, hr, hA⟩
    have : (r - 1) * (r + 1) = 0 := by linear_combination hr
    rcases mul_eq_zero.mp this with h | h
    · left
      apply Subtype.ext
      rw [← hA, sub_eq_zero.mp h]
      simp
    · right
      apply Subtype.ext
      rw [← hA, Matrix.SpecialLinearGroup.coe_neg, eq_neg_of_add_eq_zero_left h]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij, Matrix.one_apply_ne hij]
  · rintro (rfl | rfl)
    · exact ⟨1, by norm_num, by simp⟩
    · refine ⟨-1, by norm_num, ?_⟩
      rw [Matrix.SpecialLinearGroup.coe_neg]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij, Matrix.one_apply_ne hij]

end Semilinear

section Main

open CFSG.SectionRank CFSG.ShultStronglyClosedTI
open scoped IsMulCommutative

variable {F : Type} [Field F] [Finite F] {J : Type*} [Group J]

open Classical in
theorem perfect_odd_PSL2_nine_cover_semilinear_kernel_action (hF : Nat.card F = 9) [Finite J]
    [Group.IsPerfect J] (π : J →* ProjectiveSpecialLinearGroup (Fin 2) F)
    (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center J)
    (hodd : Odd (Nat.card π.ker)) (A : GL (Fin 2) F) (j : ℕ) (hj : j ≤ 1) (σ : F ≃+* F)
    (hσ : ∀ x, σ x = x ^ 3 ^ j) (α : J ≃* J) (hα : ∀ g, π (α g) = pslSemilinearAut A σ (π g)) :
    ((Subgroup.center (SpecialLinearGroup (Fin 2) F) : Set (SpecialLinearGroup (Fin 2) F)) =
      {1, -1}) ∧
    IsCyclic π.ker ∧ Nat.card π.ker ≤ 3 ∧
    (∀ e ∈ π.ker, α e = e ^ ((if IsSquare (A : Matrix (Fin 2) (Fin 2) F).det then 1 else -1) *
      (-1) ^ j : ℤ)) ∧
    (¬ IsSquare (A : Matrix (Fin 2) (Fin 2) F).det → j = 0 → ∀ e ∈ π.ker, α e = e⁻¹) ∧
    (IsSquare (A : Matrix (Fin 2) (Fin 2) F).det → j = 1 → ∀ e ∈ π.ker, α e = e⁻¹) ∧
    (¬ IsSquare (A : Matrix (Fin 2) (Fin 2) F).det → j = 1 → ∀ e ∈ π.ker, α e = e) := by
  classical
  have hchar : CharP F 3 := charP_three_of_card_nine hF
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hK : Nat.card F = 3 ^ 2 := by rw [hF]; norm_num
  obtain ⟨-, h9⟩ := psl_two_perfect_odd_cover_kernel (p := 3) (f := 2) (by norm_num) hK π hπ hC
    hodd
  obtain ⟨hcyc, hle3⟩ := h9 (by norm_num)
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ,
      ε = if IsSquare (A : Matrix (Fin 2) (Fin 2) F).det then 1 else -1 := ⟨_, rfl⟩
  have hmain : ∀ e ∈ π.ker, α e = e ^ (ε * (-1) ^ j) := by
    intro e he
    by_cases htriv : π.ker = ⊥
    · rw [htriv, Subgroup.mem_bot] at he
      rw [he, map_one, _root_.one_zpow]
    have hcard3 : Nat.card π.ker = 3 := by
      have h1 : Nat.card π.ker ≠ 1 := fun h => htriv (Subgroup.card_eq_one.mp h)
      obtain ⟨k, hk⟩ := hodd
      omega
    obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective hπ 3 (pslUSylow (by norm_num) hK)
    have hmap : (P : Subgroup J).map π = (pslU (K := F)).range := by
      rw [← Sylow.coe_mapSurjective hπ P, hP, coe_pslUSylow]
    have hlift : ∀ t : F, ∃ y ∈ (P : Subgroup J), π y = pslU (Multiplicative.ofAdd t) := by
      intro t
      have hmem : pslU (Multiplicative.ofAdd t) ∈ (P : Subgroup J).map π := hmap ▸ ⟨_, rfl⟩
      exact Subgroup.mem_map.1 hmem
    choose x hxP hx using hlift
    have hcen : ∀ g : J, π g = 1 → g ∈ Subgroup.center J := fun g hg => hC hg
    have hcomm : ∀ s t : F, π ⁅x s, x t⁆ = 1 := by
      intro s t
      rw [map_commutatorElement, hx, hx, commutatorElement_eq_one_iff_mul_comm]
      have h := congrArg pslU (mul_comm (Multiplicative.ofAdd s) (Multiplicative.ofAdd t))
      rwa [map_mul, map_mul] at h
    let b : F → F → Additive (Subgroup.center J) := fun s t =>
      Additive.ofMul ⟨⁅x s, x t⁆, hcen _ (hcomm s t)⟩
    have hb : ∀ s t, ((Additive.toMul (b s t) : Subgroup.center J) : J) = ⁅x s, x t⁆ :=
      fun _ _ => rfl
    have hbext : ∀ u v : Additive (Subgroup.center J),
        ((Additive.toMul u : Subgroup.center J) : J) = (Additive.toMul v : Subgroup.center J) →
          u = v := fun u v h => Additive.toMul.injective (Subtype.ext h)
    have hxadd : ∀ s s' : F, ∃ c ∈ Subgroup.center J, x (s + s') = x s * x s' * c := by
      intro s s'
      refine ⟨(x s * x s')⁻¹ * x (s + s'), hcen _ ?_, by group⟩
      rw [map_mul, map_inv, map_mul, hx, hx, hx, ofAdd_add, map_mul, inv_mul_cancel]
    have hadd₁ : ∀ s s' t, b (s + s') t = b s t + b s' t := by
      intro s s' t
      apply hbext
      rw [toMul_add, Subgroup.coe_mul, hb, hb, hb]
      obtain ⟨c, hc, hc'⟩ := hxadd s s'
      rw [hc', commutatorElement_mul_central_left hc,
        commutatorElement_mul_left_of_mem_center (hcen _ (hcomm s' t))]
    have hadd₂ : ∀ s t t', b s (t + t') = b s t + b s t' := by
      intro s t t'
      apply hbext
      rw [toMul_add, Subgroup.coe_mul, hb, hb, hb]
      obtain ⟨c, hc, hc'⟩ := hxadd t t'
      rw [hc', commutatorElement_mul_central_right hc,
        commutatorElement_mul_right_of_mem_center (hcen _ (hcomm s t'))]
    have halt : ∀ t, b t t = 0 := by
      intro t
      apply hbext
      rw [hb, toMul_zero, Subgroup.coe_one, commutatorElement_self]
    obtain ⟨ω, hω⟩ := exists_sq_eq_neg_one_of_card_nine hF
    have hcoord := exists_coords_of_card_nine hF hω
    have hzl : ∀ (k : ℤ) (s t : F), b (k • s) t = k • b s t := fun k s t =>
      map_zsmul (AddMonoidHom.mk' (fun s => b s t) fun s s' => hadd₁ s s' t) k s
    have hzr : ∀ (k : ℤ) (s t : F), b s (k • t) = k • b s t := fun k s t =>
      map_zsmul (AddMonoidHom.mk' (b s) (hadd₂ s)) k t
    have hω1 : b ω 1 = -b 1 ω := by
      have h := halt (1 + ω)
      rw [hadd₁, hadd₂, hadd₂, halt, halt, zero_add, add_zero] at h
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact h
    have hexpand : ∀ m n m' n' : ℤ, b ((m : F) + n * ω) ((m' : F) + n' * ω) =
        (m * n' - n * m') • b 1 ω := by
      intro m n m' n'
      have e1 : ((m : F) + n * ω) = m • (1 : F) + n • ω := by simp [zsmul_eq_mul]
      have e2 : ((m' : F) + n' * ω) = m' • (1 : F) + n' • ω := by simp [zsmul_eq_mul]
      rw [e1, e2]
      simp only [hadd₁, hadd₂, hzl, hzr, halt, hω1, smul_zero, zero_add, add_zero, smul_neg,
        smul_smul]
      rw [sub_smul, sub_eq_add_neg]
    have hexpand' : ∀ m n m' n' : ℤ, ⁅x ((m : F) + n * ω), x ((m' : F) + n' * ω)⁆ =
        ⁅x 1, x ω⁆ ^ (m * n' - n * m') := by
      intro m n m' n'
      have := congrArg (fun u : Additive (Subgroup.center J) =>
        ((Additive.toMul u : Subgroup.center J) : J)) (hexpand m n m' n')
      simpa [hb, toMul_zsmul] using this
    have hdecomp : ∀ y ∈ (P : Subgroup J), ∃ s, ∃ c ∈ Subgroup.center J, y = x s * c := by
      intro y hy
      obtain ⟨t, ht⟩ : π y ∈ (pslU (K := F)).range := hmap ▸ Subgroup.mem_map_of_mem π hy
      refine ⟨t.toAdd, (x t.toAdd)⁻¹ * y, hcen _ ?_, by group⟩
      rw [map_mul, map_inv, hx, ofAdd_toAdd, ht, inv_mul_cancel]
    have hpg : IsPGroup 3 π.ker := IsPGroup.of_card (n := 1) (by rw [hcard3, pow_one])
    have hEP := central_pSubgroup_le_sylow_derived P π.ker hC hpg
    have hPP : (commutator (P : Subgroup J)).map (P : Subgroup J).subtype ≤
        Subgroup.zpowers ⁅x 1, x ω⁆ := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype, Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      obtain ⟨s, c, hc, rfl⟩ := hdecomp g₁ hg₁
      obtain ⟨t, d, hd, rfl⟩ := hdecomp g₂ hg₂
      rw [commutatorElement_mul_central_left hc, commutatorElement_mul_central_right hd]
      obtain ⟨m, n, rfl⟩ := hcoord s
      obtain ⟨m', n', rfl⟩ := hcoord t
      rw [hexpand']
      exact Subgroup.zpow_mem_zpowers _ _
    have hEz : π.ker ≤ Subgroup.zpowers ⁅x 1, x ω⁆ := hEP.trans hPP
    obtain ⟨a, ha⟩ : ∃ a : F, a = (A : Matrix (Fin 2) (Fin 2) F).det := ⟨_, rfl⟩
    have ha0 : a ≠ 0 := by
      intro h
      have h1 := congrArg Matrix.det (show (A : Matrix (Fin 2) (Fin 2) F) *
          ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
      rw [Matrix.det_mul, ← ha, h, zero_mul, Matrix.det_one] at h1
      exact zero_ne_one h1
    obtain ⟨D', hD'⟩ : ∃ D' : Matrix (Fin 2) (Fin 2) F, D' = Matrix.diagonal ![a⁻¹, 1] :=
      ⟨_, rfl⟩
    have hD'det : D'.det = a⁻¹ := by
      rw [hD', Matrix.det_diagonal, Fin.prod_univ_two]
      simp
    let Bsl : SpecialLinearGroup (Fin 2) F := ⟨(A : Matrix (Fin 2) (Fin 2) F) * D', by
      rw [Matrix.det_mul, ← ha, hD'det, mul_inv_cancel₀ ha0]⟩
    have hBsl : ∀ t : F, slSemilinearAut A σ (slU t) * Bsl = Bsl * slU (a * σ t) := by
      intro t
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        coe_slSemilinearAut]
      change (A : Matrix (Fin 2) (Fin 2) F) * (slU t : Matrix (Fin 2) (Fin 2) F).map σ *
          ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          ((A : Matrix (Fin 2) (Fin 2) F) * D') =
        (A : Matrix (Fin 2) (Fin 2) F) * D' * (slU (a * σ t) : Matrix (Fin 2) (Fin 2) F)
      rw [Matrix.mul_assoc, Matrix.mul_assoc,
        ← Matrix.mul_assoc ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), ← Units.val_mul,
        inv_mul_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_assoc]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hD', coe_slU, Matrix.mul_apply, Fin.sum_univ_two, ha0]
    obtain ⟨y, hy⟩ := hπ (pslMk Bsl)
    have hconj : ∀ t : F, ∃ c ∈ Subgroup.center J, y⁻¹ * α (x t) * y = x (a * σ t) * c := by
      intro t
      refine ⟨(x (a * σ t))⁻¹ * (y⁻¹ * α (x t) * y), hcen _ ?_, by group⟩
      simp only [map_mul, map_inv]
      rw [hy, hα, hx, hx, pslU_apply, pslU_apply, toAdd_ofAdd, toAdd_ofAdd,
        pslSemilinearAut_pslMk]
      have h1 := congrArg pslMk (hBsl t)
      rw [map_mul, map_mul] at h1
      rw [mul_assoc ((pslMk Bsl)⁻¹), h1]
      group
    have hαb : α ⁅x 1, x ω⁆ = ⁅x a, x (a * σ ω)⁆ := by
      have hcentral : α ⁅x 1, x ω⁆ ∈ Subgroup.center J :=
        hcen _ (by rw [hα, hcomm, map_one])
      obtain ⟨c, hc, hc'⟩ := hconj 1
      obtain ⟨d, hd, hd'⟩ := hconj ω
      calc α ⁅x 1, x ω⁆ = y⁻¹ * α ⁅x 1, x ω⁆ * y := by
            rw [mul_assoc, ← Subgroup.mem_center_iff.mp hcentral y, inv_mul_cancel_left]
        _ = ⁅y⁻¹ * α (x 1) * y, y⁻¹ * α (x ω) * y⁆ := by
            rw [map_commutatorElement]
            simp only [commutatorElement_def]
            group
        _ = ⁅x (a * σ 1) * c, x (a * σ ω) * d⁆ := by rw [hc', hd']
        _ = ⁅x a, x (a * σ ω)⁆ := by
            rw [commutatorElement_mul_central_left hc, commutatorElement_mul_central_right hd,
              map_one, mul_one]
    have hσω : σ ω = (-1 : F) ^ j * ω := by
      rw [hσ]
      interval_cases j
      · simp
      · have h3 : ω ^ 3 = ω ^ 2 * ω := by ring
        rw [pow_one, h3, hω]
        ring
    obtain ⟨a₁, a₂, ha12⟩ := hcoord a
    have hTω : a * σ ω = ((-(-1) ^ j * a₂ : ℤ) : F) + (((-1) ^ j * a₁ : ℤ) : F) * ω := by
      rw [hσω, ha12]
      push_cast
      linear_combination ((-1 : F) ^ j * a₂) * hω
    have hαb' : α ⁅x 1, x ω⁆ = ⁅x 1, x ω⁆ ^ ((-1) ^ j * (a₁ ^ 2 + a₂ ^ 2)) := by
      rw [hαb, hTω, ha12, hexpand']
      congr 1
      ring
    have ha4 : a ^ 4 = ((a₁ ^ 2 + a₂ ^ 2 : ℤ) : F) := by
      have h3 : a ^ 3 = (a₁ : F) - (a₂ : F) * ω := by
        rw [ha12, add_pow_char, mul_pow, intCast_pow_three, intCast_pow_three]
        have hω3 : ω ^ 3 = -ω := by
          rw [show ω ^ 3 = ω ^ 2 * ω by ring, hω, neg_one_mul]
        rw [hω3]
        ring
      calc a ^ 4 = a * a ^ 3 := by ring
        _ = _ := by
          rw [h3, ha12]
          push_cast
          linear_combination (-(a₂ : F) ^ 2) * hω
    have hε4 : (ε : F) = a ^ 4 := by
      have := Fintype.ofFinite F
      have hring : ringChar F ≠ 2 := by
        rw [ringChar.eq F 3]
        norm_num
      have hsq := FiniteField.isSquare_iff hring ha0
      rw [show Fintype.card F / 2 = 4 by rw [← Nat.card_eq_fintype_card, hF]] at hsq
      rw [hε]
      split_ifs with h
      · have h' : IsSquare a := by rw [ha]; exact h
        rw [hsq.mp h']
        simp
      · have h8 : a ^ 8 = 1 := by
          have h8' := FiniteField.pow_card_sub_one_eq_one a ha0
          rwa [← Nat.card_eq_fintype_card, hF] at h8'
        have h4 : a ^ 4 ≠ 1 := fun h' => h (by rw [← ha]; exact hsq.mpr h')
        have hprod : (a ^ 4 - 1) * (a ^ 4 + 1) = 0 := by linear_combination h8
        rcases mul_eq_zero.mp hprod with h0 | h0
        · exact absurd (sub_eq_zero.mp h0) h4
        · rw [eq_neg_of_add_eq_zero_left h0]
          simp
    have hmod : (-1) ^ j * (a₁ ^ 2 + a₂ ^ 2) ≡ ε * (-1) ^ j [ZMOD 3] := by
      have h1 : ((a₁ ^ 2 + a₂ ^ 2 : ℤ) : F) = (ε : F) := by rw [← ha4, hε4]
      have h2 := (CharP.intCast_eq_intCast F 3).mp h1
      rw [mul_comm ε]
      exact Int.ModEq.mul_left _ h2
    have hord : orderOf ⁅x 1, x ω⁆ ∣ 3 := by
      have hmem : ⁅x 1, x ω⁆ ∈ π.ker := hcomm 1 ω
      have h1 := pow_card_eq_one' (G := π.ker) (x := ⟨_, hmem⟩)
      rw [hcard3] at h1
      exact orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val h1)
    have hαb'' : α ⁅x 1, x ω⁆ = ⁅x 1, x ω⁆ ^ (ε * (-1) ^ j) := by
      rw [hαb', zpow_eq_zpow_iff_modEq]
      exact hmod.of_dvd (by exact_mod_cast hord)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hEz he)
    rw [map_zpow, hαb'', ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]
  refine ⟨center_specialLinearGroup_two, hcyc, hle3, fun e he => ?_, fun h1 h2 e he => ?_,
    fun h1 h2 e he => ?_, fun h1 h2 e he => ?_⟩
  · rw [hmain e he, hε]
  · rw [hmain e he, hε, ite_eq_right h1, h2]
    simp
  · rw [hmain e he, hε, ite_eq_left h1, h2]
    simp
  · rw [hmain e he, hε, ite_eq_right h1, h2]
    simp

end Main

end CFSG.LinearGroups
