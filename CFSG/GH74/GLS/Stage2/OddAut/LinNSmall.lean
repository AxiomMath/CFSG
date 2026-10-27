module

public import CFSG.GH74.GLS.Stage2.OddAut.LinNAut

public section

namespace CFSG.GH74.GLS.Stage2.OddAut

open Polynomial Lagrange Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Small

variable {K : Type*} [Field K] {n r : ℕ} {ω : K}

@[expose] def eigSpN (x : Matrix (Fin n) (Fin n) K) (ζ : K) : Submodule K (Fin n → K) :=
  LinearMap.ker (Matrix.mulVecLin (x - ζ • (1 : Matrix (Fin n) (Fin n) K)))

theorem mem_eigSpN {x : Matrix (Fin n) (Fin n) K} {ζ : K} {v : Fin n → K} :
    v ∈ eigSpN x ζ ↔ x *ᵥ v = ζ • v := by
  simp only [eigSpN, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]

theorem mulVec_mem_eigSpN {x y : Matrix (Fin n) (Fin n) K} (hxy : x * y = y * x) {ζ : K}
    {v : Fin n → K} (hv : v ∈ eigSpN x ζ) : y *ᵥ v ∈ eigSpN x ζ := by
  rw [mem_eigSpN, Matrix.mulVec_mulVec, hxy, ← Matrix.mulVec_mulVec, mem_eigSpN.mp hv,
    Matrix.mulVec_smul]

theorem exists_small_eigenspace (hn0 : 0 < n) (hr : 0 < r) (hω : IsPrimitiveRoot ω r)
    (x : Matrix (Fin n) (Fin n) K) (hx : x ^ r = 1)
    (hns : ∀ c : K, x ≠ c • (1 : Matrix (Fin n) (Fin n) K)) :
    ∃ ζ : K, eigSpN x ζ ≠ ⊥ ∧ 2 * Module.finrank K (eigSpN x ζ) ≤ n := by
  classical
  set s : Finset K := nthRootsFinset r (1 : K) with hs
  have hsne : s.Nonempty := ⟨1, by rw [hs, mem_nthRootsFinset hr]; exact one_pow r⟩
  have hxa := aeval_nodal_of_pow_eq_one hr hω hx
  have hmem : ∀ ζ ∈ s, ∀ w, eigProj s x ζ *ᵥ w ∈ eigSpN x ζ := by
    intro ζ hζ w
    rw [mem_eigSpN, Matrix.mulVec_mulVec, eigProj_eigen hxa hζ, Matrix.smul_mulVec]
  have hsum : ∀ w : Fin n → K, w = ∑ ζ ∈ s, eigProj s x ζ *ᵥ w := by
    intro w
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) K => M *ᵥ w) (sum_eigProj hsne x)
    simp only [Matrix.one_mulVec, Matrix.sum_mulVec] at h
    exact h.symm
  have hpair : ∃ ζ₁ ∈ s, ∃ ζ₂ ∈ s, ζ₁ ≠ ζ₂ ∧ eigSpN x ζ₁ ≠ ⊥ ∧ eigSpN x ζ₂ ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    by_cases hex : ∃ ζ₀ ∈ s, eigSpN x ζ₀ ≠ ⊥
    · obtain ⟨ζ₀, hζ₀, hne⟩ := hex
      have hall : ∀ w, w ∈ eigSpN x ζ₀ := by
        intro w
        rw [hsum w]
        refine Submodule.sum_mem _ fun ζ hζ => ?_
        by_cases hζe : ζ = ζ₀
        · rw [hζe]
          exact hmem ζ₀ hζ₀ w
        · have hb := hcon ζ₀ hζ₀ ζ hζ (Ne.symm hζe) hne
          have h2 := hmem ζ hζ w
          rw [hb, Submodule.mem_bot] at h2
          rw [h2]
          exact Submodule.zero_mem _
      apply hns ζ₀
      ext i j
      have h := mem_eigSpN.mp (hall (Pi.single j 1))
      have h2 := congrFun h i
      simpa [Matrix.mulVec_single_one, Matrix.smul_apply, Matrix.one_apply, Pi.single_apply,
        eq_comm] using h2
    · push Not at hex
      have h0 : ∀ w : Fin n → K, w = 0 := by
        intro w
        rw [hsum w]
        refine Finset.sum_eq_zero fun ζ hζ => ?_
        have h2 := hmem ζ hζ w
        rw [hex ζ hζ, Submodule.mem_bot] at h2
        exact h2
      have := congrFun (h0 (Pi.single ⟨0, hn0⟩ 1)) ⟨0, hn0⟩
      simp at this
  obtain ⟨ζ₁, hζ₁, ζ₂, hζ₂, hne, hb₁, hb₂⟩ := hpair
  have hdisj : Disjoint (eigSpN x ζ₁) (eigSpN x ζ₂) := by
    rw [Submodule.disjoint_def]
    intro v h1 h2
    have e1 := mem_eigSpN.mp h1
    have e2 := mem_eigSpN.mp h2
    have : (ζ₁ - ζ₂) • v = 0 := by rw [sub_smul, ← e1, ← e2, sub_self]
    rcases smul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · exact h
  have hle := Submodule.finrank_add_finrank_le_of_disjoint hdisj
  rw [Module.finrank_fin_fun] at hle
  by_cases h : Module.finrank K (eigSpN x ζ₁) ≤ Module.finrank K (eigSpN x ζ₂)
  · exact ⟨ζ₁, hb₁, by omega⟩
  · exact ⟨ζ₂, hb₂, by omega⟩

theorem exists_pow_eq_of_stable (hr : r.Prime) (a : Matrix (Fin n) (Fin n) K) (α : K)
    (ha : a ^ r = α • (1 : Matrix (Fin n) (Fin n) K)) (E : Submodule K (Fin n → K))
    (hE : ∀ v ∈ E, a *ᵥ v ∈ E) (hne : E ≠ ⊥) (hdim : Module.finrank K E < r) :
    ∃ c : K, c ^ r = α := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨v, hvE, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hirr : Irreducible (X ^ r - C α : K[X]) := X_pow_sub_C_irreducible_of_prime hr hcon
  let w : Fin r → (Fin n → K) := fun i => (a ^ (i : ℕ)) *ᵥ v
  have hwE : ∀ m : ℕ, (a ^ m) *ᵥ v ∈ E := by
    intro m
    induction m with
    | zero => simpa using hvE
    | succ m ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      exact hE _ ih
  have hli : LinearIndependent K w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    by_contra hci
    set g : K[X] := ∑ j : Fin r, C (c j) * X ^ (j : ℕ) with hg
    have hgv : (aeval a g) *ᵥ v = 0 := by
      have h1 : aeval a g = ∑ j : Fin r, c j • a ^ (j : ℕ) := by
        rw [hg, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, aeval_C, aeval_X_pow, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      rw [h1, Matrix.sum_mulVec]
      simpa [Matrix.smul_mulVec, w] using hc
    have hgcoeff : g.coeff (i : ℕ) = c i := by
      simp only [hg, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        have : (i : ℕ) ≠ j := fun h => hji (Fin.ext h.symm)
        simp [this]
      · simp
    have hgne : g ≠ 0 := by
      intro h0
      rw [h0, coeff_zero] at hgcoeff
      exact hci hgcoeff.symm
    have hgdeg : g.natDegree < r := by
      have := degree_sum_fin_lt c
      rw [hg]
      exact natDegree_lt_iff_degree_lt hgne |>.mpr (by simpa [hg] using this)
    have hpdeg : (X ^ r - C α : K[X]).natDegree = r := natDegree_X_pow_sub_C
    have hcop : IsCoprime (X ^ r - C α : K[X]) g := by
      rw [hirr.coprime_iff_not_dvd]
      intro hdvd
      have := natDegree_le_of_dvd hdvd hgne
      omega
    obtain ⟨u, u', hbez⟩ := hcop
    have h2 := congrArg (fun q : K[X] => (aeval a q) *ᵥ v) hbez
    simp only [map_add, map_mul, map_sub, aeval_X_pow, aeval_C, map_one, Matrix.add_mulVec,
      Matrix.one_mulVec] at h2
    have h3 : (a ^ r - algebraMap K (Matrix (Fin n) (Fin n) K) α) = 0 := by
      rw [ha, Algebra.algebraMap_eq_smul_one, sub_self]
    rw [h3, mul_zero, Matrix.zero_mulVec, zero_add, ← Matrix.mulVec_mulVec, hgv, Matrix.mulVec_zero] at h2
    exact hv0 h2.symm
  let w' : Fin r → E := fun i => ⟨w i, hwE i⟩
  have hli' : LinearIndependent K w' := LinearIndependent.of_comp E.subtype hli
  have := hli'.fintype_card_le_finrank
  rw [Fintype.card_fin] at this
  omega

end Small

section Split

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem lin_comm_diag_n {r : ℕ} (hr : r.Prime) (hn0 : 0 < n) (hrn : n < 2 * r)
    (hrK : r ∣ Nat.card K - 1)
    (a b : Matrix (Fin n) (Fin n) K) (α β : K) (hα0 : α ≠ 0) (hβ0 : β ≠ 0)
    (ha : a ^ r = α • (1 : Matrix (Fin n) (Fin n) K)) (hb : b ^ r = β • (1 : Matrix (Fin n) (Fin n) K))
    (hab : a * b = b * a)
    (hind : ∀ (i j : ℕ) (c : K), c ≠ 0 → a ^ i * b ^ j = c • (1 : Matrix (Fin n) (Fin n) K) →
      r ∣ i ∧ r ∣ j) :
    ∃ (B : Matrix (Fin n) (Fin n) K) (da db : Fin n → K), IsUnit B.det ∧
      a * B = B * Matrix.diagonal da ∧ b * B = B * Matrix.diagonal db := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have hr0 : 0 < r := hr.pos
  obtain ⟨ω₀, hω₀⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r (by rwa [Nat.card_units])
  have hω : IsPrimitiveRoot (ω₀ : K) r := by
    have h1 := IsPrimitiveRoot.orderOf ω₀
    rw [hω₀] at h1
    exact IsPrimitiveRoot.coe_units_iff.mpr h1
  obtain ⟨i, j, γ, hi, hj, hij, hγ⟩ := exists_exponents_pow hr (Units.mk0 α hα0) (Units.mk0 β hβ0)
  have hγ' : α ^ i * β ^ j = (γ : K) ^ r := by
    have := congrArg (fun u : Kˣ => (u : K)) hγ
    simpa using this
  have hcab : Commute a b := hab
  set x : Matrix (Fin n) (Fin n) K := a ^ i * b ^ j with hx
  have hxr : x ^ r = ((γ : K) ^ r) • (1 : Matrix (Fin n) (Fin n) K) := by
    have e1 : x ^ r = (a ^ r) ^ i * (b ^ r) ^ j := by
      rw [hx, (hcab.pow_pow i j).mul_pow, ← pow_mul, ← pow_mul, mul_comm i r, mul_comm j r,
        pow_mul, pow_mul]
    rw [e1, ha, hb, _root_.smul_pow, _root_.smul_pow, one_pow, one_pow, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.one_mul, hγ']
  have hγne : (γ : K) ≠ 0 := γ.ne_zero
  set x₀ : Matrix (Fin n) (Fin n) K := ((γ : K)⁻¹) • x with hx₀
  have hx₀r : x₀ ^ r = 1 := by
    rw [hx₀, _root_.smul_pow, hxr, smul_smul, inv_pow, inv_mul_cancel₀ (pow_ne_zero r hγne), one_smul]
  have hxx₀ : x = (γ : K) • x₀ := by
    rw [hx₀, smul_smul, mul_inv_cancel₀ hγne, one_smul]
  have hns : ∀ c : K, x₀ ≠ c • (1 : Matrix (Fin n) (Fin n) K) := by
    intro c hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      rw [hc, zero_pow hr0.ne'] at hx₀r
      have := congrFun (congrFun hx₀r ⟨0, hn0⟩) ⟨0, hn0⟩
      simp at this
    have hxc : a ^ i * b ^ j = ((γ : K) * c) • (1 : Matrix (Fin n) (Fin n) K) := by
      have : x = (γ : K) • x₀ := hxx₀
      rw [hx] at this
      rw [this, hc, smul_smul]
    obtain ⟨h1, h2⟩ := hind i j _ (mul_ne_zero hγne hc0) hxc
    have hi0 : i = 0 := Nat.eq_zero_of_dvd_of_lt h1 hi
    have hj0 : j = 0 := Nat.eq_zero_of_dvd_of_lt h2 hj
    rcases hij with h | h
    · exact h hi0
    · exact h hj0
  have hca : Commute a x₀ :=
    (((Commute.refl a).pow_right i).mul_right (hcab.pow_right j)).smul_right _
  have hcb : Commute b x₀ :=
    (((hcab.symm).pow_right i).mul_right ((Commute.refl b).pow_right j)).smul_right _
  obtain ⟨ζ, hne, hdim⟩ := exists_small_eigenspace hn0 hr0 hω x₀ hx₀r hns
  have hdim' : Module.finrank K (eigSpN x₀ ζ) < r := by omega
  obtain ⟨c, hc⟩ := exists_pow_eq_of_stable hr a α ha (eigSpN x₀ ζ)
    (fun v hv => mulVec_mem_eigSpN hca.symm.eq hv) hne hdim'
  obtain ⟨d, hd⟩ := exists_pow_eq_of_stable hr b β hb (eigSpN x₀ ζ)
    (fun v hv => mulVec_mem_eigSpN hcb.symm.eq hv) hne hdim'
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hr0.ne'] at hc
    exact hα0 hc.symm
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [zero_pow hr0.ne'] at hd
    exact hβ0 hd.symm
  have ha₀ : (c⁻¹ • a) ^ r = 1 := by
    rw [_root_.smul_pow, ha, smul_smul, ← hc, inv_pow, inv_mul_cancel₀ (pow_ne_zero r hc0), one_smul]
  have hb₀ : (d⁻¹ • b) ^ r = 1 := by
    rw [_root_.smul_pow, hb, smul_smul, ← hd, inv_pow, inv_mul_cancel₀ (pow_ne_zero r hd0), one_smul]
  have hab₀ : (c⁻¹ • a) * (d⁻¹ • b) = (d⁻¹ • b) * (c⁻¹ • a) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, hab, smul_comm]
  obtain ⟨B, da, db, hB, hBa, hBb⟩ := exists_joint_eigenbasis_n hr0 hω _ _ ha₀ hb₀ hab₀
  refine ⟨B, fun m => c * da m, fun m => d * db m, hB, ?_, ?_⟩
  · have e1 : a = c • (c⁻¹ • a) := by rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
    rw [e1, Matrix.smul_mul, hBa]
    ext m l
    simp only [Matrix.smul_apply, Matrix.mul_diagonal, smul_eq_mul]
    ring
  · have e1 : b = d • (d⁻¹ • b) := by rw [smul_smul, mul_inv_cancel₀ hd0, one_smul]
    rw [e1, Matrix.smul_mul, hBb]
    ext m l
    simp only [Matrix.smul_apply, Matrix.mul_diagonal, smul_eq_mul]
    ring

omit [Finite K] in
theorem toral_of_joint_diag {V : Subgroup (MulAut (projectiveSL n K))} {a b : GL (Fin n) K}
    (hspan : ∀ v ∈ V, ∃ i j : ℕ, v = conjAut n K (a ^ i * b ^ j))
    {B₀ : Matrix (Fin n) (Fin n) K} (hB : IsUnit B₀.det) {da db : Fin n → K}
    (h1 : (a : Matrix (Fin n) (Fin n) K) * B₀ = B₀ * Matrix.diagonal da)
    (h2 : (b : Matrix (Fin n) (Fin n) K) * B₀ = B₀ * Matrix.diagonal db) :
    ∃ B : GL (Fin n) K, ∀ v ∈ V, ∃ (x : GL (Fin n) K) (d : Fin n → K), v = conjAut n K x ∧
      (x : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
        (B : Matrix (Fin n) (Fin n) K) * Matrix.diagonal d := by
  refine ⟨Matrix.nonsingInvUnit B₀ hB, fun v hv => ?_⟩
  obtain ⟨i, j, hij⟩ := hspan v hv
  refine ⟨a ^ i * b ^ j, da ^ i * db ^ j, hij, ?_⟩
  have hBg : ((Matrix.nonsingInvUnit B₀ hB : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = B₀ := rfl
  rw [hBg, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
    Matrix.mul_assoc, mul_pow_diag_n h2 j, ← Matrix.mul_assoc, mul_pow_diag_n h1 i,
    Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
  rfl

theorem inner_plane_classify_n (hn : 3 ≤ n) {r : ℕ} (hr : r.Prime) (hrn : n < 2 * r)
    (hrK : r ∣ Nat.card K - 1) (V : Subgroup (MulAut (projectiveSL n K)))
    (hVI : V ≤ (conjAut n K).range) (hVc : Nat.card V = r ^ 2) (hVe : ∀ v ∈ V, v ^ r = 1)
    (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) :
    (∃ B : GL (Fin n) K, ∀ v ∈ V, ∃ (x : GL (Fin n) K) (d : Fin n → K), v = conjAut n K x ∧
        (x : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
          (B : Matrix (Fin n) (Fin n) K) * Matrix.diagonal d) ∨
      (∃ (a b : GL (Fin n) K) (u : Kˣ), u ≠ 1 ∧ conjAut n K a ∈ V ∧ conjAut n K b ∈ V ∧
        a * b = GeneralLinearGroup.scalar (Fin n) u * (b * a)) := by
  classical
  have hn0 : 0 < n := by omega
  obtain ⟨a, b, ua, ub, u, ha, hb, hau, hbu, hab, hind, hspan⟩ :=
    exists_lifts_n hn hr V hVI hVc hVe hVab
  by_cases hu : u = 1
  · left
    rw [hu, map_one, one_mul] at hab
    have haM : (a : Matrix (Fin n) (Fin n) K) ^ r = (ua : K) • (1 : Matrix (Fin n) (Fin n) K) := by
      rw [← Units.val_pow_eq_pow_val, hau, coe_scalar_smul_n]
    have hbM : (b : Matrix (Fin n) (Fin n) K) ^ r = (ub : K) • (1 : Matrix (Fin n) (Fin n) K) := by
      rw [← Units.val_pow_eq_pow_val, hbu, coe_scalar_smul_n]
    have habM : (a : Matrix (Fin n) (Fin n) K) * (b : Matrix (Fin n) (Fin n) K) =
        (b : Matrix (Fin n) (Fin n) K) * (a : Matrix (Fin n) (Fin n) K) := by
      rw [← Units.val_mul, ← Units.val_mul, hab]
    have hindM : ∀ (i j : ℕ) (c : K), c ≠ 0 →
        (a : Matrix (Fin n) (Fin n) K) ^ i * (b : Matrix (Fin n) (Fin n) K) ^ j =
          c • (1 : Matrix (Fin n) (Fin n) K) → r ∣ i ∧ r ∣ j := by
      intro i j c hc h
      apply hind i j
      refine ⟨Units.mk0 c hc, Units.ext ?_⟩
      rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, h, coe_scalar_smul_n]
      rfl
    obtain ⟨B₀, da, db, hB, h1, h2⟩ := lin_comm_diag_n hr hn0 hrn hrK _ _ (ua : K) (ub : K)
      ua.ne_zero ub.ne_zero haM hbM habM hindM
    exact toral_of_joint_diag hspan hB h1 h2
  · exact Or.inr ⟨a, b, u, hu, ha, hb, hab⟩

end Split

end CFSG.GH74.GLS.Stage2.OddAut
