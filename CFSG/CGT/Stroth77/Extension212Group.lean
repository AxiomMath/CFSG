module

public import CFSG.CGT.Stroth77.Extension212Lift

public section

namespace CFSG.CGT.Stroth77

variable {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S} {τ : StrothTypeIndex}

theorem k_zero_eq_m_lift (τ : StrothTypeIndex) : τ.k 0 = τ.m := by
  have h := congrFun τ.k_eq 0
  simpa using h

theorem k_one_eq_n_lift (τ : StrothTypeIndex) : τ.k 1 = τ.n := by
  have h := congrFun τ.k_eq 1
  simpa using h

theorem orderOf_c_lift (D : StrothTypeData B τ) : orderOf D.c = 2 ^ τ.k 0 := by
  rw [D.orderOf_c, k_zero_eq_m_lift]

theorem orderOf_a_lift (D : StrothTypeData B τ) : orderOf D.a = 2 ^ τ.k 1 := by
  rw [D.orderOf_a, k_one_eq_n_lift]

theorem orderOf_b_lift (D : StrothTypeData B τ) : orderOf D.b = 2 ^ τ.k 2 := by
  rw [D.orderOf_b, τ.k_two]

theorem mul_comm_of_data (D : StrothTypeData B τ) (x y : B) : x * y = y * x :=
  D.ec_injective (by rw [D.ec_mul, D.ec_mul, add_comm])

section Fixed

variable (D : StrothTypeData B τ)

theorem ec_conj_uv_data (y : B) : D.ec (conjBy D.uv_mem y) = τ.action.φuv (D.ec y) :=
  D.uv_conj y

theorem ec_conj_t_data (y : B) : D.ec (conjBy D.t_mem y) = τ.action.φt (D.ec y) :=
  D.t_conj y

theorem ec_conj_u_data (y : B) : D.ec (conjBy D.u_mem y) = τ.action.φu (D.ec y) :=
  D.u_conj y

theorem ec_conj_ρ_data (y : B) : D.ec (conjBy D.ρ_mem y) = τ.action.φρ (D.ec y) :=
  D.ρ_conj y

theorem exists_mul_self_eq_of_two_nsmul (y : B) {z : Torus τ.k} (hz : 2 • z = D.ec y) :
    ∃ σ : B, σ * σ = y :=
  ⟨Additive.toMul (D.e.symm z), by
    apply D.ec_injective
    rw [D.ec_mul, ← two_nsmul, show D.ec (Additive.toMul (D.e.symm z)) = z from
      D.e.apply_symm_apply z, hz]⟩

theorem ec_conj_mul_inv {g : S} (hg : g ∈ Subgroup.normalizer B) {φ : Torus τ.k →+ Torus τ.k}
    (hφ : ∀ y : B, D.ec (conjBy hg y) = φ (D.ec y)) (y : B) :
    D.ec (conjBy hg y * y⁻¹) = φ (D.ec y) - D.ec y := by
  rw [D.ec_mul, D.ec_inv, hφ, sub_eq_add_neg]

end Fixed

section IndexTwo

theorem conj_sq_mul_inv_eq_sq (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hd2B : d * d ∈ B) {g : S} (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) :
    ∃ β : B, conjBy hgB (⟨d * d, hd2B⟩ : B) * (⟨d * d, hd2B⟩ : B)⁻¹ = β * β := by
  obtain ⟨β, hβ⟩ := exists_conj_eq hBC hrel hdC hdB g hgC hgB
  have hcommB : ∀ b : B, (b : S) * d = d * (b : S) := fun b =>
    Subgroup.mem_centralizer_iff.mp (hC hdC) (b : S) b.2
  have hβS : g⁻¹ * d * g = d * (β : S) := by
    simpa [conjBy_val] using congrArg Subtype.val hβ
  refine ⟨β, Subtype.ext ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjBy_val]
  have h1 : g⁻¹ * (d * d) * g = (g⁻¹ * d * g) * (g⁻¹ * d * g) := by group
  rw [h1, hβS]
  have h3 : (β : S) * β * d = d * ((β : S) * β) := by
    rw [mul_assoc, hcommB β, ← mul_assoc, hcommB β, mul_assoc]
  calc d * (β : S) * (d * (β : S)) * (d * d)⁻¹
      = d * ((β : S) * d) * (β : S) * (d * d)⁻¹ := by group
    _ = d * (d * (β : S)) * (β : S) * (d * d)⁻¹ := by rw [hcommB β]
    _ = d * (d * ((β : S) * β)) * (d * d)⁻¹ := by group
    _ = d * ((β : S) * β * d) * (d * d)⁻¹ := by rw [h3]
    _ = d * ((β : S) * β) * d * (d * d)⁻¹ := by group
    _ = (β : S) * β * d * d * (d * d)⁻¹ := by rw [← h3]
    _ = (β : S) * β := by group

theorem false_of_mul_self_eq (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') {x : S} (hxC : x ∈ C) (hxB : x ∉ B)
    {σ : B} (hσ : (σ : S) * σ = x * x) : False := by
  have hcomm : (σ : S)⁻¹ * x = x * (σ : S)⁻¹ := by
    exact Subgroup.mem_centralizer_iff.mp (hC hxC) ((σ : S)⁻¹) (B.inv_mem σ.2)
  let w : S := x * (σ : S)⁻¹
  have hwC : w ∈ C := C.mul_mem hxC (C.inv_mem (hBC σ.2))
  have hww : w * w = 1 := by
    calc w * w = x * ((σ : S)⁻¹ * x) * (σ : S)⁻¹ := by simp only [w]; group
      _ = x * (x * (σ : S)⁻¹) * (σ : S)⁻¹ := by rw [hcomm]
      _ = (x * x) * ((σ : S) * σ)⁻¹ := by group
      _ = 1 := by rw [hσ, mul_inv_cancel]
  have hwB : w ∈ B := hH w (hcS hwC) hww (hC hwC)
  apply hxB
  have hx : x = w * (σ : S) := by simp only [w]; group
  rw [hx]
  exact B.mul_mem hwB σ.2

theorem exists_mem_not_mem_of_index_two (hrel : Nat.card C = 2 * Nat.card B) :
    ∃ d, d ∈ C ∧ d ∉ B := by
  by_contra hcon
  push Not at hcon
  have hle := Subgroup.card_le_of_le (fun x hx => hcon x hx : C ≤ B)
  have hpos : 0 < Nat.card B := Nat.card_pos
  omega

variable (D : StrothTypeData B τ)

theorem exists_sq_eq_c_of_data (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S')
    (hsec : ∀ v : Torus τ.k, (∃ z, 2 • z = τ.action.φuv v - v) →
      (∃ z, 2 • z = τ.action.φt v - v) → (∃ z, 2 • z = τ.action.φu v - v) →
      (∃ z, 2 • z = τ.action.φρ v - v) → (∃ z, 2 • z = v) ∨ (∃ z, 2 • z = v - gen τ.k 0)) :
    ∃ d : S, d ∈ C ∧ d ∉ B ∧ d * d = (D.c : S) := by
  obtain ⟨d, hdC, hdB⟩ := exists_mem_not_mem_of_index_two hrel
  have hindex : (B.subgroupOf C).index = 2 := index_two_of_relIndex hBC hrel
  have hd2B : d * d ∈ B := sq_mem_of_index_two (x := ⟨d, hdC⟩) hindex
  let sB : B := ⟨d * d, hd2B⟩
  have hfix {g : S} (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B)
      {φ : Torus τ.k →+ Torus τ.k} (hφ : ∀ y : B, D.ec (conjBy hgB y) = φ (D.ec y)) :
      ∃ z, 2 • z = φ (D.ec sB) - D.ec sB := by
    obtain ⟨β, hβ⟩ := conj_sq_mul_inv_eq_sq hBC hC hrel hdC hdB hd2B hgC hgB
    refine ⟨D.ec β, ?_⟩
    rw [← ec_conj_mul_inv D hgB hφ, hβ, D.ec_mul, two_nsmul]
  rcases hsec (D.ec sB) (hfix (hL D.uv_mem_L) D.uv_mem (ec_conj_uv_data D))
      (hfix (hL D.t_mem_L) D.t_mem (ec_conj_t_data D))
      (hfix (hL D.u_mem_L) D.u_mem (ec_conj_u_data D))
      (hfix (hL D.ρ_mem_L) D.ρ_mem (ec_conj_ρ_data D)) with ⟨z, hz⟩ | ⟨z, hz⟩
  · obtain ⟨σ, hσ⟩ := exists_mul_self_eq_of_two_nsmul D sB hz
    have hσS : (σ : S) * σ = d * d := by simpa [sB] using congrArg Subtype.val hσ
    exact (false_of_mul_self_eq hBC hC hH hcS hdC hdB hσS).elim
  · have hz' : 2 • z = D.ec (sB * D.c⁻¹) := by
      rw [D.ec_mul, D.ec_inv, D.ec_c, hz, sub_eq_add_neg]
    obtain ⟨σ, hσ⟩ := exists_mul_self_eq_of_two_nsmul D _ hz'
    have hσS : (σ : S) * σ = d * d * (D.c : S)⁻¹ := by
      simpa [sB] using congrArg Subtype.val hσ
    have hcomm : ∀ b : B, (b : S) * d = d * (b : S) := fun b =>
      Subgroup.mem_centralizer_iff.mp (hC hdC) (b : S) b.2
    refine ⟨d * (σ : S)⁻¹, C.mul_mem hdC (C.inv_mem (hBC σ.2)), fun h => hdB ?_, ?_⟩
    · have hd : d = d * (σ : S)⁻¹ * (σ : S) := by group
      rw [hd]
      exact B.mul_mem h σ.2
    · have hσc : (σ : S)⁻¹ * d = d * (σ : S)⁻¹ := by
        simpa using (hcomm σ⁻¹)
      calc d * (σ : S)⁻¹ * (d * (σ : S)⁻¹) = d * ((σ : S)⁻¹ * d) * (σ : S)⁻¹ := by group
        _ = d * (d * (σ : S)⁻¹) * (σ : S)⁻¹ := by rw [hσc]
        _ = (d * d) * ((σ : S) * σ)⁻¹ := by group
        _ = (d * d) * (d * d * (D.c : S)⁻¹)⁻¹ := by rw [hσS]
        _ = (d * d) * ((D.c : S) * (d * d)⁻¹) := by rw [mul_inv_rev, inv_inv]
        _ = (d * d) * ((d * d)⁻¹ * (D.c : S)) := by
          have hc1 : Commute (D.c : S) d := hcomm D.c
          rw [((hc1.mul_right hc1).inv_right).eq]
        _ = (D.c : S) := by group

theorem false_of_index_two_of_data (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S')
    (hnone : ∀ v : Torus τ.k, (∃ z, 2 • z = τ.action.φuv v - v) →
      (∃ z, 2 • z = τ.action.φt v - v) → (∃ z, 2 • z = τ.action.φu v - v) →
      (∃ z, 2 • z = τ.action.φρ v - v) → ∃ z, 2 • z = v) : False := by
  obtain ⟨d, hdC, hdB⟩ := exists_mem_not_mem_of_index_two hrel
  have hindex : (B.subgroupOf C).index = 2 := index_two_of_relIndex hBC hrel
  have hd2B : d * d ∈ B := sq_mem_of_index_two (x := ⟨d, hdC⟩) hindex
  let sB : B := ⟨d * d, hd2B⟩
  have hfix {g : S} (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B)
      {φ : Torus τ.k →+ Torus τ.k} (hφ : ∀ y : B, D.ec (conjBy hgB y) = φ (D.ec y)) :
      ∃ z, 2 • z = φ (D.ec sB) - D.ec sB := by
    obtain ⟨β, hβ⟩ := conj_sq_mul_inv_eq_sq hBC hC hrel hdC hdB hd2B hgC hgB
    refine ⟨D.ec β, ?_⟩
    rw [← ec_conj_mul_inv D hgB hφ, hβ, D.ec_mul, two_nsmul]
  obtain ⟨z, hz⟩ := hnone (D.ec sB) (hfix (hL D.uv_mem_L) D.uv_mem (ec_conj_uv_data D))
    (hfix (hL D.t_mem_L) D.t_mem (ec_conj_t_data D))
    (hfix (hL D.u_mem_L) D.u_mem (ec_conj_u_data D))
    (hfix (hL D.ρ_mem_L) D.ρ_mem (ec_conj_ρ_data D))
  obtain ⟨σ, hσ⟩ := exists_mul_self_eq_of_two_nsmul D sB hz
  have hσS : (σ : S) * σ = d * d := by simpa [sB] using congrArg Subtype.val hσ
  exact false_of_mul_self_eq hBC hC hH hcS hdC hdB hσS

end IndexTwo

section Inclusion

theorem pow_two_pow_eq_one_of_orderOf (hBC : B ≤ C) {x : B} {e : ℕ} (h : orderOf x = 2 ^ e) :
    (⟨x, hBC x.2⟩ : C) ^ (2 ^ e) = 1 := by
  apply Subtype.ext
  have hx : x ^ (2 ^ e) = 1 := by rw [← orderOf_dvd_iff_pow_eq_one, h]
  simpa using congrArg Subtype.val hx

@[expose] noncomputable def incl2 (k K : Fin 3 → ℕ) (h0 : K 0 = k 0 + 1) (h1 : K 1 = k 1)
    (h2 : K 2 = k 2) : Torus k →+ Torus K :=
  torusHomOfGens k ![(2 : ℤ) • gen K 0, gen K 1, gen K 2] (fun i => by
    fin_cases i
    · change (2 ^ k 0) • ((2 : ℤ) • gen K 0) = 0
      rw [← natCast_zsmul, smul_smul]
      push_cast
      rw [← pow_succ, ← h0, two_pow_zsmul_gen]
    · change (2 ^ k 1) • gen K 1 = 0
      rw [← natCast_zsmul]
      push_cast
      rw [← h1, two_pow_zsmul_gen]
    · change (2 ^ k 2) • gen K 2 = 0
      rw [← natCast_zsmul]
      push_cast
      rw [← h2, two_pow_zsmul_gen])

@[expose] noncomputable def incl4 (k K : Fin 3 → ℕ) (h0 : K 0 = k 0) (h1 : K 1 = k 1 + 1)
    (h2 : K 2 = k 2 + 1) : Torus k →+ Torus K :=
  torusHomOfGens k ![gen K 0, (2 : ℤ) • gen K 1, (2 : ℤ) • gen K 2] (fun i => by
    fin_cases i
    · change (2 ^ k 0) • gen K 0 = 0
      rw [← natCast_zsmul]
      push_cast
      rw [← h0, two_pow_zsmul_gen]
    · change (2 ^ k 1) • ((2 : ℤ) • gen K 1) = 0
      rw [← natCast_zsmul, smul_smul]
      push_cast
      rw [← pow_succ, ← h1, two_pow_zsmul_gen]
    · change (2 ^ k 2) • ((2 : ℤ) • gen K 2) = 0
      rw [← natCast_zsmul, smul_smul]
      push_cast
      rw [← pow_succ, ← h2, two_pow_zsmul_gen])

variable {k K : Fin 3 → ℕ}

theorem incl2_apply (h0 : K 0 = k 0 + 1) (h1 : K 1 = k 1) (h2 : K 2 = k 2) (x y z : ℤ) :
    incl2 k K h0 h1 h2 (x • gen k 0 + y • gen k 1 + z • gen k 2) =
      (2 * x) • gen K 0 + y • gen K 1 + z • gen K 2 := by
  simp only [incl2, map_add, map_zsmul, torusHomOfGens_gen]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, smul_smul, mul_comm x]

theorem incl4_apply (h0 : K 0 = k 0) (h1 : K 1 = k 1 + 1) (h2 : K 2 = k 2 + 1) (x y z : ℤ) :
    incl4 k K h0 h1 h2 (x • gen k 0 + y • gen k 1 + z • gen k 2) =
      x • gen K 0 + (2 * y) • gen K 1 + (2 * z) • gen K 2 := by
  simp only [incl4, map_add, map_zsmul, torusHomOfGens_gen]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, smul_smul, mul_comm y, mul_comm z]

theorem incl2_gen0 (h0 : K 0 = k 0 + 1) (h1 : K 1 = k 1) (h2 : K 2 = k 2) :
    incl2 k K h0 h1 h2 (gen k 0) = (2 : ℤ) • gen K 0 := by
  simp [incl2, torusHomOfGens_gen]

theorem incl2_gen1 (h0 : K 0 = k 0 + 1) (h1 : K 1 = k 1) (h2 : K 2 = k 2) :
    incl2 k K h0 h1 h2 (gen k 1) = gen K 1 := by
  simp [incl2, torusHomOfGens_gen]

theorem incl2_gen2 (h0 : K 0 = k 0 + 1) (h1 : K 1 = k 1) (h2 : K 2 = k 2) :
    incl2 k K h0 h1 h2 (gen k 2) = gen K 2 := by
  simp [incl2, torusHomOfGens_gen]

theorem incl4_gen0 (h0 : K 0 = k 0) (h1 : K 1 = k 1 + 1) (h2 : K 2 = k 2 + 1) :
    incl4 k K h0 h1 h2 (gen k 0) = gen K 0 := by
  simp [incl4, torusHomOfGens_gen]

theorem incl4_gen1 (h0 : K 0 = k 0) (h1 : K 1 = k 1 + 1) (h2 : K 2 = k 2 + 1) :
    incl4 k K h0 h1 h2 (gen k 1) = (2 : ℤ) • gen K 1 := by
  simp [incl4, torusHomOfGens_gen]

theorem incl4_gen2 (h0 : K 0 = k 0) (h1 : K 1 = k 1 + 1) (h2 : K 2 = k 2 + 1) :
    incl4 k K h0 h1 h2 (gen k 2) = (2 : ℤ) • gen K 2 := by
  simp [incl4, torusHomOfGens_gen]

theorem conjTorus_incl (D : StrothTypeData B τ) (hBC : B ≤ C) (hL : D.L ≤ Subgroup.normalizer C)
    (E : Torus K ≃+ Additive C) (ι : Torus τ.k →+ Torus K)
    (hι : ∀ β : B, E (ι (D.ec β)) = Additive.ofMul (⟨β, hBC β.2⟩ : C)) {g : S} (hgL : g ∈ D.L)
    (hgB : g ∈ Subgroup.normalizer B) {φ : Torus τ.k →+ Torus τ.k}
    (hφ : ∀ y : B, D.ec (conjBy hgB y) = φ (D.ec y)) (v : Torus τ.k) :
    conjTorusIdx4 E (hL hgL) (ι v) = ι (φ v) := by
  obtain ⟨β, rfl⟩ : ∃ β : B, D.ec β = v :=
    ⟨Additive.toMul (D.e.symm v), D.e.apply_symm_apply v⟩
  have h1 : ι (D.ec β) = E.symm (Additive.ofMul (⟨β, hBC β.2⟩ : C)) :=
    ((AddEquiv.symm_apply_eq E).mpr (hι β).symm).symm
  rw [h1, conjTorusIdx4_apply_symm, ← hφ]
  have hc : conjBy (hL hgL) (⟨β, hBC β.2⟩ : C) = ⟨conjBy hgB β, hBC (conjBy hgB β).2⟩ :=
    Subtype.ext rfl
  rw [hc, AddEquiv.symm_apply_eq, hι]

theorem map_incl_eq_of_gens {A' : Torus K →+ Torus K} {φ : Torus k →+ Torus k}
    (ι : Torus k →+ Torus K) (h : ∀ j, A' (ι (gen k j)) = ι (φ (gen k j))) (v : Torus k) :
    A' (ι v) = ι (φ v) := by
  have e : A'.comp ι = ι.comp φ := torus_hom_ext _ _ fun j z => by
    have hz : Pi.single j (z : ZMod (2 ^ k j)) = z • gen k j := by
      funext i
      by_cases hij : i = j
      · subst hij
        simp [gen, Pi.single_eq_same, zsmul_eq_mul]
      · simp [gen, Pi.single_eq_of_ne hij]
    simp only [AddMonoidHom.comp_apply, hz, map_zsmul, h j]
  exact DFunLike.congr_fun e v

theorem incl2_gen (h0 : K 0 = k 0 + 1) (h1 : K 1 = k 1) (h2 : K 2 = k 2) (j : Fin 3) :
    incl2 k K h0 h1 h2 (gen k j) = (![2, 1, 1] j : ℤ) • gen K j := by
  fin_cases j
  · simpa using incl2_gen0 h0 h1 h2
  · simpa using incl2_gen1 h0 h1 h2
  · simpa using incl2_gen2 h0 h1 h2

theorem incl4_gen (h0 : K 0 = k 0) (h1 : K 1 = k 1 + 1) (h2 : K 2 = k 2 + 1) (j : Fin 3) :
    incl4 k K h0 h1 h2 (gen k j) = (![1, 2, 2] j : ℤ) • gen K j := by
  fin_cases j
  · simpa using incl4_gen0 h0 h1 h2
  · simpa using incl4_gen1 h0 h1 h2
  · simpa using incl4_gen2 h0 h1 h2

end Inclusion

theorem conjTorusIdx4_trans {k : Fin 3 → ℕ} (E : Torus k ≃+ Additive C) (φ : Torus k ≃+ Torus k)
    {g : S} (hg : g ∈ Subgroup.normalizer C) (x : Torus k) :
    conjTorusIdx4 (φ.trans E) hg x = φ.symm (conjTorusIdx4 E hg (φ x)) := rfl

theorem hasStrothTypeOver_of_basisChange (D : StrothTypeData B τ)
    (hL : D.L ≤ Subgroup.normalizer C)
    (τ' : StrothTypeIndex) (E : Torus τ'.k ≃+ Additive C) (φ : Torus τ'.k ≃+ Torus τ'.k)
    (h : ∀ j, φ.symm (conjTorusIdx4 E (hL D.uv_mem_L) (φ (gen τ'.k j))) =
        τ'.action.φuv (gen τ'.k j) ∧
      φ.symm (conjTorusIdx4 E (hL D.t_mem_L) (φ (gen τ'.k j))) = τ'.action.φt (gen τ'.k j) ∧
      φ.symm (conjTorusIdx4 E (hL D.u_mem_L) (φ (gen τ'.k j))) = τ'.action.φu (gen τ'.k j) ∧
      φ.symm (conjTorusIdx4 E (hL D.ρ_mem_L) (φ (gen τ'.k j))) = τ'.action.φρ (gen τ'.k j)) :
    HasStrothTypeOver D C τ' :=
  hasStrothTypeOver_of_conjTorus_Idx4 D hL τ' (φ.trans E) h

theorem hasStrothType_of_basisChange (D : StrothTypeData B τ) (hL : D.L ≤ Subgroup.normalizer C)
    (τ' : StrothTypeIndex) (E : Torus τ'.k ≃+ Additive C) (φ : Torus τ'.k ≃+ Torus τ'.k)
    (h : ∀ j, φ.symm (conjTorusIdx4 E (hL D.uv_mem_L) (φ (gen τ'.k j))) =
        τ'.action.φuv (gen τ'.k j) ∧
      φ.symm (conjTorusIdx4 E (hL D.t_mem_L) (φ (gen τ'.k j))) = τ'.action.φt (gen τ'.k j) ∧
      φ.symm (conjTorusIdx4 E (hL D.u_mem_L) (φ (gen τ'.k j))) = τ'.action.φu (gen τ'.k j) ∧
      φ.symm (conjTorusIdx4 E (hL D.ρ_mem_L) (φ (gen τ'.k j))) = τ'.action.φρ (gen τ'.k j)) :
    HasStrothType C τ' :=
  (hasStrothTypeOver_of_basisChange D hL τ' E φ h).hasStrothType

section BasisTwo

theorem comm_of_index_two (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) (x y : C) : x * y = y * x := by
  have hindex : (B.subgroupOf C).index = 2 := index_two_of_relIndex hBC hrel
  haveI : (B.subgroupOf C).Normal := Subgroup.normal_of_index_eq_two hindex
  have hcard : Nat.card (C ⧸ B.subgroupOf C) = 2 := by
    rw [← Subgroup.index_eq_card, hindex]
  haveI : IsCyclic (C ⧸ B.subgroupOf C) := isCyclic_of_prime_card hcard
  exact comm_of_le_centralizer_of_cyclic_quotient hBC hC inferInstance x y

variable (D : StrothTypeData B τ)

theorem exists_torusBasis_idx2_of_data (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 2 * Nat.card B) {K : Fin 3 → ℕ} (hK0 : K 0 = τ.k 0 + 1)
    (hK1 : K 1 = τ.k 1) (hK2 : K 2 = τ.k 2) {d : S} (hdC : d ∈ C) (hdB : d ∉ B)
    (hd : d * d = (D.c : S)) :
    ∃ E : Torus K ≃+ Additive C, E (gen K 0) = Additive.ofMul (⟨d, hdC⟩ : C) ∧
      E (gen K 1) = Additive.ofMul (⟨D.a, hBC D.a.2⟩ : C) ∧
      E (gen K 2) = Additive.ofMul (⟨D.b, hBC D.b.2⟩ : C) := by
  have hcomm := comm_of_index_two hBC hC hrel
  have hindex : (B.subgroupOf C).index = 2 := index_two_of_relIndex hBC hrel
  let dC : C := ⟨d, hdC⟩
  let x : Fin 3 → C := ![dC, ⟨D.a, hBC D.a.2⟩, ⟨D.b, hBC D.b.2⟩]
  have hdd : dC * dC = ⟨D.c, hBC D.c.2⟩ := Subtype.ext hd
  have hx : ∀ i, x i ^ (2 ^ K i) = 1 := by
    intro i
    fin_cases i
    · change dC ^ (2 ^ K 0) = 1
      rw [hK0, pow_succ', pow_mul, sq, hdd]
      exact pow_two_pow_eq_one_of_orderOf hBC (orderOf_c_lift D)
    · change (⟨D.a, hBC D.a.2⟩ : C) ^ (2 ^ K 1) = 1
      rw [hK1]
      exact pow_two_pow_eq_one_of_orderOf hBC (orderOf_a_lift D)
    · change (⟨D.b, hBC D.b.2⟩ : C) ^ (2 ^ K 2) = 1
      rw [hK2]
      exact pow_two_pow_eq_one_of_orderOf hBC (orderOf_b_lift D)
  have hgen : Subgroup.closure (Set.range x) = ⊤ := by
    let H := Subgroup.closure (Set.range x)
    have hd' : dC ∈ H := Subgroup.subset_closure ⟨0, rfl⟩
    have ha' : (⟨D.a, hBC D.a.2⟩ : C) ∈ H := Subgroup.subset_closure ⟨1, rfl⟩
    have hb' : (⟨D.b, hBC D.b.2⟩ : C) ∈ H := Subgroup.subset_closure ⟨2, rfl⟩
    have hBH : ∀ β : B, (⟨β, hBC β.2⟩ : C) ∈ H := by
      intro β
      obtain ⟨i, j, l, hijl⟩ := torus_eq_zsmul_gens _ (D.ec β)
      have hβ := eq_zpow_c_a_b_Idx4 D hijl
      have hβC : (⟨β, hBC β.2⟩ : C) = (dC * dC) ^ i * (⟨D.a, hBC D.a.2⟩ : C) ^ j *
          (⟨D.b, hBC D.b.2⟩ : C) ^ l := by
        rw [hdd]
        apply Subtype.ext
        simpa using congrArg Subtype.val hβ
      rw [hβC]
      exact H.mul_mem (H.mul_mem (H.zpow_mem (H.mul_mem hd' hd') i) (H.zpow_mem ha' j))
        (H.zpow_mem hb' l)
    rw [eq_top_iff]
    intro y _
    rcases mem_or_exists_mul_of_index_two hdC hdB hindex y.2 with hy | ⟨b, hbB, hb⟩
    · exact hBH ⟨y, hy⟩
    · have hy : y = dC * ⟨b, hBC hbB⟩ := Subtype.ext hb
      rw [hy]
      exact H.mul_mem hd' (hBH ⟨b, hbB⟩)
  have hcard : Nat.card (Torus K) = Nat.card C := by
    rw [card_torus, hrel, D.card, hK0, hK1, hK2]
    rw [show τ.k 0 + 1 + τ.k 1 + τ.k 2 = (τ.k 0 + τ.k 1 + τ.k 2) + 1 by ring, pow_succ]
    ring
  obtain ⟨E, hE⟩ := exists_torusEquiv_Idx4 hcomm x hx hgen hcard
  exact ⟨E, hE 0, hE 1, hE 2⟩

theorem E_incl2 (hBC : B ≤ C) {K : Fin 3 → ℕ} (hK0 : K 0 = τ.k 0 + 1) (hK1 : K 1 = τ.k 1)
    (hK2 : K 2 = τ.k 2) {d : S} (hdC : d ∈ C) (hd : d * d = (D.c : S))
    (E : Torus K ≃+ Additive C) (hE0 : E (gen K 0) = Additive.ofMul (⟨d, hdC⟩ : C))
    (hE1 : E (gen K 1) = Additive.ofMul (⟨D.a, hBC D.a.2⟩ : C))
    (hE2 : E (gen K 2) = Additive.ofMul (⟨D.b, hBC D.b.2⟩ : C)) (β : B) :
    E (incl2 τ.k K hK0 hK1 hK2 (D.ec β)) = Additive.ofMul (⟨β, hBC β.2⟩ : C) := by
  obtain ⟨i, j, l, hijl⟩ := torus_eq_zsmul_gens _ (D.ec β)
  have hβ := eq_zpow_c_a_b_Idx4 D hijl
  have hdd : (⟨d, hdC⟩ : C) * ⟨d, hdC⟩ = ⟨D.c, hBC D.c.2⟩ := Subtype.ext hd
  have hβC : (⟨β, hBC β.2⟩ : C) = (⟨d, hdC⟩ * ⟨d, hdC⟩ : C) ^ i *
      (⟨D.a, hBC D.a.2⟩ : C) ^ j * (⟨D.b, hBC D.b.2⟩ : C) ^ l := by
    rw [hdd]
    apply Subtype.ext
    simpa using congrArg Subtype.val hβ
  rw [hijl, incl2_apply, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hE0, hE1, hE2, hβC,
    ofMul_mul, ofMul_mul, ofMul_zpow, ofMul_zpow, ofMul_zpow, ofMul_mul, mul_comm (2 : ℤ) i,
    mul_zsmul, two_zsmul]

end BasisTwo

section Restrict

variable {k K : Fin 3 → ℕ}

@[expose] def diag2 : IntMat := Matrix.diagonal ![2, 1, 1]

@[expose] def diag4 : IntMat := Matrix.diagonal ![1, 2, 2]

theorem matAct_gens_diag {M' M : IntMat} (hM' : Compat K M') (hM : Compat k M)
    (ι : Torus k →+ Torus K) (v : Fin 3 → ℤ) (hι : ∀ j, ι (gen k j) = v j • gen K j)
    (h : MatEq K (M' * Matrix.diagonal v) (Matrix.diagonal v * M)) (j : Fin 3) :
    matAct K M' hM' (ι (gen k j)) = ι (matAct k M hM (gen k j)) := by
  rw [hι, map_zsmul, matAct_gen_eq, matAct_gen_eq, map_add, map_add, map_zsmul, map_zsmul,
    map_zsmul, hι, hι, hι, smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul,
    smul_smul, smul_smul]
  have e : ∀ i, (2 : ℤ) ^ K i ∣ M i j * v i - v j * M' i j := by
    intro i
    have := (h i j).dvd
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    convert this using 1
    ring
  exact zsmul_gens_eq_of_dvd (e 0) (e 1) (e 2)


theorem matAct_incl2 (h0 : K 0 = k 0 + 1) (h1 : K 1 = k 1) (h2 : K 2 = k 2) {M' M : IntMat}
    (hM' : Compat K M') (hM : Compat k M) (h : MatEq K (M' * diag2) (diag2 * M)) (v : Torus k) :
    matAct K M' hM' (incl2 k K h0 h1 h2 v) = incl2 k K h0 h1 h2 (matAct k M hM v) :=
  map_incl_eq_of_gens _ (matAct_gens_diag hM' hM _ ![2, 1, 1] (incl2_gen h0 h1 h2) h) v

theorem matAct_incl4 (h0 : K 0 = k 0) (h1 : K 1 = k 1 + 1) (h2 : K 2 = k 2 + 1) {M' M : IntMat}
    (hM' : Compat K M') (hM : Compat k M) (h : MatEq K (M' * diag4) (diag4 * M)) (v : Torus k) :
    matAct K M' hM' (incl4 k K h0 h1 h2 v) = incl4 k K h0 h1 h2 (matAct k M hM v) :=
  map_incl_eq_of_gens _ (matAct_gens_diag hM' hM _ ![1, 2, 2] (incl4_gen h0 h1 h2) h) v

end Restrict

section Agree

variable (D : StrothTypeData B τ)

theorem agreeB2_of_data (hBC : B ≤ C) (hL : D.L ≤ Subgroup.normalizer C) {K : Fin 3 → ℕ}
    (hK0 : K 0 = τ.k 0 + 1) (hK1 : K 1 = τ.k 1) (hK2 : K 2 = τ.k 2) (E : Torus K ≃+ Additive C)
    (hE : ∀ β : B, E (incl2 τ.k K hK0 hK1 hK2 (D.ec β)) = Additive.ofMul (⟨β, hBC β.2⟩ : C))
    {g : S} (hgL : g ∈ D.L) (hgB : g ∈ Subgroup.normalizer B) {φ : Torus τ.k →+ Torus τ.k}
    (hφ : ∀ y : B, D.ec (conjBy hgB y) = φ (D.ec y)) {A' : Torus K →+ Torus K}
    (hA' : ∀ v, A' (incl2 τ.k K hK0 hK1 hK2 v) = incl2 τ.k K hK0 hK1 hK2 (φ v)) :
    AgreeB2 K (conjTorusIdx4 E (hL hgL)) A' := by
  have key : ∀ v, conjTorusIdx4 E (hL hgL) (incl2 τ.k K hK0 hK1 hK2 v) =
      A' (incl2 τ.k K hK0 hK1 hK2 v) := fun v => by
    rw [conjTorus_incl D hBC hL E _ hE hgL hgB hφ, hA']
  refine ⟨?_, ?_, ?_⟩
  · rw [← incl2_gen0 hK0 hK1 hK2]; exact key _
  · rw [← incl2_gen1 hK0 hK1 hK2]; exact key _
  · rw [← incl2_gen2 hK0 hK1 hK2]; exact key _

theorem agreeB4_of_data (hBC : B ≤ C) (hL : D.L ≤ Subgroup.normalizer C) {K : Fin 3 → ℕ}
    (hK0 : K 0 = τ.k 0) (hK1 : K 1 = τ.k 1 + 1) (hK2 : K 2 = τ.k 2 + 1) (E : Torus K ≃+ Additive C)
    (hE : ∀ β : B, E (incl4 τ.k K hK0 hK1 hK2 (D.ec β)) = Additive.ofMul (⟨β, hBC β.2⟩ : C))
    {g : S} (hgL : g ∈ D.L) (hgB : g ∈ Subgroup.normalizer B) {φ : Torus τ.k →+ Torus τ.k}
    (hφ : ∀ y : B, D.ec (conjBy hgB y) = φ (D.ec y)) {A' : Torus K →+ Torus K}
    (hA' : ∀ v, A' (incl4 τ.k K hK0 hK1 hK2 v) = incl4 τ.k K hK0 hK1 hK2 (φ v)) :
    AgreeB4 K (conjTorusIdx4 E (hL hgL)) A' := by
  have key : ∀ v, conjTorusIdx4 E (hL hgL) (incl4 τ.k K hK0 hK1 hK2 v) =
      A' (incl4 τ.k K hK0 hK1 hK2 v) := fun v => by
    rw [conjTorus_incl D hBC hL E _ hE hgL hgB hφ, hA']
  refine ⟨?_, ?_, ?_⟩
  · rw [← incl4_gen0 hK0 hK1 hK2]; exact key _
  · rw [← incl4_gen1 hK0 hK1 hK2]; exact key _
  · rw [← incl4_gen2 hK0 hK1 hK2]; exact key _

end Agree

theorem hasStrothTypeOver_or_of_index_two_of_data (D : StrothTypeData B τ) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C) (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S')
    (hsec : ∀ v : Torus τ.k, (∃ z, 2 • z = τ.action.φuv v - v) →
      (∃ z, 2 • z = τ.action.φt v - v) → (∃ z, 2 • z = τ.action.φu v - v) →
      (∃ z, 2 • z = τ.action.φρ v - v) → (∃ z, 2 • z = v) ∨ (∃ z, 2 • z = v - gen τ.k 0))
    (τ₁ : StrothTypeIndex) (hK0 : τ₁.k 0 = τ.k 0 + 1) (hK1 : τ₁.k 1 = τ.k 1)
    (hK2 : τ₁.k 2 = τ.k 2) (hk : ∀ j, 1 ≤ τ₁.k j) (hk0 : 2 ≤ τ₁.k 0) (A' : SigmaFourAction τ₁.k)
    (hP : Profile2 τ₁.k τ₁.action.φuv τ₁.action.φt τ₁.action.φu τ₁.action.φρ)
    (hT : Twist2 τ₁.k τ₁.action.φuv τ₁.action.φt τ₁.action.φu τ₁.action.φρ A'.φuv A'.φt A'.φu
      A'.φρ)
    (cV : MatEq τ₁.k (τ₁.action.uv * diag2) (diag2 * τ.action.uv))
    (cW : MatEq τ₁.k (τ₁.action.t * diag2) (diag2 * τ.action.t))
    (cU : MatEq τ₁.k (τ₁.action.u * diag2) (diag2 * τ.action.u))
    (cR : MatEq τ₁.k (τ₁.action.ρ * diag2) (diag2 * τ.action.ρ)) :
    HasStrothTypeOver D C τ₁ ∨ ∃ (E : Torus τ₁.k ≃+ Additive C) (φ : Torus τ₁.k ≃+ Torus τ₁.k),
      ∀ j, φ.symm (conjTorusIdx4 E (hL D.uv_mem_L) (φ (gen τ₁.k j))) = A'.φuv (gen τ₁.k j) ∧
        φ.symm (conjTorusIdx4 E (hL D.t_mem_L) (φ (gen τ₁.k j))) = A'.φt (gen τ₁.k j) ∧
        φ.symm (conjTorusIdx4 E (hL D.u_mem_L) (φ (gen τ₁.k j))) = A'.φu (gen τ₁.k j) ∧
        φ.symm (conjTorusIdx4 E (hL D.ρ_mem_L) (φ (gen τ₁.k j))) = A'.φρ (gen τ₁.k j) := by
  obtain ⟨d, hdC, hdB, hd⟩ := exists_sq_eq_c_of_data D hBC hC hrel hL hH hcS hsec
  obtain ⟨E, hE0, hE1, hE2⟩ := exists_torusBasis_idx2_of_data D hBC hC hrel hK0 hK1 hK2 hdC hdB hd
  have hE := E_incl2 D hBC hK0 hK1 hK2 hdC hd E hE0 hE1 hE2
  have hV := agreeB2_of_data D hBC hL hK0 hK1 hK2 E hE D.uv_mem_L D.uv_mem (ec_conj_uv_data D)
    (A' := τ₁.action.φuv) (matAct_incl2 hK0 hK1 hK2 _ _ cV)
  have hW := agreeB2_of_data D hBC hL hK0 hK1 hK2 E hE D.t_mem_L D.t_mem (ec_conj_t_data D)
    (A' := τ₁.action.φt) (matAct_incl2 hK0 hK1 hK2 _ _ cW)
  have hU := agreeB2_of_data D hBC hL hK0 hK1 hK2 E hE D.u_mem_L D.u_mem (ec_conj_u_data D)
    (A' := τ₁.action.φu) (matAct_incl2 hK0 hK1 hK2 _ _ cU)
  have hR := agreeB2_of_data D hBC hL hK0 hK1 hK2 E hE D.ρ_mem_L D.ρ_mem (ec_conj_ρ_data D)
    (A' := τ₁.action.φρ) (matAct_incl2 hK0 hK1 hK2 _ _ cR)
  obtain ⟨φ, h1 | h2⟩ := classify_idx2 hk hk0 τ₁.action.rels hP hT (conjTorusIdx4_rels E D hL)
    hV hW hU hR
  · exact Or.inl (hasStrothTypeOver_of_basisChange D hL τ₁ E φ h1)
  · exact Or.inr ⟨E, φ, h2⟩

theorem hasStrothType_or_of_index_two_of_data (D : StrothTypeData B τ) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C) (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S')
    (hsec : ∀ v : Torus τ.k, (∃ z, 2 • z = τ.action.φuv v - v) →
      (∃ z, 2 • z = τ.action.φt v - v) → (∃ z, 2 • z = τ.action.φu v - v) →
      (∃ z, 2 • z = τ.action.φρ v - v) → (∃ z, 2 • z = v) ∨ (∃ z, 2 • z = v - gen τ.k 0))
    (τ₁ : StrothTypeIndex) (hK0 : τ₁.k 0 = τ.k 0 + 1) (hK1 : τ₁.k 1 = τ.k 1)
    (hK2 : τ₁.k 2 = τ.k 2) (hk : ∀ j, 1 ≤ τ₁.k j) (hk0 : 2 ≤ τ₁.k 0) (A' : SigmaFourAction τ₁.k)
    (hP : Profile2 τ₁.k τ₁.action.φuv τ₁.action.φt τ₁.action.φu τ₁.action.φρ)
    (hT : Twist2 τ₁.k τ₁.action.φuv τ₁.action.φt τ₁.action.φu τ₁.action.φρ A'.φuv A'.φt A'.φu
      A'.φρ)
    (cV : MatEq τ₁.k (τ₁.action.uv * diag2) (diag2 * τ.action.uv))
    (cW : MatEq τ₁.k (τ₁.action.t * diag2) (diag2 * τ.action.t))
    (cU : MatEq τ₁.k (τ₁.action.u * diag2) (diag2 * τ.action.u))
    (cR : MatEq τ₁.k (τ₁.action.ρ * diag2) (diag2 * τ.action.ρ)) :
    HasStrothType C τ₁ ∨ ∃ (E : Torus τ₁.k ≃+ Additive C) (φ : Torus τ₁.k ≃+ Torus τ₁.k),
      ∀ j, φ.symm (conjTorusIdx4 E (hL D.uv_mem_L) (φ (gen τ₁.k j))) = A'.φuv (gen τ₁.k j) ∧
        φ.symm (conjTorusIdx4 E (hL D.t_mem_L) (φ (gen τ₁.k j))) = A'.φt (gen τ₁.k j) ∧
        φ.symm (conjTorusIdx4 E (hL D.u_mem_L) (φ (gen τ₁.k j))) = A'.φu (gen τ₁.k j) ∧
        φ.symm (conjTorusIdx4 E (hL D.ρ_mem_L) (φ (gen τ₁.k j))) = A'.φρ (gen τ₁.k j) :=
  (hasStrothTypeOver_or_of_index_two_of_data D hBC hC hrel hL hH hcS hsec τ₁ hK0 hK1 hK2 hk hk0 A'
    hP hT cV cW cU cR).imp_left (·.hasStrothType)

end CFSG.CGT.Stroth77
