module

public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamental
public import CFSG.ClassicalInvolution.RouteD.TypeABridge

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open Matrix Module CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply)
open scoped MatrixGroups

section Frame

theorem exists_fibre_map {S : Type} [Fintype S] [DecidableEq S] (d : S → ℕ) (n : ℕ)
    (hn : ∑ s, d s = n) : ∃ ε : Fin n → S, ∀ s, Nat.card {j // ε j = s} = d s := by
  have e : Fin n ≃ Σ s, Fin (d s) := by
    apply Fintype.equivOfCardEq
    simp [Fintype.card_sigma, hn]
  refine ⟨fun j => (e j).1, fun s => ?_⟩
  have : {j // (e j).1 = s} ≃ {x : Σ s, Fin (d s) // x.1 = s} :=
    e.subtypeEquiv (fun j => Iff.rfl)
  rw [Nat.card_congr this, Nat.card_congr (Equiv.sigmaSubtype s)]
  simp

variable {K : Type} [Field K] {n : ℕ}

theorem exists_sl_frame_signs (h2 : (2 : K) ≠ 0) (hn : 0 < n) {i₁ i₂ : Matrix (Fin n) (Fin n) K}
    (h₁ : i₁ * i₁ = 1) (h₂' : i₂ * i₂ = 1) (hc : i₁ * i₂ = i₂ * i₁) :
    ∃ (P : SL(n, K)) (ε : Fin n → Bool × Bool),
      i₁ * (P : Matrix (Fin n) (Fin n) K) =
        (P : Matrix (Fin n) (Fin n) K) * Matrix.diagonal (fun j => signOf K (ε j).1) ∧
      i₂ * (P : Matrix (Fin n) (Fin n) K) =
        (P : Matrix (Fin n) (Fin n) K) * Matrix.diagonal (fun j => signOf K (ε j).2) := by
  have hint := isInternal_jointEigenspace h2 (toLin'_mul_self h₁) (toLin'_mul_self h₂')
    (toLin'_mul_comm hc)
  have hsum : ∑ s, finrank K (jointEig i₁ i₂ s) = n := by
    have := finrank_eq_sum_of_isInternal (jointEig i₁ i₂) hint
    simpa using this.symm
  obtain ⟨ε, hε⟩ := exists_fibre_map (fun s => finrank K (jointEig i₁ i₂ s)) n hsum
  obtain ⟨P, hP⟩ := exists_sl_frame h2 hn h₁ h₂' hc ε hε
  exact ⟨P, ε, hP⟩

end Frame

section Generation

variable {K : Type} [Field K] {n : ℕ}

theorem diagonal_mul_blockMat_comm {j : ℕ} (d : Fin n → K)
    (hd : ∀ a b : Fin n, (j ≤ a.val ∧ a.val < j + 2) → (j ≤ b.val ∧ b.val < j + 2) → d a = d b)
    (A : Matrix (Fin 2) (Fin 2) K) :
    Matrix.diagonal d * blockMat n j A = blockMat n j A * Matrix.diagonal d := by
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, blockMat_apply]
  by_cases h : (j ≤ a.val ∧ a.val < j + 2) ∧ (j ≤ b.val ∧ b.val < j + 2)
  · rw [dite_eq_left h, hd a b h.1 h.2, mul_comm]
  · rw [dite_eq_right h]
    by_cases hab : a = b
    · subst hab
      simp [mul_comm]
    · simp [hab]

theorem commute_conj_of_diagonal {P i y : SL(n, K)} (d : Fin n → K)
    (hi : (i : Matrix (Fin n) (Fin n) K) * (P : Matrix (Fin n) (Fin n) K) =
      (P : Matrix (Fin n) (Fin n) K) * Matrix.diagonal d)
    (hy : Matrix.diagonal d * (y : Matrix (Fin n) (Fin n) K) =
      (y : Matrix (Fin n) (Fin n) K) * Matrix.diagonal d) :
    i * (P * y * P⁻¹) = (P * y * P⁻¹) * i := by
  have hPP : ((P⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K) *
      (P : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hD : ((P⁻¹ * i * P : SL(n, K)) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc, hi,
      ← Matrix.mul_assoc, hPP, Matrix.one_mul]
  have hcomm : (P⁻¹ * i * P) * y = y * (P⁻¹ * i * P) := by
    apply Subtype.ext
    have e1 : (((P⁻¹ * i * P) * y : SL(n, K)) : Matrix (Fin n) (Fin n) K) =
        ((P⁻¹ * i * P : SL(n, K)) : Matrix (Fin n) (Fin n) K) * (y : Matrix (Fin n) (Fin n) K) :=
      Matrix.SpecialLinearGroup.coe_mul _ _
    have e2 : ((y * (P⁻¹ * i * P) : SL(n, K)) : Matrix (Fin n) (Fin n) K) =
        (y : Matrix (Fin n) (Fin n) K) * ((P⁻¹ * i * P : SL(n, K)) : Matrix (Fin n) (Fin n) K) :=
      Matrix.SpecialLinearGroup.coe_mul _ _
    rw [e1, e2, hD, hy]
  have hi' : i = P * (P⁻¹ * i * P) * P⁻¹ := by group
  calc i * (P * y * P⁻¹) = P * (P⁻¹ * i * P) * P⁻¹ * (P * y * P⁻¹) := by rw [← hi']
    _ = P * ((P⁻¹ * i * P) * y) * P⁻¹ := by group
    _ = P * (y * (P⁻¹ * i * P)) * P⁻¹ := by rw [hcomm]
    _ = (P * y * P⁻¹) * (P * (P⁻¹ * i * P) * P⁻¹) := by group
    _ = (P * y * P⁻¹) * i := by rw [← hi']

end Generation

section Main

variable {F : Type} [Field F] {m : ℕ}

theorem iSup_blockSL2_range_eq_top :
    ⨆ k : Fin m, (blockSL2 F m k).range = ⊤ := by
  rw [eq_top_iff, ← SpecialLinear.iSup_fundamentalRootSubgroup_eq_top (m := m) (F := F)]
  refine iSup_le fun k => iSup_le fun s => ?_
  have hle : SpecialLinear.fundamentalRootSubgroup m F k s ≤ (blockSL2 F m k).range := by
    rw [← rankOne_eq_range, SpecialLinear.rankOne_rootGroup]
    cases s
    · exact le_sup_right
    · exact le_sup_left
  exact hle.trans (le_iSup (fun k => (blockSL2 F m k).range) k)

theorem signOf_mul_eq_of_ne {u u' v v' : Bool} (h1 : u ≠ u') (h2 : v ≠ v') :
    signOf F u * signOf F v = signOf F u' * signOf F v' := by
  cases u <;> cases u' <;> cases v <;> cases v' <;> simp_all [signOf]

theorem iSup_longRootSet_centralizing (h2 : (2 : F) ≠ 0) (hn : 2 ≤ m + 1)
    {i₁ i₂ : SL(m + 1, F)} (h₁ : i₁ * i₁ = 1) (h₂' : i₂ * i₂ = 1) (hc : i₁ * i₂ = i₂ * i₁) :
    (⊤ : Subgroup SL(m + 1, F)) ≤ ⨆ R ∈ longRootSet (K := F) hn,
      ⨆ (_ : R ≤ Subgroup.centralizer ({i₁} : Set SL(m + 1, F)) ∨
        R ≤ Subgroup.centralizer ({i₂} : Set SL(m + 1, F)) ∨
        R ≤ Subgroup.centralizer ({i₁ * i₂} : Set SL(m + 1, F))), R := by
  have hmat : ∀ {x y : SL(m + 1, F)}, x * y = y * x →
      (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * y = y * x := fun h => by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, h]
  have hsq : ∀ {x : SL(m + 1, F)}, x * x = 1 →
      (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * x = 1 := fun h => by
    rw [← Matrix.SpecialLinearGroup.coe_mul, h, Matrix.SpecialLinearGroup.coe_one]
  obtain ⟨P, ε, hP₁, hP₂⟩ := exists_sl_frame_signs h2 (by omega) (hsq h₁) (hsq h₂') (hmat hc)
  have hP₃ : ((i₁ * i₂ : SL(m + 1, F)) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
      (P : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = (P : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
        Matrix.diagonal (fun j => signOf F (ε j).1 * signOf F (ε j).2) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc, hP₂, ← Matrix.mul_assoc, hP₁,
      Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
  set blk : Fin m → Subgroup SL(m + 1, F) :=
    fun k => ((blockSL2 F m k).range).map (MulAut.conj P).toMonoidHom with hblk
  have hmem : ∀ k, blk k ∈ longRootSet (K := F) hn := fun k =>
    longRootSet_conjInvariant hn P _
      ⟨_, isLongRootSL2_range_blockSL h2 (by have := k.isLt; omega)⟩
  have hblock : ∀ (k : Fin m) (d : Fin (m + 1) → F) (i : SL(m + 1, F)),
      (i : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * (P : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
        (P : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * Matrix.diagonal d →
      d ⟨k.val, by omega⟩ = d ⟨k.val + 1, by have := k.isLt; omega⟩ →
      blk k ≤ Subgroup.centralizer ({i} : Set SL(m + 1, F)) := by
    intro k d i hi hd
    rintro _ ⟨y, ⟨B, rfl⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hy := diagonal_mul_blockMat_comm (j := k.val) d (fun a b ha hb => by
      have ha' : a = ⟨k.val, by omega⟩ ∨ a = ⟨k.val + 1, by have := k.isLt; omega⟩ := by
        rcases ha with ⟨ha1, ha2⟩
        rcases Nat.lt_or_ge a.val (k.val + 1) with h | h
        · exact Or.inl (Fin.ext (by simp only; omega))
        · exact Or.inr (Fin.ext (by simp only; omega))
      have hb' : b = ⟨k.val, by omega⟩ ∨ b = ⟨k.val + 1, by have := k.isLt; omega⟩ := by
        rcases hb with ⟨hb1, hb2⟩
        rcases Nat.lt_or_ge b.val (k.val + 1) with h | h
        · exact Or.inl (Fin.ext (by simp only; omega))
        · exact Or.inr (Fin.ext (by simp only; omega))
      rcases ha' with h | h <;> rcases hb' with h' | h' <;> rw [h, h'] <;>
        first | rfl | exact hd | exact hd.symm) (B : Matrix (Fin 2) (Fin 2) F)
    exact (commute_conj_of_diagonal d hi hy).symm
  have hcent : ∀ k : Fin m, blk k ≤ Subgroup.centralizer ({i₁} : Set SL(m + 1, F)) ∨
      blk k ≤ Subgroup.centralizer ({i₂} : Set SL(m + 1, F)) ∨
      blk k ≤ Subgroup.centralizer ({i₁ * i₂} : Set SL(m + 1, F)) := by
    intro k
    by_cases h1 : (ε ⟨k.val, by omega⟩).1 = (ε ⟨k.val + 1, by have := k.isLt; omega⟩).1
    · exact Or.inl (hblock k _ i₁ hP₁ (by simp only [h1]))
    · by_cases h2' : (ε ⟨k.val, by omega⟩).2 = (ε ⟨k.val + 1, by have := k.isLt; omega⟩).2
      · exact Or.inr (Or.inl (hblock k _ i₂ hP₂ (by simp only [h2'])))
      · exact Or.inr (Or.inr (hblock k _ (i₁ * i₂) hP₃ (signOf_mul_eq_of_ne h1 h2')))
  have hgen : (⊤ : Subgroup SL(m + 1, F)) ≤ ⨆ k, blk k := by
    have h1 : ⨆ k : Fin m, blk k =
        (⨆ k : Fin m, (blockSL2 F m k).range).map (MulAut.conj P).toMonoidHom := by
      rw [Subgroup.map_iSup]
    rw [h1, iSup_blockSL2_range_eq_top, Subgroup.map_top_of_surjective _ (MulAut.conj P).surjective]
  exact hgen.trans (iSup_le fun k =>
    le_iSup₂_of_le (blk k) (hmem k) (le_iSup_of_le (hcent k) le_rfl))

end Main

section Center

variable {K : Type} [Field K] {n : ℕ}

theorem mul_self_eq_one_of_mem_center_longRootSet {hn : 2 ≤ n} {R : Subgroup SL(n, K)}
    (hR : R ∈ longRootSet (K := K) hn) {c : SL(n, K)} (hc : c ∈ R)
    (hcc : ∀ r ∈ R, c * r = r * c) : c * c = 1 := by
  obtain ⟨g, rfl⟩ := (mem_longRootSet_iff hn).mp hR
  obtain ⟨y, hy, rfl⟩ := hc
  obtain ⟨B, rfl⟩ := hy
  have hBc : ∀ B' : SL(2, K), B' * B = B * B' := by
    intro B'
    have hmem : (MulAut.conj g) (blockSL K n 2 0 (by omega) B') ∈
        (rootSL2 K hn).map (MulAut.conj g).toMonoidHom := ⟨_, ⟨B', rfl⟩, rfl⟩
    have h := hcc _ hmem
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    have h' : blockSL K n 2 0 (by omega) B * blockSL K n 2 0 (by omega) B' =
        blockSL K n 2 0 (by omega) B' * blockSL K n 2 0 (by omega) B := by
      have h2 := congrArg (fun z => g⁻¹ * z * g) h
      simpa [mul_assoc] using h2
    exact (blockSL_injective _ (by simpa only [map_mul] using h')).symm
  have hBz : B ∈ Subgroup.center SL(2, K) := Subgroup.mem_center_iff.mpr hBc
  obtain ⟨r, hr, hrB⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hBz
  have hBB : B * B = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, ← hrB, ← map_mul, Matrix.SpecialLinearGroup.coe_one]
    have hr2 : r * r = 1 := by simpa [pow_two] using hr
    rw [hr2, map_one]
  have hy2 : blockSL K n 2 0 (by omega) B * blockSL K n 2 0 (by omega) B = 1 := by
    rw [← map_mul, hBB, map_one]
  rw [← map_mul, hy2, map_one]

end Center

section Model

variable {p : ℕ} [Fact p.Prime]

theorem commutingFundamentalGeneration_psl (hp2 : p ≠ 2) {n e : ℕ}
    (hadm : StatedLieAdmissible .PSL n p e) : CommutingFundamentalGeneration p .PSL n e := by
  have hn : 2 ≤ n := hadm.2.2.1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h2 : (2 : GaloisField p e) ≠ 0 := by
    intro h0
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField p e) p 2).1 (by exact_mod_cast h0)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 hdvd)
  intro R₁ hR₁ R₂ hR₂ c₁ hc₁ c₂ hc₂ hz₁ hz₂ hx₂₁ hx₁₂
  have hL₁ : R₁ ∈ longRootSet (K := GaloisField p e) hn := fundamentalSubgroups_psl_subset hn hR₁
  have hL₂ : R₂ ∈ longRootSet (K := GaloisField p e) hn := fundamentalSubgroups_psl_subset hn hR₂
  have hsq₁ : c₁ * c₁ = 1 := mul_self_eq_one_of_mem_center_longRootSet hL₁ hc₁ hz₁
  have hsq₂ : c₂ * c₂ = 1 := mul_self_eq_one_of_mem_center_longRootSet hL₂ hc₂ hz₂
  have hcomm : c₁ * c₂ = c₂ * c₁ := (hx₂₁ c₁ hc₁).symm
  refine (iSup_longRootSet_centralizing h2 hn hsq₁ hsq₂ hcomm).trans ?_
  exact iSup₂_le fun R hR =>
    le_iSup₂_of_le R (longRootSet_subset_fundamentalSubgroups_psl hn hR) le_rfl

end Model

end CFSG.ClassicalInvolution.ModelFacts
