module

public import CFSG.LieType.SeitzGeneration.OutdiagHeisGen
public import CFSG.LieType.SeitzGeneration.OuterUnitaryWide
public import CFSG.LieType.SeitzGeneration.UnitaryNonabPlane
public import CFSG.LieType.SeitzGeneration.HeisTorusUGen

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.ClassicalGroups.Unitary CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LieType.Universal.Unitary CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LieType.BorelTits
open HeisP

@[expose] def SingerTorusGenU {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    (p : ℕ) : Prop :=
  ∀ α : K, h.bar α * α = 1 → (¬ ∃ μ : K, μ ^ p = α) →
    ∀ H : Subgroup (GL (Fin p) K), H ≤ unitarySU ℓ f K p →
      (∀ g ∈ unitarySU ℓ f K p,
        (∃ t : Fin p → K, (g : Matrix (Fin p) (Fin p) K) = Matrix.diagonal t) → g ∈ H) →
      (∀ g ∈ unitarySU ℓ f K p,
        (g : Matrix (Fin p) (Fin p) K) * companionMat p α =
          companionMat p α * (g : Matrix (Fin p) (Fin p) K) → g ∈ H) →
      H = unitarySU ℓ f K p

section Nonsplit

variable {ℓ f n p : ℕ} {K : Type} [Field K]

theorem finRotate_eq_add_one_nonsplit [NeZero p] (b : Fin p) : finRotate p b = b + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := NeZero.pos p; omega⟩
  exact finRotate_succ_apply b

theorem gj_zero_eq_companionMat [NeZero p] (ζ α : K) :
    HeisP.Gj ζ α 0 = companionMat p α := by
  ext a b
  have hb := b.isLt
  have hperm : Equiv.Perm.permMatrix K (finRotate p).symm a b =
      if a = b + 1 then 1 else 0 := by
    show (finRotate p).symm.toPEquiv.toMatrix a b = _
    simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
      Equiv.symm_apply_eq, finRotate_eq_add_one_nonsplit]
  rw [HeisP.Gj_apply, companionMat]
  simp only [Matrix.mul_diagonal, Matrix.of_apply]
  rw [hperm]
  have hiff : ((b : ℕ) + 1 = p) ↔ ((b : ℕ) = p - 1) :=
    ⟨fun h' => by omega, fun h' => by omega⟩
  by_cases hab : a = b + 1
  · rw [if_pos hab, if_pos hab, zero_mul, pow_zero, one_mul, one_mul]
    by_cases hbp : (b : ℕ) + 1 = p
    · rw [if_pos hbp, if_pos (hiff.1 hbp)]
    · rw [if_neg hbp, if_neg (fun h' => hbp (hiff.2 h'))]
  · rw [if_neg hab, if_neg hab, zero_mul]

theorem heis_frame_unitary_alpha [Finite K] [Fact ℓ.Prime] [CharP K ℓ] [NeZero p]
    (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1)
    {X Y : Matrix (Fin p) (Fin p) K} {ζ α : K} (hζ : IsPrimitiveRoot ζ p) (hα0 : α ≠ 0)
    (hX : X ^ p = α • 1) (hY : Y ^ p = 1) (hYX : Y * X = ζ • (X * Y))
    (hXu : ∀ u v, herm (unitaryInvolution K ℓ f) (X *ᵥ u) (X *ᵥ v) =
      herm (unitaryInvolution K ℓ f) u v)
    (hYu : ∀ u v, herm (unitaryInvolution K ℓ f) (Y *ᵥ u) (Y *ᵥ v) =
      herm (unitaryInvolution K ℓ f) u v) :
    ∃ P : Matrix (Fin p) (Fin p) K,
      (∀ a b, ∑ i, h.bar (P i a) * P i b = if a = b then 1 else 0) ∧
        X * P = P * HeisP.Gj ζ α 0 ∧ Y * P = P * HeisP.Zm ζ := by
  obtain ⟨m, ⟨F⟩⟩ := exists_heisFrameP h hp hp2 hpq hζ hα0 hX hY hYX hXu hYu
  have hn := F.card_eq (Nonsplit.isUnitaryInvolution h).invol
  have hm1 : m = 1 := Nat.eq_of_mul_eq_mul_left hp.pos (hn.symm.trans (mul_one p).symm)
  subst hm1
  obtain ⟨P, hP, hXP, hYP⟩ := F.exists_matrix
  refine ⟨P, fun a b => ?_, hXP, hYP⟩
  have h2 := hP a b
  simpa only [Nonsplit.unitaryInvolution_eq_bar h] using h2

theorem eq_top_of_heis_core_nonsplit [Finite K] [Fact ℓ.Prime] [CharP K ℓ] [NeZero p]
    (h : UnitaryFieldData ℓ f K) (hS : SingerTorusGenU h p) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ ℓ ^ f + 1) {X Y : Matrix (Fin p) (Fin p) K} {ζ α : K}
    (hζ : IsPrimitiveRoot ζ p) (hα0 : α ≠ 0) (hαN : h.bar α * α = 1)
    (hαn : ¬ ∃ μ : K, μ ^ p = α)
    (hX3 : X ^ p = α • 1) (hY3 : Y ^ p = 1) (hYX : Y * X = ζ • (X * Y))
    (hXu : ∀ u v, herm (unitaryInvolution K ℓ f) (X *ᵥ u) (X *ᵥ v) =
      herm (unitaryInvolution K ℓ f) u v)
    (hYu : ∀ u v, herm (unitaryInvolution K ℓ f) (Y *ᵥ u) (Y *ᵥ v) =
      herm (unitaryInvolution K ℓ f) u v)
    {H : Subgroup (SUid (unitaryInvolution K ℓ f) p)}
    (hCY : HeisTensor.Cent H Y) (hCX : HeisTensor.Cent H X) : H = ⊤ := by
  classical
  obtain ⟨P, hPu, hXP, hYP⟩ := heis_frame_unitary_alpha h hp hp2 hpq hζ hα0 hX3 hY3 hYX hXu hYu
  obtain ⟨Q, hQdef⟩ : ∃ Q : Matrix (Fin p) (Fin p) K, Q = Matrix.of fun a i => h.bar (P i a) :=
    ⟨_, rfl⟩
  have hQP : Q * P = 1 := by
    ext a b
    rw [hQdef, Matrix.mul_apply, Matrix.one_apply]
    simpa using hPu a b
  have hPQ : P * Q = 1 := mul_eq_one_comm.mp hQP
  have hPT : (P.map h.bar)ᵀ = Q := by
    rw [hQdef]
    ext a i
    simp
  obtain ⟨Pu, hPu1, hPu2⟩ : ∃ Pu : GL (Fin p) K,
      (Pu : Matrix (Fin p) (Fin p) K) = P ∧
        ((Pu⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = Q :=
    ⟨⟨P, Q, hPQ, hQP⟩, rfl, rfl⟩
  have hPmem : Pu ∈ primeFormUnitary h (idGram K p) := by
    rw [mem_primeFormUnitary, hPu1]
    simp only [idGram, Units.val_one, Matrix.mul_one]
    rw [hPT, hQP]
  let Pe : primeFormUnitary h (idGram K p) := ⟨Pu, hPmem⟩
  let ψ : unitarySU ℓ f K p ≃* unitarySU ℓ f K p := CFSG.RankThree.PartOne.KFU.conjSU h Pe
  let ε : SUid (unitaryInvolution K ℓ f) p ≃* unitarySU ℓ f K p :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU h.card_eq_sq p)
  let K₁ : Subgroup (unitarySU ℓ f K p) := (H.comap ε.symm.toMonoidHom).comap ψ.toMonoidHom
  let H₁ : Subgroup (GL (Fin p) K) := K₁.map (unitarySU ℓ f K p).subtype
  have hcoe : ∀ x : unitarySU ℓ f K p,
      (((ψ x : unitarySU ℓ f K p) : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) =
        P * ((x : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) * Q := by
    intro x
    show (((CFSG.RankThree.PartOne.KFU.conjSU h Pe x : unitarySU ℓ f K p) :
        GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = _
    rw [CFSG.RankThree.PartOne.KFU.coe_conjSU, Units.val_mul, Units.val_mul]
    show (Pu : Matrix (Fin p) (Fin p) K) * ((x : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) *
      ((Pu⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = _
    rw [hPu1, hPu2]
  have hε : ∀ x : unitarySU ℓ f K p,
      ((ε.symm x : SUid (unitaryInvolution K ℓ f) p) : GL (Fin p) K) = (x : GL (Fin p) K) :=
    fun x => rfl
  have hYPQ : Y = P * HeisP.Zm ζ * Q := by
    calc Y = Y * (P * Q) := by rw [hPQ, Matrix.mul_one]
      _ = (Y * P) * Q := by rw [Matrix.mul_assoc]
      _ = P * HeisP.Zm ζ * Q := by rw [hYP]
  have hXPQ : X = P * HeisP.Gj ζ α 0 * Q := by
    calc X = X * (P * Q) := by rw [hPQ, Matrix.mul_one]
      _ = (X * P) * Q := by rw [Matrix.mul_assoc]
      _ = P * HeisP.Gj ζ α 0 * Q := by rw [hXP]
  have hle : H₁ ≤ unitarySU ℓ f K p := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.1 hx
    exact y.2
  have hdiag : ∀ g ∈ unitarySU ℓ f K p,
      (∃ t : Fin p → K, (g : Matrix (Fin p) (Fin p) K) = Matrix.diagonal t) → g ∈ H₁ := by
    rintro g hg ⟨t, ht⟩
    refine Subgroup.mem_map.2 ⟨⟨g, hg⟩, ?_, rfl⟩
    show ε.symm (ψ ⟨g, hg⟩) ∈ H
    refine hCY _ ?_
    show (((ε.symm (ψ ⟨g, hg⟩) : SUid (unitaryInvolution K ℓ f) p) : GL (Fin p) K) :
        Matrix (Fin p) (Fin p) K) * Y = Y *
      (((ε.symm (ψ ⟨g, hg⟩) : SUid (unitaryInvolution K ℓ f) p) : GL (Fin p) K) :
        Matrix (Fin p) (Fin p) K)
    rw [hε, hcoe, hYPQ]
    refine conj_mul_comm_aux hQP ?_
    show (g : Matrix (Fin p) (Fin p) K) * HeisP.Zm ζ = HeisP.Zm ζ * (g : Matrix (Fin p) (Fin p) K)
    rw [ht]
    exact diagonal_mul_Zm_comm t ζ
  have hcomp : ∀ g ∈ unitarySU ℓ f K p,
      (g : Matrix (Fin p) (Fin p) K) * companionMat p α =
        companionMat p α * (g : Matrix (Fin p) (Fin p) K) → g ∈ H₁ := by
    intro g hg hcg
    refine Subgroup.mem_map.2 ⟨⟨g, hg⟩, ?_, rfl⟩
    show ε.symm (ψ ⟨g, hg⟩) ∈ H
    refine hCX _ ?_
    show (((ε.symm (ψ ⟨g, hg⟩) : SUid (unitaryInvolution K ℓ f) p) : GL (Fin p) K) :
        Matrix (Fin p) (Fin p) K) * X = X *
      (((ε.symm (ψ ⟨g, hg⟩) : SUid (unitaryInvolution K ℓ f) p) : GL (Fin p) K) :
        Matrix (Fin p) (Fin p) K)
    rw [hε, hcoe, hXPQ]
    rw [← gj_zero_eq_companionMat ζ α] at hcg
    exact conj_mul_comm_aux hQP hcg
  have hH₁ : H₁ = unitarySU ℓ f K p := hS α hαN hαn H₁ hle hdiag hcomp
  have hK₁ : ∀ x : unitarySU ℓ f K p, x ∈ K₁ := by
    intro x
    have hx : (x : GL (Fin p) K) ∈ H₁ := by
      rw [hH₁]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
    have hxy : y = x := Subtype.ext hyx
    rw [← hxy]
    exact hy
  rw [eq_top_iff]
  intro z _
  have h2 : ε.symm (ψ (ψ.symm (ε z))) ∈ H := hK₁ (ψ.symm (ε z))
  simpa using h2

theorem eq_top_of_heis_pair_prime_nonsplit [Finite K] [Fact ℓ.Prime] [CharP K ℓ]
    (h : UnitaryFieldData ℓ f K) (hS : SingerTorusGenU h p) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ ℓ ^ f + 1) {g₀ g₁ : GL (Fin p) K} (hg₀ : g₀ ∈ primeFormUnitary h (idGram K p))
    (hg₁ : g₁ ∈ primeFormUnitary h (idGram K p)) {ζ ν α : K} (hζ : IsPrimitiveRoot ζ p)
    (hν0 : ν ≠ 0) (hνN : h.bar ν * ν = 1) (hα : ¬ ∃ μ : K, μ ^ p = α)
    (hg₀p : ((g₀ ^ p : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = (ν ^ p) • 1)
    (hg₁p : ((g₁ ^ p : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = α • 1)
    (hcomm : (g₀ : Matrix (Fin p) (Fin p) K) * (g₁ : Matrix (Fin p) (Fin p) K) =
      ζ • ((g₁ : Matrix (Fin p) (Fin p) K) * (g₀ : Matrix (Fin p) (Fin p) K)))
    {H : Subgroup (SUid (unitaryInvolution K ℓ f) p)}
    (h0 : HeisTensor.Cent H (g₀ : Matrix (Fin p) (Fin p) K))
    (h1 : HeisTensor.Cent H (g₁ : Matrix (Fin p) (Fin p) K)) : H = ⊤ := by
  classical
  have hp2 : p ≠ 2 := by omega
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hα0 : α ≠ 0 := scalar_ne_zero_of_pow hg₁p
  have hαN : h.bar α * α = 1 := bar_mul_eq_one_of_scalar_pow h (by omega) hg₁ hg₁p
  have hg₁m : (g₁ : Matrix (Fin p) (Fin p) K) ^ p = α • 1 := by
    rw [← Units.val_pow_eq_pow_val]
    exact hg₁p
  have hg₀m : (g₀ : Matrix (Fin p) (Fin p) K) ^ p = (ν ^ p) • 1 := by
    rw [← Units.val_pow_eq_pow_val]
    exact hg₀p
  have hY3 : (ν⁻¹ • (g₀ : Matrix (Fin p) (Fin p) K)) ^ p = 1 := by
    rw [smul_pow, hg₀m, smul_smul, inv_pow, inv_mul_cancel₀ (pow_ne_zero p hν0), one_smul]
  have hYX : (ν⁻¹ • (g₀ : Matrix (Fin p) (Fin p) K)) * (g₁ : Matrix (Fin p) (Fin p) K) =
      ζ • ((g₁ : Matrix (Fin p) (Fin p) K) * (ν⁻¹ • (g₀ : Matrix (Fin p) (Fin p) K))) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hcomm, smul_comm]
  have hXu : ∀ u v, herm (unitaryInvolution K ℓ f)
      (((g₁ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) *ᵥ u)
      (((g₁ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) *ᵥ v) =
        herm (unitaryInvolution K ℓ f) u v :=
    fun u v => HeisTensor.herm_mulVec_of_mem h hg₁ u v
  have hYu : ∀ u v, herm (unitaryInvolution K ℓ f)
      ((ν⁻¹ • (g₀ : Matrix (Fin p) (Fin p) K)) *ᵥ u)
      ((ν⁻¹ • (g₀ : Matrix (Fin p) (Fin p) K)) *ᵥ v) =
        herm (unitaryInvolution K ℓ f) u v := by
    intro u v
    rw [Matrix.smul_mulVec, Matrix.smul_mulVec, herm_smul_left, herm_smul_right,
      HeisTensor.herm_mulVec_of_mem h hg₀, ← mul_assoc, Nonsplit.unitaryInvolution_eq_bar h,
      map_inv₀, ← mul_inv, hνN, inv_one, one_mul]
  have hcY : HeisTensor.Cent H (ν⁻¹ • (g₀ : Matrix (Fin p) (Fin p) K)) :=
    h0.smul (inv_ne_zero hν0)
  exact eq_top_of_heis_core_nonsplit h hS hp hp2 hpq hζ hα0 hαN hα (hg₁m) hY3 hYX hXu hYu
    hcY h1

end Nonsplit

section Words

open CFSG.Open

variable {ℓ f n p : ℕ} {K : Type} [Field K]

theorem pth_power_of_pow_coprime {K : Type} [Field K] {p : ℕ} (hp : p.Prime) {β s : K}
    (hβ : β ≠ 0) {b : ℕ} (hb : ¬ p ∣ b) (hs : β ^ b = s ^ p) : ∃ t : K, t ^ p = β := by
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    ((Nat.Prime.coprime_iff_not_dvd hp).2 hb).symm hp.one_lt
  obtain ⟨k, hk⟩ : ∃ k : ℕ, b * m = p * k + 1 :=
    ⟨b * m / p, by have h1 := Nat.div_add_mod (b * m) p; rw [hm] at h1; exact h1.symm⟩
  have hpow : β ^ (b * m) = (s ^ m) ^ p := by
    rw [pow_mul, hs, ← pow_mul, ← pow_mul, mul_comm]
  have hpow2 : β ^ (b * m) = (β ^ k) ^ p * β := by
    rw [hk, pow_succ, pow_mul']
  have key : (β ^ k) ^ p * β = (s ^ m) ^ p := hpow2.symm.trans hpow
  have hne : (β ^ k) ^ p ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hβ)
  refine ⟨s ^ m * (β ^ k)⁻¹, ?_⟩
  rw [mul_pow, inv_pow, ← key, mul_comm ((β ^ k) ^ p) β, mul_assoc, mul_inv_cancel₀ hne,
    mul_one]

theorem dvd_card_sub_one_of_unitary {ℓ f p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hpq : p ∣ ℓ ^ f + 1) : p ∣ Nat.card K - 1 := by
  rw [UnitaryFieldData.card_eq_sq h]
  obtain ⟨m, hm⟩ : ∃ m, ℓ ^ f = m + 1 :=
    ⟨ℓ ^ f - 1, by have := pow_pos h.prime.pos f; omega⟩
  rw [hm] at hpq ⊢
  have hsq : (m + 1) ^ 2 - 1 = (m + 1 + 1) * m := Nat.sub_eq_of_eq_add (by ring)
  rw [hsq]
  exact Dvd.dvd.mul_right hpq m

theorem hind_of_indep (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n) (hp : p.Prime)
    {E : Subgroup (MulAut (primeFormP h (idGram K n)))} (hE : IsElemAbelian p E)
    {A B : primeFormUnitary h (idGram K n)}
    (hAE : primeFormConjHom h (idGram K n) A ∈ E) (hBE : primeFormConjHom h (idGram K n) B ∈ E)
    (hB1 : primeFormConjHom h (idGram K n) B ≠ 1)
    (hAB : primeFormConjHom h (idGram K n) A ∉
      Subgroup.zpowers (primeFormConjHom h (idGram K n) B)) :
    ∀ a b : ℕ, (∃ c : K, (((A : GL (Fin n) K) ^ a * (B : GL (Fin n) K) ^ b : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = c • 1) → p ∣ a ∧ p ∣ b := by
  classical
  rintro a b ⟨c, hc⟩
  have hn0 : 0 < n := by omega
  obtain ⟨u, hu⟩ := exists_scalarGL_of_coe_eq hn0 hc
  have hmem : (A : GL (Fin n) K) ^ a * (B : GL (Fin n) K) ^ b ∈
      primeFormUnitary h (idGram K n) := mul_mem (pow_mem A.2 a) (pow_mem B.2 b)
  have hnorm : h.norm (u : K) = 1 :=
    norm_eq_one_of_scalar_mem_primeFormUnitary h (by omega) 1 (hu ▸ hmem)
  have h1 : primeFormConjHom h (idGram K n) (A ^ a * B ^ b) = 1 := by
    refine (OuterUnitaryWide.conjHom_eq_one_iff h hn _).2 ⟨u, hnorm, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow]
    exact hu
  rw [map_mul, map_pow, map_pow] at h1
  exact dvd_of_pow_mul_pow_eq_one_p hp (hE.2 _ hAE) (hE.2 _ hBE) hB1 hAB h1

theorem planeGen_of_words (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    {E : Subgroup (MulAut (primeFormP h (idGram K n)))} {A B : primeFormUnitary h (idGram K n)}
    (hAE : primeFormConjHom h (idGram K n) A ∈ E)
    (hBE : primeFormConjHom h (idGram K n) B ∈ E)
    (hind : ∀ a b : ℕ, (∃ c : K, (((A : GL (Fin n) K) ^ a * (B : GL (Fin n) K) ^ b : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = c • 1) → p ∣ a ∧ p ∣ b)
    (hcl : Subgroup.closure {g : unitarySU ℓ f K n | ∃ a b : ℕ, ¬ (p ∣ a ∧ p ∣ b) ∧
      g ∈ FixUn ℓ f n K (((A : GL (Fin n) K) ^ a * (B : GL (Fin n) K) ^ b : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K)} = ⊤) : PlaneGen E := by
  classical
  apply OuterUnitaryWide.planeGen_of_closure_fixUn h hn
  rw [eq_top_iff, ← hcl]
  refine Subgroup.closure_mono ?_
  rintro g ⟨a, b, hab, hg⟩
  have hDE : primeFormConjHom h (idGram K n) (A ^ a * B ^ b) ∈ E := by
    rw [map_mul, map_pow, map_pow]
    exact E.mul_mem (E.pow_mem hAE a) (E.pow_mem hBE b)
  have hD1 : primeFormConjHom h (idGram K n) (A ^ a * B ^ b) ≠ 1 := by
    intro h1
    obtain ⟨c, -, hc⟩ := (OuterUnitaryWide.conjHom_eq_one_iff h hn (A ^ a * B ^ b)).1 h1
    apply hab
    apply hind a b
    refine ⟨c, ?_⟩
    have := congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) hc
    simpa only [Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val,
      coe_scalarGL] using this
  exact ⟨A ^ a * B ^ b, hDE, hD1, hg⟩

theorem closure_eq_top_of_cent [Finite K] [Fact ℓ.Prime] [CharP K ℓ] (h : UnitaryFieldData ℓ f K)
    (S : Set (unitarySU ℓ f K n)) {M₀ M₁ : Matrix (Fin n) (Fin n) K}
    (h0 : ∀ g : unitarySU ℓ f K n,
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M₀ = M₀ * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →
      g ∈ Subgroup.closure S)
    (h1 : ∀ g : unitarySU ℓ f K n,
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M₁ = M₁ * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →
      g ∈ Subgroup.closure S)
    (htop : ∀ H : Subgroup (SUid (unitaryInvolution K ℓ f) n), HeisTensor.Cent H M₀ →
      HeisTensor.Cent H M₁ → H = ⊤) :
    Subgroup.closure S = ⊤ := by
  classical
  let ε : SUid (unitaryInvolution K ℓ f) n ≃* unitarySU ℓ f K n :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU h.card_eq_sq n)
  have hH := htop ((Subgroup.closure S).comap ε.toMonoidHom)
    (fun g hg => h0 (ε g) hg) (fun g hg => h1 (ε g) hg)
  rw [eq_top_iff]
  intro z _
  have hz : ε.symm z ∈ (Subgroup.closure S).comap ε.toMonoidHom := by
    rw [hH]
    exact Subgroup.mem_top _
  simpa using hz

end Words

section Outer

open CFSG.Open

theorem word_comm_left {n : ℕ} {K : Type} [Field K] {Am Bm : Matrix (Fin n) (Fin n) K} {c : K}
    (hBA : Bm * Am = c • (Am * Bm)) (a b : ℕ) :
    (Am ^ a * Bm ^ b) * Am = c ^ b • (Am * (Am ^ a * Bm ^ b)) := by
  calc (Am ^ a * Bm ^ b) * Am = Am ^ a * (Bm ^ b * Am) := by rw [Matrix.mul_assoc]
    _ = Am ^ a * (c ^ b • (Am * Bm ^ b)) := by rw [qcommMat_pow_left hBA b]
    _ = c ^ b • (Am ^ a * (Am * Bm ^ b)) := by rw [Matrix.mul_smul]
    _ = c ^ b • (Am * (Am ^ a * Bm ^ b)) := by rw [mat_pow_mul_comm]

theorem word_comm_right {n : ℕ} {K : Type} [Field K] {Am Bm : Matrix (Fin n) (Fin n) K} {c : K}
    (hBA : Bm * Am = c • (Am * Bm)) (a b : ℕ) :
    Bm * (Am ^ a * Bm ^ b) = c ^ a • ((Am ^ a * Bm ^ b) * Bm) := by
  have hBAa : Bm * Am ^ a = c ^ a • (Am ^ a * Bm) := by
    have := qcommMat_pow_pow hBA a 1
    simpa only [pow_one, mul_one] using this
  calc Bm * (Am ^ a * Bm ^ b) = (Bm * Am ^ a) * Bm ^ b := by rw [Matrix.mul_assoc]
    _ = (c ^ a • (Am ^ a * Bm)) * Bm ^ b := by rw [hBAa]
    _ = c ^ a • ((Am ^ a * Bm) * Bm ^ b) := by rw [Matrix.smul_mul]
    _ = c ^ a • (Am ^ a * (Bm * Bm ^ b)) := by rw [Matrix.mul_assoc]
    _ = c ^ a • (Am ^ a * (Bm ^ b * Bm)) := by rw [(Commute.self_pow Bm b).eq]
    _ = c ^ a • ((Am ^ a * Bm ^ b) * Bm) := by rw [Matrix.mul_assoc]

variable {ℓ f n p : ℕ} {K : Type} [Field K]

theorem mem_planeFixUnW_of {x y : GL (Fin n) K} {g : unitarySU ℓ f K n} {a b : ℕ}
    (hab : ¬ (p ∣ a ∧ p ∣ b))
    (hg : g ∈ FixUn ℓ f n K (((x ^ a * y ^ b : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)) :
    g ∈ planeFixUnW ℓ f n p K x y := by
  unfold planeFixUnW
  exact ⟨a, b, hab, hg⟩

theorem closure_eq_top_of_heis_pair [Finite K] [Fact ℓ.Prime] [CharP K ℓ]
    (h : UnitaryFieldData ℓ f K) (hS : SingerTorusGenU h p) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ ℓ ^ f + 1) {g₀ g₁ : GL (Fin p) K} (hg₀ : g₀ ∈ primeFormUnitary h (idGram K p))
    (hg₁ : g₁ ∈ primeFormUnitary h (idGram K p)) {ζ ν α : K} (hζ : IsPrimitiveRoot ζ p)
    (hν0 : ν ≠ 0) (hνN : h.bar ν * ν = 1) (hα : ¬ ∃ μ : K, μ ^ p = α)
    (hg₀p : ((g₀ ^ p : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = (ν ^ p) • 1)
    (hg₁p : ((g₁ ^ p : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = α • 1)
    (hcomm : (g₀ : Matrix (Fin p) (Fin p) K) * (g₁ : Matrix (Fin p) (Fin p) K) =
      ζ • ((g₁ : Matrix (Fin p) (Fin p) K) * (g₀ : Matrix (Fin p) (Fin p) K)))
    {S : Set (unitarySU ℓ f K p)}
    (hS₀ : ∀ g : unitarySU ℓ f K p,
      ((g : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) * (g₀ : Matrix (Fin p) (Fin p) K) =
        (g₀ : Matrix (Fin p) (Fin p) K) * ((g : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) →
      g ∈ Subgroup.closure S)
    (hS₁ : ∀ g : unitarySU ℓ f K p,
      ((g : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) * (g₁ : Matrix (Fin p) (Fin p) K) =
        (g₁ : Matrix (Fin p) (Fin p) K) * ((g : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) →
      g ∈ Subgroup.closure S) :
    Subgroup.closure S = ⊤ :=
  closure_eq_top_of_cent h S hS₀ hS₁ (fun H h0 h1 =>
    eq_top_of_heis_pair_prime_nonsplit h hS hp hp5 hpq hg₀ hg₁ hζ hν0 hνN hα hg₀p hg₁p hcomm
      h0 h1)

theorem outer_heis_five_prime {ℓ f p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hS : SingerTorusGenU h p) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ ℓ ^ f + 1) {E : Subgroup (MulAut (primeFormP h (idGram K p)))}
    (hE : IsElemAbelian p E) {A B : primeFormUnitary h (idGram K p)}
    (hAE : primeFormConjHom h (idGram K p) A ∈ E) (hBE : primeFormConjHom h (idGram K p) B ∈ E)
    (hB1 : primeFormConjHom h (idGram K p) B ≠ 1)
    (hAB : primeFormConjHom h (idGram K p) A ∉
      Subgroup.zpowers (primeFormConjHom h (idGram K p) B))
    {α β : Kˣ}
    (hx3 : (((A : GL (Fin p) K) ^ p : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = (α : K) • 1)
    (hy3 : (((B : GL (Fin p) K) ^ p : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = (β : K) • 1)
    {c : K}
    (hBAm : ((B : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) *
      ((A : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) =
        c • (((A : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) *
          ((B : GL (Fin p) K) : Matrix (Fin p) (Fin p) K)))
    (hc1 : c ≠ 1) (hcp : c ^ p = 1) (hprim : IsPrimitiveRoot c p) : PlaneGen E := by
  classical
  haveI : Finite K := h.finite
  haveI : Fact ℓ.Prime := ⟨h.prime⟩
  haveI : CharP K ℓ := h.charP
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hn3 : 3 ≤ p := by omega
  have hp2 : p ≠ 2 := by omega
  have hn0 : 0 < p := by omega
  have hind := hind_of_indep h hn3 hp hE hAE hBE hB1 hAB
  have hα0 : (α : K) ≠ 0 := α.ne_zero
  have hβ0 : (β : K) ≠ 0 := β.ne_zero
  have hx3m : ((A : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) ^ p = (α : K) • 1 := by
    rw [← Units.val_pow_eq_pow_val]
    exact hx3
  have hy3m : ((B : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) ^ p = (β : K) • 1 := by
    rw [← Units.val_pow_eq_pow_val]
    exact hy3
  by_cases hboth : (∃ μ : K, μ ^ p = (α : K)) ∧ (∃ ν : K, ν ^ p = (β : K))
  · have hT : TorusFourierGenU h p := torusFourierGenU_of_prime h hp5 hpq
    have hcl := closure_planeFixUnW_gu h hT hp hp5 hpq hn3 A.2 B.2 hα0 hβ0 hx3 hy3 hBAm hind
      (fun _ _ => hboth)
    exact planeGen_of_words h hn3 hAE hBE hind hcl
  · have hpK : p ∣ Nat.card K - 1 := dvd_card_sub_one_of_unitary h hpq
    obtain ⟨a, b, hab_nd, ν, hν⟩ := exists_pth_power_word hp hpK hα0 hβ0
    have hν0 : ν ≠ 0 := by
      rintro rfl
      exact mul_ne_zero (pow_ne_zero a hα0) (pow_ne_zero b hβ0)
        (by rw [← hν, zero_pow hp.ne_zero])
    have hy₁m : (((A ^ a * B ^ b : primeFormUnitary h (idGram K p)) : GL (Fin p) K) :
        Matrix (Fin p) (Fin p) K) = ((A : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) ^ a *
          ((B : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) ^ b := by
      simp only [Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val]
    have hy₁p : ((((A ^ a * B ^ b : primeFormUnitary h (idGram K p)) : GL (Fin p) K) ^ p :
        GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = (ν ^ p) • 1 := by
      rw [Units.val_pow_eq_pow_val, hy₁m, pow_word_p hp hp2 hx3m hy3m hBAm hcp a b, hν]
    have hyN : h.bar (ν ^ p) * ν ^ p = 1 :=
      bar_mul_eq_one_of_scalar_pow h (by omega) (A ^ a * B ^ b : primeFormUnitary h (idGram K p)).2
        hy₁p
    have hνN : h.bar ν * ν = 1 := by
      have hα' : (ν ^ p) ^ (ℓ ^ f + 1) = 1 := by
        rw [h.bar_apply, ← pow_succ] at hyN
        exact hyN
      exact bar_mul_eq_one_of_pow_eq h hp hp2 hpq hν0 rfl hα'
    have hnd10 : ¬ (p ∣ 1 ∧ p ∣ 0) := fun h1 => hp.one_lt.ne' (Nat.dvd_one.1 h1.1)
    have hnd01 : ¬ (p ∣ 0 ∧ p ∣ 1) := fun h1 => hp.one_lt.ne' (Nat.dvd_one.1 h1.2)
    by_cases hpb : p ∣ b
    ·
      have hpa : ¬ p ∣ a := fun h1 => hab_nd ⟨h1, hpb⟩
      have hcop : Nat.Coprime a p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpa).symm
      have hζ : IsPrimitiveRoot (c ^ a)⁻¹ p := (hprim.pow_of_coprime a hcop).inv
      have hc0 : c ≠ 0 := hprim.ne_zero (by omega)
      have hcomm2 : (((A ^ a * B ^ b : primeFormUnitary h (idGram K p)) : GL (Fin p) K) :
          Matrix (Fin p) (Fin p) K) * ((B : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) =
            (c ^ a)⁻¹ • (((B : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) *
              (((A ^ a * B ^ b : primeFormUnitary h (idGram K p)) : GL (Fin p) K) :
                Matrix (Fin p) (Fin p) K)) := by
        rw [hy₁m, word_comm_right hBAm a b, smul_smul, inv_mul_cancel₀ (pow_ne_zero a hc0),
          one_smul]
      have hβ_n : ¬ ∃ μ : K, μ ^ p = (β : K) := by
        rintro ⟨μ, hμ⟩
        obtain ⟨k, hk⟩ := hpb
        have hne : ((β : K) ^ k) ^ p ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hβ0)
        have hαa : (α : K) ^ a = (ν * ((β : K) ^ k)⁻¹) ^ p := by
          rw [mul_pow, inv_pow, hν, hk, pow_mul', mul_inv_cancel_right₀ hne]
        exact hboth ⟨pth_power_of_pow_coprime hp hα0 hpa hαa, ⟨μ, hμ⟩⟩
      have hgen : Subgroup.closure (planeFixUnW ℓ f p p K (A : GL (Fin p) K) (B : GL (Fin p) K)) =
          ⊤ :=
        closure_eq_top_of_heis_pair h hS hp hp5 hpq
          (A ^ a * B ^ b : primeFormUnitary h (idGram K p)).2 B.2 hζ hν0 hνN hβ_n hy₁p hy3 hcomm2
          (fun g hg => Subgroup.subset_closure (mem_planeFixUnW_of hab_nd (mem_FixUn_of_mul_comm hg)))
          (fun g hg => Subgroup.subset_closure (mem_planeFixUnW_of (a := 0) (b := 1) hnd01
            (by rw [pow_zero, pow_one, one_mul]; exact mem_FixUn_of_mul_comm hg)))
      exact planeGen_of_words h hn3 hAE hBE hind hgen
    ·
      have hcop : Nat.Coprime b p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpb).symm
      have hζ : IsPrimitiveRoot (c ^ b) p := hprim.pow_of_coprime b hcop
      have hcomm1 : (((A ^ a * B ^ b : primeFormUnitary h (idGram K p)) : GL (Fin p) K) :
          Matrix (Fin p) (Fin p) K) * ((A : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) =
            (c ^ b) • (((A : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) *
              (((A ^ a * B ^ b : primeFormUnitary h (idGram K p)) : GL (Fin p) K) :
                Matrix (Fin p) (Fin p) K)) := by
        rw [hy₁m]
        exact word_comm_left hBAm a b
      have hα_n : ¬ ∃ μ : K, μ ^ p = (α : K) := by
        rintro ⟨μ, hμ⟩
        have hβb : (β : K) ^ b = (ν * (μ ^ a)⁻¹) ^ p := by
          rw [mul_pow, inv_pow, hν, ← pow_mul, mul_comm a p, pow_mul, hμ]
          rw [mul_comm ((α : K) ^ a) ((β : K) ^ b), mul_assoc,
            mul_inv_cancel₀ (pow_ne_zero a hα0), mul_one]
        exact hboth ⟨⟨μ, hμ⟩, pth_power_of_pow_coprime hp hβ0 hpb hβb⟩
      have hgen : Subgroup.closure (planeFixUnW ℓ f p p K (A : GL (Fin p) K) (B : GL (Fin p) K)) =
          ⊤ :=
        closure_eq_top_of_heis_pair h hS hp hp5 hpq
          (A ^ a * B ^ b : primeFormUnitary h (idGram K p)).2 A.2 hζ hν0 hνN hα_n hy₁p hx3 hcomm1
          (fun g hg => Subgroup.subset_closure (mem_planeFixUnW_of hab_nd (mem_FixUn_of_mul_comm hg)))
          (fun g hg => Subgroup.subset_closure (mem_planeFixUnW_of (a := 1) (b := 0) hnd10
            (by rw [pow_one, pow_zero, mul_one]; exact mem_FixUn_of_mul_comm hg)))
      exact planeGen_of_words h hn3 hAE hBE hind hgen

theorem unitaryOuterAbFive_holds : UnitaryOuterAbFive := by
  intro ℓ f n p K _ h hp5 hn4 hp hpq hpn E hE hc hD hout hab
  classical
  haveI : Finite K := h.finite
  haveI : Fact ℓ.Prime := ⟨h.prime⟩
  haveI : CharP K ℓ := h.charP
  haveI : Fact p.Prime := ⟨hp⟩
  have hn3 : 3 ≤ n := by omega
  have hp2 : p ≠ 2 := by omega
  obtain ⟨e₁, he₁, e₂, he₂, he₂1, he₁₂⟩ := exists_independent_pair hp E hE.2 hc
  obtain ⟨A₁, hA₁⟩ : ∃ A : primeFormUnitary h (idGram K n),
      primeFormConjHom h (idGram K n) A = e₁ := hD he₁
  obtain ⟨A₂, hA₂⟩ : ∃ A : primeFormUnitary h (idGram K n),
      primeFormConjHom h (idGram K n) A = e₂ := hD he₂
  have hA₁E : primeFormConjHom h (idGram K n) A₁ ∈ E := hA₁ ▸ he₁
  have hA₂E : primeFormConjHom h (idGram K n) A₂ ∈ E := hA₂ ▸ he₂
  have hB1 : primeFormConjHom h (idGram K n) A₂ ≠ 1 := by
    rw [hA₂]
    exact he₂1
  have hAB : primeFormConjHom h (idGram K n) A₁ ∉
      Subgroup.zpowers (primeFormConjHom h (idGram K n) A₂) := by
    rw [hA₁, hA₂]
    exact he₁₂
  have hind := hind_of_indep h hn3 hp hE hA₁E hA₂E hB1 hAB
  have hcomm : A₁ * A₂ = A₂ * A₁ := hab A₁ A₂ hA₁E hA₂E
  have hcube : ∀ A : primeFormUnitary h (idGram K n),
      primeFormConjHom h (idGram K n) A ∈ E →
      ∃ α : Kˣ, ((A : GL (Fin n) K) ^ p : GL (Fin n) K) =
        Matrix.GeneralLinearGroup.scalar (Fin n) α := by
    intro A hA
    have h1 : primeFormConjHom h (idGram K n) (A ^ p) = 1 := by
      rw [map_pow]
      exact hE.2 _ hA
    obtain ⟨c, -, hc'⟩ := (OuterUnitaryWide.conjHom_eq_one_iff h hn3 (A ^ p)).1 h1
    exact ⟨c, hc'⟩
  obtain ⟨α, hα⟩ := hcube A₁ hA₁E
  obtain ⟨β, hβ⟩ := hcube A₂ hA₂E
  have hx3 : (((A₁ : GL (Fin n) K) ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (α : K) • 1 := by
    rw [hα]
    exact coe_scalarGL α
  have hy3 : (((A₂ : GL (Fin n) K) ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (β : K) • 1 := by
    rw [hβ]
    exact coe_scalarGL β
  have hc1 : ((A₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A₁ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (1 : K) •
        (((A₁ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((A₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    rw [one_smul]
    have := congrArg (fun x : primeFormUnitary h (idGram K n) =>
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hcomm.symm
    simpa only [Subgroup.coe_mul, Units.val_mul] using this
  have hT : TorusFourierGenU h p := torusFourierGenU_of_prime h hp5 hpq
  have hcl := closure_planeFixUnW_gu h hT hp hp5 hpq hn3 A₁.2 A₂.2 α.ne_zero β.ne_zero hx3 hy3
    hc1 hind (fun _ hne => absurd rfl hne)
  exact planeGen_of_words h hn3 hA₁E hA₂E hind hcl

theorem unitaryOuterHeisFive_of_singerU
    (hS : ∀ (ℓ f : ℕ) (K : Type) [Field K] (h : UnitaryFieldData ℓ f K) (p : ℕ), p.Prime →
      5 ≤ p → p ∣ ℓ ^ f + 1 → SingerTorusGenU h p) :
    UnitaryOuterHeisFive := by
  intro ℓ f n p K _ h hp5 hn4 hp hp2 hpq hpn E hE hc hD hout hab
  classical
  haveI : Finite K := h.finite
  haveI : Fact ℓ.Prime := ⟨h.prime⟩
  haveI : CharP K ℓ := h.charP
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hn3 : 3 ≤ n := by omega
  have hn0 : 0 < n := by omega
  unfold DiagLiftsCommute at hab
  push Not at hab
  obtain ⟨A, B, hAE, hBE, hAB⟩ := hab
  have hB1 : primeFormConjHom h (idGram K n) B ≠ 1 := by
    intro h1
    apply hAB
    obtain ⟨c, -, hc'⟩ := (OuterUnitaryWide.conjHom_eq_one_iff h hn3 B).1 h1
    apply Subtype.ext
    change (A : GL (Fin n) K) * B = B * A
    rw [hc']
    exact (commute_scalar c (A : GL (Fin n) K)).eq
  have hcomm' : primeFormConjHom h (idGram K n) A * primeFormConjHom h (idGram K n) B =
      primeFormConjHom h (idGram K n) B * primeFormConjHom h (idGram K n) A :=
    congrArg Subtype.val (hE.1.is_comm.comm (⟨_, hAE⟩ : E) ⟨_, hBE⟩)
  have hAB' : primeFormConjHom h (idGram K n) A ∉
      Subgroup.zpowers (primeFormConjHom h (idGram K n) B) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have h1 : primeFormConjHom h (idGram K n) (A * (B ^ k)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_zpow, hk, mul_inv_cancel]
    obtain ⟨c, -, hc'⟩ := (OuterUnitaryWide.conjHom_eq_one_iff h hn3 (A * (B ^ k)⁻¹)).1 h1
    have hc'' : (A : GL (Fin n) K) * ((B : GL (Fin n) K) ^ k)⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin n) c := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow] using hc'
    have hA : (A : GL (Fin n) K) =
        Matrix.GeneralLinearGroup.scalar (Fin n) c * (B : GL (Fin n) K) ^ k :=
      mul_inv_eq_iff_eq_mul.1 hc''
    have hcS : Commute (B : GL (Fin n) K) (Matrix.GeneralLinearGroup.scalar (Fin n) c) :=
      commute_scalar c _
    have hcB : Commute ((B : GL (Fin n) K) ^ k) (B : GL (Fin n) K) :=
      (Commute.refl (B : GL (Fin n) K)).zpow_left k
    have hcomm2 : Commute (Matrix.GeneralLinearGroup.scalar (Fin n) c * (B : GL (Fin n) K) ^ k)
        (B : GL (Fin n) K) := hcS.symm.mul_left hcB
    apply hAB
    apply Subtype.ext
    change (A : GL (Fin n) K) * B = B * A
    rw [hA]
    exact hcomm2.eq
  obtain ⟨c, -, hcBA⟩ : ∃ c : Kˣ, h.norm (c : K) = 1 ∧
      ((B * A * (A * B)⁻¹ : primeFormUnitary h (idGram K n)) : GL (Fin n) K) =
        Matrix.GeneralLinearGroup.scalar (Fin n) c := by
    refine (OuterUnitaryWide.conjHom_eq_one_iff h hn3 _).1 ?_
    rw [map_mul, map_mul, map_inv, map_mul, hcomm']
    exact mul_inv_cancel _
  have hBA : (B : GL (Fin n) K) * A =
      Matrix.GeneralLinearGroup.scalar (Fin n) c * ((A : GL (Fin n) K) * B) := by
    have : (B : GL (Fin n) K) * A * ((A : GL (Fin n) K) * B)⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin n) c := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hcBA
    rw [← this]
    group
  have hBAm : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (c : K) • (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hBA
    simp only [Units.val_mul, coe_scalarGL, Matrix.smul_mul, Matrix.one_mul] at this
    exact this
  have hc1 : (c : K) ≠ 1 := by
    intro h1
    apply hAB
    have hcu : c = 1 := Units.ext h1
    apply Subtype.ext
    change (A : GL (Fin n) K) * B = B * A
    rw [hBA, hcu, map_one, one_mul]
  have hcube : ∀ C : primeFormUnitary h (idGram K n),
      primeFormConjHom h (idGram K n) C ∈ E →
      ∃ α : Kˣ, ((C : GL (Fin n) K) ^ p : GL (Fin n) K) =
        Matrix.GeneralLinearGroup.scalar (Fin n) α := by
    intro C hC
    have h1 : primeFormConjHom h (idGram K n) (C ^ p) = 1 := by
      rw [map_pow]
      exact hE.2 _ hC
    obtain ⟨d, -, hd⟩ := (OuterUnitaryWide.conjHom_eq_one_iff h hn3 (C ^ p)).1 h1
    exact ⟨d, hd⟩
  obtain ⟨α, hα⟩ := hcube A hAE
  obtain ⟨β, hβ⟩ := hcube B hBE
  have hx3 : (((A : GL (Fin n) K) ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (α : K) • 1 := by
    rw [hα]
    exact coe_scalarGL α
  have hy3 : (((B : GL (Fin n) K) ^ p : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (β : K) • 1 := by
    rw [hβ]
    exact coe_scalarGL β
  have hcp : (c : K) ^ p = 1 := pow_eq_one_of_smul_comm_p hn0 α.ne_zero hx3 hBAm
  have hprim : IsPrimitiveRoot (c : K) p := by
    have h1 := IsPrimitiveRoot.orderOf (c : K)
    rwa [orderOf_eq_prime hcp hc1] at h1
  by_cases hnp : n = p
  · subst hnp
    exact outer_heis_five_prime h (hS _ _ _ h _ hp hp5 hpq) hp hp5 hpq hE hAE hBE hB1 hAB' hx3
      hy3 hBAm hc1 hcp hprim
  · have hT : TorusFourierGenU h p := torusFourierGenU_of_prime h hp5 hpq
    have hind := hind_of_indep h hn3 hp hE hAE hBE hB1 hAB'
    have hexcl : n = p → (c : K) ≠ 1 → (∃ μ : K, μ ^ p = (α : K)) ∧
        ∃ ν : K, ν ^ p = (β : K) := fun hn' _ => absurd hn' hnp
    have hcl := closure_planeFixUnW_gu h hT hp hp5 hpq hn3 A.2 B.2 α.ne_zero β.ne_zero hx3 hy3
      hBAm hind hexcl
    exact planeGen_of_words h hn3 hAE hBE hind hcl

end Outer

end CFSG.LieType.SeitzGeneration

end
