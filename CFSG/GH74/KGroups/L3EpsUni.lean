module

public import CFSG.GH74.KGroups.L3EpsTest
public import CFSG.GH74.KGroups.L3EpsAbs
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
public import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.ClassicalGroups.Unitary.Finite
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.GH74.KGroups.L3Eps

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped MatrixGroups

section Uni

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

local notation "𝟙" => ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)

@[expose] noncomputable def thetaU (A : primeFormUnitary h 𝟙) (σ : K ≃+* K) :
    MulAut (gramSU h 𝟙) :=
  primeFormConjSU h 𝟙 A * primeFormFieldSU h isPrimeFormGram_one σ

theorem psi_apply_mk (A : primeFormUnitary h 𝟙) (σ : K ≃+* K) (g : gramSU h 𝟙) :
    (primeFormConjHom h 𝟙 A * primeFormFieldHom h isPrimeFormGram_one σ :
        MulAut (primeFormP h 𝟙)) (g : primeFormP h 𝟙) =
      ((thetaU h A σ g : gramSU h 𝟙) : primeFormP h 𝟙) := by
  rw [MulAut.mul_apply]
  change primeFormConjAut h 𝟙 A (primeFormFieldAut h isPrimeFormGram_one σ _) = _
  rw [primeFormFieldAut_mk, primeFormConjAut_mk]
  rfl

theorem coe_thetaU (A : primeFormUnitary h 𝟙) (σ : K ≃+* K) (g : gramSU h 𝟙) :
    (((thetaU h A σ g : gramSU h 𝟙) : GL (Fin 3) K)) =
      (A : GL (Fin 3) K) * glAut σ (g : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹ := rfl

theorem trace_conj_gl' (A : GL (Fin 3) K) (M : Matrix (Fin 3) (Fin 3) K) :
    ((A : Matrix (Fin 3) (Fin 3) K) * M * ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).trace =
      M.trace := by
  rw [Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

theorem trace_thetaU (A : primeFormUnitary h 𝟙) (σ : K ≃+* K) (g : gramSU h 𝟙) :
    (((thetaU h A σ g : gramSU h 𝟙) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace =
      σ (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace) := by
  rw [coe_thetaU, Units.val_mul, Units.val_mul, trace_conj_gl', coe_glAut]
  exact (AddMonoidHom.map_trace (σ : K →+* K).toAddMonoidHom _).symm

theorem eq_of_mk_eq_u {a b : gramSU h 𝟙} {j : ℕ} (ha : a ^ 2 ^ j = 1) (hb : b ^ 2 ^ j = 1)
    (hab : (a : primeFormP h 𝟙) = b) : a = b := by
  refine eq_of_pow_eq_one_of_central (QuotientGroup.mk' (normOneScalars h (gramSU h 𝟙) 3))
    (normOneScalars h (gramSU h 𝟙) 3) (normOneScalars_le_center h _ 3) ?_
    (fun a b hab => QuotientGroup.eq.1 hab) ha hb hab
  intro s hs
  obtain ⟨c, -, hc, hsc⟩ := mem_normOneScalars.1 hs
  apply Subtype.ext
  rw [Subgroup.coe_pow, hsc, ← map_pow, hc, map_one]
  rfl

theorem trace_conj_u (x g : gramSU h 𝟙) :
    ((((x⁻¹ * g * x : gramSU h 𝟙) : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K).trace =
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace := by
  have e : (((x⁻¹ * g * x : gramSU h 𝟙)) : GL (Fin 3) K) =
      (x : GL (Fin 3) K)⁻¹ * (g : GL (Fin 3) K) * (x : GL (Fin 3) K) := rfl
  rw [e, Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle]
  have : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (((x : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [this, Matrix.one_mul]

theorem trace_cond_u [Finite K] {S : Subgroup (primeFormP h 𝟙)} (hS : IsPGroup 2 S)
    (hmax : ∀ T : Subgroup (primeFormP h 𝟙), IsPGroup 2 T → S ≤ T → T ≤ S)
    {φ : MulAut (primeFormP h 𝟙)} (hφS : ∀ s ∈ S, φ s = s) {A : primeFormUnitary h 𝟙}
    {σ : K ≃+* K}
    (hφ : φ = (primeFormConjHom h 𝟙 A * primeFormFieldHom h isPrimeFormGram_one σ :
      MulAut (primeFormP h 𝟙)))
    {g : gramSU h 𝟙} {j : ℕ} (hg : g ^ 2 ^ j = 1) :
    σ (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace) =
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace := by
  have hproj : (g : primeFormP h 𝟙) ^ 2 ^ j = 1 := by
    rw [← QuotientGroup.mk_pow, hg, QuotientGroup.mk_one]
  obtain ⟨x, hx⟩ := exists_conj_mem_of_isPGroup hS hmax hproj
  obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
  set g' : gramSU h 𝟙 := x'⁻¹ * g * x' with hg'
  have hg'S : (g' : primeFormP h 𝟙) ∈ S := by
    rw [hg', QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]; exact hx
  have hg'pow : g' ^ 2 ^ j = 1 := by
    have : g' = MulAut.conj x'⁻¹ g := by rw [hg', MulAut.conj_apply, inv_inv]
    rw [this, ← map_pow, hg, map_one]
  have hΘ : ((thetaU h A σ g' : gramSU h 𝟙) : primeFormP h 𝟙) = (g' : primeFormP h 𝟙) := by
    rw [← psi_apply_mk, ← hφ]
    exact hφS _ hg'S
  have hΘpow : (thetaU h A σ g') ^ 2 ^ j = 1 := by rw [← map_pow, hg'pow, map_one]
  have heq : thetaU h A σ g' = g' := eq_of_mk_eq_u h hΘpow hg'pow hΘ
  have := congrArg (fun y : gramSU h 𝟙 => ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace) heq
  simp only [trace_thetaU, hg', trace_conj_u] at this
  exact this

theorem center_primeFormP_three_eq_bot (h5 : 5 ≤ p ^ f) :
    Subgroup.center (primeFormP h 𝟙) = ⊥ := by
  have : Finite K := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have hnq : (3, p ^ f) ≠ (3, 2) := fun e => by have := (Prod.mk.inj e).2; omega
  obtain ⟨e₁⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := 3) (K := K))
  have e : primeFormP h 𝟙 ≃* CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ f) K) :=
    e₁.trans (unitaryPSUEquiv h (by omega))
  have hs := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p f h.card_eq_sq 3
    (by norm_num) hnq
  have hP := CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (K := K) h.card_eq_sq (n := 3)
    (by norm_num) hnq
  have hP' : Group.IsPerfect (CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ f) K)) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have hsimple : IsSimpleGroup (primeFormP h 𝟙) := e.isSimpleGroup
  have hperf : Group.IsPerfect (primeFormP h 𝟙) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (primeFormP h 𝟙)) with h0 | h1
  · exact h0
  · exfalso
    have h1' := (commutator_eq_bot_iff_center_eq_top (primeFormP h 𝟙)).2 h1
    rw [Group.IsPerfect.commutator_eq_top] at h1'
    exact top_ne_bot h1'

theorem conjHom_pow_inner (h5 : 5 ≤ p ^ f) (A : primeFormUnitary h 𝟙) {k : ℕ}
    (hk : primeFormConjHom h 𝟙 A ^ 2 ^ k = 1) : primeFormConjHom h 𝟙 A ∈ inner (primeFormP h 𝟙) := by
  have hq : ¬(3 = 3 ∧ p ^ f = 2) := fun e => by omega
  obtain ⟨-, -, hcard, -⟩ := unitary_full_diagonal_outer_order h (n := 3) (by norm_num) hq
  set D := primeFormD h 𝟙 with hD
  set x : D := ⟨primeFormConjHom h 𝟙 A, ⟨A, rfl⟩⟩ with hx
  set y : D ⧸ (inner (primeFormP h 𝟙)).subgroupOf D := (x : D ⧸ (inner (primeFormP h 𝟙)).subgroupOf D)
    with hy
  have hy1 : y ^ 2 ^ k = 1 := by
    rw [hy, ← QuotientGroup.mk_pow]
    have : x ^ 2 ^ k = 1 := Subtype.ext hk
    rw [this, QuotientGroup.mk_one]
  have hdvd : orderOf y ∣ Nat.gcd 3 (2 ^ k) := by
    apply Nat.dvd_gcd
    · exact (orderOf_dvd_natCard y).trans (by rw [hcard]; exact Nat.gcd_dvd_left _ _)
    · exact orderOf_dvd_of_pow_eq_one hy1
  have hg : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
  have hy2 : y = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 (hg ▸ hdvd))
  have : x ∈ (inner (primeFormP h 𝟙)).subgroupOf D := (QuotientGroup.eq_one_iff x).1 hy2
  exact (Subgroup.mem_subgroupOf).1 this

theorem uni_two_aut_inner (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) {S : Subgroup (primeFormP h 𝟙)}
    (hS : IsPGroup 2 S)
    (hmax : ∀ T : Subgroup (primeFormP h 𝟙), IsPGroup 2 T → S ≤ T → T ≤ S)
    {φ : MulAut (primeFormP h 𝟙)} {k : ℕ} (hφk : φ ^ 2 ^ k = 1) (hφS : ∀ s ∈ S, φ s = s) :
    ∃ s : gramSU h 𝟙, φ = MulAut.conj (s : primeFormP h 𝟙) := by
  have : Finite K := h.finite
  have hn : 3 ≤ 3 := le_rfl
  have hq : ¬(3 = 3 ∧ p ^ f = 2) := fun e => by omega
  obtain ⟨⟨A, σ⟩, hΨ⟩ := primeFormPsi_surjective h (isPrimeFormGram_one (n := 3) (K := K)) hn hq φ
  have hφ : φ = (primeFormConjHom h 𝟙 A * primeFormFieldHom h isPrimeFormGram_one σ :
      MulAut (primeFormP h 𝟙)) := by
    rw [← hΨ, primeFormPsi_apply]
  have hfac : primeFormFieldFactor h (isPrimeFormGram_one (n := 3) (K := K)) hn hq φ = σ := by
    rw [hφ]; exact primeFormFieldFactor_apply h _ hn hq A σ
  have hσk : σ ^ 2 ^ k = 1 := by
    rw [← hfac, ← map_pow, hφk, map_one]
  have hσ1 : σ = 1 := by
    by_contra hne
    obtain ⟨m, hm1, hm2⟩ := exists_pow_involution hne hσk
    obtain ⟨q₀, hq₀, hσx⟩ := eq_pow_of_involution hm1 hm2
    have hKcard : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
    have hq₀eq : q₀ = p ^ f := by
      have : q₀ * q₀ = p ^ f * p ^ f := by rw [hq₀, hKcard, sq]
      exact Nat.mul_self_inj.1 this
    obtain ⟨g, hgU, ⟨j, hgj⟩, hgt⟩ := exists_trace_pow_ne_uni h hp2 h5
    have hmem : Matrix.SpecialLinearGroup.toGL g ∈ gramSU h 𝟙 := by
      rw [mem_gramSU]
      refine ⟨?_, ?_⟩
      · rw [Units.val_one, Matrix.mul_one]; exact hgU
      · exact g.2
    let gU : gramSU h 𝟙 := ⟨Matrix.SpecialLinearGroup.toGL g, hmem⟩
    have hgUj : gU ^ 2 ^ j = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← map_pow, hgj, map_one]
      rfl
    have h1 := trace_cond_u h hS hmax hφS hφ hgUj
    have h2 : (σ ^ m) ((g : Matrix (Fin 3) (Fin 3) K).trace) = (g : Matrix (Fin 3) (Fin 3) K).trace :=
      ringEquiv_pow_fix h1 m
    rw [hσx, hq₀eq] at h2
    exact hgt h2
  subst hσ1
  have hφc : φ = primeFormConjHom h 𝟙 A := by rw [hφ, map_one, mul_one]
  have hin : φ ∈ inner (primeFormP h 𝟙) := by
    rw [hφc]
    exact conjHom_pow_inner h h5 A (by rw [← hφc]; exact hφk)
  obtain ⟨s, hs⟩ := (mem_inner_primeFormP h 𝟙 φ).1 hin
  exact ⟨s, hs.trans (primeFormConjHom_eq_conj h 𝟙 s)⟩

theorem uni_key (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) {S : Subgroup (primeFormP h 𝟙)} (hS : IsPGroup 2 S)
    (hmax : ∀ T : Subgroup (primeFormP h 𝟙), IsPGroup 2 T → S ≤ T → T ≤ S)
    {φ : MulAut (primeFormP h 𝟙)} {k : ℕ} (hφk : φ ^ 2 ^ k = 1) (hφS : ∀ s ∈ S, φ s = s) :
    ∃ z ∈ S, (∀ s ∈ S, s * z = z * s) ∧ φ = MulAut.conj z := by
  obtain ⟨x, hx⟩ := uni_two_aut_inner h hp2 h5 hS hmax hφk hφS
  have hz := mem_of_conj_fixes (center_primeFormP_three_eq_bot h h5) hS hmax
    (z := (x : primeFormP h 𝟙)) (k := k) (by rw [← hx]; exact hφk)
    (by intro s hs; rw [← hx]; exact hφS s hs)
  exact ⟨(x : primeFormP h 𝟙), hz.1, hz.2, hx⟩

end Uni

end CFSG.GH74.KGroups.L3Eps
