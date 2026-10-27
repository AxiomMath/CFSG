module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoPair
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoKernel
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAut

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KE
open scoped MatrixGroups

set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

theorem ipF4_neg_right (u v : V4) : ipF4 u (-v) = -ipF4 u v := by
  simp only [ipF4, Pi.neg_apply]
  ring

theorem ipF4_zero_right (v : V4) : ipF4 v 0 = 0 := by
  simp [ipF4]

section Aux

variable {L : Type} [Field L]

theorem rootChar_single' (b : Fin Tag.F4.rank → Lˣ) (i : Fin Tag.F4.rank) :
    rootChar b (Pi.single i 1) = b i := by
  simp only [rootChar]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem zpow_eq_zpow_iff_mod {ω : Lˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (x y : ℤ) :
    ω ^ x = ω ^ y ↔ x % 3 = y % 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf ω = 3 := orderOf_eq_prime hω3 hω1
  have h : ω ^ x = ω ^ y ↔ ω ^ (x - y) = 1 := by rw [zpow_sub, mul_inv_eq_one]
  rw [h, ← orderOf_dvd_iff_zpow_eq_one, hord]
  omega

theorem perm_sum_mod (ν : Equiv.Perm (Fin 3)) (M : Fin 3 → ℤ) :
    (2 * M (ν 2) - M (ν 1) - M (ν 0)) % 3 = (2 * M 2 - M 1 - M 0) % 3 := by
  have h := Equiv.sum_comp ν M
  rw [Fin.sum_univ_three, Fin.sum_univ_three] at h
  omega

end Aux

section Kind

variable
  {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

theorem not_inner_shape (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) {ω : Lˣ} {k : Fin Tag.F4.rank → ℕ}
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hk3 : ∀ i, k i < 3) (hk0 : ∃ i, k i ≠ 0)
    (hak : ∀ i, a i = ω ^ k i) {σ τ : Fin 3 → Fin 3 → V4} {κ κ' : ℤ} (hP : A2Pair σ τ κ κ')
    {ψ : SL(3, L) →* ModGL Tag.F4 L} (hψ : IsA2Frame ψ σ)
    (hSig : ∀ γ : V4, IsRoot Tag.F4 γ → kdot k γ % 3 = 0 → γ ∈ frameRoots σ ∨ γ ∈ frameRoots τ)
    (hq : S.D.q % 3 = 2) (π : Equiv.Perm (Fin 3))
    (hπ : ∀ x y : Fin 3, x ≠ y → S.ρ (σ x y) = σ (π x) (π y)) : False := by
  classical
  have hord : orderOf ω = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hω3 hω1
  set l : Fin 3 → Lˣ := fun _ => ω with hl
  have hl1 : l 0 * l 1 * l 2 = 1 := by
    show ω * ω * ω = 1
    rw [← pow_three']
    exact hω3
  obtain ⟨b, hb⟩ := exists_param_of_diag hψ l hl1
  have hchar : ∀ v : V4, rootChar b v = ω ^ (lab1 σ κ v + 2 * lab2 σ κ v) := by
    intro v
    rw [hP.diag_chars hψ hb v]
    show ω ^ _ * ω ^ _ = _
    rw [← zpow_add]
    congr 1
    ring
  have hb3 : ∀ i, ∃ n : ℕ, n < 3 ∧ b i = ω ^ n := by
    intro i
    have h1 := hchar (Pi.single i 1)
    rw [rootChar_single'] at h1
    refine ⟨((lab1 σ κ (Pi.single i 1) + 2 * lab2 σ κ (Pi.single i 1)) % 3).toNat, ?_, ?_⟩
    · omega
    · rw [h1, ← zpow_natCast, zpow_eq_zpow_iff_mod hω3 hω1]
      omega
  choose β hβ3 hbβ using hb3
  have hbSig : ∀ γ : V4, IsRoot Tag.F4 γ → kdot k γ % 3 = 0 → kdot β γ % 3 = 0 := by
    intro γ hγ hk
    have h1 : rootChar b γ = 1 := by
      rcases hSig γ hγ hk with ⟨x, y, hxy, rfl⟩ | hτ
      · rw [char_frame_root hψ hb hxy]
        simp [hl]
      · exact char_orth_root hψ hb hγ (fun x y hxy c c' => hP.comm γ hτ x y hxy c c')
    exact (rootChar_eq_one_iff hω3 hω1 hbβ γ).1 h1
  obtain ⟨m, hm3, hmk⟩ := unique_of_orth_kernel k β hk3 hk0 hβ3 hbSig
  have hbm : b = a ^ m := by
    funext i
    have h1 := pow_mod_orderOf ω (m * k i)
    rw [hord] at h1
    rw [hbβ i, hmk i, Pi.pow_apply, hak i, ← pow_mul, mul_comm (k i) m, h1]
  have hTb : rootDiagUnit Tag.F4 b ∈ S.D.torus := by
    rw [hbm]
    have : rootDiagUnit Tag.F4 (a ^ m) = rootDiagUnit Tag.F4 a ^ m :=
      (rootDiagUnitHom Tag.F4 L).map_pow a m
    rw [this]
    exact pow_mem hT m
  have hq' : ((S.D.q : ℕ) : ℤ) % 3 = 2 := by omega
  set M : V4 → Fin 3 → ℤ := fun v => ![0, lab1 σ κ v, lab1 σ κ v + lab2 σ κ v] with hM
  have hpair0 : ∀ v : V4, ∀ x : Fin 3, ipF4 v (σ 0 x) = κ * M v x := by
    intro v x
    fin_cases x
    · simp only [Fin.zero_eta, hP.σ_self, ipF4_zero_right]
      simp [hM]
    · simp only [Fin.mk_one]
      rw [hP.dvd01]
      simp [hM]
    · have h02 : σ 0 2 = σ 0 1 + σ 1 2 := (hP.σ_add 0 1 2).symm
      show ipF4 v (σ 0 2) = κ * M v 2
      rw [h02, ipF4_add_right, hP.dvd01, hP.dvd12]
      simp [hM]
      ring
  have hpair : ∀ v : V4, ∀ x y : Fin 3, ipF4 v (σ x y) = κ * (M v y - M v x) := by
    intro v x y
    have h1 : σ x y = -σ 0 x + σ 0 y := by
      rw [← hP.σ_add x 0 y, hP.σ_neg 0 x]
    rw [h1, ipF4_add_right, ipF4_neg_right, hpair0, hpair0]
    ring
  have hshift : ∀ v : V4, ∀ x y : Fin 3, x ≠ y →
      ipF4 (S.ρ v) (σ x y) = κ * (M v (π.symm y) - M v (π.symm x)) := by
    intro v x y hxy
    have h1 : S.ρ (σ (π.symm x) (π.symm y)) = σ x y := by
      rw [hπ _ _ (π.symm.injective.ne hxy)]
      simp
    have h2 := S.frob.iform_eq v (σ (π.symm x) (π.symm y))
    rw [h1, iform_F4, iform_F4] at h2
    rw [h2, hpair]
  have hlab1 : ∀ v : V4, lab1 σ κ (S.ρ v) = M v (π.symm 1) - M v (π.symm 0) := by
    intro v
    have h := hshift v 0 1 (by decide)
    rw [hP.dvd01] at h
    exact mul_left_cancel₀ hP.κ_ne_zero h
  have hlab2 : ∀ v : V4, lab2 σ κ (S.ρ v) = M v (π.symm 2) - M v (π.symm 1) := by
    intro v
    have h := hshift v 1 2 (by decide)
    rw [hP.dvd12] at h
    exact mul_left_cancel₀ hP.κ_ne_zero h
  have hinner : ∀ v : V4, (lab1 σ κ (S.ρ v) + 2 * lab2 σ κ (S.ρ v)) % 3 =
      (lab1 σ κ v + 2 * lab2 σ κ v) % 3 := by
    intro v
    rw [hlab1, hlab2]
    have h := perm_sum_mod π.symm (M v)
    have e1 : M v 0 = 0 := rfl
    have e2 : M v 1 = lab1 σ κ v := rfl
    have e3 : M v 2 = lab1 σ κ v + lab2 σ κ v := rfl
    omega
  have hone : ∀ v : V4, IsRoot Tag.F4 v → (lab1 σ κ v + 2 * lab2 σ κ v) % 3 = 0 := by
    intro v hv
    have h1 := S.frob.rootChar_eq b hTb v hv
    rw [hchar, hchar, ← zpow_natCast, ← zpow_mul, zpow_eq_zpow_iff_mod hω3 hω1] at h1
    have h2 := Int.mul_emod (lab1 σ κ v + 2 * lab2 σ κ v) ((S.D.q : ℕ) : ℤ) 3
    rw [hq'] at h2
    have h3 := hinner v
    omega
  have hb1 : b = 1 := by
    funext i
    have h1 := hchar (Pi.single i 1)
    rw [rootChar_single', (zpow_eq_zpow_iff_mod hω3 hω1 _ 0).2 (by
      have := hone (Pi.single i 1) (isRoot_single Tag.F4 i)
      omega), zpow_zero] at h1
    exact h1
  have hψ1 : ψ (diagSL3 l hl1) = ψ 1 := by
    rw [hb, hb1, rootDiagUnit_one, map_one]
  have hdiag1 := hψ.injective hψ1
  have h00 := congrArg (fun X : SL(3, L) => (X : Matrix (Fin 3) (Fin 3) L) 0 0) hdiag1
  simp only [coe_diagSL3, Matrix.diagonal_apply_eq, Matrix.SpecialLinearGroup.coe_one,
    Matrix.one_apply_eq] at h00
  exact hω1 (Units.ext h00)

theorem exists_outer_shape (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) {ω : Lˣ} {k : Fin Tag.F4.rank → ℕ}
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hk3 : ∀ i, k i < 3) (hk0 : ∃ i, k i ≠ 0)
    (hak : ∀ i, a i = ω ^ k i) {σ τ : Fin 3 → Fin 3 → V4} {κ κ' : ℤ} (hP : A2Pair σ τ κ κ')
    {ψ : SL(3, L) →* ModGL Tag.F4 L} (hψ : IsA2Frame ψ σ)
    (hSig : ∀ γ : V4, IsRoot Tag.F4 γ → kdot k γ % 3 = 0 → γ ∈ frameRoots σ ∨ γ ∈ frameRoots τ)
    (hq : S.D.q % 3 = 2) (hρ : (S.ρ : V4 → V4) '' frameRoots σ = frameRoots σ) :
    ∃ π : Equiv.Perm (Fin 3), ∀ x y : Fin 3, x ≠ y → S.ρ (σ x y) = σ (π y) (π x) := by
  have hnorm : ∀ x y : Fin 3, x ≠ y → iform (σ x y) (σ x y) = 2 * κ := fun x y hxy =>
    (iform_F4 _ _).trans (hP.σ_norm x y hxy)
  have hmaps : ∀ x y : Fin 3, x ≠ y → (S.ρ : V4 → V4) (σ x y) ∈ frameRoots σ := by
    intro x y hxy
    rw [← hρ]
    exact ⟨σ x y, ⟨x, y, hxy, rfl⟩, rfl⟩
  rcases (IsSLFrame.of_isA2Frame hψ).aut_cases (le_refl 3) hP.κ_ne_zero hnorm (S.ρ : V4 → V4)
      hmaps S.frob.neg_eq S.frob.iform_eq with ⟨π, hπ⟩ | ⟨π, hπ⟩
  · exact (not_inner_shape S hT hω3 hω1 hk3 hk0 hak hP hψ hSig hq π hπ).elim
  · exact ⟨π, hπ⟩

end Kind

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
