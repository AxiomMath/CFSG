module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoPair
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.RootLineCommute

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KE
open scoped MatrixGroups

set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

section Lvec

variable {L : Type} [Field L]

@[expose] def lvec (ζ : Lˣ) (e₀ e₁ : ℤ) : Fin 3 → Lˣ := ![ζ ^ e₀, ζ ^ e₁, ζ ^ (-e₀ - e₁)]

theorem lvec_det (ζ : Lˣ) (e₀ e₁ : ℤ) :
    lvec ζ e₀ e₁ 0 * lvec ζ e₀ e₁ 1 * lvec ζ e₀ e₁ 2 = 1 := by
  simp only [lvec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [← zpow_add, ← zpow_add]
  have : e₀ + e₁ + (-e₀ - e₁) = 0 := by ring
  rw [this, zpow_zero]

theorem lvec_pow {ζ : Lˣ} {N : ℕ} (hζ : ζ ^ N = 1) (e₀ e₁ : ℤ) (i : Fin 3) :
    lvec ζ e₀ e₁ i ^ N = 1 := by
  have h : ∀ e : ℤ, (ζ ^ e) ^ N = 1 := fun e => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ, one_zpow]
  fin_cases i
  · exact h e₀
  · exact h e₁
  · exact h (-e₀ - e₁)

end Lvec

section Labels


namespace A2Pair

variable {σ τ : Fin 3 → Fin 3 → V4} {κ κ' : ℤ}

theorem lab1_zero (hP : A2Pair σ τ κ κ') : lab1 σ κ 0 = 0 := by
  have h := hP.dvd01 0
  rw [ipF4_zero_left] at h
  exact (mul_eq_zero.1 h.symm).resolve_left hP.κ_ne_zero

theorem lab2_zero (hP : A2Pair σ τ κ κ') : lab2 σ κ 0 = 0 := by
  have h := hP.dvd12 0
  rw [ipF4_zero_left] at h
  exact (mul_eq_zero.1 h.symm).resolve_left hP.κ_ne_zero

theorem lab1_sub (hP : A2Pair σ τ κ κ') (u w : V4) :
    lab1 σ κ (u - w) = lab1 σ κ u - lab1 σ κ w := by
  apply mul_left_cancel₀ hP.κ_ne_zero
  rw [← hP.dvd01, ipF4_sub_left, hP.dvd01, hP.dvd01]
  ring

theorem lab2_sub (hP : A2Pair σ τ κ κ') (u w : V4) :
    lab2 σ κ (u - w) = lab2 σ κ u - lab2 σ κ w := by
  apply mul_left_cancel₀ hP.κ_ne_zero
  rw [← hP.dvd12, ipF4_sub_left, hP.dvd12, hP.dvd12]
  ring

theorem lab_bound (hP : A2Pair σ τ κ κ') {v : V4} (hv : IsRoot Tag.F4 v) :
    |lab1 σ κ v| ≤ 2 ∧ |lab2 σ κ v| ≤ 2 := by
  have h1 := pairing_bound hv (hP.σ_root 0 1 (by decide))
  have h2 := pairing_bound hv (hP.σ_root 1 2 (by decide))
  rw [hP.dvd01, hP.σ_norm 0 1 (by decide)] at h1
  rw [hP.dvd12, hP.σ_norm 1 2 (by decide)] at h2
  rcases hP.kappa with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · rw [abs_le, abs_le]
    omega
  · rw [abs_le, abs_le]
    omega

theorem eq_of_labels (hP : A2Pair σ τ κ κ') {u w : V4} (h1 : lab1 σ κ u = lab1 σ κ w)
    (h2 : lab2 σ κ u = lab2 σ κ w) (h3 : lab1 τ κ' u = lab1 τ κ' w)
    (h4 : lab2 τ κ' u = lab2 τ κ' w) : u = w := by
  obtain ⟨a, b, a', b', e1, e2, e3, e4, e5⟩ := hP.exists_dec (u - w)
  have hs := hP.symm
  have ha : a = 0 := by
    have h := hP.dvd01 (u - w)
    rw [lab1_sub hP, h1, sub_self, mul_zero, e1] at h
    exact (mul_eq_zero.1 h).resolve_left hP.κ_ne_zero
  have hb : b = 0 := by
    have h := hP.dvd12 (u - w)
    rw [lab2_sub hP, h2, sub_self, mul_zero, e2] at h
    exact (mul_eq_zero.1 h).resolve_left hP.κ_ne_zero
  have ha' : a' = 0 := by
    have h := hs.dvd01 (u - w)
    rw [lab1_sub hs, h3, sub_self, mul_zero, e3] at h
    exact (mul_eq_zero.1 h).resolve_left hs.κ_ne_zero
  have hb' : b' = 0 := by
    have h := hs.dvd12 (u - w)
    rw [lab2_sub hs, h4, sub_self, mul_zero, e4] at h
    exact (mul_eq_zero.1 h).resolve_left hs.κ_ne_zero
  rw [ha, hb, ha', hb'] at e5
  simp only [mul_zero, add_zero, zero_smul] at e5
  funext i
  have := congrFun e5 i
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at this
  omega

end A2Pair

end Labels

section Sep

variable
  {L : Type} [Field L] [IsAlgClosed L]
  {σ τ : Fin 3 → Fin 3 → V4} {κ κ' : ℤ}

theorem A2Pair.chars_lvec (hP : A2Pair σ τ κ κ') {ψ : SL(3, L) →* ModGL Tag.F4 L}
    (hψ : IsA2Frame ψ σ) (ζ : Lˣ) (e₀ e₁ : ℤ) {b : Fin Tag.F4.rank → Lˣ}
    (hb : ψ (diagSL3 (lvec ζ e₀ e₁) (lvec_det ζ e₀ e₁)) = rootDiagUnit Tag.F4 b) (v : V4) :
    rootChar b v = ζ ^ (e₀ * (lab1 σ κ v + lab2 σ κ v) + e₁ * lab2 σ κ v) := by
  rw [hP.diag_chars hψ hb v]
  simp only [lvec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [← zpow_mul, ← zpow_mul, ← zpow_add]

theorem zpow_eq_iff_dvd {ζ : Lˣ} {N : ℕ} (hζ : ∀ n : ℤ, ζ ^ n = 1 ↔ (N : ℤ) ∣ n) (x y : ℤ) :
    ζ ^ x = ζ ^ y ↔ (N : ℤ) ∣ x - y := by
  rw [← hζ, zpow_sub, mul_inv_eq_one]

theorem A2Pair.exists_sep (hP : A2Pair σ τ κ κ') {ψ ψ' : SL(3, L) →* ModGL Tag.F4 L}
    (hψ : IsA2Frame ψ σ) (hψ' : IsA2Frame ψ' τ) {ζ : Lˣ} {N : ℕ} (hN : 9 ≤ N)
    (hζ : ∀ n : ℤ, ζ ^ n = 1 ↔ (N : ℤ) ∣ n) {u w : V4} (hu : u = 0 ∨ IsRoot Tag.F4 u)
    (hw : w = 0 ∨ IsRoot Tag.F4 w) (huw : u ≠ w) :
    ∃ e₀ e₁ : ℤ, ∃ b : Fin Tag.F4.rank → Lˣ,
      (ψ (diagSL3 (lvec ζ e₀ e₁) (lvec_det ζ e₀ e₁)) = rootDiagUnit Tag.F4 b ∨
        ψ' (diagSL3 (lvec ζ e₀ e₁) (lvec_det ζ e₀ e₁)) = rootDiagUnit Tag.F4 b) ∧
      rootChar b u ≠ rootChar b w := by
  classical
  by_contra hcon
  push Not at hcon
  have hbd : ∀ v : V4, (v = 0 ∨ IsRoot Tag.F4 v) →
      |lab1 σ κ v| ≤ 2 ∧ |lab2 σ κ v| ≤ 2 ∧ |lab1 τ κ' v| ≤ 2 ∧ |lab2 τ κ' v| ≤ 2 := by
    intro v hv
    rcases hv with rfl | hv
    · simp [hP.lab1_zero, hP.lab2_zero, hP.symm.lab1_zero, hP.symm.lab2_zero]
    · exact ⟨(hP.lab_bound hv).1, (hP.lab_bound hv).2, (hP.symm.lab_bound hv).1,
        (hP.symm.lab_bound hv).2⟩
  obtain ⟨hu1, hu2, hu3, hu4⟩ := hbd u hu
  obtain ⟨hw1, hw2, hw3, hw4⟩ := hbd w hw
  obtain ⟨b1, hb1⟩ := exists_param_of_diag hψ (lvec ζ 1 0) (lvec_det ζ 1 0)
  obtain ⟨b2, hb2⟩ := exists_param_of_diag hψ (lvec ζ 0 1) (lvec_det ζ 0 1)
  obtain ⟨b3, hb3⟩ := exists_param_of_diag hψ' (lvec ζ 1 0) (lvec_det ζ 1 0)
  obtain ⟨b4, hb4⟩ := exists_param_of_diag hψ' (lvec ζ 0 1) (lvec_det ζ 0 1)
  have c1 := hcon 1 0 b1 (Or.inl hb1)
  have c2 := hcon 0 1 b2 (Or.inl hb2)
  have c3 := hcon 1 0 b3 (Or.inr hb3)
  have c4 := hcon 0 1 b4 (Or.inr hb4)
  rw [hP.chars_lvec hψ ζ 1 0 hb1 u, hP.chars_lvec hψ ζ 1 0 hb1 w, zpow_eq_iff_dvd hζ] at c1
  rw [hP.chars_lvec hψ ζ 0 1 hb2 u, hP.chars_lvec hψ ζ 0 1 hb2 w, zpow_eq_iff_dvd hζ] at c2
  rw [hP.symm.chars_lvec hψ' ζ 1 0 hb3 u, hP.symm.chars_lvec hψ' ζ 1 0 hb3 w,
    zpow_eq_iff_dvd hζ] at c3
  rw [hP.symm.chars_lvec hψ' ζ 0 1 hb4 u, hP.symm.chars_lvec hψ' ζ 0 1 hb4 w,
    zpow_eq_iff_dvd hζ] at c4
  have hN' : (9 : ℤ) ≤ N := by exact_mod_cast hN
  have hz : ∀ x : ℤ, (N : ℤ) ∣ x → |x| ≤ 8 → x = 0 := fun x hx hb =>
    Int.eq_zero_of_abs_lt_dvd hx (by omega)
  rw [abs_le] at hu1 hu2 hu3 hu4 hw1 hw2 hw3 hw4
  have d1 := hz _ c1 (by rw [abs_le]; omega)
  have d2 := hz _ c2 (by rw [abs_le]; omega)
  have d3 := hz _ c3 (by rw [abs_le]; omega)
  have d4 := hz _ c4 (by rw [abs_le]; omega)
  exact huw (hP.eq_of_labels (by omega) (by omega) (by omega) (by omega))

theorem A2Pair.commutator_contradiction (hP : A2Pair σ τ κ κ')
    {ψ ψ' : SL(3, L) →* ModGL Tag.F4 L} (hψ : IsA2Frame ψ σ) (hψ' : IsA2Frame ψ' τ) {ζ : Lˣ}
    {N : ℕ} (hN : 9 ≤ N) (hζ : ∀ n : ℤ, ζ ^ n = 1 ↔ (N : ℤ) ∣ n) {G Y : ModGL Tag.F4 L}
    (hG1 : ∀ e₀ e₁ : ℤ, G * ψ (diagSL3 (lvec ζ e₀ e₁) (lvec_det ζ e₀ e₁)) =
      ψ (diagSL3 (lvec ζ e₀ e₁) (lvec_det ζ e₀ e₁)) * G)
    (hG2 : ∀ e₀ e₁ : ℤ, G * ψ' (diagSL3 (lvec ζ e₀ e₁) (lvec_det ζ e₀ e₁)) =
      ψ' (diagSL3 (lvec ζ e₀ e₁) (lvec_det ζ e₀ e₁)) * G)
    (hY1 : ∀ e₀ e₁ : ℤ, Y * ψ (diagSL3 (lvec ζ e₀ e₁) (lvec_det ζ e₀ e₁)) =
      ψ (diagSL3 (lvec ζ e₀ e₁) (lvec_det ζ e₀ e₁)) * Y)
    (hY2 : ∀ e₀ e₁ : ℤ, Y * ψ' (diagSL3 (lvec ζ e₀ e₁) (lvec_det ζ e₀ e₁)) =
      ψ' (diagSL3 (lvec ζ e₀ e₁) (lvec_det ζ e₀ e₁)) * Y)
    {b₀ : Fin Tag.F4.rank → Lˣ} (hcomm : G * Y * G⁻¹ * Y⁻¹ = rootDiagUnit Tag.F4 b₀)
    {β : V4} (hβ : IsRoot Tag.F4 β) (hb₀ : rootChar b₀ β ≠ 1) : False := by
  classical
  set D : Set (Fin Tag.F4.rank → Lˣ) := {b | ∃ e₀ e₁ : ℤ,
    ψ (diagSL3 (lvec ζ e₀ e₁) (lvec_det ζ e₀ e₁)) = rootDiagUnit Tag.F4 b ∨
      ψ' (diagSL3 (lvec ζ e₀ e₁) (lvec_det ζ e₀ e₁)) = rootDiagUnit Tag.F4 b} with hD
  have hDG : ∀ b ∈ D, rootDiagUnit Tag.F4 b * G = G * rootDiagUnit Tag.F4 b := by
    rintro b ⟨e₀, e₁, h | h⟩
    · rw [← h]
      exact (hG1 e₀ e₁).symm
    · rw [← h]
      exact (hG2 e₀ e₁).symm
  have hDY : ∀ b ∈ D, rootDiagUnit Tag.F4 b * Y = Y * rootDiagUnit Tag.F4 b := by
    rintro b ⟨e₀, e₁, h | h⟩
    · rw [← h]
      exact (hY1 e₀ e₁).symm
    · rw [← h]
      exact (hY2 e₀ e₁).symm
  have hsep0 : ∀ u w : V4, (u = 0 ∨ IsRoot Tag.F4 u) → (w = 0 ∨ IsRoot Tag.F4 w) → u ≠ w →
      ∃ b ∈ D, rootChar b u ≠ rootChar b w := by
    intro u w hu hw huw
    obtain ⟨e₀, e₁, b, hb, hne⟩ := hP.exists_sep hψ hψ' hN hζ hu hw huw
    exact ⟨b, ⟨e₀, e₁, hb⟩, hne⟩
  set β' : Label Tag.F4 := Sum.inr ⟨β, hβ⟩ with hβ'
  have hsep : ∀ c : Label Tag.F4, c ≠ β' → ∃ a ∈ D, diagEig a c ≠ diagEig a β' := by
    intro c hc
    rcases c with j | ⟨γ, hγ⟩
    · obtain ⟨b, hbD, hne⟩ := hsep0 0 β (Or.inl rfl) (Or.inr hβ) hβ.ne_zero.symm
      refine ⟨b, hbD, fun h => hne ?_⟩
      rw [rootChar_zero]
      apply Units.ext
      simpa [diagEig, rootChar] using h
    · obtain ⟨b, hbD, hne⟩ := hsep0 γ β (Or.inr hγ) (Or.inr hβ)
        (fun h => hc (by rw [hβ']; exact congrArg Sum.inr (Subtype.ext h)))
      refine ⟨b, hbD, fun h => hne ?_⟩
      apply Units.ext
      simpa [diagEig, rootChar] using h
  have h1 := commutator_apply_single_of_commute (K := L) (τ := Tag.F4) hDG hDY hsep
  rw [hcomm] at h1
  change rootDiag b₀ (Finsupp.single β' 1) = Finsupp.single β' 1 at h1
  rw [rootDiag_single_eq] at h1
  have h2 := congrArg (fun w : RootModule Tag.F4 L => w β') h1
  simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at h2
  apply hb₀
  apply Units.ext
  simpa [diagEig, rootChar] using h2

end Sep

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
