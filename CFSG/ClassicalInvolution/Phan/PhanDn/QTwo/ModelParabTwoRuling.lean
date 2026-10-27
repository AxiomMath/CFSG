module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.ModelParabTwo
public import CFSG.ClassicalInvolution.Phan.PhanDn.Chambers
import all CFSG.ClassicalInvolution.Phan.PhanDn.Ruling

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Steinberg

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]
variable (E : QuadExt F K (unitaryInvolution K 2 1))

theorem qTwo_mem_rulingGroup_of_isKLinear {n : ℕ}
    {g : (Fin n → K) ≃ₗ[F] (Fin n → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E n))
    (hK : ∀ (a : K) (w : Fin n → K), g (a • w) = a • g w) :
    g ∈ rulingGroup E n := by
  apply mem_rulingGroup_of_map_stdLag E n hg
  apply Submodule.eq_of_le_of_finrank_eq
  · exact (map_stdLag_bcLin_le_iff E n g.toLinearMap).mpr hK
  · rw [bcLin_eq_coe_bc]
    exact (bc E n g).finrank_map_eq (stdLag n K)

theorem qTwo_tauAt_not_mem_rulingGroup {n : ℕ} (i : Fin n) :
    tauAt E i ∉ rulingGroup E n := by
  intro h
  rw [rulingGroup, Subgroup.mem_map] at h
  obtain ⟨x, hx, hxt⟩ := h
  have heq : x = ⟨tauAt E i, tauAt_mem_orthogonalGroup E i⟩ := Subtype.ext hxt
  rw [heq, MonoidHom.mem_ker, rulingHom_tauAt] at hx
  have h := congrArg Multiplicative.toAdd hx
  norm_num at h

theorem qTwo_not_isKLinear_mul_tauAt {n : ℕ}
    {g : (Fin n → K) ≃ₗ[F] (Fin n → K)} (hg : g ∈ rulingGroup E n) (i : Fin n) :
    ¬ (∀ (a : K) (w : Fin n → K),
      (g * tauAt E i) (a • w) = a • (g * tauAt E i) w) := by
  intro hlin
  have hO := ((mem_rulingGroup E n g).mp hg).1
  have hprod := qTwo_mem_rulingGroup_of_isKLinear E
    ((TauCeti.QuadraticMap.orthogonalGroup (Qn E n)).mul_mem hO
      (tauAt_mem_orthogonalGroup E i)) hlin
  have htau := (rulingGroup E n).mul_mem ((rulingGroup E n).inv_mem hg) hprod
  rw [inv_mul_cancel_left] at htau
  exact qTwo_tauAt_not_mem_rulingGroup E i htau

theorem qTwo_axis_preserving_ruling_semilinear
    {g : (Fin 2 → K) ≃ₗ[F] (Fin 2 → K)} (hg : g ∈ rulingGroup E 2)
    (h0 : ∀ a : K, g (Pi.single 0 a) 1 = 0)
    (h1 : ∀ a : K, g (Pi.single 1 a) 0 = 0) :
    (∀ (a : K) (w : Fin 2 → K), g (a • w) = a • g w) ∨
      (∀ (a : K) (w : Fin 2 → K),
        g (a • w) = unitaryInvolution K 2 1 a • g w) := by
  obtain ⟨u, v, hu, hv, hgu, hgv⟩ :=
    qTwo_axis_preserving_form E ((mem_rulingGroup E 2 g).mp hg).1 h0 h1
  let tu : normOne (unitaryInvolution K 2 1) :=
    ⟨Units.mk0 u (left_ne_zero_of_mul_eq_one hu),
      (mem_normOne _).mpr (by simpa [mul_comm] using hu)⟩
  let tv : normOne (unitaryInvolution K 2 1) :=
    ⟨Units.mk0 v (left_ne_zero_of_mul_eq_one hv),
      (mem_normOne _).mpr (by simpa [mul_comm] using hv)⟩
  let t : Fin 2 → normOne (unitaryInvolution K 2 1) := ![tu, tv]
  let d := diagHom F (unitaryInvolution K 2 1) 2 t
  have hd : d ∈ rulingGroup E 2 :=
    mem_rulingGroup_of_map_stdLag E 2 (diagHom_mem_orthogonalGroup E 2 t)
      (map_stdLag_diagHom E 2 t)
  rcases hgu with hgu | hgu <;> rcases hgv with hgv | hgv
  · left
    intro a w
    ext i
    fin_cases i <;> simp [hgu, hgv, Pi.smul_apply, mul_left_comm]
  · have hgd : g = d * tauAt E (1 : Fin 2) := by
      apply LinearEquiv.ext
      intro w
      ext i
      fin_cases i <;> simp [d, t, tu, tv, tauAt_apply, hgu, hgv]
    have hbad := (rulingGroup E 2).mul_mem ((rulingGroup E 2).inv_mem hd) hg
    rw [hgd, inv_mul_cancel_left] at hbad
    exact (qTwo_tauAt_not_mem_rulingGroup E (1 : Fin 2) hbad).elim
  · have hgd : g = d * tauAt E (0 : Fin 2) := by
      apply LinearEquiv.ext
      intro w
      ext i
      fin_cases i <;> simp [d, t, tu, tv, tauAt_apply, hgu, hgv]
    have hbad := (rulingGroup E 2).mul_mem ((rulingGroup E 2).inv_mem hd) hg
    rw [hgd, inv_mul_cancel_left] at hbad
    exact (qTwo_tauAt_not_mem_rulingGroup E (0 : Fin 2) hbad).elim
  · right
    intro a w
    ext i
    fin_cases i <;> simp [hgu, hgv, Pi.smul_apply, map_mul, mul_left_comm]

theorem qTwo_ruling_semilinear (hK : Nat.card K = 4)
    {g : (Fin 2 → K) ≃ₗ[F] (Fin 2 → K)} (hg : g ∈ rulingGroup E 2) :
    (∀ (a : K) (w : Fin 2 → K), g (a • w) = a • g w) ∨
      (∀ (a : K) (w : Fin 2 → K),
        g (a • w) = unitaryInvolution K 2 1 a • g w) := by
  rcases qTwo_isometry_permutes_axes E hK ((mem_rulingGroup E 2 g).mp hg).1 with h | h
  · exact qTwo_axis_preserving_ruling_semilinear E hg h.1 h.2
  let s : (Fin 2 → K) ≃ₗ[F] (Fin 2 → K) :=
    LinearEquiv.funCongrLeft F K (Equiv.swap (0 : Fin 2) 1)
  have hs0 (w : Fin 2 → K) : s w 0 = w 1 := by simp [s]
  have hs1 (w : Fin 2 → K) : s w 1 = w 0 := by simp [s]
  have hs_sq (w : Fin 2 → K) : s (s w) = w := by
    ext i
    fin_cases i <;> simp [hs0, hs1]
  have hsK (a : K) (w : Fin 2 → K) : s (a • w) = a • s w := by
    ext i
    fin_cases i <;> simp [hs0, hs1, Pi.smul_apply]
  have hsO : s ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E 2) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro w
    simp [Qn_apply, Fin.sum_univ_two, hs0, hs1, add_comm]
  have hsR := qTwo_mem_rulingGroup_of_isKLinear E hsO hsK
  let f := g * s
  have hfR : f ∈ rulingGroup E 2 := (rulingGroup E 2).mul_mem hg hsR
  have hs_single0 (a : K) : s (Pi.single 0 a) = Pi.single 1 a := by
    ext i
    fin_cases i <;> simp [hs0, hs1]
  have hs_single1 (a : K) : s (Pi.single 1 a) = Pi.single 0 a := by
    ext i
    fin_cases i <;> simp [hs0, hs1]
  have hf0 (a : K) : f (Pi.single 0 a) 1 = 0 := by
    change g (s (Pi.single 0 a)) 1 = 0
    rw [hs_single0]
    exact h.2 a
  have hf1 (a : K) : f (Pi.single 1 a) 0 = 0 := by
    change g (s (Pi.single 1 a)) 0 = 0
    rw [hs_single1]
    exact h.1 a
  have hgform (w : Fin 2 → K) : g w = f (s w) := by
    change g w = g (s (s w))
    rw [hs_sq]
  rcases qTwo_axis_preserving_ruling_semilinear E hfR hf0 hf1 with hf | hf
  · left
    intro a w
    rw [hgform, hsK, hf, ← hgform]
  · right
    intro a w
    rw [hgform, hsK, hf, ← hgform]

theorem qTwo_ruling_doubleTau_correction (hK : Nat.card K = 4)
    {g : (Fin 2 → K) ≃ₗ[F] (Fin 2 → K)} (hg : g ∈ rulingGroup E 2) :
    (∀ (a : K) (w : Fin 2 → K), g (a • w) = a • g w) ∨
      (∀ (a : K) (w : Fin 2 → K),
        (g * (tauAt E (0 : Fin 2) * tauAt E (1 : Fin 2))) (a • w) =
          a • (g * (tauAt E (0 : Fin 2) * tauAt E (1 : Fin 2))) w) := by
  rcases qTwo_ruling_semilinear E hK hg with h | h
  · exact Or.inl h
  right
  intro a w
  have hbar : tauAt E (0 : Fin 2) (tauAt E (1 : Fin 2) (a • w)) =
      unitaryInvolution K 2 1 a • tauAt E (0 : Fin 2) (tauAt E (1 : Fin 2) w) := by
    ext i
    fin_cases i <;> simp [tauAt_apply, Pi.smul_apply, map_mul]
  change g (tauAt E (0 : Fin 2) (tauAt E (1 : Fin 2) (a • w))) =
    a • g (tauAt E (0 : Fin 2) (tauAt E (1 : Fin 2) w))
  rw [hbar, h, E.isUnitary.invol]

theorem qTwo_isometry_coordinate_correction (hK : Nat.card K = 4)
    {g : (Fin 2 → K) ≃ₗ[F] (Fin 2 → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E 2)) :
    ∃ b₀ b₁ : Bool, ∀ (a : K) (w : Fin 2 → K),
      (g * ((if b₀ then tauAt E (0 : Fin 2) else 1) *
        (if b₁ then tauAt E (1 : Fin 2) else 1))) (a • w) =
      a • (g * ((if b₀ then tauAt E (0 : Fin 2) else 1) *
        (if b₁ then tauAt E (1 : Fin 2) else 1))) w := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := Ne.symm h01
  have axis {f : (Fin 2 → K) ≃ₗ[F] (Fin 2 → K)}
      (hf : f ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E 2))
      (h0 : ∀ a : K, f (Pi.single 0 a) 1 = 0)
      (h1 : ∀ a : K, f (Pi.single 1 a) 0 = 0) :
      ∃ b₀ b₁ : Bool, ∀ (a : K) (w : Fin 2 → K),
        (f * ((if b₀ then tauAt E (0 : Fin 2) else 1) *
          (if b₁ then tauAt E (1 : Fin 2) else 1))) (a • w) =
        a • (f * ((if b₀ then tauAt E (0 : Fin 2) else 1) *
          (if b₁ then tauAt E (1 : Fin 2) else 1))) w := by
    obtain ⟨u, v, _, _, hfu, hfv⟩ := qTwo_axis_preserving_form E hf h0 h1
    rcases hfu with hfu | hfu <;> rcases hfv with hfv | hfv
    · refine ⟨false, false, fun a w => ?_⟩
      ext i
      fin_cases i <;> simp [hfu, hfv, Pi.smul_apply, mul_left_comm]
    · refine ⟨false, true, fun a w => ?_⟩
      ext i
      fin_cases i <;>
        simp only [h01, h10, Fin.mk_zero, Fin.mk_one, Fin.isValue, Bool.false_eq_true, ↓reduceIte, one_mul, mul_one,
          LinearEquiv.mul_apply, hfu, hfv, tauAt_apply, Pi.smul_apply,
          E.isUnitary.invol, map_mul] <;> ring
    · refine ⟨true, false, fun a w => ?_⟩
      ext i
      fin_cases i <;>
        simp only [h01, h10, Fin.mk_zero, Fin.mk_one, Fin.isValue, Bool.false_eq_true, ↓reduceIte, one_mul, mul_one,
          LinearEquiv.mul_apply, hfu, hfv, tauAt_apply, Pi.smul_apply,
          E.isUnitary.invol, map_mul] <;> ring
    · refine ⟨true, true, fun a w => ?_⟩
      ext i
      fin_cases i <;>
        simp only [h01, h10, Fin.mk_zero, Fin.mk_one, Fin.isValue, Bool.false_eq_true, ↓reduceIte, one_mul, mul_one,
          LinearEquiv.mul_apply, hfu, hfv, tauAt_apply, Pi.smul_apply,
          E.isUnitary.invol, map_mul] <;> ring
  rcases qTwo_isometry_permutes_axes E hK hg with h | h
  · exact axis hg h.1 h.2
  let s : (Fin 2 → K) ≃ₗ[F] (Fin 2 → K) :=
    LinearEquiv.funCongrLeft F K (Equiv.swap (0 : Fin 2) 1)
  have hs0 (w : Fin 2 → K) : s w 0 = w 1 := by simp [s]
  have hs1 (w : Fin 2 → K) : s w 1 = w 0 := by simp [s]
  have hsK (a : K) (w : Fin 2 → K) : s (a • w) = a • s w := by
    ext i
    fin_cases i <;> simp [hs0, hs1, Pi.smul_apply]
  have hsO : s ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E 2) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro w
    simp [Qn_apply, Fin.sum_univ_two, hs0, hs1, add_comm]
  have hf0 (a : K) : (s * g) (Pi.single 0 a) 1 = 0 := by
    simpa only [LinearEquiv.mul_apply, hs1] using h.1 a
  have hf1 (a : K) : (s * g) (Pi.single 1 a) 0 = 0 := by
    simpa only [LinearEquiv.mul_apply, hs0] using h.2 a
  obtain ⟨b₀, b₁, hcorr⟩ := axis
    ((TauCeti.QuadraticMap.orthogonalGroup (Qn E 2)).mul_mem hsO hg) hf0 hf1
  refine ⟨b₀, b₁, fun a w => ?_⟩
  apply s.injective
  rw [hsK]
  exact hcorr a w

end CFSG.ClassicalInvolution.PhanDn.QTwo
