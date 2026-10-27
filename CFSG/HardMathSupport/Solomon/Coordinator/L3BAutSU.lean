module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BAutSL
public import CFSG.RankThree.PartTwo.KFacts.AutPSU

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.KFacts CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.UnitaryFlag
open Matrix.GeneralLinearGroup (scalar coe_scalar)
open scoped Matrix

variable {p f : ℕ} {K : Type} [Field K]

theorem hX_unitary (h : UnitaryFieldData p f K) {ω : K} (hω3 : ω ^ 3 = 1)
    (hq : ω ^ (p ^ f) = ω ^ 2) :
    ((hX ω).map h.bar)ᵀ * hX ω = 1 := by
  have hb : ∀ i : ℕ, h.bar (ω ^ i) = ω ^ (2 * i) := fun i => by
    rw [h.bar_apply, ← pow_mul, mul_comm, pow_mul, hq, ← pow_mul, mul_comm]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hX, Matrix.mul_apply, Matrix.diagonal_apply, hb]
  · calc ω ^ 2 * ω = ω ^ 3 := by ring
      _ = 1 := hω3
  · calc ω ^ 4 * ω ^ 2 = (ω ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hω3, one_pow]

theorem hP_unitary (h : UnitaryFieldData p f K) :
    (((hP : Matrix (Fin 3) (Fin 3) K)).map h.bar)ᵀ * hP = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hP, Matrix.mul_apply, Matrix.transpose_apply]

theorem descend_mem_of_pow_three_unitary (h : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    (hq9 : (p ^ f) % 9 = 2 ∨ (p ^ f) % 9 = 5)
    (σ : MulAut (unitarySU p f K 3)) (k : ℕ) (hσ : σ ^ 3 ^ k = 1) :
    MulAut.congr (suCenterEquiv h hq) (centerDescend _ σ) ∈ (psuConj h).range := by
  have := h.finite
  have h3 : ¬ 3 ∣ f := not_three_dvd_of_mod_nine (p := p) (f := f) (c := p ^ f) rfl (by omega)
  have hcop : Nat.Coprime 3 (2 * f) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 hd with hd | hd
    · omega
    · exact h3 hd
  obtain ⟨A, τ, hAτ⟩ := exists_psuConj_mul_psuField hq
    (MulAut.congr (suCenterEquiv h hq) (centerDescend _ σ))
  have hnorm : (psuConj h).range.Normal := (stdPinnedPSU3_stable (h := h) hq).normal
  refine mem_of_pow_coprime (psuConj h).range (r := psuField h τ) (k := k) (n := 2 * f) ?_ ?_ hcop
    ?_
  · rw [← map_pow, ← map_pow, hσ, map_one, map_one]
  · rw [← map_pow, ringEquiv_pow_eq_one h.prime (by rw [h.card]) τ, map_one]
  · rw [hAτ, mul_inv_cancel_right]
    exact ⟨A, rfl⟩

theorem sylowCentreInn_statedSU (h : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    (hq9 : (p ^ f) % 9 = 2 ∨ (p ^ f) % 9 = 5) : SylowCentreInn ↥(unitarySU p f K 3) := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have hcard : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hq3 : (p ^ f) % 3 = 2 := by omega
  obtain ⟨ω, hω3, hω1⟩ := exists_primitive_cube_root K (by
    have h1 : (p ^ f) ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq3]
    have h2 : 0 < (p ^ f) ^ 2 := by positivity
    omega)
  have hωq : ω ^ (p ^ f) = ω ^ 2 := by
    have hqe : p ^ f = 3 * (p ^ f / 3) + 2 := by omega
    rw [hqe, pow_add, pow_mul, hω3, one_pow, one_mul]
  set H : Subgroup (GL (Fin 3) K) := unitarySU p f K 3 with hH
  have hXH : Matrix.SpecialLinearGroup.toGL (hXsl hω3) ∈ H :=
    (mem_unitarySU_iff h).2 ⟨det_hX hω3, hX_unitary h hω3 hωq⟩
  have hPH : Matrix.SpecialLinearGroup.toGL (hPsl : Matrix.SpecialLinearGroup (Fin 3) K) ∈ H :=
    (mem_unitarySU_iff h).2 ⟨det_hP, hP_unitary h⟩
  let ι : MulAut ↥H →* MulAut (unitaryPSU h 3) :=
    (MulAut.congr (suCenterEquiv h hq)).toMonoidHom.comp (centerDescend ↥H)
  let D : Subgroup (MulAut ↥H) := (psuConj h).range.comap ι
  have hquasi := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hcard le_rfl
    (by intro hh; simp only [Prod.mk.injEq, true_and] at hh; omega)
  have hperfH : Group.IsPerfect ↥H := hquasi.1.1
  have hι : ∀ m : ↥H, ι (MulAut.conj m) = psuConj h ⟨m, unitarySU_le_unitaryIsom3 m.2⟩ := by
    intro m
    have h1 : centerDescend ↥H (MulAut.conj m) = MulAut.conj (m : ↥H ⧸ Subgroup.center ↥H) := by
      ext x
      induction x using QuotientGroup.induction_on with
      | H y => rfl
    show MulAut.congr (suCenterEquiv h hq) (centerDescend ↥H (MulAut.conj m)) = _
    rw [h1, congr_mulAutConj]
    exact conj_mk_eq_psuConj (h := h) m
  refine sylowCentreInn_of_family hω3 hω1 H hXH hPH D ?_ ?_ ?_ ?_
    (fun e' h' => eq_one_of_scalar_perfect hperfH e' h')
  · rintro _ ⟨m, rfl⟩
    show ι (MulAut.conj m) ∈ (psuConj h).range
    rw [hι]
    exact ⟨_, rfl⟩
  · intro σ k hσ
    exact descend_mem_of_pow_three_unitary h hq hq9 σ k hσ
  · intro d hd
    obtain ⟨A, hA⟩ := (hd : ι d ∈ (psuConj h).range)
    refine ⟨(A : GL (Fin 3) K), fun m => ?_⟩
    have h1 : unitaryProj h 3 (d m) = unitaryProj h 3 (suConj h A m) := by
      have e1 : ι d (unitaryProj h 3 m) = unitaryProj h 3 (d m) := by
        show (MulAut.congr (suCenterEquiv h hq)) (centerDescend ↥H d)
          (suCenterEquiv h hq (QuotientGroup.mk m)) = suCenterEquiv h hq (QuotientGroup.mk (d m))
        show suCenterEquiv h hq (centerDescend ↥H d
          ((suCenterEquiv h hq).symm (suCenterEquiv h hq (QuotientGroup.mk m)))) = _
        rw [MulEquiv.symm_apply_apply]
        rfl
      rw [← e1, ← hA]
      rfl
    obtain ⟨c, -, -, hc⟩ := mem_unitaryScalars.1
      ((QuotientGroup.eq (s := unitaryScalars h 3)).1 h1.symm)
    refine ⟨c, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_suConj] at hc
    exact inv_mul_eq_iff_eq_mul.1 hc
  · intro z hz
    have hz' : z ∈ unitaryScalars h 3 := by
      rw [← center_unitarySU_three (h := h) hq]
      exact hz
    obtain ⟨c, -, -, hc⟩ := mem_unitaryScalars.1 hz'
    exact ⟨c, hc⟩

end CFSG.HardMathSupport.Solomon.Coordinator
