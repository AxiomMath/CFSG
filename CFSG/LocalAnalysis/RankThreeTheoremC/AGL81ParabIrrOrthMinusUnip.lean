module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthMinusComm
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthMinusModel
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrOrthMinusSec

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.OrthMinus

open Module QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.AGLEmbedding.LeviBlock
  CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} {r s : ℕ} {d : Fin (s + 1) → ℕ}

local notation "𝕍" => (Fin r ⊕ Fin r → K) × (Fin 2 → K)

theorem pow_two_pow_eq_one_of_trivial_sections (hd : OrthCuts r d) {f : 𝕍 ≃ₗ[K] 𝕍}
    (hiso : ∀ v, quadTail r (minusTailForm K b c) (f v) = quadTail r (minusTailForm K b c) v)
    (hsec : ∀ l : Fin s, ∀ v ∈ tailFlag K (Fin 2 → K) r (d l.succ),
      f v - v ∈ tailFlag K (Fin 2 → K) r (d l.castSucc))
    (hres : TrivRes hd.last f) : f ^ 2 ^ (2 * s + 1) = 1 := by
  have hgO : f ∈ TauCeti.QuadraticMap.orthogonalGroup (quadTail r (minusTailForm K b c)) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 hiso
  have hpol : ∀ x y, polarBilin (quadTail r (minusTailForm K b c)) (f x) (f y) =
      polarBilin (quadTail r (minusTailForm K b c)) x y := fun x y => by
    simp only [polarBilin_apply_apply, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO]
  let F : ℕ → Submodule K 𝕍 := fun i =>
    tailFlag K (Fin 2 → K) r (if h : i ≤ s then d ⟨i, Nat.lt_succ_of_le h⟩ else d (Fin.last s))
  have hFl : ∀ (i : ℕ) (hi : i ≤ s),
      F i = tailFlag K (Fin 2 → K) r (d ⟨i, Nat.lt_succ_of_le hi⟩) := fun i hi => by
    simp [F, hi]
  have hpow := CFSG.SeitzReduction.OmegaPilot.sub_one_pow_eq_zero_of_isotropic_flag
    (polarBilin (quadTail r (minusTailForm K b c))) (g := f) hpol F
    (by
      rw [hFl 0 (by omega),
        show (⟨0, Nat.lt_succ_of_le (Nat.zero_le s)⟩ : Fin (s + 1)) = 0 from rfl,
        hd.zero, tailFlag_zero])
    s (fun i hi => by
      rw [hFl i (by omega), hFl (i + 1) (by omega)]
      exact orthTailFlag_mono (hd.mono.monotone (Fin.mk_le_mk.2 (by omega))))
    (fun i hi v hv => by
      rw [hFl (i + 1) (by omega)] at hv
      rw [hFl i (by omega)]
      exact hsec ⟨i, hi⟩ v hv)
    (fun v hv => by
      rw [hFl s (by omega)] at hv ⊢
      refine hres v
        ((polar_tailFlag_eq_zero_iff (qB := minusTailForm K b c) hd.last).1 fun w hw => ?_)
      rw [polar_comm]
      exact (LinearMap.BilinForm.mem_orthogonal_iff.1 hv) w hw)
  exact CFSG.SeitzReduction.OmegaPilot.pow_two_pow_eq_one_of_sub_one_pow_eq_zero hpow

theorem trivRes_of_scalarMod (hd : OrthCuts r d) {f : 𝕍 ≃ₗ[K] 𝕍}
    (hiso : ∀ v, quadTail r (minusTailForm K b c) (f v) = quadTail r (minusTailForm K b c) v)
    {a : K} (ha : ScalarMod (perpSub (K := K) (r := r) hd.last)
      (tailFlag K (Fin 2 → K) r (d (Fin.last s))) f a) : TrivRes hd.last f := by
  set v₀ : 𝕍 := ((0 : Fin r ⊕ Fin r → K), (Pi.single 0 1 : Fin 2 → K)) with hv₀def
  have hv₀P : IsResPerp hd.last v₀ := fun i => rfl
  have hQ0 : quadTail r (minusTailForm K b c) v₀ ≠ 0 := by
    rw [hv₀def, quadTail_tail, minusTailForm_apply]
    simp
  have hw := ha v₀ (mem_perpSub.2 hv₀P)
  have hpol : polar (quadTail r (minusTailForm K b c)) v₀ (f v₀ - a • v₀) = 0 :=
    (polar_tailFlag_eq_zero_iff (qB := minusTailForm K b c) hd.last).2 hv₀P _ hw
  have hdec : f v₀ = a • v₀ + (f v₀ - a • v₀) := by abel
  have h1 := hiso v₀
  rw [hdec, QuadraticMap.map_add (quadTail r (minusTailForm K b c)), QuadraticMap.map_smul,
    polar_smul_left, hpol, quadTail_eq_zero_of_mem_tailFlag hw] at h1
  have hcc : a * a = 1 := by
    have h2 : (a * a) • quadTail r (minusTailForm K b c) v₀ =
        quadTail r (minusTailForm K b c) v₀ := by
      simpa using h1
    rw [smul_eq_mul] at h2
    exact mul_right_cancel₀ hQ0 (by rw [one_mul]; exact h2)
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h8 : (a - 1) ^ 2 = 0 := by linear_combination hcc + (1 - a) * h2
  have ha1 : a = 1 := sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h8)
  intro v hv
  have h3 := ha v (mem_perpSub.2 hv)
  rwa [ha1, one_smul] at h3

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.OrthMinus
