module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Phan.PhanS4Std
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q7

open CFSG.ClassicalInvolution.PhanB3.S.Std

variable {K : Type} [Field K]

theorem pr_bf_add_right (M : Model K) (x y z : Vec K) :
    bf M x (y + z) = bf M x y + bf M x z := by
  rw [bf_comm, bf_add_left, bf_comm M y x, bf_comm M z x]

theorem pr_bf_zero_right (M : Model K) (x : Vec K) : bf M x 0 = 0 := by
  have := bf_smul_right M 0 x x
  simpa using this

theorem pr_tauV_zero (M : Model K) : tauV M (0 : Vec K) = 0 := by
  funext s
  rcases s with i | i | u <;> simp [tauV]

theorem pr_tauV_sub (M : Model K) (x y : Vec K) : tauV M (x - y) = tauV M x - tauV M y := by
  funext s
  rcases s with i | i | u <;> simp [tauV]

structure PairData (M : Model K) (a c : Vec K) (γ η : K) : Prop where
  ffa : bf M a a = 0
  ffc : bf M c c = 0
  bac : bf M a c = 1
  haa : her M a a = 1
  hcc : her M c c = γ
  hac : her M a c = η

@[expose] def Rel (M : Model K) (a c : Vec K) (μ₁ μ₂ μ₃ μ₄ : K) : Prop :=
  μ₁ • a + μ₂ • c + μ₃ • tauV M a + μ₄ • tauV M c = 0

theorem Rel.zero (M : Model K) (a c : Vec K) : Rel M a c 0 0 0 0 := by
  simp [Rel]

theorem PairData.ker {M : Model K} {a c : Vec K} {γ η : K} (h : PairData M a c γ η)
    {μ₁ μ₂ μ₃ μ₄ : K} (hr : Rel M a c μ₁ μ₂ μ₃ μ₄) :
    μ₂ + μ₃ + η * μ₄ = 0 ∧ μ₁ + M.τ η * μ₃ + γ * μ₄ = 0 ∧ μ₁ + M.τ η * μ₂ + μ₄ = 0 ∧
      η * μ₁ + γ * μ₂ + μ₃ = 0 := by
  have b_aa := h.ffa
  have b_ac := h.bac
  have b_ca : bf M c a = 1 := by rw [bf_comm]; exact b_ac
  have b_cc := h.ffc
  have b_asa : bf M a (tauV M a) = 1 := h.haa
  have b_sa_a : bf M (tauV M a) a = 1 := by rw [bf_comm]; exact b_asa
  have b_asc : bf M a (tauV M c) = η := h.hac
  have b_sc_a : bf M (tauV M c) a = η := by rw [bf_comm]; exact b_asc
  have hca : her M c a = M.τ η := by rw [her_conj_symm, h.hac]
  have b_csa : bf M c (tauV M a) = M.τ η := hca
  have b_sa_c : bf M (tauV M a) c = M.τ η := by rw [bf_comm]; exact b_csa
  have b_csc : bf M c (tauV M c) = γ := h.hcc
  have b_sc_c : bf M (tauV M c) c = γ := by rw [bf_comm]; exact b_csc
  have b_sasa : bf M (tauV M a) (tauV M a) = 0 := by rw [bf_tauV, b_aa, map_zero]
  have b_scsc : bf M (tauV M c) (tauV M c) = 0 := by rw [bf_tauV, b_cc, map_zero]
  have b_sasc : bf M (tauV M a) (tauV M c) = 1 := by rw [bf_tauV, b_ac, map_one]
  have b_scsa : bf M (tauV M c) (tauV M a) = 1 := by rw [bf_comm]; exact b_sasc
  have e1 := congrArg (bf M a) hr
  have e2 := congrArg (bf M c) hr
  have e3 := congrArg (bf M (tauV M a)) hr
  have e4 := congrArg (bf M (tauV M c)) hr
  simp only [pr_bf_add_right, bf_smul_right, pr_bf_zero_right] at e1 e2 e3 e4
  rw [b_aa, b_ac, b_asa, b_asc] at e1
  rw [b_ca, b_cc, b_csa, b_csc] at e2
  rw [b_sa_a, b_sa_c, b_sasa, b_sasc] at e3
  rw [b_sc_a, b_sc_c, b_scsa, b_scsc] at e4
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination e1
  · linear_combination e2
  · linear_combination e3
  · linear_combination e4

@[expose] def pairDisc (γ η η' : K) : K := (1 - γ - η * η') ^ 2 - 4 * γ * (η * η')

theorem disc_mul_mu2 {γ η η' μ₁ μ₂ μ₃ μ₄ : K} (e1 : μ₂ + μ₃ + η * μ₄ = 0)
    (e2 : μ₁ + η' * μ₃ + γ * μ₄ = 0) (e3 : μ₁ + η' * μ₂ + μ₄ = 0)
    (e4 : η * μ₁ + γ * μ₂ + μ₃ = 0) : pairDisc γ η η' * μ₂ = 0 := by
  unfold pairDisc
  linear_combination (-2 * η * η' - (γ - 1 - η * η')) * e1 + (2 * η) * e2 +
    (-2 * η - (γ - 1 - η * η') * η) * e3 + (γ - 1 - η * η') * e4

theorem disc_mul_mu4 {γ η η' μ₁ μ₂ μ₃ μ₄ : K} (e1 : μ₂ + μ₃ + η * μ₄ = 0)
    (e2 : μ₁ + η' * μ₃ + γ * μ₄ = 0) (e3 : μ₁ + η' * μ₂ + μ₄ = 0)
    (e4 : η * μ₁ + γ * μ₂ + μ₃ = 0) : pairDisc γ η η' * μ₄ = 0 := by
  unfold pairDisc
  linear_combination (-(γ - 1 - η * η') * η' - 2 * η' * 1) * e1 + (γ - 1 - η * η') * e2 +
    (-(γ - 1 - η * η') + 2 * η' * (-η)) * e3 + (2 * η') * e4

theorem ker_zero_of_disc {γ η η' μ₁ μ₂ μ₃ μ₄ : K} (hΔ : pairDisc γ η η' ≠ 0)
    (e1 : μ₂ + μ₃ + η * μ₄ = 0) (e2 : μ₁ + η' * μ₃ + γ * μ₄ = 0)
    (e3 : μ₁ + η' * μ₂ + μ₄ = 0) (e4 : η * μ₁ + γ * μ₂ + μ₃ = 0) :
    μ₁ = 0 ∧ μ₂ = 0 ∧ μ₃ = 0 ∧ μ₄ = 0 := by
  have hμ₂ : μ₂ = 0 := (mul_eq_zero.mp (disc_mul_mu2 e1 e2 e3 e4)).resolve_left hΔ
  have hμ₄ : μ₄ = 0 := (mul_eq_zero.mp (disc_mul_mu4 e1 e2 e3 e4)).resolve_left hΔ
  have hμ₃ : μ₃ = 0 := by rw [hμ₂, hμ₄] at e1; linear_combination e1
  have hμ₁ : μ₁ = 0 := by rw [hμ₂, hμ₄] at e3; linear_combination e3
  exact ⟨hμ₁, hμ₂, hμ₃, hμ₄⟩

theorem ker_line {γ η η' μ₁ μ₂ μ₃ μ₄ : K} (h2 : (2 : K) ≠ 0) (hη' : η' ≠ 0)
    (e1 : μ₂ + μ₃ + η * μ₄ = 0) (e2 : μ₁ + η' * μ₃ + γ * μ₄ = 0)
    (e3 : μ₁ + η' * μ₂ + μ₄ = 0) :
    ∃ t : K, μ₁ = t * (-(η' * (γ - 1 - η * η' + 2))) ∧ μ₂ = t * (γ - 1 - η * η') ∧
      μ₃ = t * (-(γ - 1 - η * η' + 2 * (η * η'))) ∧ μ₄ = t * (2 * η') := by
  have h2η : 2 * η' ≠ 0 := mul_ne_zero h2 hη'
  have eq1 : -2 * η' * μ₂ + (γ - 1 - η * η') * μ₄ = 0 := by
    linear_combination e2 - e3 - η' * e1
  refine ⟨μ₄ / (2 * η'), ?_, ?_, ?_, ?_⟩
  · have hμ₂ : μ₂ = μ₄ / (2 * η') * (γ - 1 - η * η') := by
      field_simp
      linear_combination -eq1
    have hμ₁ : μ₁ = -η' * μ₂ - μ₄ := by linear_combination e3
    rw [hμ₁, hμ₂]
    field_simp
    ring
  · field_simp
    linear_combination -eq1
  · have hμ₂ : μ₂ = μ₄ / (2 * η') * (γ - 1 - η * η') := by
      field_simp
      linear_combination -eq1
    have hμ₃ : μ₃ = -μ₂ - η * μ₄ := by linear_combination e1
    rw [hμ₃, hμ₂]
    field_simp
    ring
  · field_simp

theorem ker_special {γ η μ₁ μ₂ μ₃ μ₄ : K} (hγ : γ = 1) (hη : η = 0)
    (e1 : μ₂ + μ₃ + η * μ₄ = 0) (e2 : μ₁ + (0 : K) * μ₃ + γ * μ₄ = 0) :
    μ₃ = -μ₂ ∧ μ₄ = -μ₁ := by
  subst hγ hη
  exact ⟨by linear_combination e1, by linear_combination e2⟩

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q7
