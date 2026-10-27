module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HU7Gap
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KU6FixLin
import all CFSG.Fischer.F4
public import CFSG.Goldschmidt.Steps.G310Comp
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3LInput
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTM5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD76c
public import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1132
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3Holds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.RankTwoDown
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultSporadic
public import CFSG.LocalAnalysis.GLTheoremA.S4.YS02Holds
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72
public import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalanceThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Transitive
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Inputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item143N
public import CFSG.RankThree.PartTwo.Sec15.Item157
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec17.Item1724Two
public import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.S4Free.SuzukiEight
public import CFSG.Sporadic.HeldB.Common
public import Certificates.Certificate14953
public import Certificates.Certificate7233Base
public import Certificates.Certificate8166

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KU6Cent

namespace GapNine

open Matrix CFSG.Fischer CFSG.Open CFSG.LocalAnalysis.GLTheoremA.HU7

local notation "Mat" => Matrix (Fin 6) (Fin 6) F4
local notation "GL6" => GL (Fin 6) F4

private theorem cube_root_sum_zero :
    ∀ d d' : F4, d ^ 3 = 1 → d' ^ 3 = 1 → d ≠ d' → 1 + d ^ 2 * d' + d * d' ^ 2 = 0 := by
  decide

private theorem prim_cube_facts : ∀ κ : F4, κ ^ 3 = 1 → κ ≠ 1 → κ ^ 2 ≠ 1 ∧ κ ≠ κ ^ 2 := by
  decide

private theorem exists_k_match : ∀ l l' m m' : F4, l ^ 3 = 1 → l' ^ 3 = 1 → m ^ 3 = 1 → m' ^ 3 = 1 →
    l ≠ l' → ∃ k : Fin 3, m * l ^ (k : ℕ) = m' * l' ^ (k : ℕ) := by
  decide

private theorem sq_cube {κ : F4} (hκ3 : κ ^ 3 = 1) : (κ ^ 2) ^ 3 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, hκ3, one_pow]

private def comb (M : Mat) (α : Fin 3 → F4) (x : Fin 6 → F4) : Fin 6 → F4 :=
  α 0 • x + α 1 • (M *ᵥ x) + α 2 • (M *ᵥ (M *ᵥ x))

private theorem comb_mulVec {M X : Mat} (hX : Commute X M) (α : Fin 3 → F4) (x : Fin 6 → F4) :
    X *ᵥ comb M α x = comb M α (X *ᵥ x) := by
  have h1 : ∀ y : Fin 6 → F4, X *ᵥ (M *ᵥ y) = M *ᵥ (X *ᵥ y) := fun y => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hX.eq]
  simp only [comb, Matrix.mulVec_add, Matrix.mulVec_smul, h1]

private theorem comb_zero (M : Mat) (α : Fin 3 → F4) : comb M α 0 = 0 := by
  simp [comb]

private theorem comb_inj {B : GL6} {c : F4ˣ} (hc : c ≠ 1)
    (hB : B ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c) {x : Fin 6 → F4} (hx : x ≠ 0)
    {α β : Fin 3 → F4} (h : comb (B : Mat) α x = comb (B : Mat) β x) : α = β := by
  have hli := KU6Fix.linearIndependent_cyc hc hB hx
  rw [Fintype.linearIndependent_iff] at hli
  have h0 := hli (α - β) (by
    rw [Fin.sum_univ_three]
    have h' : comb (B : Mat) α x - comb (B : Mat) β x = 0 := sub_eq_zero.2 h
    rw [← h']
    simp only [comb, Pi.sub_apply, sub_smul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    abel)
  funext i
  exact sub_eq_zero.1 (h0 i)

private theorem exists_mulVec_ne_zero {P : Mat} (hP : P ≠ 0) : ∃ w : Fin 6 → F4, P *ᵥ w ≠ 0 := by
  by_contra h
  apply hP
  refine Matrix.ext_iff_mulVec.2 fun w => ?_
  rw [Matrix.zero_mulVec]
  by_contra hw
  exact h ⟨w, hw⟩

theorem no_three {B : GL6} {c : F4ˣ} (hc : c ≠ 1) (hB : B ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c)
    {P Q R : Mat} (hP : P * P = P) (hQ : Q * Q = Q) (hR : R * R = R)
    (hPQ : P * Q = 0) (hQP : Q * P = 0) (hPR : P * R = 0) (hRP : R * P = 0) (hQR : Q * R = 0)
    (hRQ : R * Q = 0) (hPM : Commute P (B : Mat)) (hQM : Commute Q (B : Mat)) (hRM : Commute R (B : Mat))
    (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) (hR0 : R ≠ 0) : False := by
  obtain ⟨w₁, hw₁⟩ := exists_mulVec_ne_zero hP0
  obtain ⟨w₂, hw₂⟩ := exists_mulVec_ne_zero hQ0
  obtain ⟨w₃, hw₃⟩ := exists_mulVec_ne_zero hR0
  have hmv : ∀ (X Y : Mat) (w : Fin 6 → F4), X *ᵥ (Y *ᵥ w) = (X * Y) *ᵥ w := fun X Y w =>
    Matrix.mulVec_mulVec _ _ _
  let F : (Fin 3 → F4) × (Fin 3 → F4) × (Fin 3 → F4) → (Fin 6 → F4) := fun t =>
    comb (B : Mat) t.1 (P *ᵥ w₁) + comb (B : Mat) t.2.1 (Q *ᵥ w₂) + comb (B : Mat) t.2.2 (R *ᵥ w₃)
  have hFP : ∀ t, P *ᵥ F t = comb (B : Mat) t.1 (P *ᵥ w₁) := fun t => by
    simp only [F, Matrix.mulVec_add, comb_mulVec hPM, hmv, hP, hPQ, hPR, Matrix.zero_mulVec, comb_zero,
      add_zero]
  have hFQ : ∀ t, Q *ᵥ F t = comb (B : Mat) t.2.1 (Q *ᵥ w₂) := fun t => by
    simp only [F, Matrix.mulVec_add, comb_mulVec hQM, hmv, hQ, hQP, hQR, Matrix.zero_mulVec, comb_zero,
      add_zero, zero_add]
  have hFR : ∀ t, R *ᵥ F t = comb (B : Mat) t.2.2 (R *ᵥ w₃) := fun t => by
    simp only [F, Matrix.mulVec_add, comb_mulVec hRM, hmv, hR, hRP, hRQ, Matrix.zero_mulVec, comb_zero,
      zero_add]
  have hinj : Function.Injective F := by
    rintro ⟨a₁, a₂, a₃⟩ ⟨b₁, b₂, b₃⟩ h
    have e1 := congrArg (fun x => P *ᵥ x) h
    have e2 := congrArg (fun x => Q *ᵥ x) h
    have e3 := congrArg (fun x => R *ᵥ x) h
    simp only [hFP, hFQ, hFR] at e1 e2 e3
    rw [comb_inj hc hB hw₁ e1, comb_inj hc hB hw₂ e2, comb_inj hc hB hw₃ e3]
  have hcard := Fintype.card_le_of_injective F hinj
  simp only [Fintype.card_prod, Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    F4.card] at hcard
  norm_num at hcard

theorem Eig_mul_Eig {Y : Mat} (hY : Y ^ 3 = 1) {d d' : F4} (hd : d ^ 3 = 1) (hd' : d' ^ 3 = 1)
    (hne : d ≠ d') : Eig Y d * Eig Y d' = 0 := by
  have h1 : Y * Eig Y d' = d' • Eig Y d' := B_mul_Eig hY hd'
  have h2 : Y ^ 2 * Eig Y d' = (d' * d') • Eig Y d' := by
    rw [sq, mul_assoc, h1, Matrix.mul_smul, h1, smul_smul]
  show (1 + (d ^ 2) • Y + d • (Y ^ 2)) * Eig Y d' = 0
  rw [add_mul, add_mul, one_mul, smul_mul_assoc, smul_mul_assoc, h1, h2, smul_smul, smul_smul]
  have hs : (1 : F4) + d ^ 2 * d' + d * (d' * d') = 0 := by
    have := cube_root_sum_zero d d' hd hd' hne
    linear_combination this
  calc Eig Y d' + (d ^ 2 * d') • Eig Y d' + (d * (d' * d')) • Eig Y d'
      = ((1 : F4) + d ^ 2 * d' + d * (d' * d')) • Eig Y d' := by
        rw [add_smul, add_smul, one_smul]
    _ = 0 := by rw [hs, zero_smul]

theorem conj_Eig {X Xi Y : Mat} (hXXi : X * Xi = 1) (hXiX : Xi * X = 1) (d : F4) :
    X * Eig Y d * Xi = Eig (X * Y * Xi) d := by
  have hsq : (X * Y * Xi) ^ 2 = X * Y ^ 2 * Xi := by
    rw [sq, sq]
    calc X * Y * Xi * (X * Y * Xi) = X * Y * (Xi * X) * Y * Xi := by noncomm_ring
      _ = X * (Y * Y) * Xi := by rw [hXiX]; noncomm_ring
  show X * (1 + (d ^ 2) • Y + d • (Y ^ 2)) * Xi = 1 + (d ^ 2) • (X * Y * Xi) + d • ((X * Y * Xi) ^ 2)
  rw [hsq, mul_add, mul_add, add_mul, add_mul, mul_one, hXXi, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.smul_mul]

theorem Eig_smul {Y : Mat} {κ : F4} (hκ : κ ^ 3 = 1) (d : F4) : Eig (κ • Y) d = Eig Y (d * κ ^ 2) := by
  show 1 + (d ^ 2) • (κ • Y) + d • ((κ • Y) ^ 2) = 1 + ((d * κ ^ 2) ^ 2) • Y + (d * κ ^ 2) • (Y ^ 2)
  rw [smul_pow, smul_smul, smul_smul]
  have e : d ^ 2 * κ = (d * κ ^ 2) ^ 2 := by linear_combination (-(d ^ 2 * κ)) * hκ
  rw [e]

theorem Eig_commute {Y M : Mat} (hYM : Commute Y M) (d : F4) : Commute (Eig Y d) M :=
  (commute_Eig hYM.symm d).symm

theorem kappa_eq_one {B : GL6} {c : F4ˣ} (hc : c ≠ 1) (hB : B ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c)
    {X Xi Y : Mat} (hXXi : X * Xi = 1) (hXiX : Xi * X = 1) (hY3 : Y ^ 3 = 1) (hYM : Commute Y (B : Mat))
    {κ : F4} (hκ3 : κ ^ 3 = 1) (hconj : X * Y * Xi = κ • Y) : κ = 1 := by
  by_contra hκ1
  obtain ⟨hκ21, hκκ2⟩ := prim_cube_facts κ hκ3 hκ1
  have hconjE : ∀ d : F4, X * Eig Y d * Xi = Eig Y (d * κ ^ 2) := fun d => by
    rw [conj_Eig hXXi hXiX, hconj, Eig_smul hκ3]
  have hκ4 : κ ^ 2 * κ ^ 2 = κ := by linear_combination κ * hκ3
  have hsum : Eig Y 1 + Eig Y κ + Eig Y (κ ^ 2) = 1 := Eig_sum hκ3 hκ1 Y
  have h12 : Eig Y (κ ^ 2) = X * Eig Y 1 * Xi := by rw [hconjE 1, one_mul]
  have h23 : Eig Y κ = X * Eig Y (κ ^ 2) * Xi := by rw [hconjE (κ ^ 2), hκ4]
  have hback : ∀ A : Mat, Xi * (X * A * Xi) * X = A := fun A => by
    calc Xi * (X * A * Xi) * X = (Xi * X) * A * (Xi * X) := by noncomm_ring
      _ = A := by rw [hXiX, one_mul, mul_one]
  have hne1 : Eig Y 1 ≠ 0 := by
    intro h0
    have h2 : Eig Y (κ ^ 2) = 0 := by rw [h12, h0, mul_zero, zero_mul]
    have h3 : Eig Y κ = 0 := by rw [h23, h2, mul_zero, zero_mul]
    rw [h0, h2, h3, add_zero, add_zero] at hsum
    exact zero_ne_one hsum
  have hne2 : Eig Y (κ ^ 2) ≠ 0 := by
    intro h0
    apply hne1
    rw [← hback (Eig Y 1), ← h12, h0, mul_zero, zero_mul]
  have hne3 : Eig Y κ ≠ 0 := by
    intro h0
    apply hne2
    rw [← hback (Eig Y (κ ^ 2)), ← h23, h0, mul_zero, zero_mul]
  have h1c : (1 : F4) ^ 3 = 1 := one_pow 3
  have hκ2c := sq_cube hκ3
  exact no_three hc hB (Eig_mul_self hY3 h1c) (Eig_mul_self hY3 hκ3) (Eig_mul_self hY3 hκ2c)
    (Eig_mul_Eig hY3 h1c hκ3 (Ne.symm hκ1)) (Eig_mul_Eig hY3 hκ3 h1c hκ1)
    (Eig_mul_Eig hY3 h1c hκ2c (Ne.symm hκ21)) (Eig_mul_Eig hY3 hκ2c h1c hκ21)
    (Eig_mul_Eig hY3 hκ3 hκ2c hκκ2) (Eig_mul_Eig hY3 hκ2c hκ3 (Ne.symm hκκ2))
    (Eig_commute hYM 1) (Eig_commute hYM κ) (Eig_commute hYM (κ ^ 2)) hne1 hne3 hne2

theorem scalar_on {B : GL6} {c : F4ˣ} (hc : c ≠ 1) (hB : B ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c)
    {Y A A' : Mat} (hY3 : Y ^ 3 = 1) (hYM : Commute Y (B : Mat)) (hA : A * A = A) (hA' : A' * A' = A')
    (hAA' : A * A' = 0) (hA'A : A' * A = 0) (hAM : Commute A (B : Mat)) (hA'M : Commute A' (B : Mat))
    (hYA : Commute Y A) (hYA' : Commute Y A') (hA'0 : A' ≠ 0) :
    ∃ μ : F4, μ ^ 3 = 1 ∧ Y * A = μ • A := by
  have hω3 : F4.ω ^ 3 = 1 := F4_omega_pow_three
  have hω1 : F4.ω ≠ 1 := F4_omega_ne_one
  obtain ⟨hω21, hωω2⟩ := prim_cube_facts F4.ω hω3 hω1
  have hω2c := sq_cube hω3
  have h1c : (1 : F4) ^ 3 = 1 := one_pow 3
  have hEA : ∀ d : F4, Commute (Eig Y d) A := fun d => (commute_Eig hYA.symm d).symm
  have hEA' : ∀ d : F4, Commute (Eig Y d) A' := fun d => (commute_Eig hYA'.symm d).symm
  have hidem : ∀ d : F4, d ^ 3 = 1 → Eig Y d * A * (Eig Y d * A) = Eig Y d * A := fun d hd => by
    calc Eig Y d * A * (Eig Y d * A) = Eig Y d * (A * Eig Y d) * A := by noncomm_ring
      _ = Eig Y d * Eig Y d * (A * A) := by rw [(hEA d).symm.eq]; noncomm_ring
      _ = Eig Y d * A := by rw [Eig_mul_self hY3 hd, hA]
  have horth : ∀ d d' : F4, d ^ 3 = 1 → d' ^ 3 = 1 → d ≠ d' → Eig Y d * A * (Eig Y d' * A) = 0 :=
    fun d d' hd hd' hne => by
      calc Eig Y d * A * (Eig Y d' * A) = Eig Y d * (A * Eig Y d') * A := by noncomm_ring
        _ = Eig Y d * Eig Y d' * (A * A) := by rw [(hEA d').symm.eq]; noncomm_ring
        _ = 0 := by rw [Eig_mul_Eig hY3 hd hd' hne, zero_mul]
  have hright : ∀ d : F4, Eig Y d * A * A' = 0 := fun d => by rw [mul_assoc, hAA', mul_zero]
  have hleft : ∀ d : F4, A' * (Eig Y d * A) = 0 := fun d => by
    rw [← mul_assoc, (hEA' d).symm.eq, mul_assoc, hA'A, mul_zero]
  have hcomm : ∀ d : F4, Commute (Eig Y d * A) (B : Mat) := fun d => (Eig_commute hYM d).mul_left hAM
  have hpair : ∀ d d' : F4, d ^ 3 = 1 → d' ^ 3 = 1 → d ≠ d' → Eig Y d * A ≠ 0 → Eig Y d' * A ≠ 0 →
      False := fun d d' hd hd' hne h1 h2 =>
    no_three hc hB (hidem d hd) (hidem d' hd') hA' (horth d d' hd hd' hne)
      (horth d' d hd' hd (Ne.symm hne)) (hright d) (hleft d) (hright d') (hleft d') (hcomm d) (hcomm d')
      hA'M h1 h2 hA'0
  have hsum : Eig Y 1 * A + Eig Y F4.ω * A + Eig Y (F4.ω ^ 2) * A = A := by
    rw [← add_mul, ← add_mul, Eig_sum hω3 hω1 Y, one_mul]
  have hYE : ∀ d : F4, d ^ 3 = 1 → Y * (Eig Y d * A) = d • (Eig Y d * A) := fun d hd => by
    rw [← mul_assoc, B_mul_Eig hY3 hd, Matrix.smul_mul]
  by_cases h0 : Eig Y 1 * A = 0
  · by_cases h1 : Eig Y F4.ω * A = 0
    · refine ⟨F4.ω ^ 2, hω2c, ?_⟩
      have hA2 : A = Eig Y (F4.ω ^ 2) * A := by rw [h0, h1, zero_add, zero_add] at hsum; exact hsum.symm
      rw [hA2, hYE _ hω2c]
    · have h2 : Eig Y (F4.ω ^ 2) * A = 0 := by
        by_contra h2
        exact hpair _ _ hω3 hω2c hωω2 h1 h2
      refine ⟨F4.ω, hω3, ?_⟩
      have hA1 : A = Eig Y F4.ω * A := by rw [h0, h2, zero_add, add_zero] at hsum; exact hsum.symm
      rw [hA1, hYE _ hω3]
  · have h1 : Eig Y F4.ω * A = 0 := by
      by_contra h1
      exact hpair _ _ h1c hω3 (Ne.symm hω1) h0 h1
    have h2 : Eig Y (F4.ω ^ 2) * A = 0 := by
      by_contra h2
      exact hpair _ _ h1c hω2c (Ne.symm hω21) h0 h2
    refine ⟨1, h1c, ?_⟩
    have hA0 : A = Eig Y 1 * A := by rw [h1, h2, add_zero, add_zero] at hsum; exact hsum.symm
    rw [hA0, hYE _ h1c]

private theorem pow_mul_eig {Y A : Mat} {l : F4} (h : Y * A = l • A) (k : ℕ) : Y ^ k * A = l ^ k • A := by
  induction k with
  | zero => rw [pow_zero, pow_zero, one_mul, one_smul]
  | succ k ih => rw [pow_succ', mul_assoc, ih, Matrix.mul_smul, h, smul_smul, pow_succ, mul_comm]

private theorem finish_two {Y₀ Y A A' : Mat} (hAA' : A + A' = 1) {l l' m m' : F4} (hl : l ^ 3 = 1)
    (hl' : l' ^ 3 = 1) (hm : m ^ 3 = 1) (hm' : m' ^ 3 = 1) (hne : l ≠ l') (h₀A : Y₀ * A = l • A)
    (h₀A' : Y₀ * A' = l' • A') (hYA : Y * A = m • A) (hYA' : Y * A' = m' • A') :
    ∃ (k : ℕ) (s : F4), Y * Y₀ ^ k = s • 1 := by
  obtain ⟨k, hk⟩ := exists_k_match l l' m m' hl hl' hm hm' hne
  refine ⟨k, m * l ^ (k : ℕ), ?_⟩
  calc Y * Y₀ ^ (k : ℕ) = Y * (Y₀ ^ (k : ℕ) * A) + Y * (Y₀ ^ (k : ℕ) * A') := by
        rw [← mul_add, ← mul_add, hAA', mul_one]
    _ = (m * l ^ (k : ℕ)) • A + (m' * l' ^ (k : ℕ)) • A' := by
        rw [pow_mul_eig h₀A, pow_mul_eig h₀A', Matrix.mul_smul, Matrix.mul_smul, hYA, hYA', smul_smul,
          smul_smul, mul_comm (l ^ (k : ℕ)), mul_comm (l' ^ (k : ℕ))]
    _ = (m * l ^ (k : ℕ)) • 1 := by rw [← hk, ← smul_add, hAA']

theorem exists_mul_pow_eq_smul {B : GL6} {c : F4ˣ} (hc : c ≠ 1)
    (hB : B ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c) {Y₀ Y : Mat} (hY₀3 : Y₀ ^ 3 = 1)
    (hY3 : Y ^ 3 = 1) (hY₀M : Commute Y₀ (B : Mat)) (hYM : Commute Y (B : Mat)) (hYY₀ : Commute Y Y₀)
    (hns : ∀ s : F4, Y₀ ≠ s • 1) : ∃ (k : ℕ) (s : F4), Y * Y₀ ^ k = s • 1 := by
  have hω3 : F4.ω ^ 3 = 1 := F4_omega_pow_three
  have hω1 : F4.ω ≠ 1 := F4_omega_ne_one
  obtain ⟨hω21, hωω2⟩ := prim_cube_facts F4.ω hω3 hω1
  have hω2c := sq_cube hω3
  have h1c : (1 : F4) ^ 3 = 1 := one_pow 3
  set P0 := Eig Y₀ 1 with hP0
  set P1 := Eig Y₀ F4.ω with hP1
  set P2 := Eig Y₀ (F4.ω ^ 2) with hP2
  have hsum : P0 + P1 + P2 = 1 := Eig_sum hω3 hω1 Y₀
  have hI0 : P0 * P0 = P0 := Eig_mul_self hY₀3 h1c
  have hI1 : P1 * P1 = P1 := Eig_mul_self hY₀3 hω3
  have hI2 : P2 * P2 = P2 := Eig_mul_self hY₀3 hω2c
  have h01 : P0 * P1 = 0 := Eig_mul_Eig hY₀3 h1c hω3 (Ne.symm hω1)
  have h10 : P1 * P0 = 0 := Eig_mul_Eig hY₀3 hω3 h1c hω1
  have h02 : P0 * P2 = 0 := Eig_mul_Eig hY₀3 h1c hω2c (Ne.symm hω21)
  have h20 : P2 * P0 = 0 := Eig_mul_Eig hY₀3 hω2c h1c hω21
  have h12 : P1 * P2 = 0 := Eig_mul_Eig hY₀3 hω3 hω2c hωω2
  have h21 : P2 * P1 = 0 := Eig_mul_Eig hY₀3 hω2c hω3 (Ne.symm hωω2)
  have hC0 : Commute P0 (B : Mat) := Eig_commute hY₀M 1
  have hC1 : Commute P1 (B : Mat) := Eig_commute hY₀M F4.ω
  have hC2 : Commute P2 (B : Mat) := Eig_commute hY₀M (F4.ω ^ 2)
  have hY0 : Commute Y P0 := commute_Eig hYY₀ 1
  have hY1 : Commute Y P1 := commute_Eig hYY₀ F4.ω
  have hY2 : Commute Y P2 := commute_Eig hYY₀ (F4.ω ^ 2)
  have hE0 : Y₀ * P0 = (1 : F4) • P0 := B_mul_Eig hY₀3 h1c
  have hE1 : Y₀ * P1 = F4.ω • P1 := B_mul_Eig hY₀3 hω3
  have hE2 : Y₀ * P2 = (F4.ω ^ 2) • P2 := B_mul_Eig hY₀3 hω2c
  have hnot1 : ∀ A : Mat, ∀ l : F4, Y₀ * A = l • A → A ≠ 1 := fun A l h hA1 => by
    rw [hA1, mul_one] at h
    exact hns l h
  by_cases hz0 : P0 = 0
  · have hn1 : P1 ≠ 0 := fun h => hnot1 P2 _ hE2 (by rw [hz0, h, zero_add, zero_add] at hsum; exact hsum)
    have hn2 : P2 ≠ 0 := fun h => hnot1 P1 _ hE1 (by rw [hz0, h, zero_add, add_zero] at hsum; exact hsum)
    obtain ⟨m, hm, hm1⟩ := scalar_on hc hB hY3 hYM hI1 hI2 h12 h21 hC1 hC2 hY1 hY2 hn2
    obtain ⟨m', hm', hm2⟩ := scalar_on hc hB hY3 hYM hI2 hI1 h21 h12 hC2 hC1 hY2 hY1 hn1
    exact finish_two (by rw [hz0, zero_add] at hsum; exact hsum) hω3 hω2c hm hm' hωω2 hE1 hE2 hm1 hm2
  · by_cases hz1 : P1 = 0
    · have hn2 : P2 ≠ 0 := fun h => hnot1 P0 _ hE0 (by rw [hz1, h, add_zero, add_zero] at hsum; exact hsum)
      obtain ⟨m, hm, hm0⟩ := scalar_on hc hB hY3 hYM hI0 hI2 h02 h20 hC0 hC2 hY0 hY2 hn2
      obtain ⟨m', hm', hm2⟩ := scalar_on hc hB hY3 hYM hI2 hI0 h20 h02 hC2 hC0 hY2 hY0 hz0
      exact finish_two (by rw [hz1, add_zero] at hsum; exact hsum) h1c hω2c hm hm' (Ne.symm hω21) hE0 hE2
        hm0 hm2
    · by_cases hz2 : P2 = 0
      · obtain ⟨m, hm, hm0⟩ := scalar_on hc hB hY3 hYM hI0 hI1 h01 h10 hC0 hC1 hY0 hY1 hz1
        obtain ⟨m', hm', hm1⟩ := scalar_on hc hB hY3 hYM hI1 hI0 h10 h01 hC1 hC0 hY1 hY0 hz0
        exact finish_two (by rw [hz2, add_zero] at hsum; exact hsum) h1c hω3 hm hm' (Ne.symm hω1) hE0 hE1
          hm0 hm1
      · exact (no_three hc hB hI0 hI1 hI2 h01 h10 h02 h20 h12 h21 hC0 hC1 hC2 hz0 hz1 hz2).elim

private theorem smul_cancel {a b : F4} {X : Mat} (hX : X ≠ 0) (h : a • X = b • X) : a = b := by
  obtain ⟨i, j, hij⟩ : ∃ i j, X i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hX (Matrix.ext fun i j => hcon i j)
  have h' := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h'
  exact mul_right_cancel₀ hij h'

theorem cube_mul_of_comm_smul {X Y : Mat} {κ : F4} (hκ : κ ^ 3 = 1) (h : Y * X = κ • (X * Y)) :
    (X * Y) ^ 3 = X ^ 3 * Y ^ 3 := by
  calc (X * Y) ^ 3 = X * (Y * X) * (Y * X) * Y := by noncomm_ring
    _ = X * (κ • (X * Y)) * (κ • (X * Y)) * Y := by rw [h]
    _ = (κ * κ) • (X * X * (Y * X) * Y * Y) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
        rw [show X * (X * Y) * (X * Y) * Y = X * X * (Y * X) * Y * Y by noncomm_ring]
    _ = (κ * κ) • (X * X * (κ • (X * Y)) * Y * Y) := by rw [h]
    _ = (κ * κ * κ) • (X ^ 3 * Y ^ 3) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
        rw [show X * X * (X * Y) * Y * Y = X ^ 3 * Y ^ 3 by noncomm_ring]
    _ = X ^ 3 * Y ^ 3 := by rw [show κ * κ * κ = κ ^ 3 by ring, hκ, one_smul]

theorem lift_rel_mat {g g' : Gu} (h : (QuotientGroup.mk g : PGU6) = QuotientGroup.mk g') :
    ∃ s : F4ˣ, (((g' : Gu) : GL6) : Mat) = (s : F4) • (((g : Gu) : GL6) : Mat) := by
  obtain ⟨s, hs⟩ := mem_ZG.1 (QuotientGroup.eq.1 h)
  refine ⟨s, ?_⟩
  have h1 : ((g' : Gu) : GL6) = (g : GL6) * Matrix.GeneralLinearGroup.scalar (Fin 6) s := by
    rw [hs, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  rw [h1, Units.val_mul, coe_scalar_eq, Matrix.mul_smul, Matrix.mul_one]

theorem mem_ZG_of_mat {g : Gu} {s : F4} (h : (((g : Gu) : GL6) : Mat) = s • 1) : g ∈ ZG := by
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at h
    exact Units.ne_zero (g : GL6) h
  exact mem_ZG.2 ⟨Units.mk0 s hs0, Units.ext (by rw [coe_scalar_eq, Units.val_mk0, h])⟩

theorem exists_twist {B : Gu} {E : Subgroup PGU6}
    (hEC : E ≤ Subgroup.centralizer ({(QuotientGroup.mk B : PGU6)} : Set PGU6)) (e : E) :
    ∃ l : F4ˣ, ∀ g : Gu, (QuotientGroup.mk g : PGU6) = e →
      (((B : Gu) : GL6) : Mat) * (((g : Gu) : GL6) : Mat) =
        (l : F4) • ((((g : Gu) : GL6) : Mat) * (((B : Gu) : GL6) : Mat)) := by
  obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk_surjective (e : PGU6)
  have hc := Subgroup.mem_centralizer_singleton_iff.1 (hEC e.2)
  rw [← hg₀, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at hc
  obtain ⟨l, hl⟩ := lift_rel_mat hc
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul] at hl
  refine ⟨l, fun g hg => ?_⟩
  obtain ⟨s, hs⟩ := lift_rel_mat (hg₀.trans hg.symm)
  rw [hs, Matrix.mul_smul, hl, Matrix.smul_mul, smul_comm]

theorem exists_cube {E : Subgroup PGU6} (hE : IsElemAbelian 3 E) (e : E) :
    ∃ n : F4ˣ, ∀ g : Gu, (QuotientGroup.mk g : PGU6) = e →
      (((g : Gu) : GL6) : Mat) ^ 3 = (n : F4) • 1 := by
  obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk_surjective (e : PGU6)
  have h3 : (e : PGU6) ^ 3 = 1 := hE.2 e e.2
  rw [← hg₀, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h3
  obtain ⟨n, hn⟩ := mem_ZG.1 h3
  have hn' : (((g₀ : Gu) : GL6) : Mat) ^ 3 = (n : F4) • 1 := by
    rw [← coe_scalar_eq, hn, Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  refine ⟨n, fun g hg => ?_⟩
  obtain ⟨s, hs⟩ := lift_rel_mat (hg₀.trans hg.symm)
  rw [hs, smul_pow, hn', smul_smul, pow_three_of_units s, one_mul]

private theorem twist_mul {B : Gu} {E : Subgroup PGU6}
    (hEC : E ≤ Subgroup.centralizer ({(QuotientGroup.mk B : PGU6)} : Set PGU6)) (e₁ e₂ : E) :
    (exists_twist hEC (e₁ * e₂)).choose =
      (exists_twist hEC e₁).choose * (exists_twist hEC e₂).choose := by
  obtain ⟨g₁, hg₁⟩ := QuotientGroup.mk_surjective (e₁ : PGU6)
  obtain ⟨g₂, hg₂⟩ := QuotientGroup.mk_surjective (e₂ : PGU6)
  have h12 : (QuotientGroup.mk (g₁ * g₂) : PGU6) = ((e₁ * e₂ : E) : PGU6) := by
    rw [QuotientGroup.mk_mul, hg₁, hg₂, Subgroup.coe_mul]
  have hA := (exists_twist hEC (e₁ * e₂)).choose_spec (g₁ * g₂) h12
  have h1 := (exists_twist hEC e₁).choose_spec g₁ hg₁
  have h2 := (exists_twist hEC e₂).choose_spec g₂ hg₂
  rw [Subgroup.coe_mul, Units.val_mul] at hA
  have hB : (((B : Gu) : GL6) : Mat) * ((((g₁ : Gu) : GL6) : Mat) * (((g₂ : Gu) : GL6) : Mat)) =
      (((exists_twist hEC e₁).choose : F4) * ((exists_twist hEC e₂).choose : F4)) •
        ((((g₁ : Gu) : GL6) : Mat) * (((g₂ : Gu) : GL6) : Mat) * (((B : Gu) : GL6) : Mat)) := by
    rw [← mul_assoc, h1, Matrix.smul_mul, mul_assoc, h2, Matrix.mul_smul, smul_smul, mul_assoc]
  have hne := Units.ne_zero ((g₁ : GL6) * (g₂ : GL6) * (B : GL6))
  rw [Units.val_mul, Units.val_mul] at hne
  apply Units.ext
  rw [Units.val_mul]
  exact smul_cancel hne (hA.symm.trans hB)

private theorem cube_mul {E : Subgroup PGU6} (hE : IsElemAbelian 3 E) (e₁ e₂ : E) :
    (exists_cube hE (e₁ * e₂)).choose = (exists_cube hE e₁).choose * (exists_cube hE e₂).choose := by
  obtain ⟨g₁, hg₁⟩ := QuotientGroup.mk_surjective (e₁ : PGU6)
  obtain ⟨g₂, hg₂⟩ := QuotientGroup.mk_surjective (e₂ : PGU6)
  have h12 : (QuotientGroup.mk (g₁ * g₂) : PGU6) = ((e₁ * e₂ : E) : PGU6) := by
    rw [QuotientGroup.mk_mul, hg₁, hg₂, Subgroup.coe_mul]
  have hA := (exists_cube hE (e₁ * e₂)).choose_spec (g₁ * g₂) h12
  have h1 := (exists_cube hE e₁).choose_spec g₁ hg₁
  have h2 := (exists_cube hE e₂).choose_spec g₂ hg₂
  rw [Subgroup.coe_mul, Units.val_mul] at hA
  have hcomm : (e₁ : PGU6) * e₂ = e₂ * e₁ := elemAbelian_comm hE e₁.2 e₂.2
  rw [← hg₁, ← hg₂, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at hcomm
  obtain ⟨κ, hκ⟩ := lift_rel_mat hcomm
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul] at hκ
  rw [cube_mul_of_comm_smul (pow_three_of_units κ) hκ, h1, h2, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, smul_smul] at hA
  apply Units.ext
  rw [Units.val_mul]
  exact smul_cancel one_ne_zero hA.symm

private noncomputable def twCu {B : Gu} {E : Subgroup PGU6}
    (hEC : E ≤ Subgroup.centralizer ({(QuotientGroup.mk B : PGU6)} : Set PGU6))
    (hE : IsElemAbelian 3 E) : ↥E →* F4ˣ × F4ˣ :=
  MonoidHom.mk' (fun e => ((exists_twist hEC e).choose, (exists_cube hE e).choose)) fun e₁ e₂ =>
    Prod.ext (twist_mul hEC e₁ e₂) (cube_mul hE e₁ e₂)

end GapNine

open Matrix CFSG.Fischer CFSG.Open GapNine

theorem kU6CentGapNine_holds : KU6CentGapNine := by
  intro B c hc1 hB3 E hE hEC
  set f := twCu hEC hE with hfdef
  have hker : ∀ e ∈ f.ker, ∀ g : Gu, (QuotientGroup.mk g : PGU6) = e →
      Commute (((g : Gu) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)
        (((B : Gu) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) ∧
        (((g : Gu) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) ^ 3 = 1 := by
    intro e he g hg
    rw [MonoidHom.mem_ker] at he
    have h1 : (exists_twist hEC e).choose = 1 := congrArg Prod.fst he
    have h2 : (exists_cube hE e).choose = 1 := congrArg Prod.snd he
    have ht := (exists_twist hEC e).choose_spec g hg
    have hcu := (exists_cube hE e).choose_spec g hg
    rw [h1, Units.val_one, one_smul] at ht
    rw [h2, Units.val_one, one_smul] at hcu
    exact ⟨ht.symm, hcu⟩
  have hkercard : Nat.card f.ker ≤ 3 := by
    by_cases hex : ∃ e₀ ∈ f.ker, e₀ ≠ 1
    · obtain ⟨e₀, he₀, hne⟩ := hex
      have hle : f.ker ≤ Subgroup.zpowers e₀ := by
        intro e he
        obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk_surjective ((e₀ : E) : PGU6)
        obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective ((e : E) : PGU6)
        obtain ⟨hY₀M, hY₀3⟩ := hker e₀ he₀ g₀ hg₀
        obtain ⟨hYM, hY3⟩ := hker e he g hg
        have hns : ∀ s : F4, (((g₀ : Gu) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) ≠ s • 1 := by
          intro s hs
          apply hne
          apply Subtype.ext
          rw [← hg₀, OneMemClass.coe_one, QuotientGroup.eq_one_iff]
          exact mem_ZG_of_mat hs
        have hcomm : (e₀ : PGU6) * e = e * e₀ := elemAbelian_comm hE e₀.2 e.2
        rw [← hg₀, ← hg, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at hcomm
        obtain ⟨κ, hκ⟩ := lift_rel_mat hcomm
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul] at hκ
        have hconj : (((g : Gu) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *
            (((g₀ : Gu) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *
              ((((g : Gu) : GL (Fin 6) F4)⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
            (κ : F4) • (((g₀ : Gu) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) := by
          rw [hκ, Matrix.smul_mul, mul_assoc, Units.mul_inv, mul_one]
        have hκ1 := kappa_eq_one hc1 hB3 (Units.mul_inv _) (Units.inv_mul _) hY₀3 hY₀M
          (pow_three_of_units κ) hconj
        rw [hκ1, one_smul] at hκ
        obtain ⟨k, s, hks⟩ := exists_mul_pow_eq_smul hc1 hB3 hY₀3 hY3 hY₀M hYM hκ hns
        have hmem : g * g₀ ^ k ∈ ZG := mem_ZG_of_mat (by
          rw [Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val]
          exact hks)
        have h1 : e * e₀ ^ k = 1 := by
          apply Subtype.ext
          rw [Subgroup.coe_mul, Subgroup.coe_pow, OneMemClass.coe_one, ← hg, ← hg₀, ← QuotientGroup.mk_pow,
            ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
          exact hmem
        rw [Subgroup.mem_zpowers_iff]
        exact ⟨-(k : ℤ), by rw [_root_.zpow_neg, zpow_natCast]; exact (eq_inv_of_mul_eq_one_left h1).symm⟩
      have h3 : e₀ ^ 3 = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow, OneMemClass.coe_one]; exact hE.2 _ e₀.2)
      calc Nat.card f.ker ≤ Nat.card (Subgroup.zpowers e₀) := Subgroup.card_le_of_le hle
        _ = orderOf e₀ := Nat.card_zpowers e₀
        _ ≤ 3 := orderOf_le_of_pow_eq_one (by norm_num) h3
    · have hbot : f.ker = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro e he
        by_contra hne
        exact hex ⟨e, he, hne⟩
      rw [hbot, Subgroup.card_bot]
      norm_num
  have hrange : Nat.card f.range ≤ 9 := by
    calc Nat.card f.range ≤ Nat.card (F4ˣ × F4ˣ) := Subgroup.card_le_card_group _
      _ = 9 := by rw [Nat.card_prod, Nat.card_units, Nat.card_eq_fintype_card, F4.card]
  have hEcard : Nat.card E = Nat.card f.range * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  rw [hEcard]
  calc Nat.card f.range * Nat.card f.ker ≤ 9 * 3 := Nat.mul_le_mul hrange hkercard
    _ = 3 ^ 3 := by norm_num

end CFSG.LocalAnalysis.GLTheoremA.KU6Cent

end
