module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Red
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldUniLabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldUniMark
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniData
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniScal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniCore
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.Assembly.OpenBridges
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3LInput
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD76c
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1132
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3Holds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.RankTwoDown
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultSporadic
public import CFSG.LocalAnalysis.GLTheoremA.S4.YS02Holds
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72
public import CFSG.LocalAnalysis.GLTheoremA.S6.Setup
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

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA.S10
  CFSG.LocalAnalysis.GLTheoremA.Y10GField CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni
  CFSG.LieType.SemisimpleCentralizers.HeldLang
open CFSG.LieType.SemisimpleCentralizers.Held (heldGU heldSU mem_heldGU hct_heldSU_eq_statedSU)

private theorem exists_psu_aux {T : Type} [Group T] (r P X : ℕ) [Fact P.Prime] (hP : P = 2) (hX : 1 ≤ X)
    (hr : 2 ≤ r) (hnq : (r + 1, P ^ X) ≠ (3, 2))
    (e : T ≃* StatedProj (StatedSU (r + 1) (P ^ X) (GaloisField P (2 * X)))) :
    ∃ (a m : ℕ) (E : Type) (_ : Field E) (_ : Finite E), 3 ≤ a ∧ Nat.card E = (2 ^ m) ^ 2 ∧
      (a, 2 ^ m) ≠ (3, 2) ∧ Nonempty (T ≃* StatedProj (StatedSU a (2 ^ m) E)) := by
  subst hP
  haveI : NeZero (2 * X) := ⟨by omega⟩
  refine ⟨r + 1, X, GaloisField 2 (2 * X), inferInstance, inferInstance, by omega, ?_, hnq, ⟨e⟩⟩
  rw [GaloisField.card 2 (2 * X) (by omega), ← pow_mul, mul_comm]

theorem exists_psu_of_l154Uni {T : Type} [Group T] (h : catalogIs T l154Uni) :
    ∃ (a m : ℕ) (E : Type) (_ : Field E) (_ : Finite E), 3 ≤ a ∧ Nat.card E = (2 ^ m) ^ 2 ∧
      (a, 2 ^ m) ≠ (3, 2) ∧ Nonempty (T ≃* StatedProj (StatedSU a (2 ^ m) E)) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [l154Uni, onLie] at hi
  | alternating n hn => simp [l154Uni, onLie] at hi
  | sporadic s => simp [l154Uni, onLie] at hi
  | lie d =>
    obtain ⟨t, hv⟩ := d
    cases t with
    | twistedA r q =>
      have hq : q.p = 2 := by simpa [l154Uni, onLie] using hi
      haveI : Fact q.p.Prime := ⟨q.prime_p⟩
      have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
        ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
      have hr : 2 ≤ r := hrange.1
      have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = q.p := by
        change (TauCeti.LieTypeIndex.twistedA r q).characteristic = q.p
        simp
      have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩ = q.exponent := by
        change (TauCeti.LieTypeIndex.twistedA r q).fieldExponent = q.exponent
        simp
      have hnq : (r + 1, TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ ^
          TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩) ≠ (3, 2) := by
        intro hcc
        have h1 : r + 1 = 3 := congrArg Prod.fst hcc
        have h2 : q.p ^ q.exponent = 2 := by
          have := congrArg Prod.snd hcc
          simpa only [hc, hf] using this
        have hrq := hrange.2 (by omega : r = 2)
        rw [TauCeti.PrimePower.card_def] at hrq
        omega
      exact exists_psu_aux r _ _ (hc.trans hq) (by rw [hf]; exact q.exponent_pos) hr hnq
        (e.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj r q hv))
    | _ => simp [l154Uni, onLie] at hi

theorem famUni_of_canon {lab : GLALabel} {a m : ℕ} (h : canonLabel lab = ⟨.twA, a, m⟩) : FamUni lab := by
  obtain ⟨tag, rank, n⟩ := lab
  cases tag
  all_goals first
    | exact Or.inl rfl
    | (simp [canonLabel] at h; done)
    | skip
  · by_cases h3 : rank = 3
    · simp [canonLabel, h3] at h
    · simp [canonLabel, h3] at h
  · by_cases h3 : rank = 3
    · exact Or.inr ⟨rfl, h3⟩
    · by_cases h2 : rank = 2
      · simp [canonLabel, h3, h2] at h
      · simp [canonLabel, h3, h2] at h

theorem l154_exists_moved_of_odd {K : Type} [Field K] (bar σ : K ≃+* K) (hbb : ∀ c, bar (bar c) = c)
    (hcomm : ∀ c, σ (bar c) = bar (σ c)) {p : ℕ} (hp : Odd p) (hσp : σ ^ p = 1) (hσ1 : σ ≠ 1) :
    ∃ c : K, bar c = c ∧ σ c ≠ c := by
  by_contra hcon
  push_neg at hcon
  have hroot : ∀ c, σ c = c ∨ σ c = bar c := by
    intro c
    have hs : bar (c + bar c) = c + bar c := by rw [map_add, hbb, add_comm]
    have hn : bar (c * bar c) = c * bar c := by rw [map_mul, hbb, mul_comm]
    have hs' := hcon _ hs
    have hn' := hcon _ hn
    rw [map_add, hcomm] at hs'
    rw [map_mul, hcomm] at hn'
    have h0 : (σ c - c) * (σ c - bar c) = 0 := by
      have e : (σ c - c) * (σ c - bar c) = σ c * σ c - (c + bar c) * σ c + c * bar c := by ring
      rw [e, ← hs', ← hn']
      ring
    rcases mul_eq_zero.1 h0 with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (sub_eq_zero.1 h)
  have hall : σ = bar := by
    by_contra hne
    obtain ⟨c0, hc0⟩ : ∃ c0, σ c0 ≠ c0 := by
      by_contra h
      push_neg at h
      exact hσ1 (RingEquiv.ext h)
    have hc0b : σ c0 = bar c0 := (hroot c0).resolve_left hc0
    obtain ⟨c1, hc1⟩ : ∃ c1, σ c1 ≠ bar c1 := by
      by_contra h
      push_neg at h
      exact hne (RingEquiv.ext h)
    have hc1' : σ c1 = c1 := (hroot c1).resolve_right hc1
    rcases hroot (c1 + c0) with h | h
    · rw [map_add, hc1', hc0b] at h
      exact hc0 (hc0b.trans (add_left_cancel h))
    · rw [map_add, hc1', hc0b, map_add] at h
      exact hc1 (hc1'.trans (add_right_cancel h))
  have h2 : σ ^ 2 = 1 := by
    rw [hall]
    exact RingEquiv.ext fun c => hbb c
  obtain ⟨k, rfl⟩ := hp
  apply hσ1
  rw [← hσp, pow_succ, pow_mul, h2, one_pow, one_mul]

theorem l154_uni_pow_scalar {K : Type} [Field K] [Finite K] {n d : ℕ} {τ : K ≃+* K}
    (hτ : ∀ x, τ (τ x) = x) (hτq : ∀ x, τ x = x ^ 2 ^ n) (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hd : 3 ≤ d) (hdQ : (d, 2 ^ n) ≠ (3, 2)) (A : GL (Fin d) K) (hA : A ∈ heldGU d K τ hτ) {p : ℕ}
    (u : MulAut (StatedProj (StatedSU d (2 ^ n) K)))
    (hu : ∀ g g' : ↥(StatedSU d (2 ^ n) K), (g' : GL (Fin d) K) = A * (g : GL (Fin d) K) * A⁻¹ →
      u (LargeEvenProjMk (StatedSU d (2 ^ n) K) g) = LargeEvenProjMk (StatedSU d (2 ^ n) K) g')
    (hpow : u ^ p = 1) : ∃ c : Kˣ, A ^ p = Matrix.GeneralLinearGroup.scalar (Fin d) c := by
  have hH : heldSU d K τ hτ = StatedSU d (2 ^ n) K := hct_heldSU_eq_statedSU (a := d) hτq
  have hnorm : ∀ g : GL (Fin d) K, g ∈ heldGU d K τ hτ → ∀ x ∈ StatedSU d (2 ^ n) K,
      g * x * g⁻¹ ∈ StatedSU d (2 ^ n) K := by
    intro g hg x hx
    rw [← hH] at hx ⊢
    exact heldSU_normal_in_heldGU hτ g hg x hx
  let cA : MulAut ↥(StatedSU d (2 ^ n) K) :=
    uniConjSub (StatedSU d (2 ^ n) K) A (hnorm A hA) (hnorm A⁻¹ (inv_mem hA))
  have hpowk : ∀ (k : ℕ) (h h' : ↥(StatedSU d (2 ^ n) K)),
      (h' : GL (Fin d) K) = A ^ k * (h : GL (Fin d) K) * (A ^ k)⁻¹ →
      (u ^ k) (LargeEvenProjMk (StatedSU d (2 ^ n) K) h) = LargeEvenProjMk (StatedSU d (2 ^ n) K) h' := by
    intro k
    induction k with
    | zero =>
      intro h h' hk
      have : h' = h := by
        apply Subtype.ext
        simpa using hk
      subst this
      simp
    | succ k ih =>
      intro h h' hk
      have step1 : u (LargeEvenProjMk (StatedSU d (2 ^ n) K) h) =
          LargeEvenProjMk (StatedSU d (2 ^ n) K) (cA h) := hu h (cA h) rfl
      have step2 := ih (cA h) h' (by
        rw [hk, uniConjSub_apply_val, pow_succ]
        group)
      rw [pow_succ, MulAut.mul_apply, step1, step2]
  have hAp : A ^ p ∈ heldGU d K τ hτ := pow_mem hA p
  have hconjB : ∀ g : GL (Fin d) K, g ∈ StatedSU d (2 ^ n) K → ∃ c : K,
      ((A ^ p : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (g : Matrix (Fin d) (Fin d) K) *
        (((A ^ p)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = c • (g : Matrix (Fin d) (Fin d) K) := by
    intro g hg
    let h : ↥(StatedSU d (2 ^ n) K) := ⟨g, hg⟩
    let h' : ↥(StatedSU d (2 ^ n) K) := ⟨A ^ p * g * (A ^ p)⁻¹, hnorm (A ^ p) hAp g hg⟩
    have hk : (h' : GL (Fin d) K) = A ^ p * (h : GL (Fin d) K) * (A ^ p)⁻¹ := rfl
    have hmk : LargeEvenProjMk (StatedSU d (2 ^ n) K) h' = LargeEvenProjMk (StatedSU d (2 ^ n) K) h := by
      have h1 := hpowk p h h' hk
      rw [hpow] at h1
      simpa using h1.symm
    obtain ⟨c, hc⟩ := (projMk_eq_iff_uni (StatedSU d (2 ^ n) K) h' h).mp hmk
    have hh' : (h' : GL (Fin d) K) =
        (h : GL (Fin d) K) * (Matrix.GeneralLinearGroup.scalar (Fin d) c)⁻¹ := by
      rw [hc]
      group
    have hGL : A ^ p * g * (A ^ p)⁻¹ = g * (Matrix.GeneralLinearGroup.scalar (Fin d) c)⁻¹ := hh'
    refine ⟨(c : K)⁻¹, ?_⟩
    have hM := congrArg (fun X : GL (Fin d) K => (X : Matrix (Fin d) (Fin d) K)) hGL
    simp only [Units.val_mul] at hM
    rw [hM, ← map_inv, CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.val_scalar_gl,
      Units.val_inv_eq_inv_val, Matrix.mul_smul, Matrix.mul_one]
  obtain ⟨c0, hc0⟩ := uniScalar_holds K (2 ^ n) d τ hτ hτq hcard hd hdQ (A ^ p) hconjB
  have hc0ne : c0 ≠ 0 := by
    rintro rfl
    have h1 := congrArg (fun X : GL (Fin d) K => ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K))
      (mul_inv_cancel (A ^ p))
    simp only [Units.val_mul, Units.val_one] at h1
    rw [hc0, zero_smul, Matrix.zero_mul] at h1
    have h2 := congrFun (congrFun h1 ⟨0, by omega⟩) ⟨0, by omega⟩
    simp at h2
  refine ⟨Units.mk0 c0 hc0ne, ?_⟩
  ext i j
  rw [hc0]
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]

end CFSG.LocalAnalysis.GLTheoremA.K155X
