module

public import CFSG.GF2Type.Smith1979W3.Cert690.SqCommon
public import CFSG.GF2Type.Smith1979W3.Cert690.SqData

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62

variable {K : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)} {σ : (Q0 ≃* Q0) → Q0}

private theorem repThetas_get {reps : Array ℕ} {i : ℕ} (hi : i < reps.size) :
    (repThetas reps)[i]! = liftTab reps[i]! 0 := by
  rw [repThetas]
  have h1 : i < (reps.map fun r => liftTab r 0).size := by rwa [Array.size_map]
  rw [getElem!_pos _ i h1, Array.getElem_map, getElem!_pos _ i hi]

private theorem repThetas_size {reps : Array ℕ} : (repThetas reps).size = reps.size := by
  simp [repThetas]

private theorem rep_root_lt {reps : Array ℕ} {hroots : rootsOK (innTabs ()) (repThetas reps) = true}
    {i : ℕ} (hi : i < (repThetas reps).size) :
    (repRoot (innTabs ()) (repThetas reps))[i]! < 128 := by
  have hmem : (repRoot (innTabs ()) (repThetas reps))[i]! ∈
      innRoots (innTabs ()) (compTab (repThetas reps)[i]! (repThetas reps)[i]!) :=
    (rootsOK_spec hroots hi _).mpr (Or.inl rfl)
  exact (mem_innRoots_iff.mp hmem).1

private theorem rep_root_z_lt {reps : Array ℕ}
    {hroots : rootsOK (innTabs ()) (repThetas reps) = true}
    {i : ℕ} (hi : i < (repThetas reps).size) :
    qmulN ((repRoot (innTabs ()) (repThetas reps))[i]!) z0N < 128 := by
  have h1 : enc (dec ((repRoot (innTabs ()) (repThetas reps))[i]!) * z0) =
      qmulN ((repRoot (innTabs ()) (repThetas reps))[i]!) z0N := by
    rw [← qmulN_enc, enc_dec (rep_root_lt (hroots := hroots) hi), enc_z0]
  rw [← h1]
  exact enc_lt _

private theorem rep_sigma_disj (h : IsSquareData K σ) {reps : Array ℕ} (hsize : reps.size = 2)
    (hrep : ∀ i < 2, ∃ r ∈ K, r * r = 1 ∧
      Code.HasCode (r : V₀ →ₗ[ZMod 2] V₀) reps[i]!)
    (hhom : ∀ i < 2, isHomTab (liftTab reps[i]! 0) = true)
    (hroots : rootsOK (innTabs ()) (repThetas reps) = true) {i : ℕ} (hi : i < 2) :
    σ (ofTab (liftTab reps[i]! 0) (hhom i hi)) =
        dec ((repRoot (innTabs ()) (repThetas reps))[i]!) ∨
      σ (ofTab (liftTab reps[i]! 0) (hhom i hi)) =
        dec (qmulN ((repRoot (innTabs ()) (repThetas reps))[i]!) z0N) := by
  have hsizeT : i < (repThetas reps).size := by rw [repThetas_size, hsize]; exact hi
  have hsizeR : i < reps.size := by rw [hsize]; exact hi
  obtain ⟨r, hrK, hr2, hcode⟩ := hrep i hi
  have hmem : ofTab (liftTab reps[i]! 0) (hhom i hi) ∈ ThetaOver K :=
    ofTab_liftTab_mem_thetaOver hrK hr2 hcode (hhom i hi)
  have htab : tabOf (ofTab (liftTab reps[i]! 0) (hhom i hi)) = (repThetas reps)[i]! := by
    rw [tabOf_ofTab, repThetas_get hsizeR]
  refine h.sigma_eq_dec_or hmem ?_
  intro e
  rw [htab]
  exact rootsOK_spec hroots hsizeT e

private theorem sOf_eq (root : Array ℕ) (b0 b1 : Bool) {i : ℕ} (hi : i < 2) :
    sOf root b0 b1 i =
      if (if i = 0 then b0 else b1) then qmulN root[i]! z0N else root[i]! := by
  interval_cases i <;> simp [sOf]

private theorem exists_bits_step (h : IsSquareData K σ) {reps : Array ℕ} (hsize : reps.size = 2)
    (hrep : ∀ i < 2, ∃ r ∈ K, r * r = 1 ∧
      Code.HasCode (r : V₀ →ₗ[ZMod 2] V₀) reps[i]!)
    (hhom : ∀ i < 2, isHomTab (liftTab reps[i]! 0) = true)
    (hroots : rootsOK (innTabs ()) (repThetas reps) = true) {i : ℕ} (hi : i < 2)
    (b : Bool × Bool)
    (hbi : (if i = 0 then b.1 else b.2) =
      decide (σ (ofTab (liftTab reps[i]! 0) (hhom i hi)) ≠
        dec (repRoot (innTabs ()) (repThetas reps))[i]!)) :
    sOf (repRoot (innTabs ()) (repThetas reps)) b.1 b.2 i < 128 ∧
      σ (ofTab (liftTab reps[i]! 0) (hhom i hi)) =
        dec (sOf (repRoot (innTabs ()) (repThetas reps)) b.1 b.2 i) := by
  have hsizeT : i < (repThetas reps).size := by rw [repThetas_size, hsize]; exact hi
  have hdisj := rep_sigma_disj h hsize hrep hhom hroots hi
  rw [sOf_eq _ _ _ hi]
  by_cases hbit : (if i = 0 then b.1 else b.2) = true
  · rw [if_pos hbit]
    have hne : σ (ofTab (liftTab reps[i]! 0) (hhom i hi)) ≠
        dec (repRoot (innTabs ()) (repThetas reps))[i]! := by
      have hp : decide (σ (ofTab (liftTab reps[i]! 0) (hhom i hi)) ≠
          dec (repRoot (innTabs ()) (repThetas reps))[i]!) = true := by
        rw [← hbi, hbit]
      exact of_decide_eq_true hp
    rcases hdisj with h' | h'
    · exact absurd h' hne
    · exact ⟨rep_root_z_lt (hroots := hroots) hsizeT, h'⟩
  · have hbf : (if i = 0 then b.1 else b.2) = false := by simpa using hbit
    rw [if_neg hbit]
    have heq : σ (ofTab (liftTab reps[i]! 0) (hhom i hi)) =
        dec (repRoot (innTabs ()) (repThetas reps))[i]! := by
      have hp : decide (σ (ofTab (liftTab reps[i]! 0) (hhom i hi)) ≠
          dec (repRoot (innTabs ()) (repThetas reps))[i]!) = false := by
        rw [← hbi, hbf]
      exact not_not.mp (decide_eq_false_iff_not.mp hp)
    exact ⟨rep_root_lt (hroots := hroots) hsizeT, heq⟩

theorem IsSquareData.exists_bits (h : IsSquareData K σ) {reps : Array ℕ} (hsize : reps.size = 2)
    (hrep : ∀ i < 2, ∃ r ∈ K, r * r = 1 ∧ Code.HasCode (r : V₀ →ₗ[ZMod 2] V₀) reps[i]!)
    (hhom : ∀ i < 2, isHomTab (liftTab reps[i]! 0) = true)
    (hroots : rootsOK (innTabs ()) (repThetas reps) = true) :
    ∃ b : Bool × Bool, ∀ i (hi : i < 2),
      sOf (repRoot (innTabs ()) (repThetas reps)) b.1 b.2 i < 128 ∧
      σ (ofTab (liftTab reps[i]! 0) (hhom i hi)) =
        dec (sOf (repRoot (innTabs ()) (repThetas reps)) b.1 b.2 i) := by
  classical
  let R := repRoot (innTabs ()) (repThetas reps)
  let θ : ℕ → Q0 ≃* Q0 := fun i =>
    if h : i < 2 then ofTab (liftTab reps[i]! 0) (hhom i h) else 1
  have hθ : ∀ i (hi : i < 2), θ i = ofTab (liftTab reps[i]! 0) (hhom i hi) := by
    intro i hi
    unfold θ
    rw [dif_pos hi]
  refine ⟨(decide (σ (θ 0) ≠ dec R[0]!), decide (σ (θ 1) ≠ dec R[1]!)), ?_⟩
  intro i hi
  refine exists_bits_step h hsize hrep hhom hroots hi _ ?_
  interval_cases i <;> simp [hθ 0 (by norm_num), hθ 1 (by norm_num)] <;> rfl

theorem IsSquareData.candVal_wit_eq (h : IsSquareData K σ) {reps : Array ℕ} {b : Bool × Bool}
    (hsize : reps.size = 2)
    (hrep : ∀ i < 2, ∃ r ∈ K, r * r = 1 ∧ Code.HasCode (r : V₀ →ₗ[ZMod 2] V₀) reps[i]!)
    (hhom : ∀ i < 2, isHomTab (liftTab reps[i]! 0) = true)
    (hb : ∀ i (hi : i < 2),
      sOf (repRoot (innTabs ()) (repThetas reps)) b.1 b.2 i < 128 ∧
      σ (ofTab (liftTab reps[i]! 0) (hhom i hi)) =
        dec (sOf (repRoot (innTabs ()) (repThetas reps)) b.1 b.2 i))
    {w : SqWit} (hidx : w.repIdx < 2) (hk : ∃ k ∈ K, Code.HasCode (k : V₀ →ₗ[ZMod 2] V₀) w.k)
    (hkt : isHomTab (liftTab w.k 0) = true) (hpsi : w.psi = liftTab w.k 0)
    (htp : w.tp = compTab (compTab w.psi (repThetas reps)[w.repIdx]!) (invTab w.psi))
    (hitp : w.itp = invTab w.tp) {θ : Q0 ≃* Q0} {v : ℕ}
    (hv : candVal (innTabs ()) (tabOf θ) w.psi w.tp w.itp
      (sOf (repRoot (innTabs ()) (repThetas reps)) b.1 b.2 w.repIdx) = some v) :
    v = enc (σ θ) := by
  have hsizeR : w.repIdx < reps.size := by rw [hsize]; exact hidx
  have hrt : isHomTab (liftTab reps[w.repIdx]! 0) = true := hhom w.repIdx hidx
  have hs : sOf (repRoot (innTabs ()) (repThetas reps)) b.1 b.2 w.repIdx < 128 :=
    (hb w.repIdx hidx).1
  have hσ : σ (ofTab (liftTab reps[w.repIdx]! 0) hrt) =
      dec (sOf (repRoot (innTabs ()) (repThetas reps)) b.1 b.2 w.repIdx) :=
    (hb w.repIdx hidx).2
  obtain ⟨r, hrK, hr2, hrc⟩ := hrep w.repIdx hidx
  have hvC : candVal (innTabs ()) (tabOf θ) (liftTab w.k 0)
      (compTab (compTab (liftTab w.k 0) (liftTab reps[w.repIdx]! 0))
        (invTab (liftTab w.k 0)))
      (invTab (compTab (compTab (liftTab w.k 0) (liftTab reps[w.repIdx]! 0))
        (invTab (liftTab w.k 0))))
      (sOf (repRoot (innTabs ()) (repThetas reps)) b.1 b.2 w.repIdx) = some v := by
    simpa only [hpsi, htp, hitp, repThetas_get hsizeR] using hv
  exact h.candVal_liftTab_eq hk ⟨r, hrK, hr2, hrc⟩ hkt hrt hs hσ hvC

end CFSG.GF2Type.Smith1979W3.Cert690

end
