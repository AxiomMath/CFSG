module

public import CFSG.LieType.Sp6Spin.CaseC

public section

namespace CFSG.LieType.Sp6Spin

open CFSG.LieType.TorusWeights CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.Assembly.LowTwoRank TauCeti.GLSymplecticFin
  QuadraticMap

attribute [local instance] Fintype.ofFinite Classical.propDecidable

namespace SpinSetting

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]

variable {S : SpinSetting K V}

private noncomputable def frameLong (R : S.SpinRoots) : Module.End K V :=
  S.A (.positiveLong 2) (2 ^ R.l')

private noncomputable def frameU1 (R : S.SpinRoots) : V :=
  Classical.choose (IsSpinPattern.exists_ne_zero S R.pattern ![true, true, false])

private noncomputable def frameU2 (R : S.SpinRoots) : V :=
  Classical.choose (IsSpinPattern.exists_ne_zero S R.pattern ![true, false, false])

private theorem frameU1_mem (R : S.SpinRoots) :
    frameU1 R ∈ S.X (spinWt R.x ![true, true, false]) :=
  (Classical.choose_spec (IsSpinPattern.exists_ne_zero S R.pattern ![true, true, false])).1

private theorem frameU1_ne_zero (R : S.SpinRoots) : frameU1 R ≠ 0 :=
  (Classical.choose_spec (IsSpinPattern.exists_ne_zero S R.pattern ![true, true, false])).2

private theorem frameU2_mem (R : S.SpinRoots) :
    frameU2 R ∈ S.X (spinWt R.x ![true, false, false]) :=
  (Classical.choose_spec (IsSpinPattern.exists_ne_zero S R.pattern ![true, false, false])).1

private theorem frameU2_ne_zero (R : S.SpinRoots) : frameU2 R ≠ 0 :=
  (Classical.choose_spec (IsSpinPattern.exists_ne_zero S R.pattern ![true, false, false])).2

private noncomputable def frameBase (R : S.SpinRoots) (σ : Fin 3 → Bool) : V :=
  if σ 1 = true then
    (if σ 2 = true then frameLong R (frameU1 R) else frameU1 R)
  else
    (if σ 2 = true then frameLong R (frameU2 R) else frameU2 R)

private theorem update_TTF :
    (Function.update ![true, true, false] 2 true : Fin 3 → Bool) = ![true, true, true] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem update_TFF :
    (Function.update ![true, false, false] 2 true : Fin 3 → Bool) = ![true, false, true] := by
  funext i
  fin_cases i <;> simp [Function.update]

private theorem frameBase_mem (R : S.SpinRoots) {σ : Fin 3 → Bool} (h0 : σ 0 = true) :
    frameBase R σ ∈ S.X (spinWt R.x σ) := by
  have hσ : σ = ![true, σ 1, σ 2] := by
    funext i
    fin_cases i <;> simp [h0]
  rw [hσ]
  rcases h1 : σ 1 with _ | _ <;> rcases h2 : σ 2 with _ | _ <;>
    simp only [frameBase]
  · exact frameU2_mem R
  · rw [← update_TFF]
    exact R.long_src _ (by simp) _ (frameU2_mem R)
  · exact frameU1_mem R
  · rw [← update_TTF]
    exact R.long_src _ (by simp) _ (frameU1_mem R)

private theorem frameBase_ne_zero (R : S.SpinRoots) {σ : Fin 3 → Bool} (h0 : σ 0 = true) :
    frameBase R σ ≠ 0 := by
  have hσ : σ = ![true, σ 1, σ 2] := by
    funext i
    fin_cases i <;> simp [h0]
  rw [hσ]
  rcases h1 : σ 1 with _ | _ <;> rcases h2 : σ 2 with _ | _ <;>
    simp only [frameBase]
  · exact frameU2_ne_zero R
  · intro h
    exact R.long_ne_zero _ (by simp) _ (frameU2_mem R) (frameU2_ne_zero R) h
  · exact frameU1_ne_zero R
  · intro h
    exact R.long_ne_zero _ (by simp) _ (frameU1_mem R) (frameU1_ne_zero R) h

private theorem neg_first_of_not {σ : Fin 3 → Bool} (h : ¬ σ 0 = true) :
    (fun i => !σ i) 0 = true := by
  simpa using h

private theorem not_not_fun (σ : Fin 3 → Bool) : (fun i => !(!σ i)) = σ := by
  funext i
  simp

private noncomputable def frameChoice (R : S.SpinRoots) {σ : Fin 3 → Bool}
    (h : ¬ σ 0 = true) : V :=
  Classical.choose
    (S.exists_polar_eq_one (a := spinWt R.x (fun i => !σ i))
      (u := frameBase R (fun i => !σ i))
      (frameBase_mem R (neg_first_of_not h))
      (frameBase_ne_zero R (neg_first_of_not h)))

private theorem frameChoice_mem (R : S.SpinRoots) {σ : Fin 3 → Bool}
    (h : ¬ σ 0 = true) :
    frameChoice R h ∈ S.X (-spinWt R.x (fun i => !σ i)) := by
  unfold frameChoice
  exact (Classical.choose_spec
    (S.exists_polar_eq_one (a := spinWt R.x (fun i => !σ i))
      (u := frameBase R (fun i => !σ i))
      (frameBase_mem R (neg_first_of_not h))
      (frameBase_ne_zero R (neg_first_of_not h)))).1

private theorem frameChoice_polar (R : S.SpinRoots) {σ : Fin 3 → Bool}
    (h : ¬ σ 0 = true) :
    polar S.Q (frameBase R (fun i => !σ i)) (frameChoice R h) = 1 := by
  unfold frameChoice
  exact (Classical.choose_spec
    (S.exists_polar_eq_one (a := spinWt R.x (fun i => !σ i))
      (u := frameBase R (fun i => !σ i))
      (frameBase_mem R (neg_first_of_not h))
      (frameBase_ne_zero R (neg_first_of_not h)))).2

private noncomputable def frameVec (R : S.SpinRoots) (σ : Fin 3 → Bool) : V :=
  if h : σ 0 = true then frameBase R σ else frameChoice R h

private theorem frameVec_of_true (R : S.SpinRoots) {σ : Fin 3 → Bool} (h : σ 0 = true) :
    frameVec R σ = frameBase R σ := by
  rw [frameVec, dif_pos h]

private theorem frameVec_polar_base (R : S.SpinRoots) {σ : Fin 3 → Bool}
    (h : ¬ σ 0 = true) :
    polar S.Q (frameBase R (fun i => !σ i)) (frameVec R σ) = 1 := by
  rw [frameVec, dif_neg h]
  exact frameChoice_polar R h

private theorem frameVec_mem (R : S.SpinRoots) (σ : Fin 3 → Bool) :
    frameVec R σ ∈ S.X (spinWt R.x σ) := by
  by_cases h : σ 0 = true
  · rw [frameVec_of_true R h]
    exact frameBase_mem R h
  · rw [frameVec, dif_neg h]
    have hneg : -spinWt R.x (fun i => !σ i) = spinWt R.x σ := by
      rw [neg_spinWt]
      simp
    have hmem := frameChoice_mem R h
    rwa [hneg] at hmem

private theorem frameVec_ne_zero (R : S.SpinRoots) (σ : Fin 3 → Bool) :
    frameVec R σ ≠ 0 := by
  by_cases h : σ 0 = true
  · rw [frameVec_of_true R h]
    exact frameBase_ne_zero R h
  · intro hzero
    have hp := frameVec_polar_base R h
    rw [hzero, QuadraticMap.polar_zero_right] at hp
    exact one_ne_zero hp.symm

private theorem frameVec_polar_compl (R : S.SpinRoots) (σ : Fin 3 → Bool) :
    polar S.Q (frameVec R σ) (frameVec R (fun i => !σ i)) = 1 := by
  by_cases h : σ 0 = true
  · have h' : ¬ (fun i => !σ i) 0 = true := by simp [h]
    rw [frameVec_of_true (σ := σ) R h]
    simpa [not_not_fun σ] using frameVec_polar_base (σ := fun i => !σ i) R h'
  · have h' : (fun i => !σ i) 0 = true := neg_first_of_not h
    have hbase : frameVec R (fun i => !σ i) = frameBase R (fun i => !σ i) :=
      frameVec_of_true (σ := fun i => !σ i) R h'
    rw [hbase, polar_comm]
    exact frameVec_polar_base R h

private theorem exists_spinWt_of_mult_ne_zero (R : S.SpinRoots)
    {a : Fin 3 → ZMod (Nat.card Kˣ)} (ha : S.mult a ≠ 0) :
    ∃ τ : Fin 3 → Bool, a = spinWt R.x τ := by
  have hx := R.pattern.ne_zero
  have hcoord : ∀ i, a i = R.x ∨ a i = -R.x := by
    by_contra h
    apply ha
    rw [R.pattern.mult_eq a]
    simp [h]
  refine ⟨fun i => decide (a i = R.x), ?_⟩
  funext i
  rcases hcoord i with hi | hi
  · simp [spinWt, hi]
  · simp [spinWt, hi]

private theorem frameVec_eq_of_polar_eq (R : S.SpinRoots) {σ : Fin 3 → Bool} {u u' : V}
    (hu : u ∈ S.X (spinWt R.x σ)) (hu' : u' ∈ S.X (spinWt R.x σ))
    (h : polar S.Q u (frameVec R (fun i => !σ i)) =
      polar S.Q u' (frameVec R (fun i => !σ i))) : u = u' := by
  have hx := R.pattern.ne_zero
  have hN := odd_natCard_units (K := K)
  have hw : u - u' ∈ S.X (spinWt R.x σ) := (S.X (spinWt R.x σ)).sub_mem hu hu'
  have hwz : polar S.Q (u - u') (frameVec R (fun i => !σ i)) = 0 := by
    rw [QuadraticMap.polar_sub_left, h, sub_self]
  rw [← sub_eq_zero]
  apply S.nondeg' (u - u')
  intro y
  rw [← sum_wtProj (diagHom 3 K) S.ρ y]
  rw [← QuadraticMap.polarBilin_apply_apply, map_sum]
  simp only [QuadraticMap.polarBilin_apply_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases hb : b = spinWt R.x (fun i => !σ i)
  · subst hb
    have hzb : frameVec R (fun i => !σ i) ∈ S.X (spinWt R.x (fun i => !σ i)) :=
      frameVec_mem R _
    obtain ⟨c, hc⟩ := IsSpinPattern.eq_smul S R.pattern
      (u := frameVec R (fun i => !σ i)) (v := wtProj (diagHom 3 K) S.ρ _ y)
      hzb (frameVec_ne_zero R _) (wtProj_mem (diagHom 3 K) S.ρ _ y)
    rw [hc, QuadraticMap.polar_smul_right, hwz, smul_zero]
  · by_cases hmult : S.mult b = 0
    · have hbot : S.X b = ⊥ := S.X_eq_bot_iff.mpr hmult
      have hmem : wtProj (diagHom 3 K) S.ρ b y ∈ S.X b :=
        wtProj_mem (diagHom 3 K) S.ρ b y
      rw [hbot] at hmem
      rw [show wtProj (diagHom 3 K) S.ρ b y = 0 from by simpa using hmem]
      simp
    · obtain ⟨τ, hτ⟩ := exists_spinWt_of_mult_ne_zero (S := S) R hmult
      subst hτ
      have hne : spinWt R.x σ + spinWt R.x τ ≠ 0 := by
        intro hzero
        exact hb (congrArg (spinWt R.x)
          ((spinWt_add_spinWt_eq_zero_iff hN hx).mp hzero))
      exact S.polar_eq_zero hne hw (wtProj_mem (diagHom 3 K) S.ρ (spinWt R.x τ) y)

private theorem frameLong_base (R : S.SpinRoots) {σ : Fin 3 → Bool} (h0 : σ 0 = true)
    (h2 : σ 2 = false) :
    frameLong R (frameBase R σ) = frameBase R (Function.update σ 2 true) := by
  have hσ : σ = ![true, σ 1, σ 2] := by
    funext i
    fin_cases i <;> simp [h0]
  rw [h2] at hσ
  rw [hσ]
  rcases h1 : σ 1 with _ | _ <;> simp [frameBase]

private theorem update_neg_update {σ : Fin 3 → Bool} (h2 : σ 2 = false) :
    Function.update (fun i => !(Function.update σ 2 true i)) 2 true = fun i => !σ i := by
  funext i
  fin_cases i <;> simp [Function.update, h2]

private theorem frameLong_frameVec (R : S.SpinRoots) (σ : Fin 3 → Bool) (h2 : σ 2 = false) :
    frameLong R (frameVec R σ) = frameVec R (Function.update σ 2 true) := by
  by_cases h0 : σ 0 = true
  · have h0' : (Function.update σ 2 true) 0 = true := by
      simp [Function.update, h0]
    rw [frameVec_of_true (σ := σ) R h0,
      frameVec_of_true (σ := Function.update σ 2 true) R h0']
    exact frameLong_base R h0 h2
  · have h0τ : ¬ (Function.update σ 2 true) 0 = true := by
      simp [Function.update, h0]
    have h0t : (fun i => !(Function.update σ 2 true i)) 0 = true := by
      simp [Function.update, h0]
    have h0m : (fun i => !σ i) 0 = true := neg_first_of_not h0
    have hbase : frameLong R (frameVec R (fun i => !(Function.update σ 2 true i))) =
        frameVec R (fun i => !σ i) := by
      rw [frameVec_of_true (σ := fun i => !(Function.update σ 2 true i)) R h0t,
        frameLong_base R (neg_first_of_not h0τ) (by simp)]
      rw [update_neg_update h2]
      exact (frameVec_of_true (σ := fun i => !σ i) R h0m).symm
    refine frameVec_eq_of_polar_eq (S := S) (σ := Function.update σ 2 true) R ?_ ?_ ?_
    · exact R.long_src σ h2 (frameVec R σ) (frameVec_mem R σ)
    · exact frameVec_mem R _
    · calc
        polar S.Q (frameLong R (frameVec R σ)) (frameVec R
            (fun i => !(Function.update σ 2 true i)))
            = polar S.Q (frameVec R σ) (frameLong R (frameVec R
                (fun i => !(Function.update σ 2 true i)))) :=
              S.polar_A (.positiveLong 2) (frameVec R σ) _ (2 ^ R.l')
        _ = polar S.Q (frameVec R σ) (frameVec R (fun i => !σ i)) := by rw [hbase]
        _ = 1 := frameVec_polar_compl R σ
        _ = polar S.Q (frameVec R (Function.update σ 2 true)) (frameVec R
              (fun i => !(Function.update σ 2 true i))) :=
              (frameVec_polar_compl R (Function.update σ 2 true)).symm

private theorem spinWt_ne_zero (R : S.SpinRoots) (σ : Fin 3 → Bool) :
    spinWt R.x σ ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp only [spinWt, Pi.zero_apply] at h0
  cases hs : σ 0 <;> simp [hs] at h0
  · exact R.pattern.ne_zero h0
  · exact R.pattern.ne_zero h0

private theorem frameShort_source (R : S.SpinRoots) {r : RootSubgroupIndex 3}
    (hr : IsShortIndex r) {σ : Fin 3 → Bool} (hσ : IsSrc (stdVec r) σ) :
    S.A r (2 ^ R.l) (frameVec R σ) =
      polar S.Q (S.A r (2 ^ R.l) (frameVec R σ))
        (frameVec R (fun i => !(flipAt (stdVec r) σ i))) •
      frameVec R (flipAt (stdVec r) σ) := by
  have hmem : S.A r (2 ^ R.l) (frameVec R σ) ∈
      S.X (spinWt R.x (flipAt (stdVec r) σ)) :=
    R.short_src r hr σ hσ (frameVec R σ) (frameVec_mem R σ)
  have hτmem : frameVec R (flipAt (stdVec r) σ) ∈
      S.X (spinWt R.x (flipAt (stdVec r) σ)) :=
    frameVec_mem R _
  refine frameVec_eq_of_polar_eq (S := S) (σ := flipAt (stdVec r) σ) R hmem ?_ ?_
  · exact (S.X (spinWt R.x (flipAt (stdVec r) σ))).smul_mem _ hτmem
  · rw [QuadraticMap.polar_smul_left, frameVec_polar_compl R (flipAt (stdVec r) σ),
      smul_eq_mul, mul_one]

private theorem frameShort_lam_eq (R : S.SpinRoots) {r : RootSubgroupIndex 3}
    {σ : Fin 3 → Bool} :
    polar S.Q (S.A r (2 ^ R.l) (frameVec R σ))
        (frameVec R (fun i => !(flipAt (stdVec r) σ i))) =
      polar S.Q (S.A r (2 ^ R.l) (frameVec R (fun i => !(flipAt (stdVec r) σ i))))
        (frameVec R
          (fun i => !(flipAt (stdVec r) (fun i => !(flipAt (stdVec r) σ i)) i))) := by
  have hflip : flipAt (stdVec r) (fun i => !(flipAt (stdVec r) σ i)) = fun i => !σ i := by
    rw [flipAt_not, flipAt_flipAt]
  have hneg : (fun i => !(flipAt (stdVec r) (fun i => !(flipAt (stdVec r) σ i)) i)) = σ := by
    rw [hflip]
    exact not_not_fun σ
  rw [polar_comm, ← S.polar_A (r := r) (frameVec R (fun i => !(flipAt (stdVec r) σ i)))
    (frameVec R σ) (2 ^ R.l), hneg]

private theorem frameShort_exists (R : S.SpinRoots) (r : RootSubgroupIndex 3)
    (hr : IsShortIndex r) :
    ∃ lam : K, ∀ σ, S.A r (2 ^ R.l) (frameVec R σ) =
      if IsSrc (stdVec r) σ then lam • frameVec R (flipAt (stdVec r) σ) else 0 := by
  let σ₀ : Fin 3 → Bool := Classical.choose (exists_isSrc (stdVec r))
  have hσ₀ : IsSrc (stdVec r) σ₀ := Classical.choose_spec (exists_isSrc (stdVec r))
  let σ' : Fin 3 → Bool := fun i => !(flipAt (stdVec r) σ₀ i)
  have hσ' : IsSrc (stdVec r) σ' := by
    dsimp only [σ']
    rw [isSrc_not_flipAt_iff]
    exact hσ₀
  refine ⟨polar S.Q (S.A r (2 ^ R.l) (frameVec R σ₀)) (frameVec R σ'), fun σ => ?_⟩
  by_cases hσ : IsSrc (stdVec r) σ
  · rw [if_pos hσ]
    rcases IsSrc.eq_or_eq hr hσ₀ hσ with h | h
    · rw [h]
      exact frameShort_source R hr hσ₀
    · rw [h, frameShort_source R hr hσ', ← frameShort_lam_eq (R := R) (σ := σ₀)]
  · rw [if_neg hσ]
    exact R.short_not_src r hr σ hσ (frameVec R σ) (frameVec_mem R σ)

structure SpinFrame {S : SpinSetting K V} (R : S.SpinRoots) where
  v : (Fin 3 → Bool) → V
  mem : ∀ σ, v σ ∈ S.X (spinWt R.x σ)
  Q_eq : ∀ σ, S.Q (v σ) = 0
  polar_eq : ∀ σ τ, polar S.Q (v σ) (v τ) = if τ = (fun i => !σ i) then 1 else 0
  long_eq : ∀ σ : Fin 3 → Bool, σ 2 = false →
    S.A (.positiveLong 2) (2 ^ R.l') (v σ) = v (Function.update σ 2 true)
  short_eq : ∀ r : RootSubgroupIndex 3, IsShortIndex r → ∃ lam : K, ∀ σ,
    S.A r (2 ^ R.l) (v σ) = if IsSrc (stdVec r) σ then lam • v (flipAt (stdVec r) σ) else 0

theorem SpinRoots.nonempty_spinFrame {S : SpinSetting K V} (R : S.SpinRoots) :
    Nonempty (SpinFrame R) := by
  refine ⟨{ v := frameVec R
            mem := frameVec_mem R
            Q_eq := fun σ => S.Q_eq_zero (spinWt_ne_zero R σ) (frameVec_mem R σ)
            polar_eq := fun σ τ => ?_
            long_eq := fun σ h2 => ?_
            short_eq := fun r hr => frameShort_exists R r hr }⟩
  · by_cases h : τ = fun i => !σ i
    · rw [if_pos h, h]
      exact frameVec_polar_compl R σ
    · rw [if_neg h]
      refine S.polar_eq_zero ?_ (frameVec_mem R σ) (frameVec_mem R τ)
      intro hzero
      exact h ((spinWt_add_spinWt_eq_zero_iff (odd_natCard_units (K := K))
        R.pattern.ne_zero).mp hzero)
  · simpa only [frameLong] using frameLong_frameVec R σ h2

end SpinSetting

end CFSG.LieType.Sp6Spin
