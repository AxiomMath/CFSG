module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH3U4
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH3U3CW
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH3U3Frame
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH3LNoRC
public import CFSG.GH74.Uniqueness.Bender.FrameAbelian
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice
public import CFSG.RankThree.SubgroupLists.SymplecticTransvections

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.StepH3U

namespace StepH3U3

variable {p f : ℕ} {K : Type} [Field K]

theorem hform_eq_stdHermForm (h : UnitaryFieldData p f K) (v w : Fin 3 → K) :
    CFSG.GH74.Uniqueness.Bender.Frame.A2.hform h v w = stdHermForm h 3 v w := by
  rw [CFSG.GH74.Uniqueness.Bender.Frame.A2.hform_apply, stdHermForm_apply]
  simp [CFSG.GH74.Uniqueness.Bender.Frame.herm]

theorem smul_of_isotropic_orth (h : UnitaryFieldData p f K) {v w : Fin 3 → K} (hv0 : v ≠ 0)
    (hvv : stdHermForm h 3 v v = 0) (hww : stdHermForm h 3 w w = 0)
    (hvw : stdHermForm h 3 v w = 0) : ∃ t : K, w = t • v := by
  by_contra hne
  push Not at hne
  have hli : LinearIndependent K ![v, w] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    by_cases hb : b = 0
    · subst hb
      rw [zero_smul, add_zero] at hab
      exact ⟨(smul_eq_zero.1 hab).resolve_right hv0, rfl⟩
    · exfalso
      apply hne (-(b⁻¹ * a))
      have : b • w = -(a • v) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hab
      calc w = b⁻¹ • (b • w) := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
        _ = -(b⁻¹ * a) • v := by rw [this, smul_neg, smul_smul, neg_smul]
  set U : Submodule K (Fin 3 → K) := Submodule.span K (Set.range ![v, w]) with hU
  have hU2 : Module.finrank K U = 2 := by
    rw [hU, finrank_span_eq_card hli, Fintype.card_fin]
  have hwv : stdHermForm h 3 w v = 0 := by rw [← bar_stdHermForm, hvw, map_zero]
  have hiso : ∀ y ∈ U, ∀ z ∈ U, CFSG.GH74.Uniqueness.Bender.Frame.A2.hform h y z = 0 := by
    intro y hy z hz
    rw [hform_eq_stdHermForm]
    rw [hU, Submodule.mem_span_range_iff_exists_fun] at hy hz
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨b, rfl⟩ := hz
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hvv, hww,
      hvw, hwv, mul_zero, add_zero]
  exact CFSG.GH74.Uniqueness.Bender.Frame.A2.not_totallyIsotropic_two h hU2 hiso

theorem iso_eig_or_aniso (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) {A : GL (Fin 3) K}
    (hA : A ∈ uU h 3) :
    (∃ w : Fin 3 → K, w ≠ 0 ∧ stdHermForm h 3 w w = 0 ∧
        ∃ t : K, (A : Matrix (Fin 3) (Fin 3) K) *ᵥ w = t • w) ∨
      ∃ v : Fin 3 → K, stdHermForm h 3 v v ≠ 0 ∧
        stdHermForm h 3 v ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ v) = 0 := by
  obtain ⟨v, hv0, hvA⟩ := exists_ne_zero_stdHermForm_mulVec_eq_zero h hp2 le_rfl
    (A : Matrix (Fin 3) (Fin 3) K)
  by_cases hvv : stdHermForm h 3 v v = 0
  · left
    have hAA : stdHermForm h 3 ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ v)
        ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ v) = 0 := by rw [stdHermForm_uU h hA, hvv]
    exact ⟨v, hv0, hvv, smul_of_isotropic_orth h hv0 hvv hAA hvA⟩
  · exact Or.inr ⟨v, hvv, hvA⟩

theorem oFrame_orbit (h : UnitaryFieldData p f K) {A : GL (Fin 3) K} (hA : A ∈ uU h 3) {c : K}
    (hA3 : (A : Matrix (Fin 3) (Fin 3) K) ^ 3 = c • (1 : Matrix (Fin 3) (Fin 3) K))
    {v : Fin 3 → K} (hvv : stdHermForm h 3 v v ≠ 0)
    (hvA : stdHermForm h 3 v ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ v) = 0) :
    OFrame h ![v, (A : Matrix (Fin 3) (Fin 3) K) *ᵥ v,
      (A : Matrix (Fin 3) (Fin 3) K) *ᵥ ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ v)] := by
  set M : Matrix (Fin 3) (Fin 3) K := (A : Matrix (Fin 3) (Fin 3) K) with hM
  have hiso : ∀ x y, stdHermForm h 3 (M *ᵥ x) (M *ᵥ y) = stdHermForm h 3 x y :=
    stdHermForm_uU h hA
  have hcube : M *ᵥ (M *ᵥ (M *ᵥ v)) = c • v := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      show M * M * M = M ^ 3 by rw [pow_three, Matrix.mul_assoc], hA3, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  have h01 : stdHermForm h 3 v (M *ᵥ v) = 0 := hvA
  have h12 : stdHermForm h 3 (M *ᵥ v) (M *ᵥ (M *ᵥ v)) = 0 := by rw [hiso, h01]
  have h02 : stdHermForm h 3 v (M *ᵥ (M *ᵥ v)) = 0 := by
    rw [← hiso, hcube, stdHermForm_smul_right, ← bar_stdHermForm, h01, map_zero, mul_zero]
  have hsymm : ∀ x y, stdHermForm h 3 x y = 0 → stdHermForm h 3 y x = 0 := fun x y hxy => by
    rw [← bar_stdHermForm, hxy, map_zero]
  refine ⟨fun i j hij => ?_, fun j => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all
  · fin_cases j
    · exact hvv
    · change stdHermForm h 3 (M *ᵥ v) (M *ᵥ v) ≠ 0
      rw [hiso]; exact hvv
    · change stdHermForm h 3 (M *ᵥ (M *ᵥ v)) (M *ᵥ (M *ᵥ v)) ≠ 0
      rw [hiso, hiso]; exact hvv

theorem ord3_psu3 {r : ℕ} (h : UnitaryFieldData r f K) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (α : MulAut (StatedProj (StatedSU 3 (r ^ f) K))) (hα : orderOf α = 3) :
    (∃ E : Subgroup (StatedProj (StatedSU 3 (r ^ f) K)), E ≠ ⊥ ∧ IsPGroup r ↥E ∧
      ∀ x ∈ E, α x ∈ E) ∨ HHObsAt 3 2 (StatedProj (StatedSU 3 (r ^ f) K)) α := by
  have : CharP K r := h.charP
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn : 3 ≤ 3 := le_rfl
  have hn1 : 1 ≤ 3 := by norm_num
  have hq : ¬(3 = 3 ∧ r ^ f = 2) := by
    rintro ⟨-, h2⟩
    have hodd : Odd (r ^ f) := (h.prime.odd_of_ne_two hr2).pow
    rw [h2] at hodd
    exact (Nat.not_odd_iff_even.2 (by decide)) hodd
  have hα3 : α ^ 3 = 1 := by
    have := pow_orderOf_eq_one α
    rwa [hα] at this
  obtain ⟨A, φ, hαeq⟩ := exists_uConjAut_mul_uFieldAut h hn hq α
  have hφ3 : φ ^ 3 = 1 := fieldAut_pow_eq_one h hn hq (hαeq ▸ hα3)
  by_cases hφ : φ = 1
  · rw [hφ, map_one, mul_one] at hαeq
    subst hαeq
    have h1 : uConjAut h hn1 (A ^ 3) = 1 := by rw [map_pow, hα3]
    obtain ⟨c, hc⟩ := (uConjAut_eq_one_iff h hn (A ^ 3)).mp h1
    have hA3 : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 =
        (c : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
      have e := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hc
      simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val] at e
      rw [e, smul_one_eq_diagonal]
      rfl
    rcases iso_eig_or_aniso h hr2 A.2 with ⟨w, hw0, hww, t, ht⟩ | ⟨v, hvv, hvA⟩
    ·
      left
      set W : Submodule K (Fin 3 → K) := Submodule.span K {w} with hW
      have hwW : w ∈ W := Submodule.mem_span_singleton_self w
      have horth : ∀ y ∈ W, stdHermForm h 3 w y = 0 := by
        intro y hy
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
        rw [stdHermForm_smul_right, hww, mul_zero]
      have ht0 : t ≠ 0 := by
        rintro rfl
        rw [zero_smul] at ht
        have hinj := Matrix.mulVec_injective_of_isUnit (A : GL (Fin 3) K).isUnit
        exact hw0 (hinj (ht.trans (Matrix.mulVec_zero _).symm))
      have hAW : ∀ y ∈ W, ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ y ∈ W := by
        intro y hy
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
        rw [Matrix.mulVec_smul, ht, smul_smul]
        exact Submodule.smul_mem _ _ hwW
      have hAinv : (((A : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w =
          t⁻¹ • w := by
        have e : (((A : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
            (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) = w := by
          rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
            Matrix.one_mulVec]
        rw [ht, Matrix.mulVec_smul] at e
        calc (((A : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w =
            t⁻¹ • (t • (((A : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) :=
              by rw [smul_smul, inv_mul_cancel₀ ht0, one_smul]
          _ = t⁻¹ • w := by rw [e]
      have hAW' : ∀ y ∈ W,
          (((A : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ y ∈ W := by
        intro y hy
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
        rw [Matrix.mulVec_smul, hAinv, smul_smul]
        exact Submodule.smul_mem _ _ hwW
      obtain ⟨b, hb0, hb⟩ := exists_bar_eq_neg h
      refine ⟨uElatImage W, ?_, isPGroup_uElatImage W, fun x hx =>
        uConjAut_mem_uElatImage h hn1 A hAW hAW' hx⟩
      intro hbot
      have hmem := proj_utvSU_mem_uElatImage h hwW horth hww hb
      rw [hbot, Subgroup.mem_bot] at hmem
      exact proj_utvSU_ne_one h hw0 hww hb0 hb hmem
    ·
      right
      set M : Matrix (Fin 3) (Fin 3) K := ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hM
      have hF := oFrame_orbit h A.2 hA3 hvv hvA
      have hcube : M *ᵥ (M *ᵥ (M *ᵥ v)) = (c : K) • v := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          show M * M * M = M ^ 3 by rw [pow_three, Matrix.mul_assoc], hA3, Matrix.smul_mulVec,
          Matrix.one_mulVec]
      refine hhObs_of_frame hr2 hF A (l₀ := 1) (l₁ := 1) (l₂ := (c : K)) ?_ ?_ ?_
      · change M *ᵥ v = (1 : K) • (M *ᵥ v); rw [one_smul]
      · change M *ᵥ (M *ᵥ v) = (1 : K) • (M *ᵥ (M *ᵥ v)); rw [one_smul]
      · change M *ᵥ (M *ᵥ (M *ᵥ v)) = (c : K) • v; exact hcube
  · left
    have hφord : orderOf φ = 3 := orderOf_eq_prime hφ3 hφ
    let a' : MulAut (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :=
      MulAut.congr (uTransport h hn1) α
    have ha' : orderOf a' = 3 :=
      (MulEquiv.orderOf_eq (MulAut.congr (uTransport h hn1)) α).trans hα
    have hσa : primeFormFieldFactor h isPrimeFormGram_one hn hq a' = φ := by
      have := uFactor_apply h hn hq A φ
      rw [← hαeq] at this
      exact this
    obtain ⟨-, -, -, -, -, M, hM⟩ :=
      unitary_prime_descent_char h hn hq Nat.prime_three (by norm_num) a' ha' φ hσa hφord
    have hαh : α = uConjAut h hn1 M * uFieldAut h hn1 φ * (uConjAut h hn1 M)⁻¹ := by
      have h1 : a' = primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) M *
          primeFormFieldHom h isPrimeFormGram_one φ *
          (primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) M)⁻¹ := by
        rw [← hM]
        group
      have h2 : α = (MulAut.congr (uTransport h hn1)).symm a' :=
        ((MulAut.congr (uTransport h hn1)).symm_apply_apply α).symm
      rw [h2, h1, map_mul, map_mul, map_inv]
      rfl
    rw [hαh]
    exact exists_rgroup_of_field_u h hn hn1 M φ

end StepH3U3

theorem noR_two_of_psu3
    {r f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData r f K)
    (hr2 : r ≠ 2) : NoR 2 (StatedProj (StatedSU 3 (r ^ f) K)) := by
  intro L _ _ hL ⟨e⟩
  have : Finite K := h.finite
  have : Fact r.Prime := ⟨h.prime⟩
  have : CharP K r := h.charP
  have hK : Nat.card K = (r ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hq : ((3 : ℕ), r ^ f) ≠ (3, 2) := by
    intro h32
    have h2 : r ^ f = 2 := (Prod.mk.inj h32).2
    have hodd : Odd (r ^ f) := (h.prime.odd_of_ne_two hr2).pow
    rw [h2] at hodd
    exact (Nat.not_odd_iff_even.2 (by decide)) hodd
  obtain ⟨-, ⟨e'⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SUOdd.psu_odd_hopfMultiplier
    (F := K) (p := r) (f := f) hK h.one_le (n := 3) le_rfl (by decide) hq
  have : Group.IsPerfect L := hL.1
  have hd := StepH3L.card_center_dvd_hopf e
  have hcard : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (StatedProj (StatedSU 3 (r ^ f) K))) = Nat.gcd 3 (r ^ f + 1) := by
    rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv,
      Nat.card_congr e'.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [hcard] at hd
  intro h2
  have h23 : 2 ∣ 3 := (h2.trans hd).trans (Nat.gcd_dvd_left 3 _)
  omega

theorem ord3_fu3d :
    Ord3 FU3d := by
  intro r Y _ _ hr hr2 hr3 hY b hb
  obtain ⟨f, hf, hLM⟩ := hY
  have hcm : StatedClassicalModel Y .PSU 3 r f := by
    rcases hLM with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact hc
    all_goals exact absurd h0 (by norm_num)
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hcm
  have h : UnitaryFieldData r f K := ⟨hr, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  change Ord3Concl r Y b
  apply Ord3Concl.of_mulEquiv e
  have hα : orderOf (MulAut.congr e b) = 3 := (MulEquiv.orderOf_eq _ b).trans hb
  rcases StepH3U3.ord3_psu3 h hr2 hr3 _ hα with hE | hH
  · exact Or.inl hE
  · exact Or.inr ⟨2, hH, fun _ => noR_two_of_psu3 h hr2⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
