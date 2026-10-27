module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH3Tr
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH3UEig
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55UDesc
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepHStmts

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.StepH3U

namespace StepH3U

variable {r f : ℕ} {K : Type} [Field K]

theorem exists_rgroup_of_field_u (h : UnitaryFieldData r f K) {n : ℕ} (hn : 3 ≤ n)
    (hn1 : 1 ≤ n) (M : uU h n) (φ : K ≃+* K) :
    ∃ E : Subgroup (StatedProj (StatedSU n (r ^ f) K)), E ≠ ⊥ ∧ IsPGroup r ↥E ∧
      ∀ x ∈ E, ((uConjAut h hn1 M * uFieldAut h hn1 φ * (uConjAut h hn1 M)⁻¹ :
        MulAut (StatedProj (StatedSU n (r ^ f) K))) x) ∈ E := by
  have : CharP K r := h.charP
  obtain ⟨w, hw0, hww, hφw⟩ := exists_isotropic_prime h hn
  obtain ⟨b, hb0, hb⟩ := exists_bar_eq_neg h
  set W := Submodule.span K {w} with hW
  have horth : ∀ y ∈ W, stdHermForm h n w y = 0 := by
    intro y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [stdHermForm_smul_right, hww, mul_zero]
  set E₀ := uElatImage (p := r) (f := f) W with hE₀
  set E := E₀.map (uConjAut h hn1 M).toMonoidHom with hE
  have hinv : ∀ y, (uConjAut h hn1 M)⁻¹ (uConjAut h hn1 M y) = y := fun y => by
    rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  refine ⟨E, ?_, (isPGroup_uElatImage W).map _, ?_⟩
  · intro hbot
    have hmem : uConjAut h hn1 M (projH _ (utvSU h hww hb)) ∈ E :=
      Subgroup.mem_map_of_mem _ (proj_utvSU_mem_uElatImage h
        (Submodule.mem_span_singleton_self w) horth hww hb)
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : uConjAut h hn1 M (projH _ (utvSU h hww hb)) = uConjAut h hn1 M 1 := by
      rw [hmem, map_one]
    exact proj_utvSU_ne_one h hw0 hww hb0 hb ((uConjAut h hn1 M).injective h1)
  · rintro _ ⟨x, hx, rfl⟩
    change uConjAut h hn1 M (uFieldAut h hn1 φ ((uConjAut h hn1 M)⁻¹ (uConjAut h hn1 M x))) ∈ E
    rw [hinv]
    exact Subgroup.mem_map_of_mem _ (uFieldAut_mem_uElatImage h hn1 φ (hφw φ) hx)

theorem ord3_psu4 (h : UnitaryFieldData r f K) (hr3 : r ≠ 3)
    (α : MulAut (StatedProj (StatedSU 4 (r ^ f) K))) (hα : orderOf α = 3) :
    ∃ E : Subgroup (StatedProj (StatedSU 4 (r ^ f) K)), E ≠ ⊥ ∧ IsPGroup r ↥E ∧
      ∀ x ∈ E, α x ∈ E := by
  have : CharP K r := h.charP
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn : 3 ≤ 4 := by norm_num
  have hn1 : 1 ≤ 4 := by norm_num
  have hq : ¬(4 = 3 ∧ r ^ f = 2) := fun h4 => absurd h4.1 (by norm_num)
  have hα3 : α ^ 3 = 1 := hα ▸ pow_orderOf_eq_one α
  obtain ⟨A, φ, hαeq⟩ := exists_uConjAut_mul_uFieldAut h hn hq α
  have hφ3 : φ ^ 3 = 1 := fieldAut_pow_eq_one h hn hq (hαeq ▸ hα3)
  by_cases hφ : φ = 1
  · rw [hφ, map_one, mul_one] at hαeq
    subst hαeq
    have h1 : uConjAut h hn1 (A ^ 3) = 1 := by rw [map_pow, hα3]
    obtain ⟨c, hc⟩ := (uConjAut_eq_one_iff h hn (A ^ 3)).mp h1
    have hA3 : ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ^ 3 =
        (c : K) • (1 : Matrix (Fin 4) (Fin 4) K) := by
      have e := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K)) hc
      simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val] at e
      rw [e, smul_one_eq_diagonal]
      rfl
    obtain ⟨W, ⟨w, hwW, hw0⟩, hiso, hAW, hAW'⟩ :=
      exists_isotropic_invariant_four h hr3 A.2 c.ne_zero hA3
    obtain ⟨b, hb0, hb⟩ := exists_bar_eq_neg h
    have hww : stdHermForm h 4 w w = 0 := hiso w hwW w hwW
    refine ⟨uElatImage W, ?_, isPGroup_uElatImage W, fun x hx =>
      uConjAut_mem_uElatImage h hn1 A hAW hAW' hx⟩
    intro hbot
    have hmem := proj_utvSU_mem_uElatImage h hwW (fun y hy => hiso w hwW y hy) hww hb
    rw [hbot, Subgroup.mem_bot] at hmem
    exact proj_utvSU_ne_one h hw0 hww hb0 hb hmem
  · have hφord : orderOf φ = 3 := orderOf_eq_prime hφ3 hφ
    let a' : MulAut (primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) :=
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
      have h1 : a' = primeFormConjHom h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) M *
          primeFormFieldHom h isPrimeFormGram_one φ *
          (primeFormConjHom h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) M)⁻¹ := by
        rw [← hM]
        group
      have h2 : α = (MulAut.congr (uTransport h hn1)).symm a' :=
        ((MulAut.congr (uTransport h hn1)).symm_apply_apply α).symm
      rw [h2, h1, map_mul, map_mul, map_inv]
      rfl
    rw [hαh]
    exact exists_rgroup_of_field_u h hn hn1 M φ

end StepH3U

theorem ord3_fu4d : Ord3 FU4d := by
  intro r Y _ _ hr _ hr3 hY b hb
  obtain ⟨f, hf, -, hLM⟩ := hY
  have hcm : StatedClassicalModel Y .PSU 4 r f := by
    rcases hLM with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact hc
    all_goals exact absurd h0 (by norm_num)
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hcm
  have h : UnitaryFieldData r f K := ⟨hr, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  change Ord3Concl r Y b
  apply Ord3Concl.of_mulEquiv e
  have hα : orderOf (MulAut.congr e b) = 3 := (MulEquiv.orderOf_eq _ b).trans hb
  exact Or.inl (StepH3U.ord3_psu4 h hr3 _ hα)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
