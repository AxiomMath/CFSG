module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyTorus
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleLang

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.AlgebraicGroups

set_option linter.unusedSectionVars false


section Rho

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

structure LangSetup.HexStep (S : LangSetup τ L p) : Prop where
  hel : ∀ x : Fin τ.rank → ℤ, IsRoot τ x → ∀ u : Lˣ,
    S.D.step (Hel x u) = Hel (S.ρ x) (u ^ S.D.q)
  nsl : ∀ β : Fin τ.rank → ℤ, IsRoot τ β → ∃ s : Lˣ, ∀ c : Lˣ,
    S.D.step (rootSL2 τ L β (nSL c)) = rootSL2 τ L (S.ρ β) (nSL (s * c ^ S.D.q))
  rel6 : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → S.ρ (S.ρ δ) = S.ρ δ - δ

variable (S : LangSetup τ L p)

theorem hexR_iter_neg (j : ℕ) (x : Fin τ.rank → ℤ) :
    (S.ρ : (Fin τ.rank → ℤ) → _)^[j] (-x) = -((S.ρ : (Fin τ.rank → ℤ) → _)^[j] x) := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, S.frob.neg_eq, ih]

theorem hexR_form01 (h : S.HexStep) (hτ : SimplyLacedTag τ) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) : iform γ (S.ρ γ) = 1 := by
  have h1 : iform (S.ρ γ) (S.ρ (S.ρ γ)) = iform γ (S.ρ γ) := S.frob.iform_eq γ (S.ρ γ)
  rw [h.rel6 γ hγ, iform_sub_right, iform_comm (S.ρ γ) γ,
    iform_self_eq_two hτ ((S.frob.isRoot_iff γ).2 hγ)] at h1
  omega

theorem hexR_rho3 (h : S.HexStep) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    S.ρ (S.ρ (S.ρ γ)) = -γ := by
  have h1 := h.rel6 (S.ρ γ) ((S.frob.isRoot_iff γ).2 hγ)
  rw [h1, h.rel6 γ hγ]
  abel

theorem hexR_iter_add3 (h : S.HexStep) {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) (j : ℕ) :
    (S.ρ : (Fin τ.rank → ℤ) → _)^[j + 3] δ = -((S.ρ : (Fin τ.rank → ℤ) → _)^[j] δ) := by
  rw [Function.iterate_add_apply]
  have : (S.ρ : (Fin τ.rank → ℤ) → _)^[3] δ = -δ := hexR_rho3 S h hδ
  rw [this, hexR_iter_neg]

theorem hexR_iter_six (h : S.HexStep) {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) :
    (S.ρ : (Fin τ.rank → ℤ) → _)^[6] δ = δ := by
  have := hexR_iter_add3 S h hδ 3
  rw [show (3 + 3 : ℕ) = 6 from rfl] at this
  rw [this]
  have h3 : (S.ρ : (Fin τ.rank → ℤ) → _)^[3] δ = -δ := hexR_rho3 S h hδ
  rw [h3, neg_neg]

@[expose] def hexROrbit (γ : Fin τ.rank → ℤ) : Set (Fin τ.rank → ℤ) :=
  {x | ∃ j : ℕ, x = (S.ρ : (Fin τ.rank → ℤ) → _)^[j] γ}

theorem hexR_neg_mem (h : S.HexStep) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (j : ℕ) :
    -((S.ρ : (Fin τ.rank → ℤ) → _)^[j] γ) ∈ hexROrbit S γ :=
  ⟨j + 3, (hexR_iter_add3 S h hγ j).symm ▸ rfl⟩

theorem hexR_step_prod (h : S.HexStep) {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) (v : Lˣ)
    (N : ℕ) :
    S.D.step (rootDiagUnit τ (∏ j ∈ Finset.range N,
      Hchar ((S.ρ : (Fin τ.rank → ℤ) → _)^[j] δ) (v ^ S.D.q ^ j))) =
      rootDiagUnit τ (∏ j ∈ Finset.range N,
        Hchar ((S.ρ : (Fin τ.rank → ℤ) → _)^[j + 1] δ) (v ^ S.D.q ^ (j + 1))) := by
  induction N with
  | zero => simp [rootDiagUnit_one]
  | succ N ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, rootDiagUnit_mul, rootDiagUnit_mul,
      map_mul, ih]
    congr 1
    have := h.hel _ (S.iterate_isRoot N hδ) (v ^ S.D.q ^ N)
    unfold Hel at this
    rw [this, Function.iterate_succ_apply']
    simp only [← pow_mul, pow_succ]

theorem hexR_lang (h : S.HexStep) (hτ : SimplyLacedTag τ) {δ : Fin τ.rank → ℤ}
    (hδ : IsRoot τ δ) {N : ℕ} (hN : 0 < N)
    (hρN : (S.ρ : (Fin τ.rank → ℤ) → _)^[N] δ = δ) (u : Lˣ) {Θ : Set (Fin τ.rank → ℤ)}
    (hΘ : ∀ j : ℕ, (S.ρ : (Fin τ.rank → ℤ) → _)^[j] δ ∈ Θ ∧
      -((S.ρ : (Fin τ.rank → ℤ) → _)^[j] δ) ∈ Θ) :
    ∃ b b' : Fin τ.rank → Lˣ, S.D.step (rootDiagUnit τ b) = rootDiagUnit τ b' ∧
      b * b'⁻¹ = Hchar δ u ∧ rootDiagUnit τ b ∈ rootSpan τ L Θ := by
  have hq2 : 2 ≤ S.D.q := S.hqpow.1.one_lt
  have hqN : 0 < S.D.q ^ N - 1 := by
    have : 1 < S.D.q ^ N := Nat.one_lt_pow hN.ne' (by omega)
    omega
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((u⁻¹ : Lˣ) : L) hqN
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hqN.ne'] at hz
    exact (Units.ne_zero _) hz.symm
  set v : Lˣ := Units.mk0 z hz0 with hv
  have hvu : v ^ (S.D.q ^ N - 1) = u⁻¹ := Units.ext (by simpa [hv] using hz)
  refine ⟨∏ j ∈ Finset.range N,
      Hchar ((S.ρ : (Fin τ.rank → ℤ) → _)^[j] δ) (v ^ S.D.q ^ j),
    ∏ j ∈ Finset.range N,
      Hchar ((S.ρ : (Fin τ.rank → ℤ) → _)^[j + 1] δ) (v ^ S.D.q ^ (j + 1)),
    hexR_step_prod S h hδ v N, ?_, ?_⟩
  · have h1 := Finset.prod_range_succ
      (fun j => Hchar ((S.ρ : (Fin τ.rank → ℤ) → _)^[j] δ) (v ^ S.D.q ^ j)) N
    have h2 := Finset.prod_range_succ'
      (fun j => Hchar ((S.ρ : (Fin τ.rank → ℤ) → _)^[j] δ) (v ^ S.D.q ^ j)) N
    rw [h1] at h2
    have h3 : Hchar ((S.ρ : (Fin τ.rank → ℤ) → _)^[N] δ) (v ^ S.D.q ^ N) =
        Hchar δ (v ^ S.D.q ^ N) := by rw [hρN]
    simp only [pow_zero, Function.iterate_zero, id, pow_one] at h2
    rw [h3] at h2
    have h4 : (∏ j ∈ Finset.range N,
        Hchar ((S.ρ : (Fin τ.rank → ℤ) → _)^[j] δ) (v ^ S.D.q ^ j)) *
        (∏ j ∈ Finset.range N,
          Hchar ((S.ρ : (Fin τ.rank → ℤ) → _)^[j + 1] δ) (v ^ S.D.q ^ (j + 1)))⁻¹ =
        Hchar δ v * (Hchar δ (v ^ S.D.q ^ N))⁻¹ := by
      simp only [← div_eq_mul_inv]
      exact div_eq_div_iff_mul_eq_mul.2 (by rw [h2, mul_comm])
    have hinv : ∀ g : Lˣ, (Hchar δ g)⁻¹ = Hchar (τ := τ) δ g⁻¹ := fun g => by
      have := Hchar_pow (τ := τ) δ g (-1)
      simpa using this
    have hpow : v ^ S.D.q ^ N = v ^ (S.D.q ^ N - 1) * v := by
      rw [← pow_succ]
      congr 1
      omega
    rw [h4, hinv, Hchar_mul]
    congr 1
    rw [hpow, mul_inv_rev, mul_inv_cancel_left, hvu, inv_inv]
  · have key : ∀ n : ℕ, rootDiagUnit τ
        (∏ j ∈ Finset.range n,
          Hchar ((S.ρ : (Fin τ.rank → ℤ) → _)^[j] δ) (v ^ S.D.q ^ j)) ∈ rootSpan τ L Θ := by
      intro n
      induction n with
      | zero => simp [rootDiagUnit_one, one_mem]
      | succ n ih =>
        rw [Finset.prod_range_succ, rootDiagUnit_mul]
        refine mul_mem ih ?_
        have hr : IsRoot τ ((S.ρ : (Fin τ.rank → ℤ) → _)^[n] δ) := S.iterate_isRoot n hδ
        have hsub : ({(S.ρ : (Fin τ.rank → ℤ) → _)^[n] δ,
            -((S.ρ : (Fin τ.rank → ℤ) → _)^[n] δ)} : Set (Fin τ.rank → ℤ)) ⊆ Θ := by
          intro x hx
          rcases hx with rfl | rfl
          · exact (hΘ n).1
          · exact (hΘ n).2
        exact rootSpan_mono hsub (Hel_root_mem_rootSpan hτ hr _)
    exact key N

end Rho

end CFSG.HardMathSupport.Timmesfeld.LangTorus
