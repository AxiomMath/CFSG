module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SplitLineFix
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE6
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PairFrame
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidDescent

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Steinberg.Adjoint
open scoped MatrixGroups

set_option linter.unusedSectionVars false


section Fix

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem twistedLine_exists_field (hAlg : S.IsAlgebraic) :
    ∃ k : Subfield L, Nat.card k = S.D.q ∧ IsAlgClosure k L := by
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨σ₀, hσ₀⟩ := exists_ringEquiv_frob (L := L) r e
  have hσ : ∀ c, σ₀ c = c ^ (r ^ e) := fun c => by
    have h1 : σ₀ c = iterateFrobenius L r e c := by
      rw [← hσ₀]
      rfl
    rw [h1, iterateFrobenius_def]
  obtain ⟨-, hcard⟩ := outer_fixSubfield_card (L := L) he σ₀ hσ
  have hq1 : 1 < S.D.q := by
    rw [hq]
    exact Nat.one_lt_pow he.ne' hr.one_lt
  refine ⟨fixSubfield σ₀, by rw [hcard, hq], ⟨inferInstance, ⟨fun x => ?_⟩⟩⟩
  obtain ⟨n, hn, hx⟩ := hAlg x
  refine ⟨Polynomial.X ^ (S.D.q ^ n) - Polynomial.X,
    FiniteField.X_pow_card_sub_X_ne_zero _ (Nat.one_lt_pow hn.ne' hq1), ?_⟩
  simp [hx]

theorem twistedLine_spec (hAlg : S.IsAlgebraic) (hq3 : 3 ≤ S.D.q)
    {ρ : SL(3, L) →* ModGL τ L} {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ}
    (h : IsSLFrame ρ σ) (hinj : Function.Injective ρ) (π : Equiv.Perm (Fin 3))
    (hπ : ∀ i j, i ≠ j → S.ρ (σ i j) = σ (π j) (π i)) :
    ρ.range ⊓ S.D.step.eqLocus (MonoidHom.id _) ≤ S.Γ ∧
    ⁅ρ.range ⊓ S.D.step.eqLocus (MonoidHom.id _), ρ.range ⊓ S.D.step.eqLocus (MonoidHom.id _)⁆ =
      ρ.range ⊓ S.D.step.eqLocus (MonoidHom.id _) := by
  obtain ⟨ℓ, f, hℓ, -, hf, hq⟩ := exists_char_pow S
  obtain ⟨k, hk, hcl⟩ := twistedLine_exists_field S hAlg
  obtain ⟨Fr, hFr, -⟩ := S.D.steinberg
  have hFr' : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => by rw [hFr, hq]
  have hΨ : ∀ i j, i ≠ j → ∃ b : Lˣ, ∀ c : L, S.D.step (pinnedX τ L (σ i j) c) =
      pinnedX τ L (σ (π j) (π i)) ((b : L) * Fr c) := by
    intro i j hij
    obtain ⟨μ, hμ0, hμ⟩ := step_pinnedX S (h.isRoot i j hij)
    refine ⟨Units.mk0 μ hμ0, fun c => ?_⟩
    rw [hμ c, hπ i j hij, Units.val_mk0, hFr]
  have hne : ((3 : ℕ), ℓ ^ f) ≠ (3, 2) := by
    intro h32
    have h2 : ℓ ^ f = 2 := (Prod.mk.inj h32).2
    rw [hq, h2] at hq3
    omega
  obtain ⟨-, -, hqs⟩ := h.fix_unitary hinj hℓ hf (k := k) (hk.trans hq) le_rfl Fr hFr'
    S.D.step (splitLine_step_injective S) π hΨ
  have hperf : ⁅ρ.range ⊓ S.D.step.eqLocus (MonoidHom.id _),
      ρ.range ⊓ S.D.step.eqLocus (MonoidHom.id _)⁆ =
        ρ.range ⊓ S.D.step.eqLocus (MonoidHom.id _) :=
    Subgroup.isPerfect_iff.mp (hqs hne).1.1
  refine ⟨?_, hperf⟩
  have hM : ρ.range ⊓ S.D.step.eqLocus (MonoidHom.id _) ≤ S.D.model :=
    inf_le_inf_right _ h.range_le_adjointGroup
  rw [← hperf]
  exact Subgroup.commutator_mono hM hM

theorem twistedLine_rootSpan_inf_model_le (hAlg : S.IsAlgebraic) (hq3 : 3 ≤ S.D.q)
    {ρ : SL(3, L) →* ModGL τ L} {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ}
    (h : IsSLFrame ρ σ) (hinj : Function.Injective ρ) (π : Equiv.Perm (Fin 3))
    (hπ : ∀ i j, i ≠ j → S.ρ (σ i j) = σ (π j) (π i)) :
    rootSpan τ L (frameRoots σ) ⊓ S.D.model ≤ S.Γ := by
  have hY := (twistedLine_spec S hAlg hq3 h hinj π hπ).1
  rw [← h.range]
  rintro x ⟨hx1, hx2⟩
  exact hY ⟨hx1, (Subgroup.mem_inf.1 hx2).2⟩

end Fix

section Hex

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem twistedLine_hex_shape (hrel : ∀ δ, IsRoot τ δ → S.ρ (S.ρ δ) = S.ρ δ - δ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    {ρ' : SL(3, L) →* ModGL τ L} {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ}
    (hfr : IsSLFrame ρ' σ) (h01 : σ 0 1 = γ) (h12 : σ 1 2 = -S.ρ γ) :
    (∀ i j, i ≠ j → S.ρ (σ i j) = σ (finRotate 3 j) (finRotate 3 i)) ∧
      {x | ∃ j : ℕ, x = (S.ρ : (Fin τ.rank → ℤ) → _)^[j] γ} = frameRoots σ := by
  have hργ : IsRoot τ (S.ρ γ) := (S.frob.isRoot_iff γ).2 hγ
  have h02 : σ 0 2 = γ - S.ρ γ := by rw [← hfr.add 0 1 2, h01, h12, sub_eq_add_neg]
  have h10 : σ 1 0 = -γ := by rw [hfr.neg 0 1, h01]
  have h21 : σ 2 1 = S.ρ γ := by rw [hfr.neg 1 2, h12, neg_neg]
  have h20 : σ 2 0 = S.ρ γ - γ := by rw [hfr.neg 0 2, h02, neg_sub]
  have e1 : S.ρ (S.ρ γ) = S.ρ γ - γ := hrel γ hγ
  have e2 : S.ρ (S.ρ γ - γ) = -γ := by
    have h := hrel (S.ρ γ) hργ
    rw [e1] at h
    rw [h]
    abel
  have e3 : S.ρ (γ - S.ρ γ) = γ := by
    rw [show γ - S.ρ γ = -(S.ρ γ - γ) by abel, S.frob.neg_eq, e2, neg_neg]
  have e4 : S.ρ (-γ) = -S.ρ γ := S.frob.neg_eq γ
  have e5 : S.ρ (-S.ρ γ) = γ - S.ρ γ := by
    rw [S.frob.neg_eq, e1, neg_sub]
  have r0 : finRotate 3 0 = 1 := by decide
  have r1 : finRotate 3 1 = 2 := by decide
  have r2 : finRotate 3 2 = 0 := by decide
  have hπ : ∀ i j, i ≠ j → S.ρ (σ i j) = σ (finRotate 3 j) (finRotate 3 i) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first | exact absurd rfl hij | skip
    · show S.ρ (σ 0 1) = σ (finRotate 3 1) (finRotate 3 0)
      rw [r0, r1, h01, h21]
    · show S.ρ (σ 0 2) = σ (finRotate 3 2) (finRotate 3 0)
      rw [r0, r2, h02, e3, h01]
    · show S.ρ (σ 1 0) = σ (finRotate 3 0) (finRotate 3 1)
      rw [r0, r1, h10, e4, h12]
    · show S.ρ (σ 1 2) = σ (finRotate 3 2) (finRotate 3 1)
      rw [r1, r2, h12, e5, h02]
    · show S.ρ (σ 2 0) = σ (finRotate 3 0) (finRotate 3 2)
      rw [r0, r2, h20, e2, h10]
    · show S.ρ (σ 2 1) = σ (finRotate 3 1) (finRotate 3 2)
      rw [r1, r2, h21, e1, h20]
  refine ⟨hπ, ?_⟩
  ext x
  constructor
  ·
    rintro ⟨j, rfl⟩
    induction j with
    | zero => exact ⟨0, 1, by decide, h01.symm⟩
    | succ j ih =>
      obtain ⟨a, b, hab, he⟩ := ih
      refine ⟨finRotate 3 b, finRotate 3 a, fun h => hab ((finRotate 3).injective h).symm, ?_⟩
      rw [Function.iterate_succ_apply', he, hπ a b hab]
  · rintro ⟨i, j, hij, rfl⟩
    have i0 : (S.ρ : (Fin τ.rank → ℤ) → _)^[0] γ = γ := rfl
    have i1 : (S.ρ : (Fin τ.rank → ℤ) → _)^[1] γ = S.ρ γ := rfl
    have i2 : (S.ρ : (Fin τ.rank → ℤ) → _)^[2] γ = S.ρ γ - γ := e1
    have i3 : (S.ρ : (Fin τ.rank → ℤ) → _)^[3] γ = -γ := by
      show S.ρ (S.ρ (S.ρ γ)) = -γ
      rw [e1, e2]
    have i4 : (S.ρ : (Fin τ.rank → ℤ) → _)^[4] γ = -S.ρ γ := by
      show S.ρ (S.ρ (S.ρ (S.ρ γ))) = -S.ρ γ
      rw [e1, e2, e4]
    have i5 : (S.ρ : (Fin τ.rank → ℤ) → _)^[5] γ = γ - S.ρ γ := by
      show S.ρ (S.ρ (S.ρ (S.ρ (S.ρ γ)))) = γ - S.ρ γ
      rw [e1, e2, e4, e5]
    fin_cases i <;> fin_cases j
    all_goals first | exact absurd rfl hij | skip
    · exact ⟨0, h01.trans i0.symm⟩
    · exact ⟨5, h02.trans i5.symm⟩
    · exact ⟨3, h10.trans i3.symm⟩
    · exact ⟨4, h12.trans i4.symm⟩
    · exact ⟨2, h20.trans i2.symm⟩
    · exact ⟨1, h21.trans i1.symm⟩

theorem twistedLine_hexGroup_le_of_frame (hAlg : S.IsAlgebraic) (hq3 : 3 ≤ S.D.q)
    (hrel : ∀ δ, IsRoot τ δ → S.ρ (S.ρ δ) = S.ρ δ - δ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    {ρ' : SL(3, L) →* ModGL τ L} {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ}
    (hfr : IsSLFrame ρ' σ) (hinj : Function.Injective ρ') (h01 : σ 0 1 = γ)
    (h12 : σ 1 2 = -S.ρ γ) :
    rootSpan τ L {x | ∃ j : ℕ, x = (S.ρ : (Fin τ.rank → ℤ) → _)^[j] γ} ⊓ S.D.model ≤ S.Γ := by
  obtain ⟨hπ, hset⟩ := twistedLine_hex_shape S hrel hγ hfr h01 h12
  rw [hset]
  exact twistedLine_rootSpan_inf_model_le S hAlg hq3 hfr hinj (finRotate 3) hπ

end Hex

section HexE6

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup Tag.E6 L p)

theorem twistedLine_iform_rho (hrel : ∀ δ, IsRoot Tag.E6 δ → S.ρ (S.ρ δ) = S.ρ δ - δ)
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) : iform γ (S.ρ γ) = 1 := by
  have hργ : IsRoot Tag.E6 (S.ρ γ) := (S.frob.isRoot_iff γ).2 hγ
  have h1 := S.frob.iform_eq γ (S.ρ γ)
  rw [hrel γ hγ, iform_sub_right,
    CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two (Or.inr (Or.inl rfl)) hργ,
    iform_comm (S.ρ γ) γ] at h1
  omega

theorem twistedLine_hex_frame (hrel : ∀ δ, IsRoot Tag.E6 δ → S.ρ (S.ρ δ) = S.ρ δ - δ)
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    ∃ (ρ' : SL(3, L) →* ModGL Tag.E6 L) (σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ),
      IsSLFrame ρ' σ ∧ Function.Injective ρ' ∧ σ 0 1 = γ ∧ σ 1 2 = -S.ρ γ := by
  have hργ : IsRoot Tag.E6 (S.ρ γ) := (S.frob.isRoot_iff γ).2 hγ
  have hip := twistedLine_iform_rho S hrel hγ
  have hγγ :=
    CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two (Or.inr (Or.inl rfl)) hγ
  have hne1 : γ ≠ -S.ρ γ := by
    intro h0
    have h2 : iform γ (-S.ρ γ) = iform γ γ := by rw [← h0]
    rw [iform_neg_right, hip, hγγ] at h2
    omega
  have hne2 : γ ≠ -(-S.ρ γ) := by
    rw [neg_neg]
    intro h0
    have h2 : iform γ (S.ρ γ) = iform γ γ := by rw [← h0]
    rw [hip, hγγ] at h2
    omega
  have he0 : IsRoot Tag.E6 (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) := IsRoot.basis 0
  have he2 : IsRoot Tag.E6 (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) := IsRoot.basis 2
  obtain ⟨w, hw0, hw2⟩ := LangTorus.PairFrame.exists_weyl_pair_iform
    LangTorus.PairFrame.pairInjective_E6 he0 he2 hγ (IsRoot.neg hργ) (by decide) (by decide)
    hne1 hne2 (by rw [iform_neg_right, hip]; decide)
  have hfr := (e6_base_frame (L := L)).transport w
  refine ⟨_, _, IsSLFrame.of_isA2Frame hfr, hfr.injective, ?_, ?_⟩
  · show w • _ = γ
    rw [e6_base_01, hw0]
  · show w • _ = -S.ρ γ
    rw [e6_base_12, hw2]

theorem twistedLine_hexGroup_le (hAlg : S.IsAlgebraic) (hq3 : 3 ≤ S.D.q)
    (hrel : ∀ δ, IsRoot Tag.E6 δ → S.ρ (S.ρ δ) = S.ρ δ - δ)
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    rootSpan Tag.E6 L {x | ∃ j : ℕ, x = (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[j] γ} ⊓ S.D.model ≤
      S.Γ := by
  obtain ⟨ρ', σ, hfr, hinj, h01, h12⟩ := twistedLine_hex_frame S hrel hγ
  exact twistedLine_hexGroup_le_of_frame S hAlg hq3 hrel hγ hfr hinj h01 h12

end HexE6

end CFSG.HardMathSupport.Timmesfeld.CrossChar
