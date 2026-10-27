module

public import CFSG.GH74.Uniqueness.SU.KI1r3Simple
public import CFSG.GH74.Uniqueness.SU.SU4Quot

public section

namespace CFSG.GH74.Uniqueness.SU.K.R3

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def FourFix (K : Type) [Group K] [Finite K] : Prop :=
  ∀ α : MulAut K, α ^ 2 = 1 →
    (∃ V : Subgroup K, (∀ v ∈ V, α v = v) ∧ Open.IsElemAbelian 2 V ∧ Nat.card V = 4) ∨
      4 ≤ Open.twoRank K

theorem FourFix.of_mulEquiv {K K' : Type} [Group K] [Finite K] [Group K'] [Finite K']
    (e : K ≃* K') (h : FourFix K) : FourFix K' := by
  intro α' hα'
  set α : MulAut K := MulAut.congr e.symm α' with hα
  have hα2 : α ^ 2 = 1 := by rw [hα, ← map_pow, hα', map_one]
  rcases h α hα2 with ⟨V, hV, hVel, hVc⟩ | h4
  · left
    refine ⟨V.map e.toMonoidHom, ?_, SU4.isElemAbelian_map e.toMonoidHom hVel, ?_⟩
    · rintro _ ⟨v, hv, rfl⟩
      have h1 : α v = v := hV v hv
      have h2 : e.symm (α' (e v)) = v := h1
      have h3 := congrArg e h2
      rw [MulEquiv.apply_symm_apply] at h3
      exact h3
    · rw [Subgroup.card_map_of_injective e.injective]
      exact hVc
  · right
    have h1 := SU4.pRank_map_of_injective e.toMonoidHom e.injective (⊤ : Subgroup K)
    have h2 : (⊤ : Subgroup K).map e.toMonoidHom = ⊤ :=
      Subgroup.map_top_of_surjective _ e.surjective
    rw [h2] at h1
    unfold Open.twoRank at h4 ⊢
    omega

theorem four_le_twoRank_of_card_sixteen {K : Type} [Group K] [Finite K] (E : Subgroup K)
    (hE : Open.IsElemAbelian 2 E) (hc : Nat.card E = 16) : 4 ≤ Open.twoRank K :=
  SU1.le_pRank (p := 2) (by norm_num) (le_top : E ≤ ⊤) hE (k := 4) (by rw [hc]; norm_num)

theorem FourFix.of_four_le_twoRank {K : Type} [Group K] [Finite K] (h : 4 ≤ Open.twoRank K) :
    FourFix K :=
  fun _ _ => Or.inr h

theorem FourFix.of_inner {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (hnab : ∃ a b : K, a * b ≠ b * a) (h : ∀ α : MulAut K, α ^ 2 = 1 → ∃ g : K, α = MulAut.conj g) :
    FourFix K := by
  intro α hα
  obtain ⟨g, rfl⟩ := h α hα
  left
  exact four_group_fixed_of_inner hnab g hα

@[expose] def FamAlt : Prop :=
  ∀ n : ℕ, 7 ≤ n → n ≤ 11 → FourFix (alternatingGroup (Fin n))

@[expose] def FamSp (s : TauCeti.SporadicName) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], NativeSporadic.IsSporadic K s → FourFix K

@[expose] def FamLie (t : StatedLieTag) (n : ℕ) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ p f : ℕ, p.Prime → p ≠ 2 → LieModel K t n p f → FourFix K

@[expose] def FamRee : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ f : ℕ, LieModel K .twistedG2 0 3 f → FourFix K

@[expose] def FamBender : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    (LieModel K .PSL 2 2 3 ∨ LieModel K .PSL 2 2 4 ∨ LieModel K .PSL 3 2 2 ∨
      LieModel K .PSU 3 2 2 ∨ LieModel K .twistedB2 0 2 3) → FourFix K

@[expose] def FamL2 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 → LieModel K .PSL 2 p f →
    IsSimpleGroup K → ∀ α : MulAut K, α ^ 2 = 1 →
      α ∉ (MulAut.conj : K →* MulAut K).range →
      (¬ ∃ V : Subgroup K, (∀ v ∈ V, α v = v) ∧ Open.IsElemAbelian 2 V ∧ Nat.card V = 4) →
        IsPGL2 ↥((MulAut.conj : K →* MulAut K).range ⊔ Subgroup.zpowers α) p f

end CFSG.GH74.Uniqueness.SU.K.R3
