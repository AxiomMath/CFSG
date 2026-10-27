module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3FixP1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3FixP2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3FixP3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3Conj

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr P3

@[expose] def FixTrivialPair {m : ℕ} (H : Subgroup (AEQ m)) (𝒜 : Set (Finset (Fin m))) : Prop :=
  ∀ α ∈ 𝒜, ∀ (h4 : α.card = 4) (b : Bool), ∀ β ∈ 𝒜, ∀ (h4' : β.card = 4) (b' : Bool),
    zBar β h4' = zBar α h4 → memBar α h4 b ≠ memBar β h4' b' →
    ∀ σ : ↥H →* ↥H, (∃ a : ℕ, ∀ r, (⇑σ)^[3 ^ a] r = r) →
      (∀ x : ↥H, (x : AEQ m) ∈ memBar α h4 b → σ x = x) →
      (∀ x : ↥H, (x : AEQ m) ∈ memBar β h4' b' → σ x = x) → ∀ r, σ r = r

theorem zBar_eq {α β : Finset (Fin 8)} (h : α.card = 4) (h' : β.card = 4)
    (hz : zBar β h' = zBar α h) : β = α ∨ β = αᶜ := by
  unfold zBar at hz
  rw [zOf_emb, zOf_emb] at hz
  have hv : ∀ x, ((ofVec (indV β))⁻¹ * ofVec (indV α)).vec x = indV β x + indV α x := fun x => rfl
  rcases mkQ_eq_iff.mp hz with h1 | h1
  · left
    refine Finset.ext fun x => ?_
    have := hv x
    rw [h1] at this
    have h0 : (0 : ZMod 2) = (if x ∈ β then 1 else 0) + (if x ∈ α then 1 else 0) := this
    constructor
    · intro hx
      by_contra ha
      rw [if_pos hx, if_neg ha] at h0
      exact absurd h0 (by decide)
    · intro hx
      by_contra hb
      rw [if_neg hb, if_pos hx] at h0
      exact absurd h0 (by decide)
  · right
    refine Finset.ext fun x => ?_
    have := hv x
    rw [h1] at this
    have h0 : (1 : ZMod 2) = (if x ∈ β then 1 else 0) + (if x ∈ α then 1 else 0) := this
    constructor
    · intro hx
      rw [Finset.mem_compl]
      intro ha
      rw [if_pos hx, if_pos ha] at h0
      exact absurd h0 (by decide)
    · intro hx
      by_contra hb
      rw [if_neg hb, if_neg (Finset.mem_compl.mp hx)] at h0
      exact absurd h0 (by decide)

theorem transfer {g : Wr 8} (hg : g ∈ aeSubOver agl32) {P1 P2 M1 M2 : Subgroup (AEQ 8)}
    (i1 : Into g P1 M1) (i2 : Into g P2 M2)
    (core : ∀ τ : ↥e29Sub →* ↥e29Sub, (∃ a : ℕ, ∀ r, (⇑τ)^[3 ^ a] r = r) →
      (∀ x : ↥e29Sub, (x : AEQ 8) ∈ P1 → τ x = x) → (∀ x : ↥e29Sub, (x : AEQ 8) ∈ P2 → τ x = x) →
      ∀ r, τ r = r)
    (σ : ↥e29Sub →* ↥e29Sub) (hσ : ∃ a : ℕ, ∀ r, (⇑σ)^[3 ^ a] r = r)
    (f1 : ∀ x : ↥e29Sub, (x : AEQ 8) ∈ M1 → σ x = x)
    (f2 : ∀ x : ↥e29Sub, (x : AEQ 8) ∈ M2 → σ x = x) : ∀ r, σ r = r := by
  set G : ↥e29Sub := ⟨mkQ 8 g, ⟨g, hg, rfl⟩⟩ with hG
  let σ' : ↥e29Sub →* ↥e29Sub :=
    (MulAut.conj G⁻¹).toMonoidHom.comp (σ.comp (MulAut.conj G).toMonoidHom)
  have hσ'app : ∀ r, σ' r = G⁻¹ * σ (G * r * G⁻¹) * G⁻¹⁻¹ := fun r => rfl
  have hfixM : ∀ (P M : Subgroup (AEQ 8)), Into g P M → (∀ x : ↥e29Sub, (x : AEQ 8) ∈ M → σ x = x) →
      ∀ y : ↥e29Sub, (y : AEQ 8) ∈ P → σ' y = y := by
    intro P M hi hf y hy
    have hmem : ((G * y * G⁻¹ : ↥e29Sub) : AEQ 8) ∈ M := hi _ hy
    have := hf _ hmem
    rw [hσ'app, this]
    group
  have hit : ∀ (k : ℕ) (r : ↥e29Sub), (⇑σ')^[k] r = G⁻¹ * (⇑σ)^[k] (G * r * G⁻¹) * G := by
    intro k
    induction k with
    | zero => intro r; simp only [Function.iterate_zero, id_eq]; group
    | succ k ih =>
      intro r
      rw [Function.iterate_succ_apply', ih, hσ'app, Function.iterate_succ_apply']
      group
  obtain ⟨N, hN⟩ := hσ
  have hσ'N : ∃ a : ℕ, ∀ r, (⇑σ')^[3 ^ a] r = r := ⟨N, fun r => by
    rw [hit, hN]; group⟩
  have hall := core σ' hσ'N (hfixM _ _ i1 f1) (hfixM _ _ i2 f2)
  intro r
  have := hall (G⁻¹ * r * G)
  rw [hσ'app] at this
  have e : G * (G⁻¹ * r * G) * G⁻¹ = r := by group
  rw [e, inv_inv] at this
  calc σ r = G * (G⁻¹ * σ r * G) * G⁻¹ := by group
    _ = G * (G⁻¹ * r * G) * G⁻¹ := by rw [this]
    _ = r := by group

theorem fixTrivialPair_e29 : FixTrivialPair e29Sub e29Sets := by
  intro α hα h4 b β hβ h4' b' hz hne σ hσ f1 f2
  have hcls := zBar_eq h4 h4' hz
  have hne' : ¬ (β = α ∧ b' = b) := by
    rintro ⟨rfl, rfl⟩
    exact hne rfl
  rcases pair_conj hα h4 b h4' b' hcls hne' with ⟨g, hg, i1, i2⟩ | ⟨g, hg, i1, i2⟩ |
      ⟨g, hg, i1, i2⟩
  · exact transfer hg i1 i2 (fun τ hτ a b => fixPair_P1 τ hτ a b) σ hσ f1 f2
  · exact transfer hg i1 i2 (fun τ hτ a b => fixPair_P2 τ hτ a b) σ hσ f1 f2
  · exact transfer hg i1 i2 (fun τ hτ a b => fixPair_P3 τ hτ a b) σ hσ f1 f2

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf
