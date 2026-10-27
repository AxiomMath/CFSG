module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZQ19
public import CFSG.Sporadic.Schreier.J4SProfileNode

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.RankThree.PartTwo.Census.Carrier.D4Even


section J2S

variable {K : Type} [Field K] [Finite K] [CharP K 3]

local instance : NeZero Tag.D4.rank := ⟨by decide⟩

local notation "Jtwo" => ({2} : Set (Fin Tag.D4.rank))

theorem J2_typeS_fix (hK2 : ringChar K ≠ 2) {φ : ModGL Tag.D4 K →* ModGL Tag.D4 K}
    {Γ₁ Γ₂ : ModGL Tag.D4 K} (G : A4Grp Jtwo φ Γ₁ Γ₂) {q₁ q₂ : ModGL Tag.D4 K}
    (hq₁ : q₁ ∈ parabolicRadical Tag.D4 K Jtwo) (hq₂ : q₂ ∈ parabolicRadical Tag.D4 K Jtwo)
    {b₁ b₂ : Fin Tag.D4.rank → Kˣ} (h₁2 : b₁ 2 = 1) (h₂2 : b₂ 2 = 1)
    (hΓ₁ : Γ₁ = q₁ * rootDiagUnit Tag.D4 b₁) (hΓ₂ : Γ₂ = q₂ * rootDiagUnit Tag.D4 b₂)
    (hne : ¬(b₁ 0 = 1 ∧ b₁ 1 = 1 ∧ b₁ 3 = 1)) :
    Nat.card (fixSp (lconj G.n₁ (le_refl (1 : ℤ))) ⊓ fixSp (lconj G.n₂ (le_refl (1 : ℤ))) :
        Submodule (ZMod 3) (Lyr (isLayer_degSeries (K := K) (J := Jtwo) (le_refl (1 : ℤ))))) = 1 ∧
      Nat.card (fixSp (lconj G.n₁ (show (1 : ℤ) ≤ 2 by norm_num)) ⊓
        fixSp (lconj G.n₂ (show (1 : ℤ) ≤ 2 by norm_num)) : Submodule (ZMod 3)
          (Lyr (isLayer_degSeries (K := K) (J := Jtwo) (show (1 : ℤ) ≤ 2 by norm_num)))) = 1 := by
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  have hd1 : (1 : ℤ) ≤ 1 := le_refl 1
  have hd2 : (1 : ℤ) ≤ 2 := by norm_num
  have hT₁ : ∀ {d : ℤ} (hd : 1 ≤ d) (z : Lyr (isLayer_degSeries (K := K) (J := Jtwo) hd)),
      lconj G.n₁ hd z = conjL b₁ hd z :=
    fun hd z => lconj_eq_conjL_of_typeS G.n₁ hq₁ b₁ hΓ₁ hd z
  have hT₂ : ∀ {d : ℤ} (hd : 1 ≤ d) (z : Lyr (isLayer_degSeries (K := K) (J := Jtwo) hd)),
      lconj G.n₂ hd z = conjL b₂ hd z :=
    fun hd z => lconj_eq_conjL_of_typeS G.n₂ hq₂ b₂ hΓ₂ hd z
  have hinv₁ : ∀ z, conjL b₁ hd1 (conjL b₁ hd1 z) = z := fun z => by
    calc conjL b₁ hd1 (conjL b₁ hd1 z) = lconj G.n₁ hd1 (lconj G.n₁ hd1 z) := by
          rw [hT₁ hd1, hT₁ hd1]
      _ = z := G.layer_inv₁ hd1 z
  have hinv₂ : ∀ z, conjL b₂ hd1 (conjL b₂ hd1 z) = z := fun z => by
    calc conjL b₂ hd1 (conjL b₂ hd1 z) = lconj G.n₂ hd1 (lconj G.n₂ hd1 z) := by
          rw [hT₂ hd1, hT₂ hd1]
      _ = z := G.layer_inv₂ hd1 z
  obtain ⟨β₀, hβ₀⟩ := exists_bit (eq_one_or_neg_one_of_inv b₁ h₁2 hinv₁ (Or.inl rfl))
  obtain ⟨β₁, hβ₁⟩ := exists_bit (eq_one_or_neg_one_of_inv b₁ h₁2 hinv₁ (Or.inr (Or.inl rfl)))
  obtain ⟨β₃, hβ₃⟩ := exists_bit (eq_one_or_neg_one_of_inv b₁ h₁2 hinv₁ (Or.inr (Or.inr rfl)))
  obtain ⟨γ₀, hγ₀⟩ := exists_bit (eq_one_or_neg_one_of_inv b₂ h₂2 hinv₂ (Or.inl rfl))
  obtain ⟨γ₁, hγ₁⟩ := exists_bit (eq_one_or_neg_one_of_inv b₂ h₂2 hinv₂ (Or.inr (Or.inl rfl)))
  obtain ⟨γ₃, hγ₃⟩ := exists_bit (eq_one_or_neg_one_of_inv b₂ h₂2 hinv₂ (Or.inr (Or.inr rfl)))
  have hs₁ : ∀ v, (parE β₀ β₁ β₃ v ∧ ((rootChar b₁ v : Kˣ) : K) = 1) ∨
      (¬ parE β₀ β₁ β₃ v ∧ ((rootChar b₁ v : Kˣ) : K) = -1) :=
    fun v => rootChar_one_or_neg_one b₁ h₁2 hβ₀ hβ₁ hβ₃ hK2 v
  have hs₂ : ∀ v, (parE γ₀ γ₁ γ₃ v ∧ ((rootChar b₂ v : Kˣ) : K) = 1) ∨
      (¬ parE γ₀ γ₁ γ₃ v ∧ ((rootChar b₂ v : Kˣ) : K) = -1) :=
    fun v => rootChar_one_or_neg_one b₂ h₂2 hγ₀ hγ₁ hγ₃ hK2 v
  have hD₁ : ∀ {d : ℤ} (hd : 1 ≤ d) (c : degLayerRoots Tag.D4 Jtwo d → K),
      lconj G.n₁ hd (coordMap hd c) =
        coordMap hd (fun i => ((rootChar b₁ i.1 : Kˣ) : K) * c i) :=
    fun hd c => by rw [hT₁ hd, conjL_coordMap]
  have hD₂ : ∀ {d : ℤ} (hd : 1 ≤ d) (c : degLayerRoots Tag.D4 Jtwo d → K),
      lconj G.n₂ hd (coordMap hd c) =
        coordMap hd (fun i => ((rootChar b₂ i.1 : Kˣ) : K) * c i) :=
    fun hd c => by rw [hT₂ hd, conjL_coordMap]
  have hD₁₂ : ∀ {d : ℤ} (hd : 1 ≤ d) (c : degLayerRoots Tag.D4 Jtwo d → K),
      (lconj G.n₁ hd * lconj G.n₂ hd) (coordMap hd c) =
        coordMap hd (fun i => (((rootChar b₁ i.1 : Kˣ) : K) * ((rootChar b₂ i.1 : Kˣ) : K)) * c i) := by
    intro d hd c
    rw [Module.End.mul_apply, hD₂ hd, hD₁ hd]
    congr 1
    funext i
    ring
  have hs₁₂ : ∀ v, (parE (β₀ + γ₀) (β₁ + γ₁) (β₃ + γ₃) v ∧
        ((rootChar b₁ v : Kˣ) : K) * ((rootChar b₂ v : Kˣ) : K) = 1) ∨
      (¬ parE (β₀ + γ₀) (β₁ + γ₁) (β₃ + γ₃) v ∧
        ((rootChar b₁ v : Kˣ) : K) * ((rootChar b₂ v : Kˣ) : K) = -1) := by
    intro v
    rw [parE_add_iff]
    rcases hs₁ v with ⟨p1, e1⟩ | ⟨p1, e1⟩ <;> rcases hs₂ v with ⟨p2, e2⟩ | ⟨p2, e2⟩
    · left; exact ⟨⟨fun _ => p2, fun _ => p1⟩, by rw [e1, e2]; ring⟩
    · right; exact ⟨fun h => p2 (h.1 p1), by rw [e1, e2]; ring⟩
    · right; exact ⟨fun h => p1 (h.2 p2), by rw [e1, e2]; ring⟩
    · left; exact ⟨⟨fun h => absurd h p1, fun h => absurd h p2⟩, by rw [e1, e2]; ring⟩
  have hq2 : 2 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  have c₁ := card_fixSp_diag hd1 hK2 (T := lconj G.n₁ hd1)
    (fun i => ((rootChar b₁ i.1 : Kˣ) : K)) (fun i => parE β₀ β₁ β₃ i.1) (hD₁ hd1)
    (fun i => hs₁ i.1)
  have c₂ := card_fixSp_diag hd1 hK2 (T := lconj G.n₂ hd1)
    (fun i => ((rootChar b₂ i.1 : Kˣ) : K)) (fun i => parE γ₀ γ₁ γ₃ i.1) (hD₂ hd1)
    (fun i => hs₂ i.1)
  have c₁₂ := card_fixSp_diag hd1 hK2 (T := lconj G.n₁ hd1 * lconj G.n₂ hd1)
    (fun i => ((rootChar b₁ i.1 : Kˣ) : K) * ((rootChar b₂ i.1 : Kˣ) : K))
    (fun i => parE (β₀ + γ₀) (β₁ + γ₁) (β₃ + γ₃) i.1) (hD₁₂ hd1) (fun i => hs₁₂ i.1)
  have e12 : Nat.card (fixSp (lconj G.n₂ hd1)) = Nat.card (fixSp (lconj G.n₁ hd1)) :=
    card_fixSp_eq_of_conj _ _ (G.layerB hd1) (G.layer_B₁ hd1)
  have e23 : Nat.card (fixSp (lconj G.n₁ hd1 * lconj G.n₂ hd1)) =
      Nat.card (fixSp (lconj G.n₂ hd1)) :=
    card_fixSp_eq_of_conj _ _ (G.layerB hd1) (G.layer_B₂ hd1)
  rw [c₁, c₂] at e12
  rw [c₁₂, c₂] at e23
  have n12 := Nat.pow_right_injective hq2 e12
  have n23 := Nat.pow_right_injective hq2 e23
  have k₁ := card_subtype_layer_J2 hd1 (parE β₀ β₁ β₃)
  have k₂ := card_subtype_layer_J2 hd1 (parE γ₀ γ₁ γ₃)
  have k₁₂ := card_subtype_layer_J2 hd1 (parE (β₀ + γ₀) (β₁ + γ₁) (β₃ + γ₃))
  have hβ₀' : β₀ = 0 ∨ β₀ = 1 := hβ₀.imp (·.1) (·.1)
  have hβ₁' : β₁ = 0 ∨ β₁ = 1 := hβ₁.imp (·.1) (·.1)
  have hβ₃' : β₃ = 0 ∨ β₃ = 1 := hβ₃.imp (·.1) (·.1)
  have hγ₀' : γ₀ = 0 ∨ γ₀ = 1 := hγ₀.imp (·.1) (·.1)
  have hγ₁' : γ₁ = 0 ∨ γ₁ = 1 := hγ₁.imp (·.1) (·.1)
  have hγ₃' : γ₃ = 0 ∨ γ₃ = 1 := hγ₃.imp (·.1) (·.1)
  have hne' : ¬(β₀ = 0 ∧ β₁ = 0 ∧ β₃ = 0) := by
    rintro ⟨h0, h1, h3⟩
    apply hne
    refine ⟨?_, ?_, ?_⟩
    · rcases hβ₀ with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · omega
    · rcases hβ₁ with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · omega
    · rcases hβ₃ with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · omega
  obtain ⟨z1, z2⟩ := sign_combin β₀ β₁ β₃ γ₀ γ₁ γ₃ hβ₀' hβ₁' hβ₃' hγ₀' hγ₁' hγ₃'
    (by rw [← k₁, ← k₂]; exact n12.symm)
    (by rw [← k₂, ← k₁₂]; exact n23.symm) hne'
  have hcount : ∀ {d : ℤ} (hd : 1 ≤ d),
      cntRoots d (fun v => parE β₀ β₁ β₃ v ∧ parE γ₀ γ₁ γ₃ v) = 0 →
      Nat.card (fixSp (lconj G.n₁ hd) ⊓ fixSp (lconj G.n₂ hd) : Submodule (ZMod 3)
        (Lyr (isLayer_degSeries (K := K) (J := Jtwo) hd))) = 1 := by
    intro d hd h0
    rw [card_inf_fixSp_diag hd hK2 (T := lconj G.n₁ hd) (T' := lconj G.n₂ hd)
      (fun i => ((rootChar b₁ i.1 : Kˣ) : K)) (fun i => ((rootChar b₂ i.1 : Kˣ) : K))
      (fun i => parE β₀ β₁ β₃ i.1) (fun i => parE γ₀ γ₁ γ₃ i.1) (hD₁ hd) (hD₂ hd)
      (fun i => hs₁ i.1) (fun i => hs₂ i.1)]
    have := card_subtype_layer_J2 hd (fun v => parE β₀ β₁ β₃ v ∧ parE γ₀ γ₁ γ₃ v)
    rw [this, h0, pow_zero]
  exact ⟨hcount hd1 z1, hcount hd2 z2⟩

end J2S

end CFSG.LocalAnalysis.GLTheoremA
