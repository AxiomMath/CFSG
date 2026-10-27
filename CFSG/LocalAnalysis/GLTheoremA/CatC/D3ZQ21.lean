module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZQ20

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.RankThree.PartTwo.Census.Carrier.D4Even


section J2

variable {K : Type} [Field K] [Finite K] [CharP K 3]

local instance : NeZero Tag.D4.rank := ⟨by decide⟩

local notation "Jtwo" => ({2} : Set (Fin Tag.D4.rank))

theorem J2_card_A (hK2 : ringChar K ≠ 2) {φ : ModGL Tag.D4 K →* ModGL Tag.D4 K}
    {Γ₁ Γ₂ c₁ c₂ : ModGL Tag.D4 K} {a₁ a₂ : Fin Tag.D4.rank → Kˣ} (G : A4Grp Jtwo φ Γ₁ Γ₂)
    (hc₁ : c₁ ∈ parabolicSubgroup Tag.D4 K Jtwo) (hc₂ : c₂ ∈ parabolicSubgroup Tag.D4 K Jtwo)
    (hΓ₁ : Γ₁ = c₁ * rootDiagUnit Tag.D4 a₁) (hΓ₂ : Γ₂ = c₂ * rootDiagUnit Tag.D4 a₂)
    (hne₁ : ∃ x ∈ adjointGroup Tag.D4 K, Γ₁ * x * Γ₁⁻¹ ≠ x)
    {A : Subgroup (ModGL Tag.D4 K)} (hA : A ≤ parabolicRadical Tag.D4 K Jtwo)
    (hA₁ : ∀ a ∈ A, Γ₁ * a * Γ₁⁻¹ = a) (hA₂ : ∀ a ∈ A, Γ₂ * a * Γ₂⁻¹ = a) :
    Nat.card A ≤ Nat.card K ^ 2 := by
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  have hd1 : (1 : ℤ) ≤ 1 := le_refl 1
  have hd2 : (1 : ℤ) ≤ 2 := by norm_num
  have hd3 : (1 : ℤ) ≤ 3 := by norm_num
  obtain ⟨hN₁, hN₂⟩ := J2_not_typeN G hc₁ hc₂ hΓ₁ hΓ₂
  obtain ⟨q₁, hq₁, b₁, h₁2, hb₁⟩ : ∃ q ∈ parabolicRadical Tag.D4 K Jtwo,
      ∃ b' : Fin Tag.D4.rank → Kˣ, b' 2 = 1 ∧ Γ₁ = q * rootDiagUnit Tag.D4 b' := by
    rcases gamma_dichotomy_two hK2 hc₁ a₁ (fun x hx => by
        rw [← hΓ₁]; exact G.sq₁ x (parabolicLevi_le_adjointGroup _ _ _ hx)) with
      ⟨y, q, hy, hq, hyeq⟩ | ⟨q, hq, b', h2, hΓeq⟩
    · exact (hN₁ (card_fix_sq_of_N G.n₁ hy hq (by rw [hΓ₁]; exact hyeq) hd1
        (by decide : Odd (1 : ℤ)) (fun x hx => G.sq₁ x (degSeries_le_adjointGroup 1 hx)))).elim
    · exact ⟨q, hq, b', h2, by rw [hΓ₁]; exact hΓeq⟩
  obtain ⟨q₂, hq₂, b₂, h₂2, hb₂⟩ : ∃ q ∈ parabolicRadical Tag.D4 K Jtwo,
      ∃ b' : Fin Tag.D4.rank → Kˣ, b' 2 = 1 ∧ Γ₂ = q * rootDiagUnit Tag.D4 b' := by
    rcases gamma_dichotomy_two hK2 hc₂ a₂ (fun x hx => by
        rw [← hΓ₂]; exact G.sq₂ x (parabolicLevi_le_adjointGroup _ _ _ hx)) with
      ⟨y, q, hy, hq, hyeq⟩ | ⟨q, hq, b', h2, hΓeq⟩
    · exact (hN₂ (card_fix_sq_of_N G.n₂ hy hq (by rw [hΓ₂]; exact hyeq) hd1
        (by decide : Odd (1 : ℤ)) (fun x hx => G.sq₂ x (degSeries_le_adjointGroup 1 hx)))).elim
    · exact ⟨q, hq, b', h2, by rw [hΓ₂]; exact hΓeq⟩
  have hne : ¬(b₁ 0 = 1 ∧ b₁ 1 = 1 ∧ b₁ 3 = 1) := by
    rintro ⟨h0, h1, h3⟩
    have hb' : b₁ = 1 := by
      funext k
      have h4 : ∀ k : Fin Tag.D4.rank, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by decide
      rcases h4 k with rfl | rfl | rfl | rfl <;> simp [h0, h1, h₁2, h3]
    have hΓq : Γ₁ = q₁ := by rw [hb₁, hb', rootDiagUnit_one, mul_one]
    obtain ⟨x, hx, hxne⟩ := hne₁
    refine hxne ?_
    rw [hΓq]
    exact conj_eq_of_radical_sq hq₁ (fun y hy => by rw [← hΓq]; exact G.sq₁ y hy) hx
  obtain ⟨hF1, hF2⟩ := J2_typeS_fix hK2 G hq₁ hq₂ h₁2 h₂2 hb₁ hb₂ hne
  have hL1 := isLayer_degSeries (K := K) (J := Jtwo) hd1
  have hL2 := isLayer_degSeries (K := K) (J := Jtwo) hd2
  have hL3 := isLayer_degSeries (K := K) (J := Jtwo) hd3
  have hL3card : Nat.card (Lyr hL3) = Nat.card K ^ 2 := by
    rw [card_layer hd3]
    have h2 : (degLayerRoots Tag.D4 Jtwo 3).ncard = 2 := ncard_layer_J2_three
    rw [h2]
  have h1 := card_inf_le_mul hL1 A
    ((fixSp (lconj G.n₁ hd1) ⊓ fixSp (lconj G.n₂ hd1) : Submodule (ZMod 3) (Lyr hL1)) :
      Set (Lyr hL1)) (fun a ha haH => class_mem_fix G hA₁ hA₂ hd1 a ha haH)
  have h2 := card_inf_le_mul hL2 A
    ((fixSp (lconj G.n₁ hd2) ⊓ fixSp (lconj G.n₂ hd2) : Submodule (ZMod 3) (Lyr hL2)) :
      Set (Lyr hL2)) (fun a ha haH => class_mem_fix G hA₁ hA₂ hd2 a ha haH)
  have h3 := card_inf_le_mul hL3 A (Set.univ : Set (Lyr hL3)) (fun _ _ _ => Set.mem_univ _)
  have hAH : A ⊓ degSeries Tag.D4 K Jtwo 1 = A := inf_eq_left.2 (by rwa [degSeries_one])
  have h4 : degSeries Tag.D4 K Jtwo (3 + 1) = ⊥ := degSeries_J2_four (by norm_num)
  have hbot : Nat.card ↥(A ⊓ degSeries Tag.D4 K Jtwo (3 + 1)) = 1 := by
    rw [h4, inf_bot_eq]; exact Subgroup.card_bot
  have hS1 : Nat.card (((fixSp (lconj G.n₁ hd1) ⊓ fixSp (lconj G.n₂ hd1) : Submodule (ZMod 3)
      (Lyr hL1)) : Set (Lyr hL1))) = 1 := hF1
  have hS2 : Nat.card (((fixSp (lconj G.n₁ hd2) ⊓ fixSp (lconj G.n₂ hd2) : Submodule (ZMod 3)
      (Lyr hL2)) : Set (Lyr hL2))) = 1 := hF2
  rw [hAH] at h1
  rw [hS1] at h1
  rw [hS2] at h2
  rw [hbot, mul_one, Nat.card_univ, hL3card] at h3
  calc Nat.card A ≤ 1 * Nat.card ↥(A ⊓ degSeries Tag.D4 K Jtwo (1 + 1)) := h1
    _ ≤ 1 * (1 * Nat.card ↥(A ⊓ degSeries Tag.D4 K Jtwo (2 + 1))) :=
        Nat.mul_le_mul_left _ h2
    _ ≤ 1 * (1 * Nat.card K ^ 2) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
    _ = Nat.card K ^ 2 := by ring

end J2

end CFSG.LocalAnalysis.GLTheoremA
