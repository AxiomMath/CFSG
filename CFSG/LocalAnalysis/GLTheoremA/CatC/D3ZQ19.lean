module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZQ18

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.RankThree.PartTwo.Census.Carrier.D4Even


section Gen

variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 3] {J : Set (Fin τ.rank)}

theorem lconj_eq_conjL_of_typeS {Γ q : ModGL τ K} (hΓ : NormAll J Γ)
    (hq : q ∈ parabolicRadical τ K J) (b : Fin τ.rank → Kˣ) (h : Γ = q * rootDiagUnit τ b)
    {d : ℤ} (hd : 1 ≤ d) (z : Lyr (isLayer_degSeries (K := K) (J := J) hd)) :
    lconj hΓ hd z = conjL b hd z := by
  have hq' : NormAll J q := NormAll.of_radical hq
  calc lconj hΓ hd z = lconj (hq'.mul (NormAll.of_rootDiagUnit b)) hd z := lconj_congr hΓ _ h hd z
    _ = lconj hq' hd (lconj (NormAll.of_rootDiagUnit b) hd z) := lconj_mul hq' _ hd z
    _ = conjL b hd z := by rw [lconj_radical hq hd]; rfl

theorem rootChar_sq_of_inv {b : Fin τ.rank → Kˣ} {d : ℤ} (hd : 1 ≤ d)
    (hinv : ∀ z : Lyr (isLayer_degSeries (K := K) (J := J) hd), conjL b hd (conjL b hd z) = z)
    (i : degLayerRoots τ J d) :
    ((rootChar b i.1 : Kˣ) : K) * ((rootChar b i.1 : Kˣ) : K) = 1 := by
  have hinj := (coordMap_bijective (τ := τ) (K := K) (J := J) hd).1
  have h := hinv (coordMap hd (Pi.single i 1))
  rw [conjL_coordMap, conjL_coordMap] at h
  have h' := congrFun (hinj h) i
  simpa using h'

theorem class_mem_fix {φ : ModGL τ K →* ModGL τ K} {Γ₁ Γ₂ : ModGL τ K} (G : A4Grp J φ Γ₁ Γ₂)
    {A : Subgroup (ModGL τ K)} (hA₁ : ∀ a ∈ A, Γ₁ * a * Γ₁⁻¹ = a)
    (hA₂ : ∀ a ∈ A, Γ₂ * a * Γ₂⁻¹ = a) {d : ℤ} (hd : 1 ≤ d) (a : ModGL τ K) (ha : a ∈ A)
    (haH : a ∈ degSeries τ K J d) :
    Lyr.mk (isLayer_degSeries (K := K) (J := J) hd) ⟨a, haH⟩ ∈
      ((fixSp (lconj G.n₁ hd) ⊓ fixSp (lconj G.n₂ hd) : Submodule (ZMod 3)
        (Lyr (isLayer_degSeries (K := K) (J := J) hd))) :
          Set (Lyr (isLayer_degSeries (K := K) (J := J) hd))) := by
  refine ⟨mem_fixSp.2 ?_, mem_fixSp.2 ?_⟩
  · rw [lconj_mk]; congr 1; exact Subtype.ext (hA₁ a ha)
  · rw [lconj_mk]; congr 1; exact Subtype.ext (hA₂ a ha)

end Gen

section J2S

variable {K : Type} [Field K] [Finite K] [CharP K 3]

local instance : NeZero Tag.D4.rank := ⟨by decide⟩

theorem single_mem_layer_one {k : Fin Tag.D4.rank} (hk : k = 0 ∨ k = 1 ∨ k = 3) :
    (Pi.single k 1 : Fin Tag.D4.rank → ℤ) ∈
      degLayerRoots Tag.D4 ({2} : Set (Fin Tag.D4.rank)) 1 := by
  rw [degLayerRoots_J2 le_rfl, Finset.mem_coe, Finset.mem_filter]
  rcases hk with rfl | rfl | rfl <;> decide +kernel

theorem rootChar_single_J2 (b : Fin Tag.D4.rank → Kˣ) (h2 : b 2 = 1) {k : Fin Tag.D4.rank}
    (hk : k = 0 ∨ k = 1 ∨ k = 3) : rootChar b (Pi.single k 1) = b k := by
  rw [rootChar_J2 b h2]
  rcases hk with rfl | rfl | rfl <;> simp [Pi.single_apply]

theorem eq_one_or_neg_one_of_inv (b : Fin Tag.D4.rank → Kˣ) (h2 : b 2 = 1)
    (hinv : ∀ z : Lyr (isLayer_degSeries (K := K) (J := ({2} : Set (Fin Tag.D4.rank)))
      (le_refl (1 : ℤ))), conjL b (le_refl (1 : ℤ)) (conjL b (le_refl (1 : ℤ)) z) = z)
    {k : Fin Tag.D4.rank} (hk : k = 0 ∨ k = 1 ∨ k = 3) : b k = 1 ∨ b k = -1 := by
  have h := rootChar_sq_of_inv (le_refl (1 : ℤ)) hinv ⟨_, single_mem_layer_one hk⟩
  have e : rootChar b (Pi.single k 1) = b k := rootChar_single_J2 b h2 hk
  have h' : ((b k : Kˣ) : K) * ((b k : Kˣ) : K) = 1 := by
    have := h
    simp only [e] at this
    exact this
  rcases mul_self_eq_one_iff.1 h' with h1 | h1
  · left; exact Units.ext h1
  · right; exact Units.ext (by simpa using h1)

theorem exists_bit {u : Kˣ} (h : u = 1 ∨ u = -1) : ∃ β : ℤ, (β = 0 ∧ u = 1) ∨ (β = 1 ∧ u = -1) := by
  rcases h with h | h
  · exact ⟨0, Or.inl ⟨rfl, h⟩⟩
  · exact ⟨1, Or.inr ⟨rfl, h⟩⟩

theorem parE_add_iff (β₀ β₁ β₃ γ₀ γ₁ γ₃ : ℤ) (v : Fin Tag.D4.rank → ℤ) :
    parE (β₀ + γ₀) (β₁ + γ₁) (β₃ + γ₃) v ↔ (parE β₀ β₁ β₃ v ↔ parE γ₀ γ₁ γ₃ v) := by
  unfold parE
  have e : (β₀ + γ₀) * v 0 + (β₁ + γ₁) * v 1 + (β₃ + γ₃) * v 3 =
      (β₀ * v 0 + β₁ * v 1 + β₃ * v 3) + (γ₀ * v 0 + γ₁ * v 1 + γ₃ * v 3) := by ring
  rw [e]
  generalize β₀ * v 0 + β₁ * v 1 + β₃ * v 3 = x
  generalize γ₀ * v 0 + γ₁ * v 1 + γ₃ * v 3 = y
  omega

end J2S

end CFSG.LocalAnalysis.GLTheoremA
