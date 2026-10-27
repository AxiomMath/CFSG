module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairSpinGen
public import CFSG.ClassicalInvolution.ModelFacts.CF3A

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.ModelFacts.OrthAut
  CFSG.ClassicalInvolution.ModelFacts
open scoped MatrixGroups

section Main

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

theorem commutingGeneration_spin3 [Nontrivial V] (hodd : Odd (Nat.card F)) (hQ : Q.Nondegenerate)
    {m : ℕ} (F₀ : HypFrame Q m) (hm : 3 ≤ m)
    (hrest : ∀ v : V, (∀ k r, polar Q v (F₀.vec k r) = 0) → Q v = 0 → v = 0)
    (hperfK : Group.IsPerfect (spinGroup Q)) (hrange : (spinAction Q).range ≤ elementaryGroup Q)
    (𝓕 : Set (Subgroup (spinGroup Q)))
    (hframe : ∀ R ∈ 𝓕, ∃ fr : Frame Q, R.map (spinAction Q) = fr.La.range)
    (hlift : ∀ fr : Frame Q, ∃ R ∈ 𝓕, R.map (spinAction Q) = fr.La.range)
    (hG3 : ∀ R ∈ 𝓕, Gen3 R) (hk3 : ∀ x ∈ (spinAction Q).ker, x ^ 3 = 1 → x = 1) :
    CommutingGeneration 𝓕 := by
  classical
  have h2 : (2 : F) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have : Invertible (2 : F) := invertibleOfNonzero h2
  have hker : (spinAction Q).ker ≤ Subgroup.center (spinGroup Q) := ker_spinAction_le_center Q
  intro R₁ hR₁ R₂ hR₂ c₁ hc₁ c₂ hc₂ hz₁ hz₂ hx₂₁ hx₁₂
  set Big : Subgroup (spinGroup Q) := ⨆ R ∈ 𝓕, ⨆ (_ : R ≤ Subgroup.centralizer ({c₁} : Set _) ∨
    R ≤ Subgroup.centralizer ({c₂} : Set _) ∨ R ≤ Subgroup.centralizer ({c₁ * c₂} : Set _)), R
    with hBig
  have hmemBig : ∀ R ∈ 𝓕, (R ≤ Subgroup.centralizer ({c₁} : Set _) ∨
      R ≤ Subgroup.centralizer ({c₂} : Set _) ∨ R ≤ Subgroup.centralizer ({c₁ * c₂} : Set _)) →
      R ≤ Big := fun R hR hc => le_iSup₂_of_le R hR (le_iSup_of_le hc le_rfl)
  have hcentBig : ∀ (c : spinGroup Q), (c = c₁ ∨ c = c₂ ∨ c = c₁ * c₂) → ∀ fr : Frame Q,
      (∀ A : SL(2, F), spinAction Q c * fr.La A = fr.La A * spinAction Q c) →
      fr.La.range ≤ Big.map (spinAction Q) := by
    intro c hc fr hfr
    obtain ⟨R, hR, hRfr⟩ := hlift fr
    have hRc : R ≤ Subgroup.centralizer ({c} : Set _) := by
      have hmem : c ∈ Subgroup.centralizer (R : Set (spinGroup Q)) :=
        mem_centralizer_of_map_gen3 (spinAction Q) hker hk3 (hG3 R hR) (by
          rw [Subgroup.mem_centralizer_iff]
          intro t ht
          rw [hRfr] at ht
          obtain ⟨A, rfl⟩ := ht
          exact (hfr A).symm)
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hmem y hy)
    have hRBig : R ≤ Big := by
      rcases hc with rfl | rfl | rfl
      · exact hmemBig R hR (Or.inl hRc)
      · exact hmemBig R hR (Or.inr (Or.inl hRc))
      · exact hmemBig R hR (Or.inr (Or.inr hRc))
    rw [← hRfr]
    exact Subgroup.map_mono hRBig
  have hcentral : ∀ c : spinGroup Q, (c = c₁ ∨ c = c₂ ∨ c = c₁ * c₂) → spinAction Q c = 1 →
      (⊤ : Subgroup (spinGroup Q)) ≤ Big := fun c hc hθ => by
    have := eq_top_of_frames_all h2 F₀ (by omega) hrest hperfK hrange Big fun fr =>
      hcentBig c hc fr fun B => by rw [hθ, one_mul, mul_one]
    rw [this]
  by_cases hθ₁ : spinAction Q c₁ = 1
  · exact hcentral c₁ (Or.inl rfl) hθ₁
  by_cases hθ₂ : spinAction Q c₂ = 1
  · exact hcentral c₂ (Or.inr (Or.inl rfl)) hθ₂
  by_cases hθ₁₂ : spinAction Q (c₁ * c₂) = 1
  · exact hcentral (c₁ * c₂) (Or.inr (Or.inr rfl)) hθ₁₂
  obtain ⟨fr₁, hfr₁⟩ := hframe R₁ hR₁
  obtain ⟨fr₂, hfr₂⟩ := hframe R₂ hR₂
  have hi₁ : spinAction Q c₁ = fr₁.La (-1) :=
    (map_central_eq_one_or_neg_one _ R₁ fr₁ hfr₁ hc₁ hz₁).resolve_left hθ₁
  have hi₂ : spinAction Q c₂ = fr₂.La (-1) :=
    (map_central_eq_one_or_neg_one _ R₂ fr₂ hfr₂ hc₂ hz₂).resolve_left hθ₂
  have hne : fr₂.La (-1) ≠ fr₁.La (-1) := fun h => hθ₁₂ (by
    rw [map_mul, hi₁, hi₂, h, ← map_mul, neg_mul_neg, one_mul, map_one])
  have hc : fr₂.La (-1) * fr₁.La (-1) = fr₁.La (-1) * fr₂.La (-1) := by
    rw [← hi₁, ← hi₂, ← map_mul, ← map_mul, hx₂₁ c₁ hc₁]
  have hcent : ∀ A : SL(2, F), fr₂.La (-1) * fr₁.La A = fr₁.La A * fr₂.La (-1) := by
    intro A
    obtain ⟨r, hr, hrA⟩ : fr₁.La A ∈ R₁.map (spinAction Q) := hfr₁ ▸ ⟨A, rfl⟩
    rw [← hi₂, ← hrA, ← map_mul, ← map_mul, hx₂₁ r hr]
  have horth : ∀ X Y, polar Q (fr₁.incl X) (fr₂.incl Y) = 0 :=
    (Frame.orth_or_eq h2 hc hcent).resolve_right hne
  have hm4 : 4 ≤ m := by
    by_contra hlt
    obtain rfl : m = 3 := by omega
    exact false_of_four_pairs F₀ hrest _ (frames_pairs_pairwise_orth horth)
  let a₀ : Fin m := ⟨0, by omega⟩
  let a₁ : Fin m := ⟨1, by omega⟩
  let a₂ : Fin m := ⟨2, by omega⟩
  let a₃ : Fin m := ⟨3, by omega⟩
  have h01 : a₀ ≠ a₁ := fun h => by simpa [a₀, a₁] using congrArg Fin.val h
  have h23 : a₂ ≠ a₃ := fun h => by simpa [a₂, a₃] using congrArg Fin.val h
  have h02 : a₀ ≠ a₂ := fun h => by simpa [a₀, a₂] using congrArg Fin.val h
  have h03 : a₀ ≠ a₃ := fun h => by simpa [a₀, a₃] using congrArg Fin.val h
  have h12 : a₁ ≠ a₂ := fun h => by simpa [a₁, a₂] using congrArg Fin.val h
  have h13 : a₁ ≠ a₃ := fun h => by simpa [a₁, a₃] using congrArg Fin.val h
  obtain ⟨x, hx₁, hx₂⟩ := exists_spin_conj_orth_pair hodd hQ (F₀.toFrame h01 true true)
    (F₀.toFrame h23 true true) fr₁ fr₂
    (polar_incl_toFrame_of_disjoint F₀ h01 h23 h02 h03 h12 h13 true true true true) horth
  have hθxO : spinAction Q x ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (map_spinAction Q x)
  have hfin := eq_top_of_frames_pairs h2 F₀ h01 h23 h02 h03 h12 h13 hrest hperfK hrange Big x
    fun fr hfr A => by
      have hconj : ∀ (T L : V ≃ₗ[F] V), T * L = L * T →
          (spinAction Q x * T * (spinAction Q x)⁻¹) * (spinAction Q x * L * (spinAction Q x)⁻¹) =
            (spinAction Q x * L * (spinAction Q x)⁻¹) * (spinAction Q x * T * (spinAction Q x)⁻¹) :=
        by
        intro T L h
        calc (spinAction Q x * T * (spinAction Q x)⁻¹) * (spinAction Q x * L * (spinAction Q x)⁻¹)
            = spinAction Q x * (T * L) * (spinAction Q x)⁻¹ := by group
          _ = spinAction Q x * (L * T) * (spinAction Q x)⁻¹ := by rw [h]
          _ = (spinAction Q x * L * (spinAction Q x)⁻¹) *
              (spinAction Q x * T * (spinAction Q x)⁻¹) := by group
      have hmapLa : ∀ B : SL(2, F),
          (fr.map hθxO).La B = spinAction Q x * fr.La B * (spinAction Q x)⁻¹ :=
        fun B => Frame.map_La fr hθxO B
      rw [← hmapLa A]
      rcases hfr with hT | hT | hT
      · exact hcentBig c₁ (Or.inl rfl) _ (fun B => by
          rw [hi₁, ← hx₁, hmapLa B]
          exact hconj _ _ (hT B)) ⟨A, rfl⟩
      · exact hcentBig c₂ (Or.inr (Or.inl rfl)) _ (fun B => by
          rw [hi₂, ← hx₂, hmapLa B]
          exact hconj _ _ (hT B)) ⟨A, rfl⟩
      · refine hcentBig (c₁ * c₂) (Or.inr (Or.inr rfl)) _ (fun B => ?_) ⟨A, rfl⟩
        have : spinAction Q (c₁ * c₂) = spinAction Q x * ((F₀.toFrame h01 true true).La (-1) *
            (F₀.toFrame h23 true true).La (-1)) * (spinAction Q x)⁻¹ := by
          rw [map_mul, hi₁, hi₂, ← hx₁, ← hx₂]
          group
        rw [this, hmapLa B]
        exact hconj _ _ (hT B)
  rw [hfin]

end Main

end CFSG.ClassicalInvolution.Balance.Bootstrap
