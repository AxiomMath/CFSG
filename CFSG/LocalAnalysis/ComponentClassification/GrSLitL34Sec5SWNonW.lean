module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWIsoD
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWIsoD1

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]


theorem wGroup_eq_of_not_stronglyIsolated {a x : G} {J S W : Subgroup G}
    (hset : L34Sec4Setting G a x J S) (hcent : ∀ s ∈ S, s * a = a * s)
    (hWB : ∀ B : Subgroup G, B ≤ S ⊓ withKernel J → IsAbelianTwoOfRank 3 B → wGroup B = W)
    {F : Subgroup G} (hFS : F ≤ S) (hF : IsEightGroup F)
    (hns : ∃ s ∈ S, s * s = 1 ∧ (∀ e ∈ F, s * e = e * s) ∧ s ∉ F) : wGroup F = W := by
  have hGW : GWTwoBalanced G :=
    gwTwoBalanced_of_locallyTwoBalanced solomonCommutingCoreInput hset.1.2.2.2.2.2.1
  obtain ⟨-, hU3, hL34, -, hSyl, -, -⟩ := id hset
  obtain ⟨ha2, -, -, hJa, hJc, -, -⟩ := hU3
  have hJper : ⁅J, J⁆ = J := UnbalancedCorr.commutator_eq_of_isPComponent hJa hJc
  have hT : IsSylowTwoIn (S ⊓ J) J := GrS4.isSylowTwoIn_inf hSyl
  have hS2 : IsPGroup 2 S := GrS4.isPGroup_of_isSylowTwoIn hSyl
  have key : ∀ n : ℕ, ∀ F : Subgroup G, F ≤ S → IsEightGroup F →
      (∃ s ∈ S, s * s = 1 ∧ (∀ e ∈ F, s * e = e * s) ∧ s ∉ F) →
      8 - Nat.card ↥(F ⊓ withKernel J) ≤ n → wGroup F = W := by
    intro n
    induction n with
    | zero =>
      intro F hFS hF _ hn
      have h1 : F ⊓ withKernel J = F := Subgroup.eq_of_le_of_card_ge inf_le_left (by
        rw [hF.2]
        omega)
      exact hWB F (le_inf hFS (h1 ▸ inf_le_right)) (hF.1.isAbelianTwoOfRank hF.2.ge)
    | succ n ih =>
      intro F hFS hF hns hn
      by_cases hle : F ≤ withKernel J
      · exact hWB F (le_inf hFS hle) (hF.1.isAbelianTwoOfRank hF.2.ge)
      have hEK : F ⊓ withKernel J ≤ F := inf_le_left
      by_cases hiso : ∀ s ∈ S ⊓ withKernel J, s * s = 1 → (∀ e ∈ F, s * e = e * s) → s ∈ F
      ·
        obtain ⟨haE, haK⟩ := mem_of_isolated hset hcent hFS hiso
        have hEC : 2 ≤ Nat.card ↥(F ⊓ coreActionKernel J) := by
          have hsub : zpowers a ≤ F ⊓ coreActionKernel J :=
            zpowers_le.mpr (mem_inf.mpr ⟨haE, haK⟩)
          have := Subgroup.card_le_of_le hsub
          rw [Nat.card_zpowers, ha2] at this
          exact this
        have hECK : Nat.card ↥(F ⊓ coreActionKernel J) ≤ Nat.card ↥(F ⊓ withKernel J) :=
          Subgroup.card_le_of_le (inf_le_inf_left _ le_sup_right)
        by_cases h2 : Nat.card ↥(F ⊓ withKernel J) ≤ 2
        · exfalso
          have hZ : S ⊓ zStarIn J ≠ ⊥ := fun hZ =>
            absurd (two_lt_card_of_zOne hset hcent hFS hiso hZ) (by omega)
          obtain ⟨s, hsS, hss, hsc, hsn⟩ := l34WCriterionD1Fact_of_certs G J S hJper hL34 hT hS2
            hSyl.1 hZ F hFS hF (by omega) hEC
          exact hsn (hiso s hsS hss hsc)
        have h4 : Nat.card ↥(F ⊓ withKernel J) = 4 := by
          have hdvd : Nat.card ↥(F ⊓ withKernel J) ∣ 8 := by
            have := Subgroup.card_dvd_of_le hEK
            rwa [hF.2] at this
          have hne : Nat.card ↥(F ⊓ withKernel J) ≠ 8 := fun h8 => hle (by
            have := Subgroup.eq_of_le_of_card_ge hEK (by rw [h8, hF.2])
            exact this ▸ inf_le_right)
          obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
            (show Nat.card ↥(F ⊓ withKernel J) ∣ 2 ^ 3 by norm_num; exact hdvd)
          interval_cases k <;> simp only [Nat.reducePow] at hk' <;> omega
        obtain ⟨-, hnext⟩ := l34WCriterionDFact_of_certs G J S hJper hL34 hT hS2 hSyl.1 F hFS hF h4
          hEC hiso
        obtain ⟨s, hsS, hss, hsc, hsn⟩ := hns
        obtain ⟨s', hs'S, hs's, hs'c, hs'n⟩ := hnext s hsS hss hsc hsn
        set E₁ := F ⊓ withKernel J with hE₁
        have hE₁e : IsElemTwo E₁ := hF.1.mono hEK
        have hsE₁ : s ∉ E₁ := fun h => hsn (hEK h)
        obtain ⟨hE', hE'c⟩ := GrS4.isElemTwo_sup_zpowers hE₁e hss hsE₁
          (fun e he => (hsc e (hEK he)).symm)
        have hs'E₁ : s' ∉ E₁ := fun h => hs'n (mem_sup_left h)
        obtain ⟨hF', hF'c⟩ := GrS4.isElemTwo_sup_zpowers hE₁e hs's hs'E₁
          (fun e he => (hs'c e (mem_sup_left he)).symm)
        have hE'8 : 8 ≤ Nat.card ↥(E₁ ⊔ zpowers s) := by omega
        have hF'8 : 8 ≤ Nat.card ↥(E₁ ⊔ zpowers s') := by omega
        have hFS₁ : E₁ ⊔ zpowers s' ≤ S ⊓ withKernel J :=
          sup_le (le_inf (hEK.trans hFS) inf_le_right) (zpowers_le.mpr hs'S)
        have hEE' : ∀ u ∈ F, ∀ v ∈ E₁ ⊔ zpowers s, u * v = v * u := by
          intro u hu v hv
          have hle' : E₁ ⊔ zpowers s ≤ centralizer ({u} : Set G) := by
            refine sup_le (fun w hw => mem_centralizer_singleton_iff.mpr ?_) (zpowers_le.mpr ?_)
            · exact hF.1.1 w (hEK hw) u hu
            · exact mem_centralizer_singleton_iff.mpr (hsc u hu)
          exact (mem_centralizer_singleton_iff.mp (hle' hv)).symm
        have hE'F : ∀ u ∈ E₁ ⊔ zpowers s, ∀ v ∈ E₁ ⊔ zpowers s', u * v = v * u := by
          intro u hu v hv
          have hle' : E₁ ⊔ zpowers s' ≤ centralizer ({u} : Set G) := by
            refine sup_le (fun w hw => mem_centralizer_singleton_iff.mpr ?_) (zpowers_le.mpr ?_)
            · exact hE'.1 w (mem_sup_left hw) u hu
            · exact mem_centralizer_singleton_iff.mpr (hs'c u hu)
          exact (mem_centralizer_singleton_iff.mp (hle' hv)).symm
        rw [wGroup_eq_of_commute hGW (hF.1.isAbelianTwoOfRank hF.2.ge)
          (hE'.isAbelianTwoOfRank hE'8) hEE', wGroup_eq_of_commute hGW
          (hE'.isAbelianTwoOfRank hE'8) (hF'.isAbelianTwoOfRank hF'8) hE'F]
        exact hWB _ hFS₁ (hF'.isAbelianTwoOfRank hF'8)
      ·
        push Not at hiso
        obtain ⟨s, hsS, hss, hsF, hsn⟩ := hiso
        set F₁ : Subgroup G := F ⊓ withKernel J with hF₁def
        have hF₁K : F₁ ≤ withKernel J := inf_le_right
        have hF₁ : IsElemTwo F₁ := hF.1.mono hEK
        have hsF₁ : s ∉ F₁ := fun h => hsn (hEK h)
        obtain ⟨-, hA₀c⟩ := GrS4.isElemTwo_sup_zpowers hF₁ hss hsF₁
          (fun e he => (hsF e (hEK he)).symm)
        obtain ⟨hB, hBc⟩ := GrS4.isElemTwo_sup_zpowers hF.1 hss hsn (fun e he => (hsF e he).symm)
        have hF₁lt : Nat.card F₁ < 8 := by
          have h1 : Nat.card F₁ ≤ 8 := hF.2 ▸ Subgroup.card_le_of_le hEK
          refine lt_of_le_of_ne h1 fun h => hle ?_
          have h2 : F₁ = F := Subgroup.eq_of_le_of_card_ge hEK (by rw [h, hF.2])
          exact h2 ▸ hF₁K
        have hF₁4 := GrS4.card_le_four_of_lt_eight hF₁ hF₁lt
        have hpos : 0 < Nat.card F₁ := Nat.card_pos
        obtain ⟨F', h1, h2, h3, h4⟩ := GrS4.exists_eight_between 8 (A := F₁ ⊔ zpowers s)
          (B := F ⊔ zpowers s) (by omega) (sup_le_sup_right hEK _) hB (by omega)
          (by rw [hBc, hF.2]; omega)
        have hF'S : F' ≤ S := h2.trans (sup_le hFS (zpowers_le.mpr hsS.1))
        have hcard : Nat.card F₁ < Nat.card ↥(F' ⊓ withKernel J) := by
          have hc := Subgroup.card_le_of_le
            (le_inf h1 (sup_le hF₁K (zpowers_le.mpr hsS.2)) :
              F₁ ⊔ zpowers s ≤ F' ⊓ withKernel J)
          omega
        have hmeas : 8 - Nat.card ↥(F' ⊓ withKernel J) ≤ n := by omega
        have hFF' : ¬ F ≤ F' := fun hFF => by
          have heq : F = F' := Subgroup.eq_of_le_of_card_ge hFF (by rw [hF.2, h4])
          rw [← heq] at hcard
          exact absurd hcard (lt_irrefl _)
        have hns' : ∃ t ∈ S, t * t = 1 ∧ (∀ e ∈ F', t * e = e * t) ∧ t ∉ F' := by
          obtain ⟨t, htF, htF'⟩ : ∃ t ∈ F, t ∉ F' := by
            by_contra h
            push Not at h
            exact hFF' h
          exact ⟨t, hFS htF, hF.1.2 t htF,
            fun e he => hB.1 t ((le_sup_left : F ≤ F ⊔ zpowers s) htF) e (h2 he), htF'⟩
        rw [← ih F' hF'S ⟨h3, h4⟩ hns' hmeas]
        exact wGroup_eq_of_commute hGW (hF.1.isAbelianTwoOfRank hF.2.ge)
          (h3.isAbelianTwoOfRank h4.ge)
          (fun u hu v hv => hB.1 u ((le_sup_left : F ≤ F ⊔ zpowers s) hu) v (h2 hv))
  exact key 8 F hFS hF hns (by omega)

end CFSG.ComponentClassification.GrSLit.GrS5S
