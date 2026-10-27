module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Frames
public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Norm

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley

section Orbits

theorem rootChar_single_td4 {K : Type} [Field K] (a : Fin d4.rank → Kˣ) (i : Fin d4.rank) :
    rootChar a (Pi.single i 1) = a i := by
  have := rootChar_nsmul_single a i 1
  rw [one_smul, pow_one] at this
  exact this

theorem td4Orb_single_two : td4Orb (Pi.single (nd 2) 1) = {Pi.single (nd 2) 1} := by
  simp [td4Orb, rho_single, rhoPerm_two]

theorem td4Orb_neg_single_two : td4Orb (-Pi.single (nd 2) 1) = {-Pi.single (nd 2) 1} := by
  simp [td4Orb, rho_neg_single, rhoPerm_two]

theorem td4Orb_single_zero : td4Orb (Pi.single (nd 0) 1) =
    {Pi.single (nd 0) 1, Pi.single (nd 1) 1, Pi.single (nd 3) 1} := by
  simp only [td4Orb, rho_single, rhoPerm_zero, rhoPerm_one]

theorem td4Orb_neg_single_zero : td4Orb (-Pi.single (nd 0) 1) =
    {-Pi.single (nd 0) 1, -Pi.single (nd 1) 1, -Pi.single (nd 3) 1} := by
  simp only [td4Orb, rho_neg_single, rhoPerm_zero, rhoPerm_one]

end Orbits

section Nodes

variable {K : Type} [Field K]

theorem mem_normalizer_nodeGroup_long (σ : K →+* K) (hσ : ∀ c, σ (σ (σ c)) = c)
    (hK : (-1 : Kˣ) ≠ 1) {g : ModGL d4 K} (hg : g ∈ graphFixedRootGroup TwistTag.D4 K σ)
    (hga : g ∈ Subgroup.centralizer ({rootDiagUnit d4 (aLongTD4 K)} : Set (ModGL d4 K))) :
    g ∈ Subgroup.normalizer (nodeGroupTD4 σ (Pi.single (nd 2) 1) : Set (ModGL d4 K)) := by
  let σK : K ≃+* K := RingEquiv.ofBijective σ ⟨σ.injective, fun x => ⟨σ (σ x), hσ x⟩⟩
  have hσK : σK.toRingHom = σ := RingHom.ext fun _ => rfl
  have hW : ∀ w : WeylGroup d4, weylTwist TwistTag.D4 w = w →
      (∀ v, rootChar (aLongTD4 K) (w • v) = rootChar (aLongTD4 K) v) →
        w • Pi.single (nd 2) 1 ∈ td4Orb (Pi.single (nd 2) 1) ∨
          w • Pi.single (nd 2) 1 ∈ td4Orb (-Pi.single (nd 2) 1) := by
    intro w hwρ hwa
    have hroot : IsRoot d4 (w • Pi.single (nd 2) 1) := IsRoot.smul (isRoot_single d4 (nd 2)) w
    have hchar : rootChar (aLongTD4 K) (w • Pi.single (nd 2) 1) = 1 := by
      rw [hwa, rootChar_single_td4]
      rfl
    have hpar := (rootChar_aLong_eq_one_iff hK _).1 hchar
    have hfix : rho (w • Pi.single (nd 2) 1) = w • Pi.single (nd 2) 1 := by
      rw [← smul_rho_td4 hwρ, rho_single, rhoPerm_two]
    rcases long_rho_fixed _ (mem_rootFinset.2 hroot) hpar hfix with h | h
    · exact Or.inl (by rw [h]; exact self_mem_td4Orb _)
    · exact Or.inr (by rw [h]; exact self_mem_td4Orb _)
  have hc : ∀ α ∈ psiTD4 (aLongTD4 K), ∀ β ∈ psiTD4 (aLongTD4 K), IsRoot d4 (α + β) →
      α + β ∈ psiTD4 (aLongTD4 K) := by
    intro α hα β hβ hr
    exact absurd (mem_rootFinset.2 hr) (long_closed α (mem_rootFinset.2 hα.2.1) β
      (mem_rootFinset.2 hβ.2.1) ((rootChar_aLong_eq_one_iff hK α).1 hα.1.2)
      ((rootChar_aLong_eq_one_iff hK β).1 hβ.1.2) hα.2.2 hβ.2.2)
  have hr : ∀ α ∈ psiTD4 (aLongTD4 K), rho α ∈ psiTD4 (aLongTD4 K) := by
    intro α hα
    obtain ⟨h1, h2, h3⟩ := long_rho_stable α (mem_rootFinset.2 hα.2.1)
      ((rootChar_aLong_eq_one_iff hK α).1 hα.1.2) hα.2.2
    exact ⟨⟨mem_rootFinset.1 h1, (rootChar_aLong_eq_one_iff hK _).2 h2⟩,
      ⟨mem_rootFinset.1 h1, h3⟩⟩
  have hn : ∀ γ ∈ psiTD4 (aLongTD4 K), γ ∉ td4Orb (Pi.single (nd 2) 1) →
      ∀ δ ∈ td4Orb (Pi.single (nd 2) 1) ∪ td4Orb (-Pi.single (nd 2) 1),
        γ ≠ δ ∧ γ ≠ -δ ∧ ¬IsRoot d4 (γ + δ) := by
    intro γ hγ hγo δ hδ
    have hne : γ ≠ Pi.single (nd 2) 1 := fun h => hγo (h ▸ self_mem_td4Orb _)
    obtain ⟨h1, h2, h3⟩ := long_commute γ (mem_rootFinset.2 hγ.2.1)
      ((rootChar_aLong_eq_one_iff hK γ).1 hγ.1.2) hγ.2.2 hne
    rw [td4Orb_single_two, td4Orb_neg_single_two] at hδ
    rcases hδ with h | h
    · rw [Set.mem_singleton_iff] at h
      subst h
      exact ⟨hne, h1, fun hr => h2 (mem_rootFinset.2 hr)⟩
    · rw [Set.mem_singleton_iff] at h
      subst h
      exact ⟨h1, by rw [neg_neg]; exact hne, fun hr => h3 (mem_rootFinset.2 hr)⟩
  have := mem_normalizer_nodeGroup_of_centralizes σK (aLongTD4 K) (isRoot_single d4 (nd 2)) hW hc
    hr hn (by rw [hσK]; exact hg) hga
  rwa [hσK] at this

theorem mem_normalizer_nodeGroup_short (σ : K →+* K) (hσ : ∀ c, σ (σ (σ c)) = c)
    (hK : (-1 : Kˣ) ≠ 1) {g : ModGL d4 K} (hg : g ∈ graphFixedRootGroup TwistTag.D4 K σ)
    (hga : g ∈ Subgroup.centralizer ({rootDiagUnit d4 (aShortTD4 K)} : Set (ModGL d4 K))) :
    g ∈ Subgroup.normalizer (nodeGroupTD4 σ (Pi.single (nd 0) 1) : Set (ModGL d4 K)) := by
  let σK : K ≃+* K := RingEquiv.ofBijective σ ⟨σ.injective, fun x => ⟨σ (σ x), hσ x⟩⟩
  have hσK : σK.toRingHom = σ := RingHom.ext fun _ => rfl
  have hW : ∀ w : WeylGroup d4, weylTwist TwistTag.D4 w = w →
      (∀ v, rootChar (aShortTD4 K) (w • v) = rootChar (aShortTD4 K) v) →
        w • Pi.single (nd 0) 1 ∈ td4Orb (Pi.single (nd 0) 1) ∨
          w • Pi.single (nd 0) 1 ∈ td4Orb (-Pi.single (nd 0) 1) := by
    intro w hwρ hwa
    have hroot : IsRoot d4 (w • Pi.single (nd 0) 1) := IsRoot.smul (isRoot_single d4 (nd 0)) w
    have hchar : rootChar (aShortTD4 K) (w • Pi.single (nd 0) 1) = 1 := by
      rw [hwa, rootChar_single_td4]
      rfl
    have hpar := (rootChar_aShort_eq_one_iff hK _).1 hchar
    have hne : rho (w • Pi.single (nd 0) 1) ≠ w • Pi.single (nd 0) 1 := by
      intro h
      rw [← smul_rho_td4 hwρ, rho_single, rhoPerm_zero] at h
      have h2 := congrFun (MulAction.injective w h) (nd 1)
      rw [Pi.single_eq_same, Pi.single_eq_of_ne (show nd 1 ≠ nd 0 by decide)] at h2
      exact one_ne_zero h2
    rcases short_rho_ne _ (mem_rootFinset.2 hroot) hpar hne with h | h | h | h | h | h
    · exact Or.inl (by rw [h]; exact self_mem_td4Orb _)
    · exact Or.inl (by rw [h, td4Orb_single_zero]; simp)
    · exact Or.inl (by rw [h, td4Orb_single_zero]; simp)
    · exact Or.inr (by rw [h]; exact self_mem_td4Orb _)
    · exact Or.inr (by rw [h, td4Orb_neg_single_zero]; simp)
    · exact Or.inr (by rw [h, td4Orb_neg_single_zero]; simp)
  have hc : ∀ α ∈ psiTD4 (aShortTD4 K), ∀ β ∈ psiTD4 (aShortTD4 K), IsRoot d4 (α + β) →
      α + β ∈ psiTD4 (aShortTD4 K) := by
    intro α hα β hβ hr
    exact absurd (mem_rootFinset.2 hr) (short_closed α (mem_rootFinset.2 hα.2.1) β
      (mem_rootFinset.2 hβ.2.1) ((rootChar_aShort_eq_one_iff hK α).1 hα.1.2)
      ((rootChar_aShort_eq_one_iff hK β).1 hβ.1.2) hα.2.2 hβ.2.2)
  have hr : ∀ α ∈ psiTD4 (aShortTD4 K), rho α ∈ psiTD4 (aShortTD4 K) := by
    intro α hα
    obtain ⟨h1, h2, h3⟩ := short_rho_stable α (mem_rootFinset.2 hα.2.1)
      ((rootChar_aShort_eq_one_iff hK α).1 hα.1.2) hα.2.2
    exact ⟨⟨mem_rootFinset.1 h1, (rootChar_aShort_eq_one_iff hK _).2 h2⟩,
      ⟨mem_rootFinset.1 h1, h3⟩⟩
  have hn : ∀ γ ∈ psiTD4 (aShortTD4 K), γ ∉ td4Orb (Pi.single (nd 0) 1) →
      ∀ δ ∈ td4Orb (Pi.single (nd 0) 1) ∪ td4Orb (-Pi.single (nd 0) 1),
        γ ≠ δ ∧ γ ≠ -δ ∧ ¬IsRoot d4 (γ + δ) := by
    intro γ hγ hγo δ hδ
    rw [td4Orb_single_zero] at hγo
    have h0 : γ ≠ Pi.single (nd 0) 1 := fun h => hγo (by simp [h])
    have h1 : γ ≠ Pi.single (nd 1) 1 := fun h => hγo (by simp [h])
    have h3 : γ ≠ Pi.single (nd 3) 1 := fun h => hγo (by simp [h])
    obtain ⟨⟨a0, b0, c0⟩, ⟨a1, b1, c1⟩, ⟨a3, b3, c3⟩⟩ := short_commute γ
      (mem_rootFinset.2 hγ.2.1) ((rootChar_aShort_eq_one_iff hK γ).1 hγ.1.2) hγ.2.2 h0 h1 h3
    rw [td4Orb_single_zero, td4Orb_neg_single_zero] at hδ
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hδ
    rcases hδ with (h | h | h) | (h | h | h) <;> subst h
    · exact ⟨h0, a0, fun hr => b0 (mem_rootFinset.2 hr)⟩
    · exact ⟨h1, a1, fun hr => b1 (mem_rootFinset.2 hr)⟩
    · exact ⟨h3, a3, fun hr => b3 (mem_rootFinset.2 hr)⟩
    · exact ⟨a0, by rw [neg_neg]; exact h0, fun hr => c0 (mem_rootFinset.2 hr)⟩
    · exact ⟨a1, by rw [neg_neg]; exact h1, fun hr => c1 (mem_rootFinset.2 hr)⟩
    · exact ⟨a3, by rw [neg_neg]; exact h3, fun hr => c3 (mem_rootFinset.2 hr)⟩
  have := mem_normalizer_nodeGroup_of_centralizes σK (aShortTD4 K) (isRoot_single d4 (nd 0)) hW
    hc hr hn (by rw [hσK]; exact hg) hga
  rwa [hσK] at this

end Nodes

end CFSG.ClassicalInvolution.G2D4Models
