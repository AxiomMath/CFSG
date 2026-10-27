module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SELin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEComb
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEMod1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SESim

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem sec9e_hlift {hQ : Q.Nondegenerate} (F : Subgroup (ProjSim Q))
    (hF : ∀ f ∈ F, f ≠ 1 → (SimInOmegaStar hQ f ∧ SimHasDim f 4) ∨ SimHasDim f 3) :
    ∀ f ∈ F, f ≠ 1 → ∃ t : OGroup Q, t * t = 1 ∧ phiSim Q t = f ∧ 2 ≤ invDim t ∧
      invDim t ≤ 4 := by
  intro f hf hne
  rcases hF f hf hne with ⟨-, t, htt, ht4, htf⟩ | ⟨t, htt, ht3, htf⟩
  · exact ⟨t, htt, htf, by omega, by omega⟩
  · exact ⟨t, htt, htf, by omega, by omega⟩

theorem sec9e_invDim_even (hQ : Q.Nondegenerate) (h6 : Module.finrank (ZMod 3) V = 6)
    (F : Subgroup (ProjSim Q)) (hF16 : Nat.card F = 2 ^ 4)
    (hlift : ∀ f ∈ F, f ≠ 1 → ∃ t : OGroup Q, t * t = 1 ∧ phiSim Q t = f ∧ 2 ≤ invDim t ∧
      invDim t ≤ 4) :
    ∀ g ∈ F.comap (phiSim Q), Even (invDim g) := by
  classical
  let Ft : Subgroup (OGroup Q) := F.comap (phiSim Q)
  let E := ↥Ft
  have hlift' : ∀ f ∈ F, f ≠ 1 → ∃ t : OGroup Q, t * t = 1 ∧ phiSim Q t = f := by
    intro f hf hne
    obtain ⟨t, htt, htf, -, -⟩ := hlift f hf hne
    exact ⟨t, htt, htf⟩
  haveI : Finite V := Module.finite_of_finite (ZMod 3)
  haveI : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
      (fun e₁ e₂ h => LinearEquiv.ext (congrFun h))
  haveI : Finite (OGroup Q) :=
    Finite.of_injective (fun g : OGroup Q => (g : V ≃ₗ[ZMod 3] V)) Subtype.val_injective
  haveI : Finite E := Finite.of_injective (Subtype.val : E → OGroup Q) Subtype.val_injective
  haveI : Fintype E := Fintype.ofFinite E
  let ρ : E →* (V ≃ₗ[ZMod 3] V) :=
    (Subgroup.subtype (TauCeti.QuadraticMap.orthogonalGroup Q)).comp (Subgroup.subtype Ft)
  have hρ : Function.Injective ρ :=
    (Subgroup.subtype_injective _).comp (Subgroup.subtype_injective _)
  have hE : ∀ g : E, g * g = 1 := by
    intro g
    apply Subtype.ext
    exact sec9e_comap_sq F hlift' (g : OGroup Q) g.2
  obtain ⟨A, hAinj, hAmul, hAcard⟩ := sec9e_exists_subsets ρ hρ hE
  have hAcard' : ∀ g : E, (A g).card = invDim (g : OGroup Q) := by
    intro g
    rw [hAcard g]
    rfl
  have hcardE : Nat.card E = 2 ^ 5 := by
    have hc : Nat.card (F.comap (phiSim Q)) = Nat.card F * 2 :=
      sec9e_card_comap (by rw [h6]; norm_num) F hlift'
    change Nat.card (F.comap (phiSim Q)) = 2 ^ 5
    rw [hc, hF16]
    norm_num
  let 𝒜 : Finset (Finset (Fin (Module.finrank (ZMod 3) V))) := Finset.univ.image A
  have hcard : 𝒜.card = 2 ^ (Module.finrank (ZMod 3) V - 1) := by
    have hcardA : 𝒜.card = 2 ^ 5 := by
      change (Finset.univ.image A).card = 2 ^ 5
      rw [Finset.card_image_of_injective _ hAinj, Finset.card_univ,
        Fintype.card_eq_nat_card, hcardE]
    rw [hcardA]
    have h5 : Module.finrank (ZMod 3) V - 1 = 5 := by omega
    rw [h5]
  have hA1 : A (1 : E) = ∅ := by
    have h := hAmul 1 1
    simpa [mul_one, symmDiff_self, Finset.bot_eq_empty] using h
  have h0 : (∅ : Finset (Fin (Module.finrank (ZMod 3) V))) ∈ 𝒜 :=
    Finset.mem_image.mpr ⟨1, Finset.mem_univ 1, hA1⟩
  have hΔ : ∀ B ∈ 𝒜, ∀ C ∈ 𝒜, symmDiff B C ∈ 𝒜 := by
    intro B hB C hC
    obtain ⟨g, -, hg⟩ := Finset.mem_image.mp hB
    obtain ⟨h, -, hh⟩ := Finset.mem_image.mp hC
    refine Finset.mem_image.mpr ⟨g * h, Finset.mem_univ _, ?_⟩
    rw [← hg, ← hh]
    exact hAmul g h
  have hs : ∀ i : Fin (Module.finrank (ZMod 3) V),
      ({i} : Finset (Fin (Module.finrank (ZMod 3) V))) ∉ 𝒜 := by
    intro i hi
    obtain ⟨g, -, hg⟩ := Finset.mem_image.mp hi
    have hcard1 : (A g).card = 1 := by rw [hg, Finset.card_singleton]
    have hdim : invDim (g : OGroup Q) = 1 := by rw [← hAcard' g, hcard1]
    have hg1 : (g : OGroup Q) = 1 := by
      by_contra hc
      exact sec9e_comap_invDim_ne_one hQ h6 F hlift (g : OGroup Q) g.2 hc hdim
    have hAg : A g = ∅ := by
      have hge : g = 1 := Subtype.ext hg1
      rw [hge, hA1]
    have hmem : i ∈ ({i} : Finset (Fin (Module.finrank (ZMod 3) V))) :=
      Finset.mem_singleton_self i
    rw [← hg, hAg] at hmem
    exact Finset.notMem_empty i hmem
  intro g hg
  have hmem : A ⟨g, hg⟩ ∈ 𝒜 :=
    Finset.mem_image.mpr ⟨⟨g, hg⟩, Finset.mem_univ _, rfl⟩
  have heven : Even (A ⟨g, hg⟩).card :=
    sec9e_even_of_no_singleton (n := Module.finrank (ZMod 3) V) (by omega) 𝒜 hcard h0 hΔ hs
      (A ⟨g, hg⟩) hmem
  rw [hAcard' ⟨g, hg⟩] at heven
  simpa using heven

theorem asc82E16Model : Asc82E16Model := by
  intro V _ _ _ Q hQ h6 _ F hF16 hF f hf
  by_cases hf1 : f = 1
  · subst hf1
    exact ⟨1, (omegaProj hQ).one_mem, map_one _⟩
  · rcases hF f hf hf1 with ⟨hΩ, -⟩ | ⟨t, htt, ht3, htf⟩
    · exact hΩ
    · have hmem : t ∈ F.comap (phiSim Q) := by
        rw [Subgroup.mem_comap]
        change projOrthToProjSim Q (toProj Q t) ∈ F
        rw [htf]
        exact hf
      obtain ⟨k, hk⟩ := sec9e_invDim_even hQ h6 F hF16.2 (sec9e_hlift F hF) t hmem
      omega

end CFSG.OddStandard.SmallF3.Omega
