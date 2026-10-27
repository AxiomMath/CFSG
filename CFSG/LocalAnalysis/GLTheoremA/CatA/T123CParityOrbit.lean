module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CParityLift
public import CFSG.Quasithin.H13.NQTermRadicalLocalization

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T123C

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barAut_mk glaPComponent_uniqueAux)

variable {G : Type} [Group G] [Finite G]

theorem exists_twoSubgroup_of_pComponent_orbit {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X K T E : Subgroup G} (hK : GLAPComponent p X K) (hTK : T ≤ K) (hT : T ≠ ⊥)
    (hT2 : IsPGroup 2 T) (hE : IsElemAbelian p E) (hEX : E ≤ Subgroup.normalizer (X : Set G))
    (hET : E ⊓ Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (T : Set G)) :
    ∃ T' : Subgroup G, T' ≤ X ∧ T' ≠ ⊥ ∧ IsPGroup 2 T' ∧
      E ≤ Subgroup.normalizer (T' : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKe : ∀ e ∈ E, GLAPComponent p X (GLBConj e K) := fun e he => by
    have h := glaPComponent_gLBConj hK e
    rwa [mem_normalizer_iff_gLBConj_eq.1 (hEX he)] at h
  set f : ↥E → Subgroup (↥X ⧸ GLAPPrimeCore p ↥X) :=
    fun e => barX p X (GLBConj (e : G) T) with hf
  have hf2 : ∀ e : ↥E, IsPGroup 2 (f e) := fun e =>
    (IsPGroup.comap_subtype (K := X) (hT2.map (MulAut.conj (e : G)⁻¹).toMonoidHom)).map
      (QuotientGroup.mk' (GLAPPrimeCore p ↥X))
  have hfK : ∀ e : ↥E, f e ≤ barX p X (GLBConj (e : G) K) := by
    rintro e _ ⟨w, hw, rfl⟩
    exact ⟨w, Subgroup.mem_subgroupOf.2
      (GLTheoremB.gLBConj_mono _ hTK (Subgroup.mem_subgroupOf.1 hw)), rfl⟩
  have hc : ∀ e₁ e₂ : ↥E, f e₁ ≠ f e₂ → ⁅f e₁, f e₂⁆ = ⊥ := by
    intro e₁ e₂ hne
    have hKK : GLBConj (e₁ : G) K ≠ GLBConj (e₂ : G) K := by
      intro hKK
      apply hne
      have hd : (e₁ : G) * (e₂ : G)⁻¹ ∈ E ⊓ Subgroup.normalizer (K : Set G) := by
        refine Subgroup.mem_inf.2 ⟨E.mul_mem e₁.2 (E.inv_mem e₂.2), ?_⟩
        rw [mem_normalizer_iff_gLBConj_eq, ← gLBConj_gLBConj, hKK, gLBConj_gLBConj,
          mul_inv_cancel, gLBConj_one]
      have hTd := mem_normalizer_iff_gLBConj_eq.1 (hET hd)
      have hTT : GLBConj (e₁ : G) T = GLBConj (e₂ : G) T := by
        rw [show (e₁ : G) = (e₁ : G) * (e₂ : G)⁻¹ * (e₂ : G) by group, ← gLBConj_gLBConj, hTd]
      simp only [hf, hTT]
    have hbar : barX p X (GLBConj (e₁ : G) K) ≠ barX p X (GLBConj (e₂ : G) K) := fun h =>
      hKK (glaPComponent_uniqueAux (hKe _ e₁.2) (hKe _ e₂.2) h)
    have hcomm : ⁅barX p X (GLBConj (e₁ : G) K), barX p X (GLBConj (e₂ : G) K)⁆ = ⊥ :=
      CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _
        (hKe _ e₁.2).2.2.1 (hKe _ e₂.2).2.2.1 hbar
    exact eq_bot_iff.2 ((Subgroup.commutator_mono (hfK e₁) (hfK e₂)).trans hcomm.le)
  set Mbar : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X) := ⨆ e, f e
  have hM2 : IsPGroup 2 Mbar :=
    CFSG.Quasithin.H13.NQTerm.isPGroup_iSup_of_eq_or_commute f hf2 hc
  set M : Subgroup G := (Mbar.comap (QuotientGroup.mk' (GLAPPrimeCore p ↥X))).map X.subtype
    with hM
  have hMX : M ≤ X := Subgroup.map_subtype_le _
  have hEM : E ≤ Subgroup.normalizer (M : Set G) := by
    refine le_normalizer_of_conj_mem fun e he m hm => ?_
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hm
    set γ : ↥(Subgroup.normalizer (X : Set G)) := ⟨e, hEX he⟩
    have hinv : Mbar ≤ Mbar.comap (barAut p X γ).toMonoidHom := by
      refine iSup_le fun e' z hz => ?_
      obtain ⟨w, hw, rfl⟩ := hz
      have hw' : (e' : G) * w * (e' : G)⁻¹ ∈ T := mem_gLBConj.1 (Subgroup.mem_subgroupOf.1 hw)
      refine Subgroup.mem_comap.2
        (le_iSup f ⟨(e' : G) * e⁻¹, E.mul_mem e'.2 (E.inv_mem he)⟩ ?_)
      refine ⟨X.normalizerMonoidHom γ w, Subgroup.mem_subgroupOf.2 (mem_gLBConj.2 ?_), ?_⟩
      · rw [chev_coe_normalizerMonoidHom]
        have key : (e' : G) * e⁻¹ * (e * (w : G) * e⁻¹) * ((e' : G) * e⁻¹)⁻¹ ∈ T := by
          rw [show (e' : G) * e⁻¹ * (e * (w : G) * e⁻¹) * ((e' : G) * e⁻¹)⁻¹ =
            (e' : G) * w * (e' : G)⁻¹ by group]
          exact hw'
        exact key
      · exact (barAut_mk p X γ w).symm
    refine Subgroup.mem_map.2 ⟨X.normalizerMonoidHom γ x, ?_, rfl⟩
    have h : barAut p X γ (QuotientGroup.mk x) ∈ Mbar := hinv (Subgroup.mem_comap.1 hx)
    rw [barAut_mk] at h
    exact h
  have hTM : T ≤ M := by
    intro t ht
    have htX : t ∈ X := hK.1 (hTK ht)
    refine Subgroup.mem_map.2 ⟨⟨t, htX⟩, ?_, rfl⟩
    refine Subgroup.mem_comap.2 (le_iSup f 1 ?_)
    refine ⟨⟨t, htX⟩, Subgroup.mem_subgroupOf.2 ?_, rfl⟩
    show t ∈ GLBConj 1 T
    rw [gLBConj_one]
    exact ht
  have hM2' : 2 ∣ Nat.card M :=
    (S8.L89.two_dvd_card_of_two hT2 hT).trans (Subgroup.card_dvd_of_le hTM)
  have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥X)) := by
    unfold GLAPPrimeCore
    exact CFSG.pPrimeCore_coprime_card
  have hMp : ¬ p ∣ Nat.card M := by
    rw [hM, Subgroup.card_map_of_injective X.subtype_injective]
    exact not_dvd_card_comap_of_isPGroup_two hp hp2 _
      (by rw [QuotientGroup.ker_mk']; exact hcop) hM2
  obtain ⟨T', hT'M, hT'1, hT'2, hET'⟩ :=
    CFSG.StandardType.ggExists_invariant_two_subgroup hE hEM hMp hM2'
  exact ⟨T', hT'M.trans hMX, hT'1, hT'2, hET'⟩

end CFSG.LocalAnalysis.GLTheoremA.T123C

end
