module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.Perm
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ThetaSCore

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Quasithin CFSG.Open
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

variable {G : Type} [Group G] [Finite G] {S M : Subgroup G} {r : ℕ}

theorem theta_S_form (hA : Asc81bHyp M S) (hSM : S ≤ M) (hr : r = 3 ∨ 5 ≤ r)
    (θ : ↥M →* Perm (OmegaE r 4)) (hker : ∀ m : ↥M, θ m = 1 → (m : G) ∈ S)
    (hAlt : ∀ x ∈ alternatingGroup (OmegaE r 4), ∃ m : ↥M, θ m = x)
    (hW : ((thompsonJ S).subgroupOf M).map θ = Wr r 4) :
    ∀ s : ↥M, (s : G) ∈ S → ∃ σ₁ ∈ blockFix (Fin r), ∃ σ₂ ∈ CFSG.pCore 2 (Perm (Fin 4)),
      θ s = Perm.sumCongr σ₁ σ₂ := by
  intro s hs
  obtain ⟨hPN, hP2, hPnorm, -⟩ := theta_S_normal_pCore hA hSM θ hker hAlt hW (by omega)
  exact exists_sumCongr_of_normal_isPGroup (by omega) ((S.subgroupOf M).map θ) hP2
    (fun g hg => hPN hg) hPnorm (θ s) ⟨s, Subgroup.mem_subgroupOf.2 hs, rfl⟩

theorem exists_decomp (hA : Asc81bHyp M S) (hSM : S ≤ M) (hr : r = 3 ∨ 5 ≤ r)
    (θ : ↥M →* Perm (OmegaE r 4)) (hker : ∀ m : ↥M, θ m = 1 → (m : G) ∈ S)
    (hAlt : ∀ x ∈ alternatingGroup (OmegaE r 4), ∃ m : ↥M, θ m = x)
    (hW : ((thompsonJ S).subgroupOf M).map θ = Wr r 4) :
    ∀ s ∈ S, ∃ j ∈ thompsonJ S, ∃ δ : ↥M, (δ : G) ∈ S ∧
      (∀ p : Fin r × Bool, θ δ (Sum.inl p) = Sum.inl p) ∧ θ δ ∈ alternatingGroup (OmegaE r 4) ∧
      s = (δ : G) * j := by
  intro s hs
  have hsM : s ∈ M := hSM hs
  obtain ⟨σ₁, h1, σ₂, h2, hθs⟩ := theta_S_form hA hSM hr θ hker hAlt hW ⟨s, hsM⟩ hs
  have hw : embL r 4 σ₁ ∈ Wr r 4 := ⟨σ₁, h1, rfl⟩
  rw [← hW] at hw
  obtain ⟨j₀, hj₀, hθj⟩ := hw
  have hj₀J : (j₀ : G) ∈ thompsonJ S := Subgroup.mem_subgroupOf.1 hj₀
  have hj₀S : (j₀ : G) ∈ S := thompsonJ_le_self S hj₀J
  have hembL : embL r 4 σ₁ = Perm.sumCongr σ₁ 1 := rfl
  have hθδ : θ (⟨s, hsM⟩ * j₀⁻¹) = Perm.sumCongr 1 σ₂ := by
    rw [map_mul, map_inv, hθj, hθs, hembL, Perm.sumCongr_inv, Perm.sumCongr_mul]
    simp
  refine ⟨(j₀ : G), hj₀J, ⟨s, hsM⟩ * j₀⁻¹, ?_, ?_, ?_, ?_⟩
  · have : ((⟨s, hsM⟩ * j₀⁻¹ : ↥M) : G) = s * (j₀ : G)⁻¹ := rfl
    rw [this]
    exact S.mul_mem hs (S.inv_mem hj₀S)
  · intro p
    rw [hθδ]
    simp
  · rw [hθδ, mem_alternatingGroup, Perm.sign_sumCongr]
    have := mem_alternatingGroup_of_mem_pCore_perm_four h2
    rw [mem_alternatingGroup] at this
    simp [this]
  · show s = s * (j₀ : G)⁻¹ * (j₀ : G)
    group

omit [Finite G] in
theorem characteristic_commutator_subgroupOf {P E : Subgroup G} (hEP : E ≤ P)
    (hE : (E.subgroupOf P).Characteristic) : ((⁅E, P⁆).subgroupOf P).Characteristic := by
  have h : (⁅E, P⁆).subgroupOf P = ⁅E.subgroupOf P, (⊤ : Subgroup P)⁆ := by
    have hmap : ⁅E.subgroupOf P, (⊤ : Subgroup P)⁆.map P.subtype = ⁅E, P⁆ := by
      rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hEP,
        ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [← hmap, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
  rw [h]
  infer_instance

omit [Finite G] in
theorem mem_normalizer_of_char_commute {C : Subgroup G} (hA : Asc81bHyp M S) (hCS : C ≤ S)
    (hCne : C ≠ ⊥) (hCchar : (C.subgroupOf S).Characteristic) {g : G} (hgM : g ∈ M)
    (hgC : ∀ c ∈ C, g * c * g⁻¹ = c) : g ∈ Subgroup.normalizer (S : Set G) := by
  have hgN : g ∈ Subgroup.normalizer (C : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨fun hc => (hgC c hc).symm ▸ hc, fun h => ?_⟩
    have h1 := hgC _ h
    have h2 : g * c * g⁻¹ = c := by
      have := congrArg (fun x => g⁻¹ * x * g) h1
      simpa [mul_assoc] using this
    exact h2 ▸ h
  have hcgs : M ⊓ Subgroup.normalizer (C : Set G) ≤ cgsIn M S :=
    le_iSup_of_le C (le_iSup_of_le hCS (le_iSup_of_le hCne (le_iSup_of_le hCchar le_rfl)))
  rw [hA.cgs] at hcgs
  exact (hcgs ⟨hgM, hgN⟩).2

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure
