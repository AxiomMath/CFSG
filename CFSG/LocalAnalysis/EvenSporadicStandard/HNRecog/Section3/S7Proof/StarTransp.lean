module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.StarModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.StarAlt

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem s7_sym8_transposition {G : Type} [Group G] {S A : Subgroup G} (hAS : A ≤ S)
    (ψ : ↥S ≃* Sym 8) (hA : Nat.card ↥A = 20160) {c : G} (hc : c ∈ S) (hc2 : c ^ 2 = 1)
    (hcA : c ∉ A) (h720 : Nat.card ↥(A ⊓ Gx c) = 720) : (ψ ⟨c, hc⟩).cycleType = {2} := by
  obtain ⟨φ₀, hφ₀⟩ := s7_alt_equiv hAS ψ hA
  let ρ : Sym 8 →* G := S.subtype.comp ψ.symm.toMonoidHom
  let σ : Sym 8 := ψ ⟨c, hc⟩
  have hρ_inj : Function.Injective ρ := by
    intro x y hxy
    have h1 : (ψ.symm x : ↥S) = ψ.symm y := Subtype.ext hxy
    exact ψ.symm.injective h1
  have hρσ : ρ σ = c := by
    show ((ψ.symm (ψ ⟨c, hc⟩) : ↥S) : G) = c
    rw [MulEquiv.symm_apply_apply]
  have hρ_eq_φ : ∀ s : alternatingGroup (Fin 8), ρ (s : Sym 8) = ((φ₀ s : ↥A) : G) := by
    intro s
    rw [hφ₀ s]
    rfl
  have hc2S : (⟨c, hc⟩ : ↥S) ^ 2 = 1 := by
    apply Subtype.ext
    simp [hc2]
  have hσ2 : σ ^ 2 = 1 := by
    change (ψ ⟨c, hc⟩) ^ 2 = 1
    rw [← map_pow, hc2S, map_one]
  have hsign : Equiv.Perm.sign σ = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · exfalso
      have hsalt : σ ∈ alternatingGroup (Fin 8) := Equiv.Perm.mem_alternatingGroup.2 h
      have hval : ((φ₀ ⟨σ, hsalt⟩ : ↥A) : G) = c := by
        rw [hφ₀]
        have hsval : ((⟨σ, hsalt⟩ : alternatingGroup (Fin 8)) : Sym 8) = ψ ⟨c, hc⟩ := by
          change σ = ψ ⟨c, hc⟩
          rfl
        rw [hsval, MulEquiv.symm_apply_apply]
      have hmem : c ∈ A := by
        rw [← hval]
        exact (φ₀ ⟨σ, hsalt⟩).2
      exact hcA hmem
    · exact h
  have hcard : Nat.card ↥(alternatingGroup (Fin 8) ⊓
      Subgroup.centralizer ({σ} : Set (Sym 8))) = 720 := by
    have hmap : (alternatingGroup (Fin 8) ⊓
        Subgroup.centralizer ({σ} : Set (Sym 8))).map ρ = A ⊓ Gx c := by
      ext g
      constructor
      · intro hg
        rw [Subgroup.mem_map] at hg
        obtain ⟨s, hs, rfl⟩ := hg
        rw [Subgroup.mem_inf] at hs
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · have h : ρ s = ((φ₀ ⟨s, hs.1⟩ : ↥A) : G) := hρ_eq_φ ⟨s, hs.1⟩
          rw [h]
          exact (φ₀ ⟨s, hs.1⟩).2
        · rw [mem_Gx]
          have hsσ : s * σ = σ * s := by
            have h1 := (Subgroup.mem_centralizer_iff.mp hs.2) σ (Set.mem_singleton σ)
            exact h1.symm
          have hmul : ρ s * ρ σ = ρ σ * ρ s := by
            simpa only [map_mul] using congrArg ρ hsσ
          rw [hρσ] at hmul
          exact hmul.symm
      · intro hg
        rw [Subgroup.mem_inf] at hg
        let s : alternatingGroup (Fin 8) := φ₀.symm ⟨g, hg.1⟩
        have hρs : ρ (s : Sym 8) = g := by
          rw [hρ_eq_φ s]
          show ((φ₀ (φ₀.symm ⟨g, hg.1⟩) : ↥A) : G) = g
          rw [MulEquiv.apply_symm_apply]
        refine Subgroup.mem_map.2 ⟨(s : Sym 8), ?_, hρs⟩
        rw [Subgroup.mem_inf]
        refine ⟨s.2, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        apply hρ_inj
        simp only [map_mul, hρs, hρσ]
        exact mem_Gx.mp hg.2
    calc Nat.card ↥(alternatingGroup (Fin 8) ⊓
            Subgroup.centralizer ({σ} : Set (Sym 8)))
        = Nat.card ↥((alternatingGroup (Fin 8) ⊓
            Subgroup.centralizer ({σ} : Set (Sym 8))).map ρ) :=
          Nat.card_congr (Subgroup.equivMapOfInjective (alternatingGroup (Fin 8) ⊓
            Subgroup.centralizer ({σ} : Set (Sym 8))) ρ hρ_inj).toEquiv
      _ = Nat.card ↥(A ⊓ Gx c) := by rw [hmap]
      _ = 720 := h720
  exact s7_sym8_cycleType_of_card hσ2 hsign hcard

end CFSG.EvenSporadicStandard.HNRecog.Section3
