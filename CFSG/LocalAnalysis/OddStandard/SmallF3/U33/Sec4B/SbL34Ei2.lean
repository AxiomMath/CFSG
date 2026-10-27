module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Ei

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34E

private lemma card_subgroupOf_of_le {G : Type*} [Group G] {H L : Subgroup G} (h : H ≤ L) :
    Nat.card ↥(H.subgroupOf L) = Nat.card ↥H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

private lemma centralizer_inf_subgroupOf {G : Type*} [Group G] {L H : Subgroup G} {σ : G}
    (hσ : σ ∈ L) :
    Subgroup.centralizer ({⟨σ, hσ⟩} : Set ↥L) ⊓ H.subgroupOf L =
      (Subgroup.centralizer ({σ} : Set G) ⊓ H).subgroupOf L := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hx1, hx2⟩
    exact ⟨by simpa using congrArg (fun y : ↥L => (y : G)) hx1, hx2⟩
  · rintro ⟨hx1, hx2⟩
    exact ⟨by apply Subtype.ext; simpa using hx1, hx2⟩

theorem crit_of_surj {G : Type} [Group G] [Finite G] {Λ : Type} [Group Λ] [Finite Λ]
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Module.Finite (ZMod 2) E]
    (L K P W : Subgroup G) (hKP : K ≤ P) (hKW : K ≤ W) (hPL : P ≤ L) (hWL : W ≤ L)
    (π : ↥L →* Λ) (hπ : Function.Surjective π) (hker : π.ker = K.subgroupOf L)
    (ι : Λ →* (E ≃ₗ[ZMod 2] E)) (hι : Function.Injective ι)
    (hdim : Module.finrank (ZMod 2) E = 6) {ρ σ : G} (hρL : ρ ∈ L) (hσL : σ ∈ L)
    (hρ3 : ρ * ρ * ρ = 1) (hρP : ρ ∉ P) (hσ2 : σ * σ = 1) (hσρ : σ * ρ * σ⁻¹ = ρ⁻¹)
    (hPn : ∀ g ∈ L, ∀ p ∈ P, g * p * g⁻¹ ∈ P) (hcard : Nat.card L = 6 * Nat.card P)
    (hfpf : ∀ p ∈ P, ρ * p * ρ⁻¹ * p⁻¹ ∈ K → p ∈ K)
    (hW2 : IsPGroup 2 W) (hWi : ¬ 2 ∣ W.relIndex L) (hσW : σ ∈ W)
    (hD : Nat.card ↥(Subgroup.centralizer ({σ} : Set G) ⊓ W) = 2 ^ 7)
    (hDK : Nat.card ↥(Subgroup.centralizer ({σ} : Set G) ⊓ K) = 2 ^ 5)
    (hcentW : ∀ w ∈ W, σ * w * σ⁻¹ * w⁻¹ ∈ K →
      ∃ k ∈ K, ∃ d ∈ Subgroup.centralizer ({σ} : Set G) ⊓ W, w = k * d) :
    Crit ι ((P.subgroupOf L).map π) ((W.subgroupOf L).map π) (π ⟨ρ, hρL⟩) (π ⟨σ, hσL⟩) := by
  haveI : (P.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff hPL).mpr fun p g hp hg => hPn g hg p hp
  refine crit_of_surj_core (ρ := ⟨ρ, hρL⟩) (σ := ⟨σ, hσL⟩)
    π hπ (P.subgroupOf L) (W.subgroupOf L) ?_ ?_ ι hι hdim
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  ·
    rw [hker]
    exact Subgroup.subgroupOf_mono L hKP
  ·
    rw [hker]
    exact Subgroup.subgroupOf_mono L hKW
  ·
    apply Subtype.ext
    simpa using hρ3
  ·
    intro h
    exact hρP (Subgroup.mem_subgroupOf.mp h)
  ·
    apply Subtype.ext
    simpa using hσ2
  ·
    apply Subtype.ext
    simpa using hσρ
  ·
    rw [card_subgroupOf_of_le hPL]
    exact hcard
  ·
    intro p hp hmem
    rw [hker] at hmem ⊢
    rw [Subgroup.mem_subgroupOf] at hmem
    exact Subgroup.mem_subgroupOf.mpr
      (hfpf (p : G) (Subgroup.mem_subgroupOf.mp hp) (by simpa using hmem))
  ·
    exact hW2.of_equiv (Subgroup.subgroupOfEquivOfLe hWL).symm
  ·
    simpa only [Subgroup.relIndex] using hWi
  ·
    exact Subgroup.mem_subgroupOf.mpr hσW
  ·
    rw [centralizer_inf_subgroupOf hσL,
      card_subgroupOf_of_le (le_trans inf_le_right hWL)]
    exact hD
  ·
    rw [hker, centralizer_inf_subgroupOf hσL,
      card_subgroupOf_of_le (le_trans inf_le_right (le_trans hKP hPL))]
    exact hDK
  ·
    intro w hw hmem
    rw [hker] at hmem ⊢
    rw [Subgroup.mem_subgroupOf] at hmem
    obtain ⟨k, hk, d, hd, hwd⟩ :=
      hcentW (w : G) (Subgroup.mem_subgroupOf.mp hw) (by simpa using hmem)
    have hkL : k ∈ L := hPL (hKP hk)
    have hdL : d ∈ L := hWL hd.2
    refine ⟨⟨k, hkL⟩, Subgroup.mem_subgroupOf.mpr hk, ⟨d, hdL⟩, ?_, ?_⟩
    · refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_subgroupOf.mpr hd.2⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (by apply Subtype.ext
            simpa using (Subgroup.mem_centralizer_singleton_iff.mp hd.1))
    · apply Subtype.ext
      simpa using hwd

end CFSG.OddStandard.SmallF3.HarrisU33.L34E
