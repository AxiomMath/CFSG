module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ADefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMExcBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA

theorem uexc_induces_map {Ω Ω' : Type} [Group Ω] [Group Ω'] (π : Ω →* Ω') {S : Subgroup Ω}
    {R : Type} [Group R] {θ : ↥S ⧸ Subgroup.center ↥S ≃* R}
    {θ' : ↥(S.map π) ⧸ Subgroup.center ↥(S.map π) ≃* R}
    (hθ : ∀ s : ↥S, θ' (QuotientGroup.mk (π.subgroupMap S s)) = θ (QuotientGroup.mk s))
    {b : Ω} (hb : b ∈ Subgroup.normalizer (S : Set Ω)) {φ : MulAut R}
    (h : LargeEvenInduces θ (fun l l' : ↥S => (l' : Ω) = b⁻¹ * l * b) φ) :
    LargeEvenInduces θ' (fun l l' : ↥(S.map π) => (l' : Ω') = (π b)⁻¹ * l * π b) φ := by
  intro l l' hll'
  obtain ⟨s, rfl⟩ := π.subgroupMap_surjective S l
  have hs' : b⁻¹ * (s : Ω) * b ∈ S := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hb) (s : Ω)).1 s.2
    simpa using this
  have hl' : l' = π.subgroupMap S ⟨b⁻¹ * (s : Ω) * b, hs'⟩ := by
    apply Subtype.ext
    rw [hll']
    simp
  rw [hl', hθ s, hθ]
  exact h s ⟨b⁻¹ * (s : Ω) * b, hs'⟩ rfl

theorem uexc_splitInnerDiagMarking16_map {p : ℕ} {Ω Ω' : Type} [Group Ω] [Group Ω']
    (π : Ω →* Ω') {S B : Subgroup Ω} (hkc : π.ker ≤ Subgroup.centralizer (S : Set Ω))
    (h : SplitInnerDiagMarking16 p B S) :
    SplitInnerDiagMarking16 p (B.map π) (S.map π) := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := h
  refine ⟨?_, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw⟩
  · haveI : Group.IsPerfect ↥S := ⟨hperf⟩
    haveI : Group.IsPerfect ↥(S.map π) :=
      Group.IsPerfect.ofSurjective (f := π.subgroupMap S) (π.subgroupMap_surjective S)
    exact Group.IsPerfect.commutator_eq_top
  · rintro R _ I F ⟨hs, hna, θ, hsplit, hBN, hb⟩
    obtain ⟨θ', hθ'⟩ := uexc_theta_bar π hperf hkc θ
    refine ⟨hs, hna, θ', hsplit, (Subgroup.map_mono hBN).trans (Subgroup.le_normalizer_map π), ?_⟩
    intro b' hb'
    obtain ⟨b, hbB, rfl⟩ := Subgroup.mem_map.1 hb'
    obtain ⟨φ, hφI, hind⟩ := hb b hbB
    exact ⟨φ, hφI, uexc_induces_map π hθ' (hBN hbB) hind⟩

theorem uexc_uniMarking_map {p n d : ℕ} {F : Type} [Field F] [Finite F] {Ω Ω' : Type} [Group Ω]
    [Group Ω'] (π : Ω →* Ω') {S B : Subgroup Ω} (hperf : commutator ↥S = ⊤)
    (hkc : π.ker ≤ Subgroup.centralizer (S : Set Ω))
    {θ : ↥S ⧸ Subgroup.center ↥S ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n))}
    (h : UniMarking p S B n d F θ) :
    ∃ θ' : ↥(S.map π) ⧸ Subgroup.center ↥(S.map π) ≃*
        LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n)),
      UniMarking p (S.map π) (B.map π) n d F θ' := by
  obtain ⟨hF, hn1, hd3, hdn, hpq, hBN, hact⟩ := h
  obtain ⟨θ', hθ'⟩ := uexc_theta_bar π hperf hkc θ
  refine ⟨θ', hF, hn1, hd3, hdn, hpq, (Subgroup.map_mono hBN).trans
    (Subgroup.le_normalizer_map π), ?_⟩
  intro b' hb'
  obtain ⟨b, hbB, rfl⟩ := Subgroup.mem_map.1 hb'
  obtain ⟨φ, hφ, hind⟩ := hact b hbB
  exact ⟨φ, hφ, uexc_induces_map π hθ' (hBN hbB) hind⟩

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
