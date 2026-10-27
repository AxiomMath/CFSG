module

public import CFSG.ClassicalInvolution.Asc77.AscT7TZStar
public import CFSG.ClassicalInvolution.Asc77.AscT7TFix
public import CFSG.ClassicalInvolution.Asc77.AscT7G2Swap

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7T

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' : Subgroup G} {z : G}

theorem twin_sq (hs : Hyp23Setting p f Ω K K' z) {x : G} (hx : x * z * x⁻¹ = z) :
    conjSub (x * x) K = K := by
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have hKx : conjSub x K = K ∨ conjSub x K = K' := by
    have hmem : conjSub x K ∈ twinSet Ω K :=
      ⟨hΩ.conjInvariant x K hK, z, hz, by simpa [hx] using hz.conj x⟩
    rw [hs.twinSet_eq] at hmem
    exact hmem
  have hK'x : conjSub x K' = K ∨ conjSub x K' = K' := by
    have hmem : conjSub x K' ∈ twinSet Ω K :=
      ⟨hΩ.conjInvariant x K' hs.hK'.1, z, hz, by simpa [hx] using hz'.conj x⟩
    rw [hs.twinSet_eq] at hmem
    exact hmem
  rw [conjSub_mul]
  rcases hKx with h | h
  · rw [h, h]
  · rw [h]
    rcases hK'x with h' | h'
    · exact h'
    · exfalso
      exact hs.hne (conjSub_injective x (h.trans h'.symm)).symm


theorem c25_5_proved : C25_5 p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp A hzA hAS hAnorm hZ
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hz : IsUniqueInvolution K z := hs.hz
  have hz2 : z * z = 1 := hz.sq
  have hz1 : z ≠ 1 := hz.ne_one
  obtain ⟨t', ht'S, ht'2, ⟨g, hg⟩, ht'R, hnf⟩ := T7G2.exists_swap_nonfused hyp
  have hRS : R ≤ (S : Subgroup G) := hyp.hR.2.2
  have hRne : R ≠ R' := T7ER.ne_of_hyp25 hyp
  have hzt' : z ≠ t' := by
    intro h
    apply hRne
    have h1 : conjSub t' R = R := by
      rw [← h]
      exact T7F2.conjSub_eq_of_centralizes fun r hr => hyp.hzS r (hRS hr)
    rw [← ht'R, h1]
  have hyp' : Hyp25 p f Ω K K' W S R R' z t' u₁ u₂ := { hyp with ht := ⟨ht'S, hzt'.symm, g, hg⟩ }
  have hnosq : ∀ b ∈ A ⊓ Subgroup.centralizer ({t'} : Set G), b * b ≠ z := by
    intro b hb hbb
    have hbt : b * t' = t' * b := Subgroup.mem_centralizer_singleton_iff.mp hb.2
    have hx : (g⁻¹ * b * g) * z * (g⁻¹ * b * g)⁻¹ = z := by
      calc (g⁻¹ * b * g) * z * (g⁻¹ * b * g)⁻¹ = g⁻¹ * b * (g * z * g⁻¹) * b⁻¹ * g := by group
        _ = g⁻¹ * b * t' * b⁻¹ * g := by rw [hg]
        _ = g⁻¹ * (b * t' * b⁻¹) * g := by group
        _ = g⁻¹ * t' * g := by rw [hbt]; group
        _ = z := by rw [← hg]; group
    have h1 := twin_sq hs hx
    have h2 : conjSub (b * b) (conjSub g K) = conjSub g K := by
      calc conjSub (b * b) (conjSub g K) = conjSub ((b * b) * g) K := (conjSub_mul (b * b) g K).symm
        _ = conjSub (g * ((g⁻¹ * b * g) * (g⁻¹ * b * g))) K := by congr 1; group
        _ = conjSub g (conjSub ((g⁻¹ * b * g) * (g⁻¹ * b * g)) K) := by rw [conjSub_mul]
        _ = conjSub g K := by rw [h1]
    rw [hbb] at h2
    exact T7G2.not_normalizes_of_nonfused hyp hg hzt' hnf h2
  have hinv : ∀ c ∈ A ⊓ Subgroup.centralizer ({t'} : Set G), c * c = 1 → c ≠ 1 → c ≠ z → False := by
    intro c hc hc2 hc1 hcz
    have hcA : c ∈ A := hc.1
    have hcz' : c * z = z * c := hyp.hzS c (hAS hcA)
    have h4 := T7A.isElemAbelian2_closure_pair hc2 hz2 hc1 hz1 hcz hcz'
    have hle : Subgroup.closure ({c, z} : Set G) ≤ A := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact hcA
      · exact hzA
    have hlet : Subgroup.closure ({c, z} : Set G) ≤ Subgroup.centralizer ({t'} : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact hc.2
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hyp.hzS t' ht'S).symm
    obtain ⟨a, hacl, ha1, haz⟩ := c25_3_proved (p := p) (f := f) G Ω K K' W S R R' z t' u₁ u₂
      hyp' _ h4 (Subgroup.subset_closure (by simp)) fun a ha =>
        Subgroup.mem_centralizer_singleton_iff.mp (hlet ha)
    exact haz (hZ a (hle hacl) ha1)
  have hB2 : IsPGroup 2 ↥(A ⊓ Subgroup.centralizer ({t'} : Set G)) :=
    S.isPGroup'.to_le (inf_le_left.trans hAS)
  have hBz := eq_one_or_eq_of_isPGroup hB2 hnosq hinv
  by_contra hne
  have hbig : ∃ a ∈ A, a ≠ 1 ∧ a ≠ z := by
    by_contra hall
    push Not at hall
    apply hne
    apply le_antisymm
    · intro a ha
      by_cases h1 : a = 1
      · rw [h1]; exact one_mem _
      · rw [hall a ha h1]; exact Subgroup.mem_zpowers z
    · exact Subgroup.zpowers_le.mpr hzA
  have ht'inv : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht'2
  have htA : ∀ a ∈ A, t' * a * t'⁻¹ ∈ A := fun a ha => by
    have := conj_mem_conjSub (n := t') ha
    rwa [hAnorm t' ht'S] at this
  have htz : t' * z * t'⁻¹ = z := by
    rw [hyp.hzS t' ht'S]; group
  have hfix : ∀ a ∈ A, t' * a * t'⁻¹ = a → a = 1 ∨ a = z := fun a ha h => by
    refine hBz a ⟨ha, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : t' * a = a * t' := by
      calc t' * a = (t' * a * t'⁻¹) * t' := by group
        _ = a * t' := by rw [h]
    exact h1.symm
  obtain ⟨a, haA, ha1, haz, hcon⟩ := exists_conj_eq_mul_of_isPGroup (S.isPGroup'.to_le hAS) hzA
    hz2 hz1 (fun a ha => (hyp.hzS a (hAS ha)).symm) ht'2 htA htz hfix hbig
  apply hnf
  refine ⟨a⁻¹ * g, ?_⟩
  have h1 : t' * a = a * z * t' := by
    calc t' * a = (t' * a * t'⁻¹) * t' := by group
      _ = a * z * t' := by rw [hcon]
  calc a⁻¹ * g * z * (a⁻¹ * g)⁻¹ = a⁻¹ * (g * z * g⁻¹) * a := by group
    _ = a⁻¹ * t' * a := by rw [hg]
    _ = a⁻¹ * (t' * a) := by group
    _ = a⁻¹ * (a * z * t') := by rw [h1]
    _ = z * t' := by group
    _ = t' * z := (hyp.hzS t' ht'S).symm

end T7T

end CFSG.ClassicalInvolution.Asc77
