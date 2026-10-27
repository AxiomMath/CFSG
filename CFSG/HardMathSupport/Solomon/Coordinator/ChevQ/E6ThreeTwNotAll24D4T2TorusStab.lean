module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityTw

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Stab

set_option linter.unusedSectionVars false


theorem d4t2ts_stable_torus {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime]
    [CharP L ℓ] (f : ℕ) (hf : 1 ≤ f) {Φ : ModGL TwistTag.E6.tag L →* ModGL TwistTag.E6.tag L}
    (hΦ : Φ = twistHom TwistTag.E6 L (iterateFrobenius L ℓ f))
    {a : Fin TwistTag.E6.tag.rank → Lˣ} {n g₀ : ModGL TwistTag.E6.tag L}
    (hg₀ : g₀ ∈ adjointGroup TwistTag.E6.tag L) (hlang : Φ g₀ = g₀ * n)
    {F₀ : Subgroup (ModGL TwistTag.E6.tag L)} (hfix : ∀ x ∈ F₀, n * Φ x * n⁻¹ = x)
    (hdF : rootDiagUnit TwistTag.E6.tag a ∈ F₀) {g₁ : ModGL TwistTag.E6.tag L}
    (hg₁ : g₁ ∈ toralCentralizer TwistTag.E6.tag L a)
    (hT : ∀ x ∈ F₀, g₁⁻¹ * x * g₁ ∈ torusGroup TwistTag.E6.tag L) :
    ∃ (y : ModGL TwistTag.E6.tag L) (w : WeylGroup TwistTag.E6.tag),
      y ∈ toralCentralizer TwistTag.E6.tag L a ∧
      n * Φ y = y * canonicalRep (coxeterSystem TwistTag.E6.tag) L w ∧
      ∀ x ∈ F₀, y⁻¹ * x * y ∈ torusGroup TwistTag.E6.tag L := by
  classical
  have hfam : ∀ s : F₀, ∃ b : Fin TwistTag.E6.tag.rank → Lˣ,
      g₁⁻¹ * (s : ModGL TwistTag.E6.tag L) * g₁ = rootDiagUnit TwistTag.E6.tag b :=
    fun s => exists_rootDiagUnit_eq_of_mem_torusGroup (hT s s.2)
  choose b hb using hfam
  have hg₁A : g₁ ∈ adjointGroup TwistTag.E6.tag L := (mem_toralCentralizer.1 hg₁).1
  have hgA : g₀ * g₁ ∈ adjointGroup TwistTag.E6.tag L := mul_mem hg₀ hg₁A
  have hcoc : (g₀ * g₁)⁻¹ * Φ (g₀ * g₁) = g₁⁻¹ * n * Φ g₁ := by
    rw [map_mul, hlang]
    group
  have hn : ∀ s : F₀, ((g₀ * g₁)⁻¹ * Φ (g₀ * g₁)) * Φ (rootDiagUnit TwistTag.E6.tag (b s)) *
      ((g₀ * g₁)⁻¹ * Φ (g₀ * g₁))⁻¹ = rootDiagUnit TwistTag.E6.tag (b s) := by
    intro s
    rw [← hb s, hcoc, map_mul, map_mul, map_inv]
    have h := hfix s s.2
    calc g₁⁻¹ * n * Φ g₁ * ((Φ g₁)⁻¹ * Φ s * Φ g₁) * (g₁⁻¹ * n * Φ g₁)⁻¹
        = g₁⁻¹ * (n * Φ s * n⁻¹) * g₁ := by group
      _ = g₁⁻¹ * s * g₁ := by rw [h]
  have hn' := hn
  rw [hΦ] at hn'
  obtain ⟨w', z, hz, hlang'⟩ := exists_lang_datum_of_plane_twisted ℓ TwistTag.E6 f hf b hgA hn'
  rw [← hΦ] at hlang'
  have hzC := familyGroup_le_familyCentralizer (K := L) b hz
  obtain ⟨-, hzcomm⟩ := mem_familyCentralizer.1 hzC
  have hzd : ∀ s : F₀, z⁻¹ * rootDiagUnit TwistTag.E6.tag (b s) * z =
      rootDiagUnit TwistTag.E6.tag (b s) := by
    intro s
    have h := hzcomm s
    rw [mul_inv_eq_iff_eq_mul] at h
    calc z⁻¹ * rootDiagUnit TwistTag.E6.tag (b s) * z
        = z⁻¹ * (rootDiagUnit TwistTag.E6.tag (b s) * z) := by group
      _ = z⁻¹ * (z * rootDiagUnit TwistTag.E6.tag (b s)) := by rw [h]
      _ = rootDiagUnit TwistTag.E6.tag (b s) := by group
  have hdfix : g₁⁻¹ * rootDiagUnit TwistTag.E6.tag a * g₁ = rootDiagUnit TwistTag.E6.tag a := by
    have hc : rootDiagUnit TwistTag.E6.tag a * g₁ = g₁ * rootDiagUnit TwistTag.E6.tag a :=
      mul_inv_eq_iff_eq_mul.1 (mem_toralCentralizer.1 hg₁).2
    calc g₁⁻¹ * rootDiagUnit TwistTag.E6.tag a * g₁
        = g₁⁻¹ * (rootDiagUnit TwistTag.E6.tag a * g₁) := by group
      _ = g₁⁻¹ * (g₁ * rootDiagUnit TwistTag.E6.tag a) := by rw [hc]
      _ = rootDiagUnit TwistTag.E6.tag a := by group
  have hba : b ⟨rootDiagUnit TwistTag.E6.tag a, hdF⟩ = a :=
    CFSG.LieType.Chevalley.rootDiagUnit_injective ((hb ⟨_, hdF⟩).symm.trans hdfix)
  have hzM : z ∈ toralRootGroup TwistTag.E6.tag L a := by
    have hsub : rootSpan TwistTag.E6.tag L (familyKernel b) ≤
        rootSpan TwistTag.E6.tag L (rootCharKernel a) :=
      rootSpan_mono fun α hα => ⟨hα.1, by simpa [hba] using hα.2 ⟨_, hdF⟩⟩
    exact sup_le_sup_left hsub _ hz
  refine ⟨g₁ * z, w', mul_mem hg₁ (toralRootGroup_le a hzM), ?_, ?_⟩
  · have h1 : (g₀ * g₁ * z)⁻¹ * Φ (g₀ * g₁ * z) = (g₁ * z)⁻¹ * (n * Φ (g₁ * z)) := by
      rw [map_mul, map_mul, map_mul, hlang]
      group
    rw [h1] at hlang'
    exact inv_mul_eq_iff_eq_mul.1 hlang'
  · intro x hx
    have hbx : g₁⁻¹ * x * g₁ = rootDiagUnit TwistTag.E6.tag (b ⟨x, hx⟩) := hb ⟨x, hx⟩
    have h : (g₁ * z)⁻¹ * x * (g₁ * z) = rootDiagUnit TwistTag.E6.tag (b ⟨x, hx⟩) := by
      calc (g₁ * z)⁻¹ * x * (g₁ * z) = z⁻¹ * (g₁⁻¹ * x * g₁) * z := by group
        _ = z⁻¹ * rootDiagUnit TwistTag.E6.tag (b ⟨x, hx⟩) * z := by rw [hbx]
        _ = rootDiagUnit TwistTag.E6.tag (b ⟨x, hx⟩) := hzd _
    rw [h]
    exact rootDiagUnit_mem_torusGroup _

theorem d4t2ts_stable_torus_E6 {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime]
    [CharP L ℓ] (f : ℕ) (hf : 1 ≤ f) {Φ : ModGL Tag.E6 L →* ModGL Tag.E6 L}
    (hΦ : Φ = twistHom TwistTag.E6 L (iterateFrobenius L ℓ f))
    {a : Fin Tag.E6.rank → Lˣ} {n g₀ : ModGL Tag.E6 L}
    (hg₀ : g₀ ∈ adjointGroup Tag.E6 L) (hlang : Φ g₀ = g₀ * n)
    {F₀ : Subgroup (ModGL Tag.E6 L)} (hfix : ∀ x ∈ F₀, n * Φ x * n⁻¹ = x)
    (hdF : rootDiagUnit Tag.E6 a ∈ F₀) {g₁ : ModGL Tag.E6 L}
    (hg₁ : g₁ ∈ toralCentralizer Tag.E6 L a)
    (hT : ∀ x ∈ F₀, g₁⁻¹ * x * g₁ ∈ torusGroup Tag.E6 L) :
    ∃ (y : ModGL Tag.E6 L) (w : WeylGroup Tag.E6),
      y ∈ toralCentralizer Tag.E6 L a ∧
      n * Φ y = y * canonicalRep (coxeterSystem Tag.E6) L w ∧
      ∀ x ∈ F₀, y⁻¹ * x * y ∈ torusGroup Tag.E6 L :=
  d4t2ts_stable_torus f hf hΦ hg₀ hlang hfix hdF hg₁ hT

end Stab

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
