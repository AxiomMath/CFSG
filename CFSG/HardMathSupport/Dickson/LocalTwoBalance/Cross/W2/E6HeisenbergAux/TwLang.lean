module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityTw

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem lang_step_single_tw {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime]
    [CharP L ℓ] (f : ℕ) (hf : 1 ≤ f) {x g : ModGL TwistTag.E6.tag L}
    (hg : g ∈ adjointGroup TwistTag.E6.tag L) (a : Fin TwistTag.E6.tag.rank → Lˣ)
    (ha3 : ∀ i, a i ^ 3 = 1) (hga : g⁻¹ * x * g = rootDiagUnit TwistTag.E6.tag a)
    (hFix : twistHom TwistTag.E6 L (iterateFrobenius L ℓ f) x = x) :
    ∃ (w : WeylGroup TwistTag.E6.tag) (z : ModGL TwistTag.E6.tag L),
      z ∈ torusGroup TwistTag.E6.tag L ⊔ rootSpan TwistTag.E6.tag L (rootCharKernel a) ∧
      twistHom TwistTag.E6 L (iterateFrobenius L ℓ f) (g * z) =
        (g * z) * canonicalRep (coxeterSystem TwistTag.E6.tag) L w ∧
      (g * z)⁻¹ * x * (g * z) = rootDiagUnit TwistTag.E6.tag a ∧
      rootDiagUnit TwistTag.E6.tag a ∈ twistedTorusOf
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L w)
        (twistHom TwistTag.E6 L (iterateFrobenius L ℓ f)) := by
  classical
  have hn : ∀ s : Unit, (g⁻¹ * twistHom TwistTag.E6 L (iterateFrobenius L ℓ f) g) *
      twistHom TwistTag.E6 L (iterateFrobenius L ℓ f)
        (rootDiagUnit TwistTag.E6.tag ((fun _ : Unit => a) s)) *
      (g⁻¹ * twistHom TwistTag.E6 L (iterateFrobenius L ℓ f) g)⁻¹ =
        rootDiagUnit TwistTag.E6.tag ((fun _ : Unit => a) s) := by
    intro s
    show (g⁻¹ * twistHom TwistTag.E6 L (iterateFrobenius L ℓ f) g) *
      twistHom TwistTag.E6 L (iterateFrobenius L ℓ f) (rootDiagUnit TwistTag.E6.tag a) *
        (g⁻¹ * twistHom TwistTag.E6 L (iterateFrobenius L ℓ f) g)⁻¹ =
          rootDiagUnit TwistTag.E6.tag a
    rw [← hga, map_mul, map_mul, map_inv, hFix]
    group
  obtain ⟨w', z, hz, hlang⟩ := exists_lang_datum_of_plane_twisted ℓ TwistTag.E6 f hf
    (fun _ : Unit => a) hg hn
  have hzC := familyGroup_le_familyCentralizer (K := L) (fun _ : Unit => a) hz
  obtain ⟨hzG, hzcomm⟩ := mem_familyCentralizer.1 hzC
  have hzd : z⁻¹ * rootDiagUnit TwistTag.E6.tag a * z = rootDiagUnit TwistTag.E6.tag a := by
    have := hzcomm ()
    rw [mul_inv_eq_iff_eq_mul] at this
    calc z⁻¹ * rootDiagUnit TwistTag.E6.tag a * z
        = z⁻¹ * (rootDiagUnit TwistTag.E6.tag a * z) := by group
      _ = z⁻¹ * (z * rootDiagUnit TwistTag.E6.tag a) := by rw [this]
      _ = rootDiagUnit TwistTag.E6.tag a := by group
  have hu : twistHom TwistTag.E6 L (iterateFrobenius L ℓ f) (g * z) =
      (g * z) * canonicalRep (coxeterSystem TwistTag.E6.tag) L w' := inv_mul_eq_iff_eq_mul.1 hlang
  have ht : (g * z)⁻¹ * x * (g * z) = rootDiagUnit TwistTag.E6.tag a := by
    calc (g * z)⁻¹ * x * (g * z) = z⁻¹ * (g⁻¹ * x * g) * z := by group
      _ = rootDiagUnit TwistTag.E6.tag a := by rw [hga, hzd]
  refine ⟨w', z, ?_, hu, ht, ?_⟩
  · have hsub : rootSpan TwistTag.E6.tag L (familyKernel (fun _ : Unit => a)) ≤
        rootSpan TwistTag.E6.tag L (rootCharKernel a) :=
      biSup_mono fun β hβ => ⟨hβ.1, hβ.2 ()⟩
    exact sup_le_sup_left hsub _ hz
  · rw [mem_twistedTorusOf]
    refine ⟨rootDiagUnit_mem_torusGroup _, ?_⟩
    have hFd : twistHom TwistTag.E6 L (iterateFrobenius L ℓ f) (rootDiagUnit TwistTag.E6.tag a) =
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L w')⁻¹ * rootDiagUnit TwistTag.E6.tag a *
          canonicalRep (coxeterSystem TwistTag.E6.tag) L w' := by
      rw [← ht, map_mul, map_mul, map_inv, hFix, hu]
      group
    rw [hFd]
    group

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis
