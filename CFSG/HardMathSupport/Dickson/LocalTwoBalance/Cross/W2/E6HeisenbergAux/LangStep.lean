module

public import CFSG.HardMathSupport.Timmesfeld.Torality.LangAssembly

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem lang_step_single {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ]
    (f : ℕ) (hf : 1 ≤ f) (hpq : Nat.Coprime 3 (ℓ ^ f)) {x g : ModGL Tag.E6 L}
    (hg : g ∈ adjointGroup Tag.E6 L) (a : Fin Tag.E6.rank → Lˣ) (ha3 : ∀ i, a i ^ 3 = 1)
    (hga : g⁻¹ * x * g = rootDiagUnit Tag.E6 a)
    (hFix : entrywiseFrobGL Tag.E6 L ℓ f x = x) :
    ∃ (w : WeylGroup Tag.E6) (z : ModGL Tag.E6 L),
      z ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (rootCharKernel a) ∧
      entrywiseFrobGL Tag.E6 L ℓ f (g * z) = (g * z) * canonicalRep (coxeterSystem Tag.E6) L w ∧
      (g * z)⁻¹ * x * (g * z) = rootDiagUnit Tag.E6 a ∧
      rootDiagUnit Tag.E6 a ∈ twistedTorusOf (canonicalRep (coxeterSystem Tag.E6) L w)
        (entrywiseFrobGL Tag.E6 L ℓ f) := by
  classical
  have hn : ∀ s : Unit, (g⁻¹ * entrywiseFrobGL Tag.E6 L ℓ f g) *
      entrywiseFrobGL Tag.E6 L ℓ f (rootDiagUnit Tag.E6 ((fun _ : Unit => a) s)) *
      (g⁻¹ * entrywiseFrobGL Tag.E6 L ℓ f g)⁻¹ = rootDiagUnit Tag.E6 ((fun _ : Unit => a) s) := by
    intro s
    show (g⁻¹ * entrywiseFrobGL Tag.E6 L ℓ f g) * entrywiseFrobGL Tag.E6 L ℓ f
      (rootDiagUnit Tag.E6 a) * (g⁻¹ * entrywiseFrobGL Tag.E6 L ℓ f g)⁻¹ = rootDiagUnit Tag.E6 a
    rw [← hga, map_mul, map_mul, map_inv, hFix]
    group
  obtain ⟨w', z, hz, hlang⟩ := exists_lang_datum_of_plane ℓ f hf hpq (fun _ : Unit => a)
    (fun _ i => ha3 i) hg hn
  have hzC := familyGroup_le_familyCentralizer (K := L) (fun _ : Unit => a) hz
  obtain ⟨hzG, hzcomm⟩ := mem_familyCentralizer.1 hzC
  have hzd : z⁻¹ * rootDiagUnit Tag.E6 a * z = rootDiagUnit Tag.E6 a := by
    have := hzcomm ()
    rw [mul_inv_eq_iff_eq_mul] at this
    calc z⁻¹ * rootDiagUnit Tag.E6 a * z = z⁻¹ * (rootDiagUnit Tag.E6 a * z) := by group
      _ = z⁻¹ * (z * rootDiagUnit Tag.E6 a) := by rw [this]
      _ = rootDiagUnit Tag.E6 a := by group
  have hu : entrywiseFrobGL Tag.E6 L ℓ f (g * z) =
      (g * z) * canonicalRep (coxeterSystem Tag.E6) L w' := inv_mul_eq_iff_eq_mul.1 hlang
  have ht : (g * z)⁻¹ * x * (g * z) = rootDiagUnit Tag.E6 a := by
    calc (g * z)⁻¹ * x * (g * z) = z⁻¹ * (g⁻¹ * x * g) * z := by group
      _ = rootDiagUnit Tag.E6 a := by rw [hga, hzd]
  refine ⟨w', z, ?_, hu, ht, ?_⟩
  · have hsub : rootSpan Tag.E6 L (familyKernel (fun _ : Unit => a)) ≤
        rootSpan Tag.E6 L (rootCharKernel a) :=
      biSup_mono fun β hβ => ⟨hβ.1, hβ.2 ()⟩
    exact sup_le_sup_left hsub _ hz
  · rw [mem_twistedTorusOf]
    refine ⟨rootDiagUnit_mem_torusGroup _, ?_⟩
    have hFd : entrywiseFrobGL Tag.E6 L ℓ f (rootDiagUnit Tag.E6 a) =
        (canonicalRep (coxeterSystem Tag.E6) L w')⁻¹ * rootDiagUnit Tag.E6 a *
          canonicalRep (coxeterSystem Tag.E6) L w' := by
      rw [← ht, map_mul, map_mul, map_inv, hFix, hu]
      group
    rw [hFd]
    group

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis
