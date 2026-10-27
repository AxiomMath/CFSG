module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinAut
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporBasic
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdSporadic
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral

public section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open CFSG Subgroup RestrictedStd RestrictedStd.Spor

theorem fixSub_eq_fixedPoints {Y : Type} [Group Y] (α : MulAut Y) :
    Sporadic.Schreier.fixSub α = fixedPoints α := by
  ext y
  rfl

theorem hinFor_of_comps_simple {s : TauCeti.SporadicName}
    (hin : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ x y : G, x * y ≠ y * x) →
      Nonempty (G ≃* Blueprint.NativeSporadic.Carrier s) → ∀ t : G, orderOf t = 2 →
        CompsSatisfy (centralizer ({t} : Set G)) fun Y _ => ¬ SmallCentralQuotient Y)
    (hout : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ x y : G, x * y ≠ y * x) →
      Nonempty (G ≃* Blueprint.NativeSporadic.Carrier s) → ∀ α : MulAut G, α * α = 1 →
        α ∉ OuterAutomorphisms.inner G →
        CompsSatisfy (Sporadic.Schreier.fixSub α) fun Y _ => ¬ SmallCentralQuotient Y) :
    HinFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y s := by
  intro Y _ _ _ hY hnab p m hp hp2 hm h16 _ τ hτ hL
  exfalso
  have hsmall : ∀ (B : Type) [Group B], (B ≃* ↥(GSThmB.layerIn (fixedPoints τ))) →
      SmallCentralQuotient B := by
    intro B _ eB
    have hs := isSimpleGroup_pLayer hL
    have hBs : IsSimpleGroup B := (eB.trans (layerInEquiv _)).isSimpleGroup
    have hBnab : ∃ a b : B, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := nonabelian_of_lieModel_psl2 hL
      exact ⟨eB.symm a, eB.symm b, fun h => hab (eB.symm.injective (by rw [map_mul, map_mul, h]))⟩
    have hZ : center B = ⊥ := (LocalCores.isQuasisimple_of_isSimpleGroup hBnab).2
    have h7 := seven_le_of_sixteen_dvd hp hp2 hm h16
    exact Or.inl ⟨p, m, hp, hp2, hm, by omega, lieModel_psl2_of_mulEquiv
      (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans eB) hL⟩
  have hZY : center Y = ⊥ := (LocalCores.isQuasisimple_of_isSimpleGroup hnab).2
  by_cases hinn : τ ∈ innAut Y
  · obtain ⟨t, rfl⟩ := hinn
    have ht2 : orderOf t = 2 := by
      rw [← orderOf_injective _ (conj_injective_of_center hZY) t]
      exact hτ
    obtain ⟨B, hB, ⟨eB⟩⟩ := exists_isComponent_of_eq (centralizer_eq_fixedPoints_conj t) hL
    exact hin Y inferInstance hnab hY t ht2 B hB (hsmall B eB)
  · have hsq : τ * τ = 1 := by
      have := pow_orderOf_eq_one τ
      rwa [hτ, pow_two] at this
    obtain ⟨B, hB, ⟨eB⟩⟩ := exists_isComponent_of_eq (fixSub_eq_fixedPoints τ) hL
    exact hout Y inferInstance hnab hY τ hsq hinn B hB (hsmall B eB)

theorem hinFor_of_comps {s : TauCeti.SporadicName}
    (hin : ∀ (G : Type) [Group G] [Finite G], Nonempty (G ≃* Blueprint.NativeSporadic.Carrier s) →
      ∀ t : G, orderOf t = 2 →
        CompsSatisfy (centralizer ({t} : Set G)) fun Y _ => ¬ SmallCentralQuotient Y)
    (hout : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ x y : G, x * y ≠ y * x) →
      Nonempty (G ≃* Blueprint.NativeSporadic.Carrier s) → ∀ α : MulAut G, α * α = 1 →
        α ∉ OuterAutomorphisms.inner G →
        CompsSatisfy (Sporadic.Schreier.fixSub α) fun Y _ => ¬ SmallCentralQuotient Y) :
    HinFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y s :=
  hinFor_of_comps_simple (fun G _ _ _ _ hG => hin G hG) hout

end CFSG.ComponentClassification.HarrisLit.Hin
