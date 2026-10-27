module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.SeitzGeneration.OrthBlocks
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open QuadraticMap CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.SeitzGeneration.OrthBlk
open CFSG.RankThree.Classical2

namespace OmTorus

variable {F W : Type} [Field F] [CharP F 2] [AddCommGroup W] [Module F W]
  [FiniteDimensional F W] {Q : QuadraticForm F W}

theorem commute_of_orthogonal_supports {U₁ U₂ : Submodule F W}
    (hU₁ : PolarNondegOn Q U₁) (hU₂ : PolarNondegOn Q U₂)
    (horth : U₁ ≤ perp Q U₂)
    {t₁ t₂ : W ≃ₗ[F] W}
    (ht₁fix : ∀ w ∈ perp Q U₁, t₁ w = w)
    (ht₂fix : ∀ w ∈ perp Q U₂, t₂ w = w)
    (ht₁map : ∀ x ∈ U₁, t₁ x ∈ U₁)
    (ht₂map : ∀ x ∈ U₂, t₂ x ∈ U₂) :
    Commute t₁ t₂ := by
  classical
  have horth' : U₂ ≤ perp Q U₁ := by
    intro x hx
    rw [mem_perp]
    intro y hy
    rw [polar_comm]
    exact mem_perp.mp (horth hy) x hx
  have hsup : PolarNondegOn Q (U₁ ⊔ U₂) := by
    intro x hx hxperp
    obtain ⟨a₁, ha₁, a₂, ha₂, hx'⟩ := Submodule.mem_sup.mp hx
    have h1 : ∀ y ∈ U₁, polar Q a₁ y = 0 := by
      intro y hy
      have hp : polar Q x y = 0 := hxperp y (Submodule.mem_sup_left hy)
      rw [← hx', polar_add_left, mem_perp.mp (horth hy) a₂ ha₂, add_zero] at hp
      exact hp
    have h2 : ∀ y ∈ U₂, polar Q a₂ y = 0 := by
      intro y hy
      have hp : polar Q x y = 0 := hxperp y (Submodule.mem_sup_right hy)
      rw [← hx', polar_add_left, mem_perp.mp (horth' hy) a₁ ha₁, zero_add] at hp
      exact hp
    have ha₁0 : a₁ = 0 := hU₁ a₁ ha₁ h1
    have ha₂0 : a₂ = 0 := hU₂ a₂ ha₂ h2
    rw [ha₁0, ha₂0, zero_add] at hx'
    rw [hx']
  let C : Submodule F W := perp Q (U₁ ⊔ U₂)
  have hcompl : IsCompl (U₁ ⊔ U₂) C := isCompl_perp hsup
  have hC₁ : C ≤ perp Q U₁ := by
    intro x hx
    rw [mem_perp] at hx ⊢
    intro y hy
    exact hx y (Submodule.mem_sup_left hy)
  have hC₂ : C ≤ perp Q U₂ := by
    intro x hx
    rw [mem_perp] at hx ⊢
    intro y hy
    exact hx y (Submodule.mem_sup_right hy)
  ext x
  obtain ⟨s, c, hx⟩ := CFSG.RankThree.PartOne.KCOrthogonal.exists_coe_add_of_isCompl hcompl x
  obtain ⟨a₁, ha₁, a₂, ha₂, hs⟩ := Submodule.mem_sup.mp s.2
  have hx' : x = (a₁ : W) + (a₂ : W) + (c : W) := by
    rw [← hx, ← hs]
  rw [hx', LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  have ht₂a₁ : t₂ (a₁ : W) = a₁ := ht₂fix a₁ (horth ha₁)
  have ht₁a₂ : t₁ (a₂ : W) = a₂ := ht₁fix a₂ (horth' ha₂)
  have ht₁c : t₁ (c : W) = c := ht₁fix c (hC₁ c.2)
  have ht₂c : t₂ (c : W) = c := ht₂fix c (hC₂ c.2)
  have ht₂a₂ : t₂ (a₂ : W) ∈ U₂ := ht₂map a₂ ha₂
  have ht₁a₁ : t₁ (a₁ : W) ∈ U₁ := ht₁map a₁ ha₁
  have ht₁t₂a₂ : t₁ (t₂ (a₂ : W)) = t₂ (a₂ : W) := ht₁fix _ (horth' ht₂a₂)
  have ht₂t₁a₁ : t₂ (t₁ (a₁ : W)) = t₁ (a₁ : W) := ht₂fix _ (horth ht₁a₁)
  simp only [map_add, ht₂a₁, ht₁a₂, ht₁c, ht₂c, ht₁t₂a₂, ht₂t₁a₁]

end OmTorus

end CFSG.LocalAnalysis.GLTheoremA.Y10F
