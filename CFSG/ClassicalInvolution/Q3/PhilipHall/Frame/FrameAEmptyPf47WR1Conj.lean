module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64Main

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.WR1

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem inA_of_aViol {K J : Subgroup G} {zK zJ : G} (h : AViol Ω K J zK zJ) : InA Ω K J :=
  ⟨h.star, h.not_nbr, zK, zJ, h.hzK, h.hzJ, fun ⟨g, hg, he⟩ => h.no_conj g hg he⟩

variable [Finite G]

theorem exists_conj_of_inA (hΩ : HypOmegaGen Ω) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hA : InA Ω K J) {z j : G} (hz : IsUniqueInvolution K z) (hj : IsUniqueInvolution J j) :
    ∃ g : G, g * j * g⁻¹ = z := by
  obtain ⟨-, -, -, -, Ks, -, -, -, -, -, -, -, -, -, -, -, -, -, -, htw, ⟨y, -, hy⟩, -⟩ :=
    Sec6Gen.l6_4ThreeGen G Ω hΩ K hK J hJ hA z j hz hj _ _ rfl rfl
  have hKs : Ks ∈ twinSet Ω K := by
    rw [htw]
    exact Or.inr rfl
  obtain ⟨-, z', hz', hKsz'⟩ := hKs
  have h1 : IsUniqueInvolution Ks (y * j * y⁻¹) := by
    rw [← hy]
    exact hj.conj y
  exact ⟨y, (hKsz'.eq h1).symm.trans (hz.eq hz').symm⟩

theorem exists_conj_of_mem_aStar (hΩ : HypOmegaGen Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) {L : Subgroup G} (hL : L ∈ aStar Ω K) :
    L ∈ Ω ∧ ∀ l : G, IsUniqueInvolution L l → ∃ g : G, g * z * g⁻¹ = l := by
  induction hL with
  | refl => exact ⟨hK, fun l hl => ⟨1, by rw [hz.eq hl]; group⟩⟩
  | tail _ hML ih =>
    obtain ⟨hMΩ, ihM⟩ := ih
    refine ⟨hML.1, fun l hl => ?_⟩
    obtain ⟨m, hm⟩ := Sec6Gen.exists_uniqueInvolution hΩ hMΩ
    obtain ⟨g, hg⟩ := ihM m hm
    rcases hML.2 with ⟨a, b, hv⟩ | ⟨a, b, hv⟩ | ⟨⟨-, w, hwM, hwL⟩, -⟩
    · obtain ⟨h, hh⟩ := exists_conj_of_inA hΩ hMΩ hML.1 (inA_of_aViol hv) hm hl
      refine ⟨h⁻¹ * g, ?_⟩
      calc h⁻¹ * g * z * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * z * g⁻¹) * h := by group
        _ = h⁻¹ * (h * l * h⁻¹) * h := by rw [hg, hh]
        _ = l := by group
    · obtain ⟨h, hh⟩ := exists_conj_of_inA hΩ hML.1 hMΩ (inA_of_aViol hv) hl hm
      refine ⟨h * g, ?_⟩
      calc h * g * z * (h * g)⁻¹ = h * (g * z * g⁻¹) * h⁻¹ := by group
        _ = l := by rw [hg, hh]
    · exact ⟨g, by rw [hg, hm.eq hwM, hwL.eq hl]⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.WR1
