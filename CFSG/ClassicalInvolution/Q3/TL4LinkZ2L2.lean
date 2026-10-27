module

public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2L2Defs
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2L2M10

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.Blueprint

theorem Z2M10.linkZ2Model_of_m10 {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}
    (hq : ∀ L ∈ Φ, ∀ P : Subgroup X, IsSylow2In P L → Nonempty (↥P ≃* QuaternionGroup 2))
    {L₀ : Subgroup X} (hL₀ : L₀ ∈ Φ) (hs : IsSimpleGroup ↥(genFittingFStar X))
    (hidx : (genFittingFStar X).index ≤ 2) {p f : ℕ} (hL : LieModel (FStarQuot X) .PSL 2 p f)
    (h9 : p ^ f = 9) : LinkZ2Model X Φ := by
  obtain ⟨P₀, hP₀, -⟩ := IsSylow2In.exists_ge (P := L₀) (T := ⊥) IsPGroup.of_bot bot_le
  obtain ⟨e₀⟩ := hq L₀ hL₀ P₀ hP₀
  obtain ⟨hnab, hinv, halpha, hconj, hgen, h163⟩ := Z2M10.fields_of_fstar hs hidx hL h9
    (ι := P₀.subtype.comp e₀.symm.toMonoidHom) (Subtype.val_injective.comp e₀.symm.injective)
  refine ⟨hs, hnab, hinv, halpha, hconj, hgen, ?_⟩
  intro L hL a ha P hP β hβ hfix
  obtain ⟨e⟩ := hq L hL P hP
  have hz : ((e.symm (QuaternionGroup.a 2) : ↥P) : X) = a := by
    rcases ha.unique _ (hP.1 (e.symm (QuaternionGroup.a 2)).2) (by
        rw [← Subgroup.coe_mul, ← map_mul, show QuaternionGroup.a 2 * QuaternionGroup.a 2 =
          (1 : QuaternionGroup 2) by decide, map_one, Subgroup.coe_one]) with h | h
    · exfalso
      have h1 : e.symm (QuaternionGroup.a 2) = 1 := Subtype.ext h
      rw [map_eq_one_iff _ e.symm.injective] at h1
      exact absurd h1 (by decide)
    · exact h
  rw [← hz]
  exact h163 P e β hβ hfix

section Cit3


variable {n : ℕ}

theorem tightLinkZ2L2R_of (hα : TightLinkZ2AlphaR 3 n) (hbig : TightLinkZ2L2BigR 3 n) :
    TightLinkZ2L2R 3 n := by
  intro Y _ _ R S t hL hc hT hbad hZ2 hsimp hidx ⟨p, f, hp, hp2, hf, hk⟩
  by_cases h9 : p ^ f = 9
  · obtain ⟨J, hJ, u, hu, hne⟩ := hbad
    have hΦ := (typeRFam_coreLinkFam hL).restrict (linkGrp R t)
    have hM : LinkZ2Model ↥(linkGrp R t) (linkFam R t) :=
      Z2M10.linkZ2Model_of_m10 (fun L hL' P hP => hΦ.quat L hL' P hP)
        (subgroupOf_mem_linkRestrict (t := t) hJ) hsimp hidx hk h9
    exact hne (hα Y R S t hL hc hT hZ2 (Or.inl hM) J hJ u hu)
  · exact hbig Y R S t hL hc hT hbad hZ2 hsimp hidx ⟨p, f, hp, hp2, hf, h9, hk⟩

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
