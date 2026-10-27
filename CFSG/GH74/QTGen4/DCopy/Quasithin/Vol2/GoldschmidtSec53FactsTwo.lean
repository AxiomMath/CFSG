module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsTwo
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.GoldschmidtSec53FactsLoc

public section

namespace CFSG.Quasithin.H13.Sec53F

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F1

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D L₂ : Subgroup G} {n : ℕ}
  {P : Type} [Group P] [Finite P] {N₁ N₂ : Subgroup P}
  (Φ : (RankTwoAmalgam.ofSubgroups (fG1 M L H B) (fG2 M L H D)).Iso
    (RankTwoAmalgam.ofSubgroups N₁ N₂))

include Φ

theorem facts_ii_F4 (h527 : Stmt5_2_7_F4) (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m f : ℕ} (hty : IsOfLieType52 M L H B D T t m f)
    (hF : TransFacts N₁ N₂) :
    (∀ z ∈ centerOf L, z ≠ 1 → ∀ z' ∈ centerOf L, z' ≠ 1 → ∃ g ∈ B ⊔ D, g * z * g⁻¹ = z') ∧
    (∀ z ∈ centerOf (oTwoUpper H), z ≠ 1 → ∀ z' ∈ centerOf (oTwoUpper H), z' ≠ 1 →
      ∃ g ∈ B ⊔ D, g * z * g⁻¹ = z') := by
  have hsol := isSolvable_fG12 Φ hF.solv
  have hpc1 := perfectCore_fG1 hyp hsol
  have hpc2 := perfectCore_fG2 hyp hty hsol
  refine ⟨fun z hz hz1 z' hz' hz1' => ?_, fun z hz hz1 z' hz' hz1' => ?_⟩
  · exact exists_conj_of_equiv (isoφ1 Φ) (BD_le_normalizer_L hyp) (fG1_eq_F4 h527 hyp)
      (perfectCore_le N₁) (mem_L_iff Φ hpc1) (R := fun x => x ≠ 1) (R' := fun y => y ≠ 1)
      (ne_one_iff_of_equiv (isoφ1 Φ))
      (fun a ha ha1 a' ha' ha1' => hF.trans₁ a ha a' ha' ha1 ha1') hz hz' hz1 hz1'
  · exact exists_conj_of_equiv (isoφ2 Φ) (BD_le_normalizer_K hyp) (fG2_eq_F4 h527 hyp)
      (perfectCore_le N₂) (mem_K_iff Φ hpc2) (R := fun x => x ≠ 1) (R' := fun y => y ≠ 1)
      (ne_one_iff_of_equiv (isoφ2 Φ))
      (fun a ha ha1 a' ha' ha1' => hF.trans₂ a ha a' ha' ha1 ha1') hz hz' hz1 hz1'

end CFSG.Quasithin.H13.Sec53F
