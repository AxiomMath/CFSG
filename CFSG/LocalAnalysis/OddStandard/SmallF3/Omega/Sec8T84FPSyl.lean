module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84FPInv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84FPModel
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup Certificates.Asc82NormA6

private theorem isSylow2Of_card_eq {G G' : Type} [Group G] [Finite G] [Group G'] [Finite G']
    {S : Subgroup G} {S' : Subgroup G'} (hS : IsSylow2Of S ⊤) (hS' : IsSylow2Of S' ⊤)
    (hcard : Nat.card G = Nat.card G') : Nat.card S = Nat.card S' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hS.exists_sylow
  obtain ⟨P', hP'⟩ := hS'.exists_sylow
  have h1 : Nat.card (⊤ : Subgroup G) = Nat.card G := Subgroup.card_top
  have h2 : Nat.card (⊤ : Subgroup G') = Nat.card G' := Subgroup.card_top
  rw [← hP, ← hP',
    Subgroup.card_map_of_injective (Subgroup.subtype_injective (⊤ : Subgroup G)),
    Subgroup.card_map_of_injective (Subgroup.subtype_injective (⊤ : Subgroup G')),
    Sylow.card_eq_multiplicity P, Sylow.card_eq_multiplicity P', h1, h2, hcard]

theorem sec8t84_facts_transfer {F : Facts} {Y : Type} [Group Y] [Finite Y] {E P : Subgroup Y}
    (Θ : Y ≃* Sec8T84FPM0 F) (hΘ : E.map Θ.toMonoidHom = Sec8T84FPV0 F) (hP : IsSylow2Of P ⊤)
    {P₀ F₀ : Subgroup (Sec8T84FPM0 F)} (hP₀ : IsSylow2Of P₀ ⊤)
    (hF : Sec8T84PFacts (Sec8T84FPM0 F) (Sec8T84FPV0 F) P₀ F₀) :
    ∃ F' : Subgroup Y, Sec8T84PFacts Y E P F' := by
  classical
  have hQ : IsPGroup 2 (P.map Θ.toMonoidHom) := IsPGroup.map hP.2.1 Θ.toMonoidHom
  obtain ⟨c, -, hc⟩ := exists_conj_le_of_isSylow2Of hP₀ hQ le_top
  set θ : Y ≃* Sec8T84FPM0 F := Θ.trans (MulAut.conj c) with hθdef
  have hθ_apply : ∀ y : Y, θ y = c * Θ y * c⁻¹ := by
    intro y
    simp [hθdef, MulAut.conj_apply]
  have hθP : P.map θ.toMonoidHom = P₀ := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro x hx
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
      change θ p ∈ P₀
      rw [hθ_apply p]
      exact hc (Θ p) (Subgroup.mem_map_of_mem Θ.toMonoidHom hp)
    · rw [Subgroup.card_map_of_injective θ.injective]
      exact le_of_eq (isSylow2Of_card_eq hP hP₀ (Nat.card_congr Θ.toEquiv)).symm
  have hhom : θ.toMonoidHom = (MulAut.conj c).toMonoidHom.comp Θ.toMonoidHom := rfl
  have hEθ : E.map θ.toMonoidHom = Sec8T84FPV0 F := by
    haveI : (Sec8T84FPV0 F).Normal := sec8t84FPV0_normal F
    rw [hhom, ← Subgroup.map_map, hΘ]
    exact Subgroup.Normal.map_conj_eq (Sec8T84FPV0 F) c
  have hV : (Sec8T84FPV0 F).map θ.symm.toMonoidHom = E := by
    rw [← hEθ, Subgroup.map_map]
    simp
  have hP' : P₀.map θ.symm.toMonoidHom = P := by
    rw [← hθP, Subgroup.map_map]
    simp
  refine ⟨F₀.map θ.symm.toMonoidHom, ?_⟩
  rw [← hV, ← hP']
  exact Sec8T84PFacts.map θ.symm hF

end CFSG.OddStandard.SmallF3.Omega
