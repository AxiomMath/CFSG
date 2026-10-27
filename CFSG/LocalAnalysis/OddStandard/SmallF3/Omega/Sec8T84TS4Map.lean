module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84FPSound
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84TS4Idx
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private theorem sec8t84ts4_card_eq {G G' : Type} [Group G] [Finite G] [Group G'] [Finite G']
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

theorem sec8t84ts4_theta {W : Certificates.Asc82NormA6.Facts} {Y : Type} [Group Y] [Finite Y]
    {E P : Subgroup Y} (Θ : Y ≃* Sec8T84FPM0 W) (hΘ : E.map Θ.toMonoidHom = Sec8T84FPV0 W)
    (hP : IsSylow2Of P ⊤) {P₀ : Subgroup (Sec8T84FPM0 W)} (hP₀ : IsSylow2Of P₀ ⊤) :
    ∃ θ : Y ≃* Sec8T84FPM0 W, E.map θ.toMonoidHom = Sec8T84FPV0 W ∧
      P.map θ.toMonoidHom = P₀ := by
  classical
  have hQ : IsPGroup 2 (P.map Θ.toMonoidHom) := IsPGroup.map hP.2.1 Θ.toMonoidHom
  obtain ⟨c, -, hc⟩ := exists_conj_le_of_isSylow2Of hP₀ hQ le_top
  set θ : Y ≃* Sec8T84FPM0 W := Θ.trans (MulAut.conj c) with hθdef
  have hθ_apply : ∀ y : Y, θ y = c * Θ y * c⁻¹ := by
    intro y
    simp [hθdef, MulAut.conj_apply]
  refine ⟨θ, ?_, ?_⟩
  · have hhom : θ.toMonoidHom = (MulAut.conj c).toMonoidHom.comp Θ.toMonoidHom := rfl
    haveI : (Sec8T84FPV0 W).Normal := sec8t84FPV0_normal W
    rw [hhom, ← Subgroup.map_map, hΘ]
    exact Subgroup.Normal.map_conj_eq (Sec8T84FPV0 W) c
  · refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro x hx
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
      change θ p ∈ P₀
      rw [hθ_apply p]
      exact hc (Θ p) (Subgroup.mem_map_of_mem Θ.toMonoidHom hp)
    · rw [Subgroup.card_map_of_injective θ.injective]
      exact le_of_eq (sec8t84ts4_card_eq hP hP₀ (Nat.card_congr Θ.toEquiv)).symm

theorem sec8t84ts4_coord (G : Certificates.T84P.Facts)
    {Y : Type} [Group Y] [Finite Y] {E H P F : Subgroup Y} [E.Normal] (hE : IsElemAb2 E 4)
    (hH : Nonempty (↥H ≃* alternatingGroup (Fin 6))) (hEH : E ⊓ H = ⊥) (hEH' : E ⊔ H = ⊤)
    (htr : ∀ a ∈ E, a ≠ 1 → ∀ b ∈ E, b ≠ 1 → ∃ h ∈ H, h * a * h⁻¹ = b)
    (hP : IsSylow2Of P ⊤) (hF : Sec8T84PFacts Y E P F) :
    ∃ rr : Y → Certificates.T84P.Elt, Sec8T84TS4Coord (E ⊔ F) rr := by
  set W := Certificates.certificate442267 with hW
  obtain ⟨Θ, hΘ⟩ := sec8t84_iso_model hE hH hEH hEH' htr
  obtain ⟨hP₀, hF₀⟩ := sec8t84_model_facts W G
  obtain ⟨θ, hθE, hθP⟩ := sec8t84ts4_theta Θ hΘ hP hP₀
  have hmap := Sec8T84PFacts.map θ hF
  rw [hθE, hθP] at hmap
  have hFF : F.map θ.toMonoidHom = sec8t84FPF0 W G := by
    rcases hF₀.only (F.map θ.toMonoidHom) hmap.F_le hmap.F_e16 with h | h
    · exact absurd h hmap.F_ne
    · exact h
  have hJ : (E ⊔ F).map θ.toMonoidHom = sec8t84FPJ0 W G := by
    rw [Subgroup.map_sup, hθE, hFF, sec8t84FPJ_eq W G]
  refine ⟨fun y => sec8t84FPRaw W (θ y), ?_⟩
  exact
    { mul := fun x y => by rw [map_mul, sec8t84FPRaw_mul]
      one := by rw [map_one, sec8t84FPRaw_one]
      inj := fun x y h => θ.injective (sec8t84FPRaw_injective W h)
      mem := fun x => sec8t84FPRaw_mem W _
      surj := fun z hz => by
        obtain ⟨x, hx⟩ := sec8t84FPRaw_surj W hz
        exact ⟨θ.symm x, by simp [hx]⟩
      card := by rw [Nat.card_congr θ.toEquiv, sec8t84FPM0_card]
      J_iff := fun x => by
        have h1 : θ x ∈ (E ⊔ F).map θ.toMonoidHom ↔ x ∈ E ⊔ F := by
          rw [Subgroup.mem_map_equiv]
          simp
        rw [← h1, hJ]
        exact Iff.rfl }

end CFSG.OddStandard.SmallF3.Omega
