module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeIdentOrbit
public import CFSG.Quasithin.AppendixH.H16.OctadTransv
public import CFSG.Quasithin.AppendixH.Common.OctadStd
public import CFSG.Quasithin.AppendixH.H16.MaskChief

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.LU24
  CFSG.ASVolI.AppH CFSG.ASVolI.H16

theorem rhoC11_octStab_fix_three {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ AutPerm)
    (hσS : σ ∈ octStab octad0) :
    rhoC11 AutPerm le_rfl ⟨σ, hσ⟩ (toW 11 3) = toW 11 3 := by
  have hmem : rhoCd hσ ∈ imgCd (octStab octad0) := rhoCd_mem_imgCd hσ hσS
  have h1 : rhoCd hσ (toW 11 3) ∈ octV1 :=
    isActsInv_octV1 (fun v => rhoCd hσ v) ⟨rhoCd hσ, hmem, rfl⟩ (toW 11 3)
      ((mem_octV1_iff _).2 (Or.inr rfl))
  rcases (mem_octV1_iff _).1 h1 with h2 | h2
  · exact absurd ((rhoCd hσ).injective (by rw [map_one]; exact h2)) toW_three_ne_one
  · exact h2

theorem card_orbit_toW_three_dvd :
    Nat.card (MulAction.orbit ↥(rhoC11 AutPerm le_rfl).range (toW 11 3)) ∣ 759 := by
  let ρ := rhoC11 AutPerm le_rfl
  let R := ρ.range
  let ρ' : ↥AutPerm →* ↥R := ρ.rangeRestrict
  let T : Subgroup ↥R := MulAction.stabilizer ↥R (toW 11 3)
  let S' : Subgroup ↥AutPerm := (octStab octad0).subgroupOf AutPerm
  have hle : S' ≤ T.comap ρ' := by
    intro g hg
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
    have hg' : (g : Equiv.Perm (Fin 24)) ∈ octStab octad0 := Subgroup.mem_subgroupOf.mp hg
    show ρ g (toW 11 3) = toW 11 3
    exact rhoC11_octStab_fix_three g.2 hg'
  have hdiv : T.index ∣ S'.index := by
    have h1 : (T.comap ρ').index ∣ S'.index := Subgroup.index_dvd_of_le hle
    rwa [Subgroup.index_comap_of_surjective (H := T) ρ.rangeRestrict_surjective] at h1
  have hS : S'.index = 759 := by
    have hcard : Nat.card ↥S' = 322560 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe octStab_octad0_le_AutPerm).toEquiv]
      exact card_octStab_octad0
    have h := S'.card_mul_index
    rw [hcard, card_AutPerm] at h
    have h2 : 244823040 = 322560 * 759 := by norm_num
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) (h.trans h2)
  have hT : T.index = Nat.card (MulAction.orbit ↥R (toW 11 3)) := by
    rw [MulAction.index_stabilizer ↥R (toW 11 3), Nat.card_coe_set_eq]
  rw [← hT, ← hS]
  exact hdiv

theorem exists_ne_one_card_orbit_dvd_of_mathieuCode24
    {V : Type*} [CommGroup V] {L : Subgroup (MulAut V)} (h : MathieuCode24 L ⊤ ⊥) :
    ∃ x : V, x ≠ 1 ∧ Nat.card ↥(MulAction.orbit ↥L x) ∣ 759 := by
  obtain ⟨e, he⟩ := code24_std h
  refine ⟨e.symm (toW 11 3), fun h1 => toW_three_ne_one ?_, ?_⟩
  · simpa using congrArg e h1
  · have key : ∀ L' : Subgroup (MulAut W11), L' = (rhoC11 AutPerm le_rfl).range →
        Nat.card ↥(MulAction.orbit ↥L' (toW 11 3)) ∣ 759 := by
      rintro _ rfl
      exact card_orbit_toW_three_dvd
    exact (dvd_of_eq (card_orbit_map_congrHom_symm e L (toW 11 3)).symm).trans (key _ he)

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
