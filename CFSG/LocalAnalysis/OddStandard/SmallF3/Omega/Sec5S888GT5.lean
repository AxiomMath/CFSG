module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888GT1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5InputsB4

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

private theorem s888_card_comap_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (H : Subgroup Q') : Nat.card (H.comap e.toMonoidHom) = Nat.card H := by
  have h := Subgroup.card_map_of_injective (K := H.comap e.toMonoidHom)
    (f := e.toMonoidHom) e.injective
  rw [Subgroup.map_comap_eq_self_of_surjective e.surjective H] at h
  exact h.symm

private theorem s888_map_oddCore_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') :
    (oddCore Q).map e.toMonoidHom = oddCore Q' := by
  unfold oddCore
  rw [(Subgroup.gc_map_comap e.toMonoidHom).l_sSup_eq_sSup_image]
  congr 1
  ext N'
  constructor
  · rintro ⟨N, ⟨hNnorm, hNodd⟩, rfl⟩
    exact ⟨hNnorm.map e.toMonoidHom e.surjective,
      by rw [Subgroup.card_map_of_injective e.injective]; exact hNodd⟩
  · intro hN'
    exact ⟨N'.comap e.toMonoidHom,
      ⟨hN'.1.comap e.toMonoidHom,
        by rw [s888_card_comap_mulEquiv e N']; exact hN'.2⟩,
      Subgroup.map_comap_eq_self_of_surjective e.surjective N'⟩

theorem pocket_to_G {G : Type} [Group G] (z : G) {P : Subgroup ↥(centralizer ({z} : Set G))}
    {p n : ℕ} [Fact p.Prime] (hzP : zCent z ∈ P) (hsub : P.IsSubnormal)
    (hmod : IsSL2qMod P p n) :
    Sl2qPocketIn (⊤ : Subgroup G) z (P.map (centralizer ({z} : Set G)).subtype) p n := by
  classical
  have hsubOf : (P.map (centralizer ({z} : Set G)).subtype).subgroupOf
      (centralizer ({z} : Set G)) = P :=
    Subgroup.comap_map_eq_self_of_injective
      (Subgroup.subtype_injective (centralizer ({z} : Set G))) P
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨zCent z, hzP, rfl⟩
  · exact le_inf le_top (Subgroup.map_subtype_le P)
  · rw [top_inf_eq, hsubOf]
    exact hsub
  · obtain ⟨e₀⟩ := hmod
    let e : ↥(P.map (centralizer ({z} : Set G)).subtype) ≃* ↥P :=
      (P.equivMapOfInjective (centralizer ({z} : Set G)).subtype
        (Subgroup.subtype_injective _)).symm
    exact ⟨(QuotientGroup.congr (oddCore ↥(P.map (centralizer ({z} : Set G)).subtype))
      (oddCore ↥P) e (s888_map_oddCore_mulEquiv e)).trans e₀⟩

end CFSG.OddStandard.SmallF3.Omega
