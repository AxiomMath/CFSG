module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3NSC

public section

namespace CFSG.QuasithinUnique.A5.Kc3NSC

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5

theorem card_permHom_range : Nat.card permHom.range = 120 := by
  rw [Nat.card_congr (MonoidHom.ofInjective permHom_injective).toEquiv.symm, Nat.card_perm,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem not_subnormal_of_big_image {G : Type} [Group G] [Finite G] {L X V S₁ : Subgroup G}
    (hLX : L ≤ X) (hXV : X ≤ Subgroup.normalizer (V : Set G))
    (α : ↥L →* ↥(alternatingGroup (Fin 5))) (hα : Function.Surjective α) (β : ↥V ≃* Dm)
    (hβ : ∀ (l : ↥L) (v w : ↥V), (w : G) = l * v * l⁻¹ →
      Multiplicative.toAdd (β w) =
        vact ((α l : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5))
          (Multiplicative.toAdd (β v)))
    (hS₁ : IsSylowTwoOf S₁ X) (h16 : 16 ∣ Nat.card (rhoY V X hXV β).range) :
    ¬ IsSubnormal L (L ⊔ S₁) := by
  classical
  intro hsub
  have hSX : S₁ ≤ X := hS₁.1
  have hYX : L ⊔ S₁ ≤ X := sup_le hLX hSX
  have hYV : L ⊔ S₁ ≤ Subgroup.normalizer (V : Set G) := hYX.trans hXV
  have hnsc := nsc_perm (le_sup_left : L ≤ L ⊔ S₁) hYV α hα β hβ hsub
  set ρ : ↥X →* MulAut Dm := rhoY V X hXV β with hρ
  set S' : Subgroup ↥X := S₁.subgroupOf X with hS'
  have hperm : S'.map ρ ≤ permHom.range := by
    rintro _ ⟨s, hs, rfl⟩
    have hsS : (s : G) ∈ S₁ := Subgroup.mem_subgroupOf.1 hs
    obtain ⟨σ, hσ⟩ := hnsc (s : G) (Subgroup.mem_sup_right hsS)
    refine ⟨σ, ?_⟩
    refine MulEquiv.ext fun x => ?_
    have hw := rhoY_spec V X hXV β s x
    have h := hσ (β.symm x) (β.symm (ρ s x)) (by simpa using hw)
    simp only [MulEquiv.apply_symm_apply] at h
    rw [permHom_apply, ← h, ofAdd_toAdd]
  let ρ' : ↥X →* ρ.range := ρ.rangeRestrict
  have hρ'surj : Function.Surjective ρ' := ρ.rangeRestrict_surjective
  have hidx : (S'.map ρ').index ∣ S'.index := Subgroup.index_map_dvd S' hρ'surj
  have hodd : ¬ 2 ∣ (S'.map ρ').index := fun h => hS₁.2.2 (h.trans hidx)
  have hcop : Nat.Coprime 16 (S'.map ρ').index := by
    have : Nat.Coprime 2 (S'.map ρ').index := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd
    simpa using this.pow_left 4
  have hmul := Subgroup.card_mul_index (S'.map ρ')
  have h16' : 16 ∣ Nat.card (S'.map ρ') := by
    have : 16 ∣ Nat.card (S'.map ρ') * (S'.map ρ').index := by rw [hmul]; exact h16
    exact hcop.dvd_of_dvd_mul_right this
  have hmapeq : (S'.map ρ').map ρ.range.subtype = S'.map ρ := by
    rw [Subgroup.map_map]
    rfl
  have hcard : Nat.card (S'.map ρ') = Nat.card (S'.map ρ) := by
    rw [← hmapeq, Subgroup.card_map_of_injective ρ.range.subtype_injective]
  rw [hcard] at h16'
  have hdvd : Nat.card (S'.map ρ) ∣ 120 := by
    have := Subgroup.card_dvd_of_le hperm
    rwa [card_permHom_range] at this
  have := h16'.trans hdvd
  omega

end CFSG.QuasithinUnique.A5.Kc3NSC
