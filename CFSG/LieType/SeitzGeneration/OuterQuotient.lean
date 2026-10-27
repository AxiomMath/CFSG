module

public import CFSG.LieType.SeitzGeneration.Defs

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.ComponentClassification.OuterAutomorphisms

theorem le_inner_of_coprime_card_outer {K : Type*} [Group K] {E : Subgroup (MulAut K)}
    (h : Nat.Coprime (Nat.card E) (Nat.card (Outer K))) :
    E ≤ (MulAut.conj : K →* MulAut K).range := by
  let π : MulAut K →* Outer K := @QuotientGroup.mk' (MulAut K) _ (inner K) (innerNormal K)
  let f : E →* Outer K := π.comp E.subtype
  have h1 : Nat.card f.range = 1 :=
    Nat.eq_one_of_dvd_coprimes h (Subgroup.card_dvd_of_surjective f.rangeRestrict_surjective)
      (Subgroup.card_subgroup_dvd_card _)
  have h2 : f.range = ⊥ := Subgroup.card_eq_one.mp h1
  intro φ hφ
  have hf : f ⟨φ, hφ⟩ = 1 := by
    have : f ⟨φ, hφ⟩ ∈ f.range := ⟨⟨φ, hφ⟩, rfl⟩
    rwa [h2, Subgroup.mem_bot] at this
  exact (@QuotientGroup.eq_one_iff (MulAut K) _ (inner K) (innerNormal K) φ).mp hf

theorem injective_outer_of_coprime_card {K : Type*} [Group K] {E : Subgroup (MulAut K)}
    (h : Nat.Coprime (Nat.card E) (Nat.card K)) :
    ∃ f : E →* Outer K, Function.Injective f := by
  let π : MulAut K →* Outer K := @QuotientGroup.mk' (MulAut K) _ (inner K) (innerNormal K)
  let f : E →* Outer K := π.comp E.subtype
  have hmap : f.ker.map E.subtype ≤ (MulAut.conj : K →* MulAut K).range := by
    rintro _ ⟨x, hx, rfl⟩
    exact (@QuotientGroup.eq_one_iff (MulAut K) _ (inner K) (innerNormal K) (x : MulAut K)).mp hx
  have hcard : Nat.card f.ker = Nat.card (f.ker.map E.subtype) :=
    (Subgroup.card_map_of_injective E.subtype_injective).symm
  have hdvd : Nat.card f.ker ∣ Nat.card K := by
    rw [hcard]
    exact (Subgroup.card_dvd_of_le hmap).trans
      (Subgroup.card_dvd_of_surjective (MonoidHom.rangeRestrict_surjective _))
  have h1 : Nat.card f.ker = 1 :=
    Nat.eq_one_of_dvd_coprimes h (Subgroup.card_subgroup_dvd_card _) hdvd
  exact ⟨f, (MonoidHom.ker_eq_bot_iff f).mp (Subgroup.card_eq_one.mp h1)⟩

theorem innerPlane_of_coprime_card_outer {d : TauCeti.ValidLieTypeIndex} {p : ℕ}
    {E : Subgroup (MulAut (Cat d))} (h : Nat.Coprime (Nat.card E) (Nat.card (Outer (Cat d)))) :
    InnerPlane d p E :=
  le_inner_of_coprime_card_outer h

end CFSG.LieType.SeitzGeneration
