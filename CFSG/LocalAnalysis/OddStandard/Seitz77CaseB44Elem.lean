module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB43Glue

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.OddStandard.Seitz77.CaseB45
  CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open scoped commutatorElement

theorem prod_radicals_of_card {k : Type} [Field k] (hk : Nat.card k = 4)
    {W' : Subgroup (↥(unipAll k) × ↥(unipAll k))} (hsq : ∀ g ∈ W', g * g = 1)
    (hcard : Nat.card ↥W' = 2 ^ 8) :
    ∃ E₁ E₂ : Subgroup ↥(unipAll k), (E₁ = radOne k ∨ E₁ = radTwo k) ∧
      (E₂ = radOne k ∨ E₂ = radTwo k) ∧ W' = E₁.prod E₂ := by
  have hchar : CharP k 2 := charP_two_of_card_four_B42 hk
  have hfin : Finite k := Nat.finite_of_card_ne_zero (by omega)
  have hk2 : Nat.card k ^ 2 = 16 := by rw [hk]; norm_num
  have hr1 : Nat.card ↥(radOne k) = 16 := by rw [card_radOne, hk2]
  have hr2 : Nat.card ↥(radTwo k) = 16 := by rw [card_radTwo, hk2]
  have hf1 : Finite ↥(radOne k) := Nat.finite_of_card_ne_zero (by omega)
  have hf2 : Finite ↥(radTwo k) := Nat.finite_of_card_ne_zero (by omega)
  have key : ∀ Q : Subgroup ↥(unipAll k), (∀ g ∈ Q, g * g = 1) →
      Finite ↥Q ∧ Nat.card ↥Q ≤ 16 := by
    intro Q hQ
    rcases le_radOne_or_le_radTwo Q hQ with h | h
    · exact ⟨Finite.of_injective _ (Subgroup.inclusion_injective h),
        hr1 ▸ Subgroup.card_le_of_le h⟩
    · exact ⟨Finite.of_injective _ (Subgroup.inclusion_injective h),
        hr2 ▸ Subgroup.card_le_of_le h⟩
  set P₁ : Subgroup ↥(unipAll k) := W'.map (MonoidHom.fst _ _) with hP₁
  set P₂ : Subgroup ↥(unipAll k) := W'.map (MonoidHom.snd _ _) with hP₂
  have hsq₁ : ∀ g ∈ P₁, g * g = 1 := by
    rintro _ ⟨p, hp, rfl⟩
    exact congrArg Prod.fst (hsq p hp)
  have hsq₂ : ∀ g ∈ P₂, g * g = 1 := by
    rintro _ ⟨p, hp, rfl⟩
    exact congrArg Prod.snd (hsq p hp)
  obtain ⟨hfP₁, h1⟩ := key P₁ hsq₁
  obtain ⟨hfP₂, h2⟩ := key P₂ hsq₂
  have hle : W' ≤ P₁.prod P₂ := fun p hp => ⟨⟨p, hp, rfl⟩, ⟨p, hp, rfl⟩⟩
  have hcard12 : Nat.card ↥(P₁.prod P₂) = Nat.card ↥P₁ * Nat.card ↥P₂ := by
    rw [Nat.card_congr (Subgroup.prodEquiv P₁ P₂).toEquiv, Nat.card_prod]
  have hfin12 : Finite ↥(P₁.prod P₂) :=
    Finite.of_equiv _ (Subgroup.prodEquiv P₁ P₂).toEquiv.symm
  have hle' : Nat.card ↥W' ≤ Nat.card ↥(P₁.prod P₂) := Subgroup.card_le_of_le hle
  rw [hcard, hcard12] at hle'
  have hc1 : Nat.card ↥P₁ = 16 := by nlinarith
  have hc2 : Nat.card ↥P₂ = 16 := by nlinarith
  refine ⟨P₁, P₂, eq_radOne_or_radTwo_of_card hsq₁ (by rw [hc1, hk2]),
    eq_radOne_or_radTwo_of_card hsq₂ (by rw [hc2, hk2]), ?_⟩
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard12, hc1, hc2, hcard]; norm_num)

theorem SwapPair.elem_classify {G : Type} [Group G] {A B : Subgroup G} {t : G}
    (P : SwapPair A B t) {k : Type} [Field k] (hk : Nat.card k = 4)
    {e : ↥A ≃* ↥(unipAll k)} {W : Subgroup G} (hWS : W ≤ A ⊔ B) (hW : IsElemAbelian 2 W)
    (hcard : Nat.card W = 2 ^ 8) :
    ∃ E₁ E₂ : Subgroup ↥(unipAll k), (E₁ = radOne k ∨ E₁ = radTwo k) ∧
      (E₂ = radOne k ∨ E₂ = radTwo k) ∧
      W = radIn A e E₁ ⊔ cs t (radIn A e E₂) := by
  have hinj : Function.Injective (P.psi e) := P.psi_inj e
  have hrange : W ≤ (P.psi e).range := fun y hy => by
    obtain ⟨p, hp⟩ := P.exists_psi_eq e (hWS hy)
    exact ⟨p, hp⟩
  have hmap : (W.comap (P.psi e)).map (P.psi e) = W := Subgroup.map_comap_eq_self hrange
  have hcard' : Nat.card ↥(W.comap (P.psi e)) = 2 ^ 8 := by
    have h := Subgroup.card_map_of_injective (K := W.comap (P.psi e)) hinj
    rw [hmap, hcard] at h
    exact h.symm
  have hsq : ∀ g ∈ W.comap (P.psi e), g * g = 1 := by
    intro g hg
    apply hinj
    rw [map_mul, map_one]
    exact mul_self_of_isElemAbelian_two hW hg
  obtain ⟨E₁, E₂, h1, h2, hprod⟩ := prod_radicals_of_card hk hsq hcard'
  refine ⟨E₁, E₂, h1, h2, ?_⟩
  have hmemW : ∀ p, p ∈ E₁.prod E₂ ↔ P.psi e p ∈ W := fun p => by
    rw [← hprod]
    exact Iff.rfl
  ext y
  constructor
  · intro hy
    obtain ⟨p, hp⟩ := P.exists_psi_eq e (hWS hy)
    have hp' : p ∈ E₁.prod E₂ := (hmemW p).mpr (hp ▸ hy)
    rw [← hp, P.psi_apply]
    refine mul_mem (mem_sup_left ?_) (mem_sup_right ?_)
    · exact mem_radIn.mpr ⟨e.symm p.1, by simpa using hp'.1, rfl⟩
    · exact mem_cs_iff.mpr (mem_radIn.mpr ⟨e.symm p.2, by simpa using hp'.2, rfl⟩)
  · intro hy
    obtain ⟨o, ho, z, hz, rfl⟩ := mem_sup_of_forall_comm (O := radIn A e E₁)
      (E := cs t (radIn A e E₂))
      (fun x hx y hy => P.comm x (radIn_le hx) y (P.cs_le radIn_le hy)) hy
    obtain ⟨a, ha, rfl⟩ := mem_radIn.mp ho
    obtain ⟨b, hb, hbz⟩ := mem_radIn.mp (mem_cs.mp hz)
    have hz' : z = t * (b : G) * t⁻¹ := by
      rw [hbz]
      group
    have hpsi : (a : G) * z = P.psi e (e a, e b) := by
      rw [P.psi_apply, hz']
      simp
    rw [hpsi]
    exact (hmemW _).mp ⟨ha, hb⟩

end CFSG.OddStandard.Seitz77
