module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitGH
public import CFSG.GroupTheory.PCore.PrimeSetCore

public section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup Blueprint HSFLit

@[expose] def ConclusionA (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* NativeSporadic.HS) ∨
    ∃ A K : Subgroup X, A.Normal ∧ Nonempty (A ≃* Multiplicative (ZMod 4 × ZMod 4 × ZMod 4)) ∧
      Nonempty (K ≃* GL (Fin 3) (ZMod 2)) ∧ A ⊓ K = ⊥ ∧ A ⊔ K = ⊤ ∧
      ∃ g ∈ K, ∃ a ∈ A, g * a * g⁻¹ ≠ a

@[expose] def TheoremACore : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsTypeHS G →
    (∀ N : Subgroup G, N.Normal → N.index ≠ 2) → pPrimeCore 2 G = ⊥ → ConclusionA G

variable {G : Type} [Group G] [Finite G]

theorem inf_pPrimeCore_eq_bot {P : Subgroup G} (hP : IsPGroup 2 P) :
    P ⊓ pPrimeCore 2 G = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hcop : Nat.Coprime (Nat.card P) (Nat.card (pPrimeCore 2 G)) := by
    rw [hk]
    exact Nat.Coprime.pow_left k pPrimeCore_coprime_card
  rw [← card_eq_one]
  exact Nat.eq_one_of_dvd_coprimes hcop (card_dvd_of_le inf_le_left)
    (card_dvd_of_le inf_le_right)

theorem nonempty_equiv_map_mk {P : Subgroup G} (hP : IsPGroup 2 P) :
    Nonempty (P ≃* P.map (QuotientGroup.mk' (pPrimeCore 2 G))) := by
  set f := (QuotientGroup.mk' (pPrimeCore 2 G)).comp P.subtype
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxO : (x : G) ∈ pPrimeCore 2 G := (QuotientGroup.eq_one_iff (x : G)).mp hx
    have hx' : (x : G) ∈ P ⊓ pPrimeCore 2 G := ⟨x.2, hxO⟩
    rw [inf_pPrimeCore_eq_bot hP, mem_bot] at hx'
    exact Subtype.ext hx'
  have hr : f.range = P.map (QuotientGroup.mk' (pPrimeCore 2 G)) := by
    rw [MonoidHom.range_comp, range_subtype]
  exact ⟨(MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hr)⟩

theorem isTypeHS_quotient (h : IsTypeHS G) : IsTypeHS (G ⧸ pPrimeCore 2 G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, Q, ⟨e⟩⟩ := h
  obtain ⟨e'⟩ := nonempty_equiv_map_mk P.isPGroup'
  exact ⟨P.mapSurjective (QuotientGroup.mk'_surjective _), Q, ⟨e'.symm.trans e⟩⟩

omit [Finite G] in
theorem index_ne_two_quotient (h : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) :
    ∀ N : Subgroup (G ⧸ pPrimeCore 2 G), N.Normal → N.index ≠ 2 := by
  intro N hN h2
  apply h (N.comap (QuotientGroup.mk' (pPrimeCore 2 G))) (hN.comap _)
  exact (index_comap_of_surjective (H := N) (QuotientGroup.mk'_surjective _)).trans h2

theorem gorensteinHarrisInput_of_core (h : TheoremACore) : GorensteinHarrisInput := by
  intro G _ _ hT hN
  exact h (G ⧸ pPrimeCore 2 G) (isTypeHS_quotient hT) (index_ne_two_quotient hN)
    (pPrimeCore_quotient_eq_bot Nat.prime_two)

end CFSG.ComponentClassification.GHarris
