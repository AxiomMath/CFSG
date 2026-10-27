module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.Adapters.QiuzhenLegacy.GorensteinWalter.ConjClassCount

public section

namespace CFSG.EvenSporadicStandard.HSStd.HL34

open CFSG.ComponentClassification.PSL3Four Subgroup

theorem card_carrier_mul_card_centralizer {G : Type*} [Group G] [Finite G] (x : G) :
    Nat.card (ConjClasses.mk x).carrier * Nat.card (centralizer ({x} : Set G)) = Nat.card G := by
  rw [← CFSG.EvenSporadicStandard.SuzOuter.card_conj_mul_card_centralizer x]
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
  rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := h
    exact ⟨c⁻¹, by rw [← hc]; group⟩
  · rintro ⟨c, hc⟩
    exact ⟨c⁻¹, by rw [hc]; group⟩

theorem mem_inf_centralizer_conj {c y x : Equiv.Perm (Fin 42)}
    (hc : c ∈ R) :
    y ∈ centralizer ({c * x * c⁻¹} : Set (Equiv.Perm (Fin 42))) ⊓ S ↔
      c⁻¹ * y * c ∈ centralizer ({x} : Set (Equiv.Perm (Fin 42))) ⊓ S := by
  have hS : y ∈ S ↔ c⁻¹ * y * c ∈ S := by
    constructor
    · intro h
      simpa using conj_mem_S (R.inv_mem hc) h
    · intro h
      have := conj_mem_S hc h
      simpa [mul_assoc] using this
  have hC : y ∈ centralizer ({c * x * c⁻¹} : Set (Equiv.Perm (Fin 42))) ↔
      c⁻¹ * y * c ∈ centralizer ({x} : Set (Equiv.Perm (Fin 42))) := by
    rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc (c⁻¹ * y * c) * x = c⁻¹ * (y * (c * x * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * x * c⁻¹) * y) * c := by rw [h]
        _ = x * (c⁻¹ * y * c) := by group
    · intro h
      calc y * (c * x * c⁻¹) = c * ((c⁻¹ * y * c) * x) * c⁻¹ := by group
        _ = c * (x * (c⁻¹ * y * c)) * c⁻¹ := by rw [h]
        _ = (c * x * c⁻¹) * y := by group
  rw [mem_inf, mem_inf, hS, hC]

theorem card_inf_centralizer_conj {c : Equiv.Perm (Fin 42)}
    (hc : c ∈ R) (x : Equiv.Perm (Fin 42)) :
    Nat.card ↥(centralizer ({c * x * c⁻¹} : Set (Equiv.Perm (Fin 42))) ⊓ S) =
      Nat.card ↥(centralizer ({x} : Set (Equiv.Perm (Fin 42))) ⊓ S) :=
  Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj c⁻¹).toEquiv fun y => by
    simpa using mem_inf_centralizer_conj hc)

theorem orderOf_eq_two_of_mul_self {G : Type*} [Group G] {x : G} (hx : x * x = 1) (h1 : x ≠ 1) :
    orderOf x = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rwa [sq]) h1

theorem sixty_le_card_inf_centralizer (x : R) (hx : x * x = 1) :
    60 ≤ Nat.card ↥(centralizer ({(x : Equiv.Perm (Fin 42))} : Set (Equiv.Perm (Fin 42))) ⊓ S) := by
  by_cases h1 : x = 1
  · have hc : centralizer ({(x : Equiv.Perm (Fin 42))} : Set (Equiv.Perm (Fin 42))) = ⊤ := by
      rw [eq_top_iff]
      intro g _
      rw [mem_centralizer_singleton_iff, h1]
      simp
    rw [hc, top_inf_eq, card_S]
    norm_num
  · have hx2 := orderOf_eq_two_of_mul_self hx h1
    rcases (orderOf_eq_two_iff x).1 hx2 with h | h | h | h
    · obtain ⟨c, hc, hxc⟩ := eq_conj_of_isConj h
      rw [hxc, card_inf_centralizer_conj hc]
      exact card_C₁.symm ▸ (by norm_num)
    · obtain ⟨c, hc, hxc⟩ := eq_conj_of_isConj h
      rw [hxc, card_inf_centralizer_conj hc]
      exact card_C₂.symm ▸ (by norm_num)
    · obtain ⟨c, hc, hxc⟩ := eq_conj_of_isConj h
      rw [hxc, card_inf_centralizer_conj hc]
      exact card_C₃.symm ▸ (by norm_num)
    · obtain ⟨c, hc, hxc⟩ := eq_conj_of_isConj h
      rw [hxc, card_inf_centralizer_conj hc]
      exact card_C₄.symm ▸ (by norm_num)

theorem card_inf_centralizer_of_isConj_r₂ {x : R}
    (h : IsConj x r₂R) :
    Nat.card ↥(centralizer ({(x : Equiv.Perm (Fin 42))} : Set (Equiv.Perm (Fin 42))) ⊓ S) =
      168 := by
  obtain ⟨c, hc, hxc⟩ := eq_conj_of_isConj h
  rw [hxc, card_inf_centralizer_conj hc]
  exact card_C₂

theorem isConj_r₃_of_dvd {x : R} (hx : orderOf x = 2)
    (hd : 240 ∣ Nat.card ↥(centralizer ({x} : Set R))) : IsConj x r₃R := by
  have hk := card_carrier_mul_card_centralizer x
  rw [card_R] at hk
  rcases (orderOf_eq_two_iff x).1 hx with h | h | h | h
  · rw [(ConjClasses.mk_eq_mk_iff_isConj.2 h), conjClass₁.2] at hk
    omega
  · rw [(ConjClasses.mk_eq_mk_iff_isConj.2 h), conjClass₂.2] at hk
    omega
  · exact h
  · rw [(ConjClasses.mk_eq_mk_iff_isConj.2 h), conjClass₄.2] at hk
    omega

end CFSG.EvenSporadicStandard.HSStd.HL34
