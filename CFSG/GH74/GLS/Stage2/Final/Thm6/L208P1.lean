module

public import CFSG.GH74.GLS.Stage2.Final.M12Odd

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L208Key

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage1.Thm6.Prod CFSG.GH74.GLS.Stage2.Final

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

theorem oddCore_eq_bot_of_key {k : Kind} (hctx : Stage2Ctx G z k S) (hmax : IsCoatom (Cen z))
    {U : Subgroup G} (hU4 : IVK.IsFourSubgroup U) (hzU : z ∈ U)
    (hAut : AutOrd (⊤ : Subgroup G) U = 6)
    (key : ∀ g ∈ normalizer (U : Set G), g * z * g⁻¹ ≠ z → ∀ a ∈ OddCore z, g * a * g⁻¹ ∈ OddCore z) :
    pPrimeCore 2 ↥(Cen z) = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hz2 : orderOf z = 2 := hctx.central.1
  have hz1 : z ≠ 1 := by intro e; rw [e, orderOf_one] at hz2; omega
  obtain ⟨g, hgN, hgz⟩ := exists_move_of_autOrd hU4 hzU hz1 hAut
  have hkey := key g hgN hgz
  have hconj_le : (OddCore z).map (MulAut.conj g).toMonoidHom ≤ OddCore z := by
    rintro _ ⟨a, ha, rfl⟩
    exact hkey a ha
  have hconj_eq : (OddCore z).map (MulAut.conj g).toMonoidHom = OddCore z := by
    apply Subgroup.eq_of_le_of_card_ge hconj_le
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hgA : g ∈ normalizer ((OddCore z : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx; exact hkey x hx
    · intro hx
      have : g * x * g⁻¹ ∈ (OddCore z).map (MulAut.conj g).toMonoidHom := by rw [hconj_eq]; exact hx
      obtain ⟨y, hy, hyx⟩ := this
      have : y = x := by
        have h1 : g * y * g⁻¹ = g * x * g⁻¹ := hyx
        simpa using h1
      rw [← this]
      exact hy
  rcases (hmax.le_iff.1 (Cen_le_normalizer_OddCore z)) with hN | hN
  ·
    have hnorm : (OddCore z).Normal := Subgroup.normalizer_eq_top_iff.1 hN
    have := hnorm
    rcases (hctx.std.kps.1).eq_bot_or_eq_top_of_normal (OddCore z) with hbot | htop
    · apply hne
      have : (pPrimeCore 2 ↥(Cen z)).map (Cen z).subtype = ⊥ := hbot
      exact (Subgroup.map_eq_bot_iff_of_injective (pPrimeCore 2 ↥(Cen z))
        (Cen z).subtype_injective).1 this
    · have hzA : z ∈ OddCore z := by rw [htop]; exact mem_top z
      have := coprime_orderOf_of_mem_OddCore hzA
      rw [hz2] at this
      exact absurd this (by norm_num)
  ·
    rw [hN] at hgA
    have := Subgroup.mem_centralizer_singleton_iff.1 hgA
    apply hgz
    rw [this]
    group

end CFSG.GH74.GLS.Stage2.Final.Thm6.L208Key
