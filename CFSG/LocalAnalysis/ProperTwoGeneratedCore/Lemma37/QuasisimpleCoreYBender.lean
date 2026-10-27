module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreYCenter

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {X : Type} [Group X] [Finite X]

namespace OneComponent

variable {Y : Subgroup X} {e v : X} {L : Subgroup X}

theorem isStronglyEmbeddedOrder_map (hL : OneComponent Y e v L) (hc : BaseConfig Y e)
    (hv : v * v = e) (hvn : (Subgroup.zpowers v).Normal)
    (hZ : Nat.card (Subgroup.center L) = 2) :
    CFSG.BenderSuzuki.IsStronglyEmbeddedOrder
      ((Y.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center L))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (Subgroup.center L) with hπdef
  set Bs := (Y.subgroupOf L).map π with hBs
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Y.subgroupOf L := by
    rw [QuotientGroup.ker_mk']
    exact hL.center_le_subgroupOf hc
  have hmemB : ∀ l : L, π l ∈ Bs ↔ (l : X) ∈ Y := fun l => by
    rw [← Subgroup.mem_comap, hBs, Subgroup.comap_map_eq_self hker, Subgroup.mem_subgroupOf]
  have hvY : v ∈ Y := hc.twoCore_le (hc.mem_twoCore_of_sq hv hvn)
  have hvc : ∀ l : L, (l : X) * v = v * l := fun l =>
    Subgroup.mem_centralizer_iff.mp hL.mem_centralizer l l.2
  refine ⟨CyclicCase.map_ne_top_of_ker_le π hker hL.subgroupOf_ne_top, ?_, fun g hg => ?_⟩
  ·
    obtain ⟨S, hSB, -⟩ := hL.exists_sylow_le hc
    let Ss : Sylow 2 (L ⧸ Subgroup.center L) := S.mapSurjective hπ
    have hSs : (Ss : Subgroup (L ⧸ Subgroup.center L)) = (S : Subgroup L).map π :=
      Sylow.coe_mapSurjective _ _
    have hne : (Ss : Subgroup (L ⧸ Subgroup.center L)) ≠ ⊥ :=
      Ss.ne_bot_of_dvd_card (even_iff_two_dvd.mp (hL.even_card_quotient hc))
    obtain ⟨n, hn⟩ := Ss.isPGroup'.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hne (Subgroup.card_eq_one.mp (by rw [hn, pow_zero]))
    have h2 : 2 ∣ Nat.card ((S : Subgroup L).map π) := by
      rw [← hSs, hn]
      exact dvd_pow_self 2 hn0
    exact even_iff_two_dvd.mpr (h2.trans (Subgroup.card_dvd_of_le (Subgroup.map_mono hSB)))
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hodd)
  obtain ⟨hwB, hwg⟩ := Subgroup.mem_inf.mp w.2
  obtain ⟨b, hbB, hbw⟩ := Subgroup.mem_map.mp hwg
  obtain ⟨l, rfl⟩ := hπ g
  obtain ⟨a, ha⟩ := hπ (w : L ⧸ Subgroup.center L)
  have hw2 : orderOf (π a) = 2 := by
    rw [ha, Subgroup.orderOf_coe]
    exact hw
  have hlY : (l : X) ∉ Y := fun h => hg ((hmemB l).mpr h)
  have haY : (a : X) ∈ Y := (hmemB a).mp (ha ▸ hwB)
  have hlaY : (l : X)⁻¹ * a * l ∈ Y := by
    have hb : b = π (l⁻¹ * a * l) := by
      rw [map_mul, map_mul, map_inv, ha, ← hbw]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have h := (hmemB _).mp (hb ▸ hbB)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h
  have haZ : a ∉ Subgroup.center L := fun h => by
    rw [show π a = 1 from (QuotientGroup.eq_one_iff a).mpr h, orderOf_one] at hw2
    exact absurd hw2 (by decide)
  have haa : a * a ∈ Subgroup.center L := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, ← pow_two, ← hw2]
    exact pow_orderOf_eq_one _
  have hae : (a : X) ≠ e := fun h => haZ (by
    rw [show a = ⟨e, hL.mem⟩ from Subtype.ext h]
    exact hL.mem_center hc)
  rcases hL.eq_one_or_eq_of_card_two hc hZ haa with h1 | he
  ·
    have ha2 : orderOf (a : X) = 2 := by
      rw [Subgroup.orderOf_coe]
      refine orderOf_eq_prime (by rw [pow_two]; exact h1) fun h => haZ (h ▸ Subgroup.one_mem _)
    exact hlY (hc.mem_of_conj_mem haY ha2 hae hlaY)
  ·
    obtain ⟨hva2, hvae⟩ := hL.mul_involution_of_card_two hc hv hZ a.2 he
    have hconj : (l : X)⁻¹ * (v * a) * l = v * ((l : X)⁻¹ * a * l) := by
      have hlv : (l : X)⁻¹ * v = v * (l : X)⁻¹ := by
        have := hvc l⁻¹
        simpa only [Subgroup.coe_inv] using this
      calc (l : X)⁻¹ * (v * a) * l = (l : X)⁻¹ * v * a * l := by group
        _ = v * (l : X)⁻¹ * a * l := by rw [hlv]
        _ = v * ((l : X)⁻¹ * a * l) := by group
    exact hlY (hc.mem_of_conj_mem (Y.mul_mem hvY haY) hva2 hvae
      (hconj ▸ Y.mul_mem hvY hlaY))

theorem cover_of_card_two
    (hL : OneComponent Y e v L) (hc : BaseConfig Y e) (hv : v * v = e)
    (hvn : (Subgroup.zpowers v).Normal) (hZ : Nat.card (Subgroup.center L) = 2) :
    Nonempty (L ⧸ Subgroup.center L ≃* CFSG.Theory.Comparator.PSL2Model 2) ∨
      Nonempty (L ⧸ Subgroup.center L ≃* ↥(CFSG.Theory.Comparator.SzModel 1)) := by
  have := hL.simple
  exact bender_cover_quotient hL.perfect hZ
    (CFSG.BenderSuzuki.bender_suzuki _ (hL.isStronglyEmbeddedOrder_map hc hv hvn hZ))

theorem center_card_and_cover
    (hL : OneComponent Y e v L) (hc : BaseConfig Y e)
    (hv : v * v = e) (hvn : (Subgroup.zpowers v).Normal) (IH : CanonicalBelow (Nat.card X)) :
    Nat.card (Subgroup.center L) = 2 ∧ v ∉ L ∧
      (Nonempty (L ⧸ Subgroup.center L ≃* CFSG.Theory.Comparator.PSL2Model 2) ∨
        Nonempty (L ⧸ Subgroup.center L ≃* ↥(CFSG.Theory.Comparator.SzModel 1))) := by
  have hZ := hL.center_card_eq_two hc IH
  exact ⟨hZ, hL.not_mem_of_card_two hc hv hZ, hL.cover_of_card_two hc hv hvn hZ⟩

end OneComponent

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
