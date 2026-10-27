module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdLeaves
public import CFSG.ClassicalInvolution.Q3.TL4SecIdDatum

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups

theorem sl2Three_pow_four_of_pow_eight : ∀ a : SL(2, ZMod 3), a ^ 8 = 1 → a ^ 4 = 1 := by
  decide +kernel

theorem mem_sl2ThreeQ_of_isPGroup {a : SL(2, ZMod 3)} (ha : IsPGroup 2 (Subgroup.zpowers a)) :
    a ∈ sl2ThreeQ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp ha
  rw [Nat.card_zpowers] at hm
  have h24 : orderOf a ∣ 8 * 3 := by
    have h := orderOf_dvd_natCard a
    rwa [natCard_sl2Three] at h
  have h8 : orderOf a ∣ 8 := by
    rw [hm] at h24 ⊢
    exact (Nat.Coprime.pow_left m (by norm_num : Nat.Coprime 2 3)).dvd_of_dvd_mul_right h24
  exact mem_sl2ThreeQ_iff.mpr
    (sl2Three_pow_four_of_pow_eight a (orderOf_dvd_iff_pow_eq_one.mp h8))

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem isPGroup_of_inO2 (hd : TightDatum R S t) (hO : TightOddFree Y) (hE2 : TightInO2 t) :
    IsPGroup 2 ↥R := by
  obtain ⟨P, hPn, hP2, htP⟩ := hE2
  exact hd.isPGroup_of_oddCent (TC.oddCoreImg_centralizer_eq_bot hO hPn hP2 htP)

section Cit3


theorem SecIdLie3.isPGroup_core (hl : SecIdLie3 R t) (hO : TightOddFree Y) :
    IsPGroup 2 ↥(tightCore R) := by
  obtain ⟨L, hKL, hL, -, ι, _, ⟨D⟩⟩ := hl
  have hinj : Function.Injective (QuotientGroup.mk' (classicalInvolutionOddCore Y)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact hO
  have h24 : Nat.card ↥L = 24 := by
    rw [← D.card_eq _ ⟨L, CoreAssembly.mem_conjClass_self L, rfl⟩]
    exact Nat.card_congr (L.equivMapOfInjective _ hinj).toEquiv
  obtain ⟨e⟩ := hL.nonempty_equiv
  have hq : Nat.card (↥L ⧸ classicalInvolutionOddCore ↥L) = 24 := by
    rw [Nat.card_congr e.toEquiv, natCard_sl2Three]
  have hOL : classicalInvolutionOddCore ↥L = ⊥ := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (classicalInvolutionOddCore ↥L)
    rw [h24, hq] at h
    exact Subgroup.eq_bot_of_card_eq _ (by omega)
  obtain ⟨f⟩ := hL.nonempty_equiv_sl2 hOL
  have hQ : IsPGroup 2 ↥sl2ThreeQ := IsPGroup.of_card (n := 3) (by rw [natCard_sl2ThreeQ]; rfl)
  have hP : IsPGroup 2 ↥((sl2ThreeQ.comap f.toMonoidHom).map L.subtype) :=
    (hQ.comap_of_injective f.toMonoidHom f.injective).map L.subtype
  refine hP.to_le ?_
  show Subgroup.closure {x : Y | x ∈ R ∧ IsPGroup 2 (Subgroup.zpowers x)} ≤ _
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hxR, hx2⟩
  have hxL : x ∈ L := hKL (Subgroup.subset_closure ⟨hxR, hx2⟩)
  refine ⟨⟨x, hxL⟩, ?_, rfl⟩
  show f ⟨x, hxL⟩ ∈ sl2ThreeQ
  apply mem_sl2ThreeQ_of_isPGroup
  have h1 : IsPGroup 2 (Subgroup.zpowers (⟨x, hxL⟩ : ↥L)) := isPGroup_zpowers_coe_iff.mp hx2
  have h2 := h1.map f.toMonoidHom
  rwa [MonoidHom.map_zpowers] at h2

theorem isPGroup_core_of_secIdentOut3 (hE4 : SecIdE4OddCent) (hd : TightDatum R S t)
    (hc : TightCls Y R S t) (h : SecIdentOut3 Y R t) (hedge : ¬ TightEdgeless R) :
    IsPGroup 2 ↥(tightCore R) := by
  rcases h with h2 | ⟨he, -⟩ | ⟨he, -⟩ | ⟨hZ, h4⟩ | hl
  · exact (isPGroup_of_inO2 hd hc.2.2 h2).to_le (tightCore_le R)
  · exact absurd he hedge
  · exact absurd he hedge
  · by_cases hE2 : TightInO2 t
    · exact (isPGroup_of_inO2 hd hc.2.2 hE2).to_le (tightCore_le R)
    · exact (hd.isPGroup_of_oddCent (hE4 Y R S t hd hc hE2 hZ h4)).to_le (tightCore_le R)
  · exact hl.isPGroup_core hc.2.2

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
