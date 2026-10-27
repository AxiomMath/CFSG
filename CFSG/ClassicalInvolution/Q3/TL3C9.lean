module

public import CFSG.ClassicalInvolution.Q3.TL3S8Mu
public import CFSG.ClassicalInvolution.Q3.TL3C1
public import CFSG.ClassicalInvolution.Q3.TL3GlueJ
public import CFSG.ClassicalInvolution.Q3.TL3C7

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

@[expose] def TightOddCent {Y : Type} [Group Y] (t : Y) : Prop :=
  oddCoreImg (Subgroup.centralizer ({t} : Set Y)) = ⊥

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem TightDatum.oddCoreImg_eq_bot (hd : TightDatum R S t) (hO : TightOddCent t) :
    oddCoreImg R = ⊥ := by
  rw [eq_bot_iff, ← hO]
  have hodd : Odd (Nat.card ↥(oddCoreImg R)) :=
    (CFSG.ComponentClassification.OddCore.odd_card ↥R).of_dvd_nat (Subgroup.card_map_dvd _ _)
  refine TC.le_oddCoreImg_of_normalizes ((oddCoreImg_le R).trans hd.cent) ?_ hodd
  intro e he n hn
  have hnR : n ∈ R := oddCoreImg_le R hn
  have h1 : e * n * e⁻¹ ∈ R :=
    (Subgroup.mem_normalizer_iff.mp (hd.le_normalizer he) n).mp hnR
  refine hd.mem_oddCoreImg_of_odd h1 ?_
  have h2 : orderOf (e * n * e⁻¹) = orderOf n := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
  rw [h2]
  have h3 : orderOf n ∣ Nat.card ↥(oddCoreImg R) := Subgroup.orderOf_dvd_natCard _ hn
  exact hodd.of_dvd_nat h3

theorem TightDatum.isPGroup_of_oddCent (hd : TightDatum R S t) (hO : TightOddCent t) :
    IsPGroup 2 R := by
  have hR := hd.oddCoreImg_eq_bot hO
  have hbot : classicalInvolutionOddCore ↥R = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : (x : Y) ∈ oddCoreImg R := ⟨x, hx, rfl⟩
    rw [hR, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (Subtype.ext this)
  intro r
  obtain ⟨k, hk⟩ := hd.twoGroup (QuotientGroup.mk' (classicalInvolutionOddCore ↥R) r)
  refine ⟨k, ?_⟩
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hbot] at hk
  exact (Subgroup.mem_bot).mp hk

omit [Finite Y] in
theorem tightCore_eq_self_of_isPGroup (h2 : IsPGroup 2 R) : tightCore R = R := by
  refine le_antisymm (tightCore_le R) fun x hx => Subgroup.subset_closure ⟨hx, ?_⟩
  exact h2.to_le (Subgroup.zpowers_le.mpr hx)

theorem TightDatum.isPGroup_member (hd : TightDatum R S t) (hO : TightOddCent t) :
    ∀ J ∈ CoreAssembly.conjClass (tightCore R), IsPGroup 2 J := by
  intro J hJ
  obtain ⟨g, rfl⟩ := CoreAssembly.single_class (tightCore R) J hJ
  have h2 := hd.isPGroup_of_oddCent hO
  rw [tightCore_eq_self_of_isPGroup h2]
  exact h2.map (MulAut.conj g).toMonoidHom

theorem TightDatum.isNormalTwoIn_member (hd : TightDatum R S t) (hO : TightOddCent t)
    {J : Subgroup Y} (hJ : J ∈ CoreAssembly.conjClass (tightCore R)) {u : Y}
    (hu : IsUniqueInvolution J u) : TC.IsNormalTwoIn J u := by
  have hN := hd.normalizer_eq_centralizer_member hJ hu
  refine ⟨fun j hj => ?_, hd.isPGroup_member hO J hJ, fun c hc p hp => ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have hjN : j ∈ Subgroup.normalizer (J : Set Y) := Subgroup.le_normalizer hj
    rw [hN, Subgroup.mem_centralizer_singleton_iff] at hjN
    exact hjN
  · rw [← hN] at hc
    exact (Subgroup.mem_normalizer_iff.mp hc p).mp hp

theorem TightDatum.uAt_self (hd : TightDatum R S t) (hO : TightOddCent t) :
    ∀ L ∈ CoreAssembly.conjClass (tightCore R), ∀ u : Y, IsUniqueInvolution L u →
      TC.UAt (CoreAssembly.conjClass (tightCore R)) u L := by
  intro L hL u hu
  have h2 := hd.isPGroup_member hO L hL
  have hLs : IsSylow2In L L := ⟨le_rfl, h2, fun Q hQL _ hLQ => le_antisymm hQL hLQ⟩
  obtain ⟨U, hU, hUL, -⟩ := Sec6Gen.exists_invariant_mem_USet hd.hypOmegaGen hL hLs h2 le_rfl
    fun q hq => conjSub_eq_self_of_mem hq
  exact ⟨U, hU, hUL, L, hd.isNormalTwoIn_member hO hL hu, hUL⟩

end CFSG.ClassicalInvolution.Q3
