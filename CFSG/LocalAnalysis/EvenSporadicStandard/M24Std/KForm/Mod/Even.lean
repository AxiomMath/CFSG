module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.Defs

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open Subgroup CFSG CFSG.Open CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem z2s6_mod_even_inner (hBT : EvenLieInvolutionTwoConstrained) {S : Type} [Group S] [Finite S]
    (hinj : Function.Injective (MulAut.conj : S →* MulAut S)) (heven : EvenLieType S)
    {σ : MulAut S} {J : Subgroup ↥(fixedSubgroup σ)} (hdata : Z2S6ModData S σ J)
    (hin : σ ∈ (MulAut.conj : S →* MulAut S).range) : False := by
  obtain ⟨u, hu⟩ := hin
  have hu2 : orderOf u = 2 := by
    rw [← orderOf_injective (MulAut.conj : S →* MulAut S) hinj u, hu]
    exact hdata.order_two
  have hfix : fixedSubgroup σ = centralizer ({u} : Set S) := by
    rw [← hu]
    ext x
    rw [mem_centralizer_singleton_iff]
    change u * x * u⁻¹ = x ↔ x * u = u * x
    rw [mul_inv_eq_iff_eq_mul]
    exact eq_comm
  let φ := MulEquiv.subgroupCongr hfix
  have hpc : CFSG.pCore 2 ↥(centralizer ({u} : Set S)) ≤
      center ↥(centralizer ({u} : Set S)) := by
    intro y hy
    rw [← CFSG.pCore_map_iso 2 φ] at hy
    rcases hy with ⟨x, hx, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨w, rfl⟩ := φ.surjective z
    calc φ w * φ x = φ (w * x) := (map_mul φ w x).symm
      _ = φ (x * w) := by
        rw [Subgroup.mem_center_iff.mp (hdata.pCore_le_center hx) w]
      _ = φ x * φ w := map_mul φ x w
  have htop : CFSG.pCore 2 ↥(centralizer ({u} : Set S)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    refine hBT S heven u hu2 ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_center_iff.mp (hpc hy) x).symm
  have hP : IsPGroup 2 ↥(centralizer ({u} : Set S)) := by
    have hp : IsPGroup 2 (⊤ : Subgroup ↥(centralizer ({u} : Set S))) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥(centralizer ({u} : Set S)))).to_le
        (le_of_eq htop.symm)
    exact hp.of_equiv Subgroup.topEquiv
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hcard : Nat.card ↥(fixedSubgroup σ) = 2 ^ k := by
    rw [Nat.card_congr φ.toEquiv, hk]
  have h3 : 3 ∣ 2 ^ k := by
    have h := dvd_trans (by norm_num : 3 ∣ 360) hdata.dvd_card
    rwa [hcard] at h
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

theorem z2s6_mod_even_outer (hEL : EvenOuterA6LeafMod) {S : Type} [Group S] [Finite S]
    (heven : EvenLieType S) {σ : MulAut S} {J : Subgroup ↥(fixedSubgroup σ)}
    (hdata : Z2S6ModData S σ J) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) :
    Z2S6Socle S :=
  hEL S heven σ hdata.order_two hout J hdata

theorem z2s6_mod_even_arm (hBT : EvenLieInvolutionTwoConstrained) (hEL : EvenOuterA6LeafMod)
    {S : Type} [Group S] [Finite S] (hinj : Function.Injective (MulAut.conj : S →* MulAut S))
    (heven : EvenLieType S) {σ : MulAut S} {J : Subgroup ↥(fixedSubgroup σ)}
    (hdata : Z2S6ModData S σ J) : Z2S6Socle S := by
  by_cases hin : σ ∈ (MulAut.conj : S →* MulAut S).range
  · exact (z2s6_mod_even_inner hBT hinj heven hdata hin).elim
  · exact z2s6_mod_even_outer hEL heven hdata hin

end CFSG.EvenSporadicStandard.M24Std.KForm.Mod
