module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.CatZ2S6Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Reduction.RHyp

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open Subgroup

variable {F : Type} [Group F] [Finite F] (Φ : F →* Z2S6)

theorem snd_eq_one_of_mem_centralizer_a6Factor {x : Z2S6}
    (hx : x ∈ centralizer (a6Factor : Set Z2S6)) : x.2 = 1 := by
  refine CFSG.EvenSporadicStandard.HSStd.InvCent.RHyp.eq_one_of_commute
    (CFSG.EvenSporadicStandard.M24Std.KForm.Reduction.rhyp_perm6) (x := x.2) ?_
  intro a ha
  have hy : ((1 : Multiplicative (ZMod 2)), a) ∈ a6Factor := mem_a6Factor.2 ⟨rfl, ha⟩
  have h := Subgroup.mem_centralizer_iff.1 hx _ hy
  exact (congrArg Prod.snd h).symm

private theorem eq_one_of_mem_odd_of_pow_two_pow_eq_one' {W : Subgroup F}
    (hW : Odd (Nat.card W)) {x : F} (hx : x ∈ W) {k : ℕ} (hk : x ^ 2 ^ k = 1) : x = 1 := by
  have hdiv1 : orderOf x ∣ Nat.card W := Subgroup.orderOf_dvd_natCard W hx
  have hdiv2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hodd : Odd (orderOf x) := hW.of_dvd_nat hdiv1
  obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv2
  have hj0 : j = 0 := by
    by_contra hj
    exact (Nat.not_even_iff_odd.mpr (hjeq ▸ hodd))
      (even_iff_two_dvd.mpr (dvd_pow_self 2 hj))
  exact orderOf_eq_one_iff.mp (hjeq.trans (by rw [hj0, pow_zero]))

theorem natCard_le_two_of_le_centralizer (hodd : Odd (Nat.card Φ.ker)) {J : Subgroup F}
    (hJ : J.map Φ = a6Factor) {U : Subgroup F} (hU : IsPGroup 2 U)
    (hUJ : U ≤ centralizer (J : Set F)) : Nat.card U ≤ 2 := by
  have hInjU : Function.Injective (fun u : U => Φ (u : F)) := by
    intro u v huv
    have hwker : (u : F) * (v : F)⁻¹ ∈ Φ.ker := by
      simp only [MonoidHom.mem_ker, map_mul, map_inv, huv, mul_inv_cancel]
    have hwU : (u : F) * (v : F)⁻¹ ∈ U := U.mul_mem u.2 (U.inv_mem v.2)
    obtain ⟨k, hk⟩ := hU.exists_pow_pow_eq_one ⟨(u : F) * (v : F)⁻¹, hwU⟩
    have h1 : (u : F) * (v : F)⁻¹ = 1 :=
      eq_one_of_mem_odd_of_pow_two_pow_eq_one' hodd hwker (k := k) (by simpa using hk)
    exact Subtype.ext (mul_inv_eq_one.mp h1)
  have hmap_le : U.map Φ ≤ centralizer (a6Factor : Set Z2S6) := by
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨u, hu, rfl⟩ := hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' : z ∈ J.map Φ := hJ.symm ▸ hz
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hz'
    have hcomm : j * u = u * j := by
      have h' := hUJ hu
      rw [Subgroup.mem_centralizer_iff] at h'
      exact h' j hj
    rw [← map_mul, ← map_mul, hcomm]
  have hf_inj : Function.Injective (fun u : U => (Φ (u : F)).1) := by
    intro u v huv
    apply hInjU
    refine Prod.ext huv ?_
    rw [snd_eq_one_of_mem_centralizer_a6Factor (hmap_le (Subgroup.mem_map_of_mem Φ u.2)),
      snd_eq_one_of_mem_centralizer_a6Factor (hmap_le (Subgroup.mem_map_of_mem Φ v.2))]
  calc Nat.card U ≤ Nat.card (Multiplicative (ZMod 2)) :=
        Nat.card_le_card_of_injective _ hf_inj
    _ = 2 := by simp [Nat.card_eq_fintype_card]

end CFSG.EvenSporadicStandard.M24Std.KForm.Mod
