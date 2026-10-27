module

public import CFSG.ClassicalInvolution.Q3.Q3AM289S4LSU01
public import CFSG.ClassicalInvolution.Q3.Q3AM289S4LSU03
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Q3.Q3PP (F9 card_F9 two_ne_zero_F9)

section Frame

variable {X : Type} [Group X] {Φ : Set (Subgroup X)} {zb : X}

theorem isUniqueInvolution_map_LcU {ψ : Su F9 3 1 4 →* X}
    (hk : ψ.ker ≤ Subgroup.center (Su F9 3 1 4)) (T : Pair 4) :
    IsUniqueInvolution ((LcU F9 3 1 T).map ψ) (ψ (zEltU F9 3 1 T)) :=
  isUniqueInvolution_map ψ hk (isUniqueInvolution_LcU card_F9 (by norm_num) (by norm_num) T)
    fun _ hy hc => LcU_center T hy hc

theorem s4Frame_su4 (ψ : Su F9 3 1 4 →* X) (hs : Function.Surjective ψ)
    (hk : ψ.ker ≤ Subgroup.center (Su F9 3 1 4)) {z : Su F9 3 1 4}
    (hz : z ∈ Subgroup.center (Su F9 3 1 4)) (hzb : ψ z = zb)
    (hΦ : ∀ T : Pair 4, (LcU F9 3 1 T).map ψ ∈ Φ) :
    S4Frame Φ zb (ψ (zEltU F9 3 1 pair01)) := by
  subst hzb
  obtain ⟨i, hi, hσi⟩ := Q3MFOU4.exists_iota
  have hU := isUniqueInvolution_map_LcU hk
  have hz1 : ψ (zEltU F9 3 1 pair01) * ψ (zEltU F9 3 1 pair01) = 1 := by
    rw [← map_mul, zEltU_mul_self, map_one]
  have hz2 : ψ (zEltU F9 3 1 pair02) * ψ (zEltU F9 3 1 pair02) = 1 := by
    rw [← map_mul, zEltU_mul_self, map_one]
  have hu2 : ψ (uElt hi hσi) * ψ (uElt hi hσi) = ψ (zEltU F9 3 1 pair02) := by
    rw [← map_mul, uElt_mul_self]
  have hz3 : zEltU F9 3 1 pair12 ∉ Subgroup.center (Su F9 3 1 4) := fun hc =>
    zEltU_ne_one two_ne_zero_F9 pair12 (LcU_center pair12
      (isUniqueInvolution_LcU card_F9 (by norm_num) (by norm_num) pair12).mem hc)
  have hne : ∀ c ∈ Subgroup.center (Su F9 3 1 4),
      ψ (zEltU F9 3 1 pair02) ≠ ψ c * ψ (zEltU F9 3 1 pair01) := by
    intro c hc h
    apply hz3
    have h1 : ψ (zEltU F9 3 1 pair12 * c⁻¹) = 1 := by
      have e : zEltU F9 3 1 pair12 * c⁻¹ =
          zEltU F9 3 1 pair02 * zEltU F9 3 1 pair01 * c⁻¹ := by
        rw [zEltU_pair02_mul_pair01]
      rw [e, map_mul, map_mul, map_inv, h]
      calc ψ c * ψ (zEltU F9 3 1 pair01) * ψ (zEltU F9 3 1 pair01) * (ψ c)⁻¹
          = ψ c * (ψ (zEltU F9 3 1 pair01) * ψ (zEltU F9 3 1 pair01)) * (ψ c)⁻¹ := by
            rw [mul_assoc (ψ c)]
        _ = 1 := by rw [hz1, mul_one, mul_inv_cancel]
    have h2 := Subgroup.mul_mem _ (hk (MonoidHom.mem_ker.mpr h1)) hc
    rwa [inv_mul_cancel_right] at h2
  have hsq : ψ (uElt hi hσi) ^ 2 = ψ (zEltU F9 3 1 pair02) := by rw [pow_two, hu2]
  have hord : orderOf (ψ (uElt hi hσi)) = 4 := by
    refine (orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_).trans (by norm_num)
    · rw [pow_one, hsq]
      exact (hU pair02).ne_one
    · rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, hsq, pow_two, hz2]
  refine ⟨(LcU F9 3 1 pair02).map ψ, hΦ pair02, ψ (zEltU F9 3 1 pair02), ψ (uElt hi hσi),
    hU pair02, ?_, ?_, ?_, Subgroup.mem_map_of_mem ψ (uElt_mem_LcU hi hσi), hord, hu2, ?_,
    ⟨(LcU F9 3 1 pair12).map ψ, hΦ pair12, ?_⟩, ?_⟩
  · intro h
    exact hne 1 (Subgroup.one_mem _) (by rw [map_one, one_mul]; exact h)
  · intro h
    exact hne z hz h
  · rw [← map_mul, ← map_mul, zEltU_pair01_mul_pair02, zEltU_pair02_mul_pair01]
  · rw [← map_mul, ← map_mul, uElt_comm]
  · rw [← map_mul, zEltU_pair01_mul_pair02]
    exact hU pair12
  ·
    have hmap : ∀ w : Su F9 3 1 4, (Subgroup.centralizer ({w} : Set (Su F9 3 1 4))).map ψ ≤
        Subgroup.centralizer ({ψ w} : Set X) := by
      intro w
      rintro _ ⟨g, hg, rfl⟩
      have hg' := Subgroup.mem_centralizer_singleton_iff.mp hg
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      rw [← map_mul, ← map_mul, hg']
    rw [eq_top_iff]
    calc (⊤ : Subgroup X) = (⊤ : Subgroup (Su F9 3 1 4)).map ψ :=
          (Subgroup.map_top_of_surjective ψ hs).symm
      _ = (Subgroup.centralizer ({zEltU F9 3 1 pair01} : Set (Su F9 3 1 4)) ⊔
            Subgroup.centralizer ({zEltU F9 3 1 pair02} : Set (Su F9 3 1 4))).map ψ := by
          rw [centralizer_pair01_sup_pair02]
      _ = (Subgroup.centralizer ({zEltU F9 3 1 pair01} : Set (Su F9 3 1 4))).map ψ ⊔
            (Subgroup.centralizer ({zEltU F9 3 1 pair02} : Set (Su F9 3 1 4))).map ψ :=
          Subgroup.map_sup _ _ _
      _ ≤ Subgroup.centralizer ({ψ (zEltU F9 3 1 pair01)} : Set X) ⊔
            Subgroup.centralizer ({ψ (zEltU F9 3 1 pair02)} : Set X) :=
          sup_le_sup (hmap _) (hmap _)
      _ ≤ _ := le_sup_left

end Frame

section Leaf


theorem s4LinkModelLeafAt_su4 : S4LinkModelLeafAt (CompData.model .PSU 4) := by
  intro X _ _ Φ zb hΦ hlay _ A hA a ha
  obtain ⟨ψ, hs, hk, hΦ1, z, hz, hzb⟩ := hlay.exists_su4_hom
  obtain ⟨R₀, hR₀, hAR⟩ := hΦ1 A hA
  have hmem : ∀ R ∈ longRootSetU (K := F9) (p := 3) (f := 1) (show 2 ≤ 4 by norm_num),
      R.map ψ ∈ Φ := fun R hR => by
    obtain ⟨g, hg⟩ := exists_conj_map_longRoot ψ hR₀ hR
    rw [hg, ← hAR]
    exact hΦ g A hA
  have hmemLc : ∀ T : Pair 4, (LcU F9 3 1 T).map ψ ∈ Φ := fun T =>
    hmem _ (LcU_mem_longRootSetU two_ne_zero_F9 _ T)
  have htrans : ∀ A ∈ Φ, ∀ B ∈ Φ, ∃ g : X, conjSub g A = B := by
    intro A' hA' B hB
    obtain ⟨R₁, hR₁, rfl⟩ := hΦ1 A' hA'
    obtain ⟨R₂, hR₂, rfl⟩ := hΦ1 B hB
    obtain ⟨g, hg⟩ := exists_conj_map_longRoot ψ hR₁ hR₂
    exact ⟨g, hg.symm⟩
  exact s4Frame_of_exists hlay.zb_mem_center hΦ htrans (hmemLc pair01)
    (isUniqueInvolution_map_LcU hk pair01) (s4Frame_su4 ψ hs hk hz hzb hmemLc) hA ha

end Leaf

end CFSG.ClassicalInvolution.Q3.Q3AM
