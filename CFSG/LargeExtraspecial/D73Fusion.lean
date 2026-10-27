module

public import CFSG.LargeExtraspecial.D73Setting
public import CFSG.LargeExtraspecial.D73GLInv

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW.D73

open Subgroup
open scoped MatrixGroups

theorem exists_conj_commute_ne {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) {z : G} (hz : orderOf z = 2) :
    ∃ g : G, g * z * g⁻¹ * z = z * (g * z * g⁻¹) ∧ g * z * g⁻¹ ≠ z := by
  have : Fintype G := Fintype.ofFinite G
  have hz1 : z ≠ 1 := fun h => by simp [h] at hz
  have hzz : z * z = 1 := by rw [← pow_two, ← hz, pow_orderOf_eq_one]
  by_contra hcon
  push Not at hcon
  obtain ⟨K, hKn, hKodd, hK⟩ := CFSG.ZStar.glauberman_zStar G z hz1 hzz hcon
  rcases Subgroup.Normal.eq_bot_or_eq_top K with hbot | htop
  · have hcent : z ∈ center G := mem_center_iff.mpr fun g => by
      have h := hK g
      rw [hbot, mem_bot, mul_inv_eq_one] at h
      calc g * z = g * z * g⁻¹ * g := by group
        _ = z * g := by rw [h]
    have hc : center G = ⊥ := by
      rcases Subgroup.Normal.eq_bot_or_eq_top (center G) with h | h
      · exact h
      · obtain ⟨a, b, hab⟩ := hnab
        exact absurd (mem_center_iff.mp (h ▸ mem_top a) b).symm hab
    rw [hc, mem_bot] at hcent
    exact hz1 hcent
  · rw [htop, card_top] at hKodd
    have h2 : 2 ∣ Nat.card G := hz ▸ _root_.orderOf_dvd_natCard z
    exact (Nat.not_even_iff_odd.mpr hKodd) (even_iff_two_dvd.mpr h2)

theorem exists_conj_mem_QG (h35 : S14.AschbacherThreeTranspositionCore) {G : Type} [Group G]
    [Finite G] [IsSimpleGroup G] {N : ℕ} (hN : 6 ≤ N) (z : G) (hz : orderOf z = 2)
    (φ : centralizer ({z} : Set G) ≃* Ct N (by omega)) :
    ∃ g : G, g * z * g⁻¹ ∈ (settingOfCorner hN z hz φ).QG ∧ g * z * g⁻¹ ≠ z := by
  set S := settingOfCorner hN z hz φ with hS
  have hw : S.width = N - 2 := width_settingOfCorner hN z hz φ
  have hSz : S.z = z := settingOfCorner_z hN z hz φ
  by_contra hcon
  push Not at hcon
  have hbound : 5 ≤ S.width ∨ S.MbarTwoBound 7 := by
    by_cases h7 : 7 ≤ N
    · exact Or.inl (by omega)
    · refine Or.inr (Setting.MbarTwoBound.of _ fun P hP => ?_)
      have hb := (mbarTwoBound hN z hz φ).card_le P hP
      obtain rfl : N = 6 := by omega
      exact hb.trans (by norm_num)
  have hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z := by
    simpa only [hSz] using hcon
  have h3 := h35 G S (by omega) hbound hW
  simp only [hSz] at h3
  obtain ⟨g, hcomm, hne⟩ := exists_conj_commute_ne (exists_ne_mul_comm hN z φ) hz
  have hzz : z * z = 1 := by rw [← pow_two, ← hz, pow_orderOf_eq_one]
  have hxM : g * z * g⁻¹ ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.mpr hcomm
  set x : centralizer ({z} : Set G) := ⟨g * z * g⁻¹, hxM⟩ with hx
  set ψ : centralizer ({z} : Set G) →* GL (Fin (N - 2)) (ZMod 2) :=
    (midBlock (N := N) (by omega)).comp φ.toMonoidHom with hψ
  have hu1 : ψ x ≠ 1 := fun h => hne (hcon g ((mem_QG_iff hN z hz φ).mpr ⟨hxM, h⟩))
  have hxx : x ^ 2 = 1 := by
    refine Subtype.ext ?_
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, pow_two, hx]
    change g * z * g⁻¹ * (g * z * g⁻¹) = 1
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hzz]; group
  have hu2 : orderOf (ψ x) = 2 := orderOf_eq_prime (by rw [← map_pow, hxx, map_one]) hu1
  obtain ⟨gbar, hgbar⟩ := exists_orderOf_mul_conj_eq_four (k := N - 2) (by omega) hu2
  obtain ⟨m', hm'⟩ := midBlock_surjective (N := N) (by omega) gbar
  set m : centralizer ({z} : Set G) := φ.symm m' with hm
  have hψm : ψ m = gbar := by
    rw [hψ, MonoidHom.comp_apply, hm, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, hm']
  set Y : centralizer ({z} : Set G) := x * (m * x * m⁻¹) with hY
  have h4 : 4 ∣ orderOf Y := by
    have h := orderOf_map_dvd ψ Y
    rwa [hY, map_mul, map_mul, map_mul, map_inv, hψm, hgbar] at h
  have hYG : (Y : G) = g * z * g⁻¹ * ((m * g) * z * (m * g)⁻¹) := by
    rw [hY, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hx]
    group
  have h3Y := h3 g (m * g)
  rw [← hYG, Subgroup.orderOf_coe] at h3Y
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h3Y
  rcases h3Y with h | h | h <;> rw [h] at h4 <;> omega

end CFSG.LargeExtraspecial.DW.D73
