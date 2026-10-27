module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL31c

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

namespace GHSylow

variable (D : GHSylow G)

omit [Finite G] in
theorem CZ_le_normalizer : D.CZ ≤ normalizer D.Zset := fun c hc =>
  mem_normalizer_of_conj (fun w hw => by
    have h : c * w * c⁻¹ = w := by rw [← (mem_centralizer_iff.mp hc w hw)]; group
    rw [h]
    exact hw) (fun w hw => by
    have h : c⁻¹ * w * c = w := by
      rw [show c⁻¹ * w * c = c⁻¹ * (w * c) by group, (mem_centralizer_iff.mp hc w hw)]; group
    rw [h]
    exact hw)

omit [Finite G] in

theorem normalizer_le_normalizer_CZ :
    normalizer D.Zset ≤ normalizer (D.CZ : Set G) := by
  intro h hh
  have key : ∀ k ∈ normalizer D.Zset, ∀ x ∈ D.CZ, k * x * k⁻¹ ∈ D.CZ := by
    intro k hk x hx
    refine mem_centralizer_iff.mpr fun w hw => ?_
    have hw' : k⁻¹ * w * k ∈ D.Zset := conj_mem_of_mem_normalizer hk hw
    have hc := mem_centralizer_iff.mp hx _ hw'
    calc w * (k * x * k⁻¹) = k * ((k⁻¹ * w * k) * x) * k⁻¹ := by group
      _ = k * (x * (k⁻¹ * w * k)) * k⁻¹ := by rw [hc]
      _ = k * x * k⁻¹ * w := by group
  refine fun x => ⟨fun hx => key h hh x hx, fun hx => ?_⟩
  have := key h⁻¹ (inv_mem hh) _ hx
  rwa [show h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x by group] at this

theorem isSylowOf_Ct_CZ : IsSylowOf 2 ((D.S : Subgroup G) ⊓ D.CZ) D.CZ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ((isSylowOf_top D.S).of_le D.S_le_normalizer_Zset le_top).inf_of_le_normalizer
    D.CZ_le_normalizer D.normalizer_le_normalizer_CZ

omit [Finite G] in
theorem exists_swap_normalizer_Zset {s : G} (hsN : s ∈ normalizer D.Zset)
    (hsz : s⁻¹ * D.z * s ≠ D.z) :
    ∃ u ∈ normalizer D.Zset, u⁻¹ * D.z * u = D.t ∧ u⁻¹ * D.t * u = D.z := by
  set y := D.toG (SE.gen 7)
  have hyN : y ∈ normalizer D.Zset := D.S_le_normalizer_Zset (D.toG_mem _)
  have hyz : y⁻¹ * D.z * y = D.z := D.conj_z_S (D.toG_mem _)
  have hyt : y⁻¹ * D.t * y = D.t * D.z := D.conj_y_t
  have htt := D.t_mul_t
  have hzz := D.z_mul_z
  have hzt := D.z_comm_t
  have hsZ : s⁻¹ * D.z * s ∈ D.Zset := conj_mem_of_mem_normalizer hsN (by simp)
  have hsT : s⁻¹ * D.t * s ∈ D.Zset := conj_mem_of_mem_normalizer hsN (by simp)
  have hs1 : s⁻¹ * D.z * s ≠ 1 := fun h => D.z_ne_one (by
    calc D.z = s * (s⁻¹ * D.z * s) * s⁻¹ := by group
      _ = 1 := by rw [h]; group)
  have ht1 : s⁻¹ * D.t * s ≠ 1 := fun h => D.t_ne_one (by
    calc D.t = s * (s⁻¹ * D.t * s) * s⁻¹ := by group
      _ = 1 := by rw [h]; group)
  have hne : s⁻¹ * D.t * s ≠ s⁻¹ * D.z * s := fun h => D.z_ne_t (by
    calc D.z = s * (s⁻¹ * D.z * s) * s⁻¹ := by group
      _ = s * (s⁻¹ * D.t * s) * s⁻¹ := by rw [h]
      _ = D.t := by group)
  have hconj_tz : s⁻¹ * (D.t * D.z) * s = (s⁻¹ * D.t * s) * (s⁻¹ * D.z * s) := by group
  rcases hsZ with h1 | h1 | h1 | h1
  · exact absurd h1 hs1
  · exact absurd h1 hsz
  · rcases hsT with h2 | h2 | h2 | h2
    · exact absurd h2 ht1
    · exact ⟨s, hsN, h1, h2⟩
    · exact absurd (h2.trans h1.symm) hne
    · refine ⟨y * s, mul_mem hyN hsN, ?_, ?_⟩
      · rw [show (y * s)⁻¹ * D.z * (y * s) = s⁻¹ * (y⁻¹ * D.z * y) * s by group, hyz, h1]
      · rw [show (y * s)⁻¹ * D.t * (y * s) = s⁻¹ * (y⁻¹ * D.t * y) * s by group, hyt,
          hconj_tz, h1, h2]
        calc D.t * D.z * D.t = D.z * (D.t * D.t) := by rw [← hzt]; group
          _ = D.z := by rw [htt, mul_one]
  · rcases hsT with h2 | h2 | h2 | h2
    · exact absurd h2 ht1
    · refine ⟨s * y, mul_mem hsN hyN, ?_, ?_⟩
      · rw [show (s * y)⁻¹ * D.z * (s * y) = y⁻¹ * (s⁻¹ * D.z * s) * y by group, h1,
          show y⁻¹ * (D.t * D.z) * y = (y⁻¹ * D.t * y) * (y⁻¹ * D.z * y) by group, hyt, hyz,
          mul_assoc, hzz, mul_one]
      · rw [show (s * y)⁻¹ * D.t * (s * y) = y⁻¹ * (s⁻¹ * D.t * s) * y by group, h2, hyz]
    · refine ⟨y * s * y, mul_mem (mul_mem hyN hsN) hyN, ?_, ?_⟩
      · rw [show (y * s * y)⁻¹ * D.z * (y * s * y) = y⁻¹ * (s⁻¹ * (y⁻¹ * D.z * y) * s) * y by
          group, hyz, h1, show y⁻¹ * (D.t * D.z) * y = (y⁻¹ * D.t * y) * (y⁻¹ * D.z * y) by group,
          hyt, hyz, mul_assoc, hzz, mul_one]
      · rw [show (y * s * y)⁻¹ * D.t * (y * s * y) = y⁻¹ * (s⁻¹ * (y⁻¹ * D.t * y) * s) * y by
          group, hyt, hconj_tz, h1, h2, show D.t * (D.t * D.z) = D.z by
            rw [← mul_assoc, htt, one_mul], hyz]
    · exact absurd (h2.trans h1.symm) hne

theorem exists_swap_z_t
    (hzt : ∃ g : G, g⁻¹ * D.z * g = D.t) :
    ∃ n ∈ normalizer (D.Ct : Set G), n⁻¹ * D.z * n = D.t ∧ n⁻¹ * D.t * n = D.z := by
  obtain ⟨g, hg⟩ := hzt
  obtain ⟨T, hT, hCtT, hTcard⟩ := D.exists_sylow_Ct hg
  have h2 : 2 * Nat.card D.Ct = Nat.card T := by
    rw [hTcard, show Nat.card D.Ct = 256 from D.card_centralizer_invRep_G 1]
  have hTN : T ≤ normalizer D.Zset := by
    intro s hs
    have key : ∀ k ∈ T, ∀ w ∈ D.Zset, k⁻¹ * w * k ∈ D.Zset := by
      intro k hk w hw
      rw [D.mem_Zset_iff]
      refine ⟨conj_mem_of_two_mul_card hCtT h2 hk (D.Zset_subset_Ct hw), fun p hp => ?_⟩
      have hp' : k * p * k⁻¹ ∈ D.Ct := by
        have := conj_mem_of_two_mul_card hCtT h2 (inv_mem hk) hp
        rwa [inv_inv] at this
      have hc := D.comm_of_mem_Zset hw hp'
      calc p * (k⁻¹ * w * k) = k⁻¹ * ((k * p * k⁻¹) * w) * k := by group
        _ = k⁻¹ * (w * (k * p * k⁻¹)) * k := by rw [hc]
        _ = k⁻¹ * w * k * p := by group
    exact mem_normalizer_of_conj (fun w hw => by
      have := key s⁻¹ (inv_mem hs) w hw
      rwa [inv_inv] at this) (fun w hw => key s hs w hw)
  obtain ⟨s, hsT, hsz⟩ := D.exists_mem_move_z hg hT hCtT hTcard
  obtain ⟨u, huN, huz, hut⟩ := D.exists_swap_normalizer_Zset (hTN hsT) hsz
  obtain ⟨c, hcCZ, hc⟩ := exists_mul_mem_normalizer D.normalizer_le_normalizer_CZ
    D.isSylowOf_Ct_CZ huN
  rw [D.Ct_eq] at hc
  have hct : D.t * c = c * D.t := mem_centralizer_iff.mp hcCZ D.t (by simp)
  have hcz : D.z * c = c * D.z := mem_centralizer_iff.mp hcCZ D.z (by simp)
  refine ⟨u * c, hc, ?_, ?_⟩
  · rw [show (u * c)⁻¹ * D.z * (u * c) = c⁻¹ * (u⁻¹ * D.z * u) * c by group, huz,
      show c⁻¹ * D.t * c = c⁻¹ * (D.t * c) by group, hct]
    group
  · rw [show (u * c)⁻¹ * D.t * (u * c) = c⁻¹ * (u⁻¹ * D.t * u) * c by group, hut,
      show c⁻¹ * D.z * c = c⁻¹ * (D.z * c) by group, hcz]
    group

end GHSylow

end CFSG.ComponentClassification.GHarris
