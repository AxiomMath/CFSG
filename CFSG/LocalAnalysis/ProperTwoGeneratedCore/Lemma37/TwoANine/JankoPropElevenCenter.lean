module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropElevenMbar
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoEleven

open Subgroup CFSG.Semidihedral.Principal.PrimewiseScalar

variable {G : Type} [Group G] {z : G} {fr : JankoFrame G z}

theorem N_le_normalizer_Mbar [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) : fr.N ≤ normalizer (fr.Mbar : Set G) :=
  N_le_centralizer_P₁.trans (centralizer_P₁_le_normalizer_P₁.trans
    (normalizer_P₁_le_normalizer_Mbar p7 p10 hz))

theorem ZN_inf_Mbar_ne_bot [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) : fr.ZN ⊓ fr.Mbar ≠ ⊥ := by
  have : Group.IsNilpotent fr.N := (isPGroup_N p10).isNilpotent
  have hle : fr.Mbar ≤ fr.N := Mbar_le_M.trans M_le_N
  have : (fr.Mbar.subgroupOf fr.N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr (N_le_normalizer_Mbar p7 p10 hz)
  have hne : fr.Mbar.subgroupOf fr.N ≠ ⊥ := by
    intro h
    have h1 : Nat.card (fr.Mbar.subgroupOf fr.N) = 81 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, card_Mbar p10]
    rw [h, Subgroup.card_bot] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨⟨n, hnM, hnZ⟩, hn1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  intro h
  have hmem : (n : G) ∈ fr.ZN ⊓ fr.Mbar := by
    refine ⟨⟨n.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩, hnM⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hnZ ⟨y, hy⟩)
  rw [h, Subgroup.mem_bot] at hmem
  exact hn1 (Subtype.ext (Subtype.ext hmem))

theorem t_mem_normalizer_ZN [Finite G] (p7 : JankoProp7 fr) :
    fr.t ∈ normalizer (fr.ZN : Set G) := mem_normalizer_ZN (t_mem_normalizer_N p7)

theorem ℓ_mem_normalizer_ZN : fr.ℓ ∈ normalizer (fr.ZN : Set G) :=
  mem_normalizer_ZN ℓ_mem_normalizer_N

theorem t_mem_normalizer_Mbar [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) : fr.t ∈ normalizer (fr.Mbar : Set G) :=
  normalizer_P₁_le_normalizer_Mbar p7 p10 hz (t_mem_normalizer_P₁ p7)

theorem ℓ_mem_normalizer_Mbar [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) : fr.ℓ ∈ normalizer (fr.Mbar : Set G) :=
  normalizer_P₁_le_normalizer_Mbar p7 p10 hz
    (centralizer_P₁_le_normalizer_P₁ ℓ_mem_centralizer_P₁)

theorem P3bar_le_At (p10 : JankoProp10 fr) : fr.P3bar ≤ fr.At :=
  fun _ hx => ⟨ZN_le_M p10 hx.1, hx.2⟩

theorem P3bbar_le_Atz (p10 : JankoProp10 fr) : fr.P3bbar ≤ fr.Atz :=
  fun _ hx => ⟨ZN_le_M p10 hx.1, hx.2⟩

theorem P3bar_le_ZN : fr.P3bar ≤ fr.ZN := inf_le_left

theorem P3bbar_le_ZN : fr.P3bbar ≤ fr.ZN := inf_le_left

theorem S_le_ZN : fr.S ≤ fr.ZN := sup_le P3bar_le_ZN P3bbar_le_ZN

theorem S_le_M (p10 : JankoProp10 fr) : fr.S ≤ fr.M := S_le_ZN.trans (ZN_le_M p10)

theorem S_eq [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr) (hz : orderOf z = 2) :
    fr.S = fr.ZN ⊓ fr.Mbar := by
  refine le_antisymm (sup_le (le_inf P3bar_le_ZN ((P3bar_le_At p10).trans At_le_Mbar))
    (le_inf P3bbar_le_ZN ((P3bbar_le_Atz p10).trans Atz_le_Mbar))) fun y hy => ?_
  have hYM : fr.ZN ⊓ fr.Mbar ≤ fr.M := inf_le_left.trans (ZN_le_M p10)
  obtain ⟨b, hb, c, hc, hbt, hct, rfl⟩ := exists_fixed_mul_inverted
    (fun a ha b hb => p10.M_comm a (hYM ha) b (hYM hb)) t_mul_t
    (fun _ ha => conj_mem_of_mem_normalizer
      (inf_mem_normalizer (t_mem_normalizer_ZN p7) (t_mem_normalizer_Mbar p7 p10 hz)) ha)
    hy (p10.M_pow_three _ (hYM hy))
  have hb' : b ∈ fr.P3bar := ⟨hb.1, mem_centralizer_singleton_iff_conj.mpr hbt⟩
  have hc' : c ∈ fr.P3bbar := by
    refine ⟨hc.1, mem_centralizer_singleton_iff_conj.mpr ?_⟩
    calc fr.t * z * c * (fr.t * z)⁻¹ = fr.t * (z * c * z⁻¹) * fr.t⁻¹ := by group
      _ = c := by rw [inv_of_mem_Mbar p10 hz hc.2, conj_inv_conj, hct, inv_inv]
  exact mul_mem_sup hb' hc'

theorem ℓ_sq_mem_normalizer_ZN : fr.ℓ ^ 2 ∈ normalizer (fr.ZN : Set G) :=
  pow_mem ℓ_mem_normalizer_ZN 2

theorem map_P3bar (hz : orderOf z = 2) :
    fr.P3bar.map (MulAut.conj (fr.ℓ ^ 2)).toMonoidHom = fr.P3bbar := by
  have h := map_conj_inf_centralizer (ℓ_sq_mem_normalizer_ZN (fr := fr)) fr.t
  rwa [ℓ_sq_conj_t hz] at h

theorem card_P3bbar_eq (hz : orderOf z = 2) : Nat.card fr.P3bbar = Nat.card fr.P3bar := by
  rw [← map_P3bar hz, Subgroup.card_map_of_injective (MulAut.conj _).injective]

theorem card_S (p10 : JankoProp10 fr) :
    Nat.card fr.S = Nat.card fr.P3bar * Nat.card fr.P3bbar := by
  have hle : fr.P3bar ≤ normalizer (fr.P3bbar : Set G) :=
    le_normalizer_of_comm p10.M_comm ((P3bar_le_At p10).trans inf_le_left)
      ((P3bbar_le_Atz p10).trans inf_le_left)
  have h := card_sup_mul_card_inf hle
  have hbot : fr.P3bar ⊓ fr.P3bbar = ⊥ :=
    le_bot_iff.mp ((At_inf_Atz p10) ▸ inf_le_inf (P3bar_le_At p10) (P3bbar_le_Atz p10))
  rw [hbot, Subgroup.card_bot, mul_one] at h
  exact h

theorem card_P3bar_and_S [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) : Nat.card fr.P3bar = 3 ∧ Nat.card fr.S = 9 := by
  have hS : Nat.card fr.S = Nat.card fr.P3bar ^ 2 := by
    rw [card_S p10, card_P3bbar_eq hz, pow_two]
  have hS1 : Nat.card fr.S ≠ 1 := by
    rw [Ne, Subgroup.card_eq_one, S_eq p7 p10 hz]
    exact ZN_inf_Mbar_ne_bot p7 p10 hz
  have hSle : fr.S ≤ fr.Mbar := by rw [S_eq p7 p10 hz]; exact inf_le_right
  have hS81 : Nat.card fr.S ≠ 81 := by
    intro h81
    have heq : fr.S = fr.Mbar :=
      Subgroup.eq_of_le_of_card_ge hSle (by rw [h81, card_Mbar p10])
    refine p10.not_At_le fun a ha => ?_
    have haZ : a ∈ fr.ZN := S_le_ZN (heq ▸ At_le_Mbar ha)
    rw [centralizer_P₂_eq, mem_centralizer_singleton_iff]
    exact (comm_of_mem_ZN haZ (E_le_N s₂_mem_E)).symm
  have hdvd : Nat.card fr.P3bar ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← p10.card_At]
    exact Subgroup.card_dvd_of_le (P3bar_le_At p10)
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases k
  · exact absurd (by rw [hS, hk']; norm_num) hS1
  · exact ⟨by rw [hk']; norm_num, by rw [hS, hk']; norm_num⟩
  · exact absurd (by rw [hS, hk']; norm_num) hS81

theorem card_P3bar [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) : Nat.card fr.P3bar = 3 := (card_P3bar_and_S p7 p10 hz).1

theorem card_P3bbar [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) : Nat.card fr.P3bbar = 3 := by
  rw [card_P3bbar_eq hz, card_P3bar p7 p10 hz]

theorem card_S_eq [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr)
    (hz : orderOf z = 2) : Nat.card fr.S = 9 := (card_P3bar_and_S p7 p10 hz).2

theorem ZN_eq [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr) (hz : orderOf z = 2) :
    fr.ZN = fr.P₁ ⊔ fr.S := by
  refine le_antisymm (fun x hx => ?_) (sup_le P₁_le_ZN S_le_ZN)
  obtain ⟨b, hb, c, hc, hbz, hcz, rfl⟩ := exists_fixed_mul_inverted
    (fun a ha b hb => p10.M_comm a (ZN_le_M p10 ha) b (ZN_le_M p10 hb)) (z_mul_z hz)
    (fun _ ha => conj_mem_of_mem_normalizer (mem_normalizer_ZN z_mem_normalizer_N) ha)
    hx (p10.M_pow_three _ (ZN_le_M p10 hx))
  have hb' : b ∈ fr.P₁ := by
    rw [← p10.M_inf_centralizer_z]
    exact ⟨ZN_le_M p10 hb, mem_centralizer_singleton_iff_conj.mpr hbz⟩
  have hc' : c ∈ fr.S := by
    rw [S_eq p7 p10 hz]
    exact ⟨hc, mem_Mbar_of_inv p7 p10 hz (ZN_le_M p10 hc) hcz⟩
  exact mul_mem_sup hb' hc'

theorem card_ZN [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr) (hz : orderOf z = 2) :
    Nat.card fr.ZN = 27 := by
  have hle : fr.P₁ ≤ normalizer (fr.S : Set G) :=
    le_normalizer_of_comm p10.M_comm p10.P₁_le_M (S_le_M p10)
  have h := card_sup_mul_card_inf hle
  have hbot : fr.P₁ ⊓ fr.S = ⊥ := by
    rw [S_eq p7 p10 hz]
    exact le_bot_iff.mp ((P₁_inf_Mbar p10 hz) ▸ inf_le_inf_left _ inf_le_right)
  rw [hbot, Subgroup.card_bot, mul_one, card_P₁, card_S_eq p7 p10 hz, ← ZN_eq p7 p10 hz] at h
  exact h

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoEleven
