module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.TabBigKlein
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspL33Core
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsSL3
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6A312Ord

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Vol2Native.L239.L33Insp

set_option maxRecDepth 100000

theorem cent_complete_L33 : ∀ x ∈ nL, nmul x nt0 = nmul nt0 x → x ∈ c48p := by
  decide +kernel

theorem klein_check_L33 :
    ∀ b ∈ c48p, b ≠ nid → b ≠ nt0 → nmul b b = nid →
      ∀ x ∈ nL, nmul x nt0 = nmul nt0 x → nmul x b = nmul b x →
        x = nid ∨ x = nt0 ∨ x = b ∨ x = nmul b nt0 := by
  decide +kernel

theorem rn_comm_iff (x y : S3) : x * y = y * x ↔ nmul (rn x) (rn y) = nmul (rn y) (rn x) := by
  rw [← rn_mul, ← rn_mul]
  exact ⟨fun h => by rw [h], fun h => rn_inj h⟩

theorem kleinSC_S3_u0 {b g : S3} (hb2 : b * b = 1) (hb1 : b ≠ 1) (hbu : b ≠ u0)
    (hbc : b * u0 = u0 * b) (hgu : g * u0 = u0 * g) (hgb : g * b = b * g) :
    g = 1 ∨ g = u0 ∨ g = b ∨ g = b * u0 := by
  have hbc' : nmul (rn b) nt0 = nmul nt0 (rn b) := by
    rw [← rn_u0]; exact (rn_comm_iff b u0).mp hbc
  have hgc' : nmul (rn g) nt0 = nmul nt0 (rn g) := by
    rw [← rn_u0]; exact (rn_comm_iff g u0).mp hgu
  have hgbc' : nmul (rn g) (rn b) = nmul (rn b) (rn g) := (rn_comm_iff g b).mp hgb
  have hb1' : rn b ≠ nid := fun h => hb1 (rn_inj (by rw [h, rn_one]))
  have hbu' : rn b ≠ nt0 := fun h => hbu (rn_inj (by rw [h, rn_u0]))
  have hb2' : nmul (rn b) (rn b) = nid := by rw [← rn_mul, hb2, rn_one]
  have hbC : rn b ∈ c48p := cent_complete_L33 (rn b) (rn_mem_nL b) hbc'
  rcases klein_check_L33 (rn b) hbC hb1' hbu' hb2' (rn g) (rn_mem_nL g) hgc' hgbc' with
    h | h | h | h
  · exact Or.inl (rn_inj (by rw [h, rn_one]))
  · exact Or.inr (Or.inl (rn_inj (by rw [h, rn_u0])))
  · exact Or.inr (Or.inr (Or.inl (rn_inj h)))
  · exact Or.inr (Or.inr (Or.inr (rn_inj (by rw [h, rn_mul, rn_u0]))))

theorem kleinSC_S3 : KleinSC S3 := by
  intro V hV4 hV2 g hg
  obtain ⟨t, htV, ht1, b, hbV, hb1, hbt⟩ := exists_two_ne_one_of_card_four hV2 hV4
  have ht2 : t * t = 1 := hV2 t htV
  obtain ⟨c, hc⟩ := exists_conj_u0 ht2 ht1
  have hbtc : b * t = t * b := comm_of_sq_eq_one hV2 hbV htV
  have hgt : g * t = t * g := hg t htV
  have hgb : g * b = b * g := hg b hbV
  have hcc : c⁻¹ * c = 1 := inv_mul_cancel c
  have hu : c⁻¹ * t * c = u0 := by rw [← hc]; group
  have hb2 : (c⁻¹ * b * c) * (c⁻¹ * b * c) = 1 := by
    calc (c⁻¹ * b * c) * (c⁻¹ * b * c) = c⁻¹ * (b * b) * c := by group
      _ = 1 := by rw [hV2 b hbV]; group
  have hb1' : c⁻¹ * b * c ≠ 1 := by
    intro h
    apply hb1
    calc b = c * (c⁻¹ * b * c) * c⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hbu' : c⁻¹ * b * c ≠ u0 := by
    intro h
    apply hbt
    rw [← hu] at h
    calc b = c * (c⁻¹ * b * c) * c⁻¹ := by group
      _ = c * (c⁻¹ * t * c) * c⁻¹ := by rw [h]
      _ = t := by group
  have hbc' : (c⁻¹ * b * c) * u0 = u0 * (c⁻¹ * b * c) := by
    rw [← hu]
    calc c⁻¹ * b * c * (c⁻¹ * t * c) = c⁻¹ * (b * t) * c := by group
      _ = c⁻¹ * (t * b) * c := by rw [hbtc]
      _ = c⁻¹ * t * c * (c⁻¹ * b * c) := by group
  have hgu' : (c⁻¹ * g * c) * u0 = u0 * (c⁻¹ * g * c) := by
    rw [← hu]
    calc c⁻¹ * g * c * (c⁻¹ * t * c) = c⁻¹ * (g * t) * c := by group
      _ = c⁻¹ * (t * g) * c := by rw [hgt]
      _ = c⁻¹ * t * c * (c⁻¹ * g * c) := by group
  have hgb' : (c⁻¹ * g * c) * (c⁻¹ * b * c) = (c⁻¹ * b * c) * (c⁻¹ * g * c) := by
    calc c⁻¹ * g * c * (c⁻¹ * b * c) = c⁻¹ * (g * b) * c := by group
      _ = c⁻¹ * (b * g) * c := by rw [hgb]
      _ = c⁻¹ * b * c * (c⁻¹ * g * c) := by group
  rcases kleinSC_S3_u0 hb2 hb1' hbu' hbc' hgu' hgb' with h | h | h | h
  · have : g = 1 := by
      calc g = c * (c⁻¹ * g * c) * c⁻¹ := by group
        _ = 1 := by rw [h]; group
    rw [this]; exact V.one_mem
  · have : g = t := by
      calc g = c * (c⁻¹ * g * c) * c⁻¹ := by group
        _ = c * (c⁻¹ * t * c) * c⁻¹ := by rw [h, hu]
        _ = t := by group
    rw [this]; exact htV
  · have : g = b := by
      calc g = c * (c⁻¹ * g * c) * c⁻¹ := by group
        _ = c * (c⁻¹ * b * c) * c⁻¹ := by rw [h]
        _ = b := by group
    rw [this]; exact hbV
  · have : g = b * t := by
      calc g = c * (c⁻¹ * g * c) * c⁻¹ := by group
        _ = c * ((c⁻¹ * b * c) * (c⁻¹ * t * c)) * c⁻¹ := by rw [h, hu]
        _ = b * t := by group
    rw [this]; exact V.mul_mem hbV htV

theorem kleinSC_of_psl33 {X : Type} [Group X] (h : StatedClassicalModel X .PSL 3 3 1) :
    KleinSC X := by
  obtain ⟨e₀⟩ := CFSG.QuasithinUnique.Unc25K1.psl33_equiv h
  exact KleinSC.of_mulEquiv (e₀.trans CFSG.QuasithinUnique.Unc25K1.psl33EquivS3) kleinSC_S3

theorem card_dvd_of_psl33 {X : Type} [Group X] (h : StatedClassicalModel X .PSL 3 3 1) :
    16 ∣ Nat.card X := by
  rw [CFSG.QuasithinUnique.Unc25G2.A312Sub.card_psl_three_three h]
  norm_num

end CFSG.QuasithinUnique.DoubleA3
