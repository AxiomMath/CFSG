module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDModel
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltFiveRankTools
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.OddStandard.SmallF3.L33

open Subgroup CFSG.Blueprint CFSG.OddStandard.SmallF3.L33.KD

private lemma x4_eq_one_of_eq_cube {L : Type} [Group L] {x : L} (h : x = x ^ 3) :
    x ^ 4 = 1 := by
  have hx2 : x ^ 2 = 1 := by
    have h1 : x⁻¹ * x = x⁻¹ * x ^ 3 := congrArg (fun z => x⁻¹ * z) h
    rw [inv_mul_cancel] at h1
    have h2 : x⁻¹ * x ^ 3 = x ^ 2 := by group
    rw [h2] at h1
    exact h1.symm
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hx2, one_pow]

theorem three_le_twoRank_of_l33
    {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} (hL : LieModel ↥L .PSL 3 3 1)
    (hLt : L ≤ centralizer ({t} : Set G)) (ht2 : orderOf t = 2) (htL : t ∉ L) :
    3 ≤ CFSG.Open.twoRank G := by
  classical
  obtain ⟨M⟩ := SDModel.exists_sdModel hL
  let x : ↥L := M.F.x
  let y : ↥L := M.F.y
  set a : G := L.subtype (x ^ 4) with ha
  set b : G := L.subtype y with hb
  have hx8 : x ^ 8 = 1 := M.F.x_pow_eight
  have hx4ne : x ^ 4 ≠ 1 := M.F.x_pow_four_ne_one
  have hy2 : y ^ 2 = 1 := M.F.y_sq
  have hyconj : y * x * y⁻¹ = x ^ 3 := M.F.y_conj
  have hy1 : y ≠ 1 := by
    intro hy
    exact hx4ne (x4_eq_one_of_eq_cube (by simpa [hy] using hyconj))
  have hx4conj : x ^ 4 * x * (x ^ 4)⁻¹ = x := by group
  have h4conj : y * x ^ 4 * y⁻¹ = x ^ 4 := by
    calc y * x ^ 4 * y⁻¹ = MulAut.conj y (x ^ 4) := (MulAut.conj_apply y (x ^ 4)).symm
      _ = (MulAut.conj y x) ^ 4 := map_pow (MulAut.conj y) x 4
      _ = (x ^ 3) ^ 4 := by rw [MulAut.conj_apply, hyconj]
      _ = x ^ 4 := by
          rw [← pow_mul, show 3 * 4 = 4 + 8 by norm_num, pow_add, hx8, mul_one]
  have hcomm_xy4 : y * x ^ 4 = x ^ 4 * y := mul_inv_eq_iff_eq_mul.mp h4conj
  have hxy4 : x ^ 4 ≠ y := by
    intro h
    have hc : x = x ^ 3 := by
      have h' := hyconj
      rw [← h, hx4conj] at h'
      exact h'
    exact hx4ne (x4_eq_one_of_eq_cube hc)
  have hx4sq : (x ^ 4 : ↥L) ^ 2 = 1 := by
    rw [← pow_mul, show 4 * 2 = 8 by norm_num, hx8]
  have ha2 : a ^ 2 = 1 := by rw [ha, ← map_pow, hx4sq, map_one]
  have ha1 : a ≠ 1 := by
    rw [ha]
    intro h
    exact hx4ne (L.subtype_injective (by rw [h, map_one]))
  have hb2 : b ^ 2 = 1 := by rw [hb, ← map_pow, hy2, map_one]
  have hb1 : b ≠ 1 := by
    rw [hb]
    intro h
    exact hy1 (L.subtype_injective (by rw [h, map_one]))
  have ha_ne_b : a ≠ b := by
    rw [ha, hb]
    intro h
    exact hxy4 (L.subtype_injective h)
  have hab : a * b = b * a := by
    rw [ha, hb]
    simpa [map_mul] using (congrArg L.subtype hcomm_xy4).symm
  have haL : a ∈ L := by rw [ha]; exact (x ^ 4 : ↥L).2
  have hbL : b ∈ L := by rw [hb]; exact (y : ↥L).2
  have hAL : (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) ≤ L :=
    sup_le (Subgroup.zpowers_le.mpr haL) (Subgroup.zpowers_le.mpr hbL)
  have horda : orderOf a = 2 := orderOf_eq_prime ha2 ha1
  have hordb : orderOf b = 2 := orderOf_eq_prime hb2 hb1
  have ha_mem : ∀ u : G, u ∈ Subgroup.zpowers a → u = 1 ∨ u = a := by
    intro u hu
    rw [mem_zpowers_iff_mem_range_orderOf (x := a) (y := u), Finset.mem_image] at hu
    obtain ⟨i, hi, hiu⟩ := hu
    rw [Finset.mem_range, horda] at hi
    rw [← hiu]
    interval_cases i <;> simp
  have hb_mem : ∀ u : G, u ∈ Subgroup.zpowers b → u = 1 ∨ u = b := by
    intro u hu
    rw [mem_zpowers_iff_mem_range_orderOf (x := b) (y := u), Finset.mem_image] at hu
    obtain ⟨i, hi, hiu⟩ := hu
    rw [Finset.mem_range, hordb] at hi
    rw [← hiu]
    interval_cases i <;> simp
  have hdisj_ab : Subgroup.zpowers b ⊓ Subgroup.zpowers a = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [Subgroup.mem_bot]
    rw [Subgroup.mem_inf] at hu
    rcases ha_mem u hu.2 with h | h
    · exact h
    · rcases hb_mem u hu.1 with h' | h'
      · exact h'
      · exact absurd (h.symm.trans h') ha_ne_b
  have ht2' : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have ht_mem : ∀ u : G, u ∈ Subgroup.zpowers t → u = 1 ∨ u = t := by
    intro u hu
    rw [mem_zpowers_iff_mem_range_orderOf (x := t) (y := u), Finset.mem_image] at hu
    obtain ⟨i, hi, hiu⟩ := hu
    rw [Finset.mem_range, ht2] at hi
    rw [← hiu]
    interval_cases i <;> simp
  have ht_notin : t ∉ (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) :=
    fun h => htL (hAL h)
  have hdisj_at : Subgroup.zpowers t ⊓ (Subgroup.zpowers a ⊔ Subgroup.zpowers b) = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [Subgroup.mem_bot]
    rw [Subgroup.mem_inf] at hu
    rcases ht_mem u hu.1 with h | h
    · exact h
    · exact absurd (h ▸ hu.2) ht_notin
  have hbC : b ∈ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact (show Commute a b from hab).zpow_left k
  have hbotC : a ∈ Subgroup.centralizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu1 : u = 1 := by simpa using hu
    rw [hu1, one_mul, mul_one]
  have htC : t ∈ Subgroup.centralizer
      (((Subgroup.zpowers a ⊔ Subgroup.zpowers b) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (Subgroup.mem_centralizer_iff.mp (hLt (hAL hu)) t (by simp)).symm
  have hstep1 := CFSG.AGLEmbeddingD2.pRank_succ_le_sup_zpowers (q := 2) (A := ⊥)
    (z := a) ha2 ha1 hbotC (by simp)
  have h1 : 1 ≤ CFSG.Open.pRank 2 (Subgroup.zpowers a) := by
    simp only [bot_sup_eq] at hstep1
    omega
  have hstep2 := CFSG.AGLEmbeddingD2.pRank_succ_le_sup_zpowers (q := 2)
    (A := Subgroup.zpowers a) (z := b) hb2 hb1 hbC hdisj_ab
  have h2 : 2 ≤ CFSG.Open.pRank 2 (Subgroup.zpowers a ⊔ Subgroup.zpowers b) := by
    omega
  have hstep3 := CFSG.AGLEmbeddingD2.pRank_succ_le_sup_zpowers (q := 2)
    (A := Subgroup.zpowers a ⊔ Subgroup.zpowers b) (z := t) ht2' ht1 htC hdisj_at
  have h3 : 3 ≤ CFSG.Open.pRank 2
      ((Subgroup.zpowers a ⊔ Subgroup.zpowers b) ⊔ Subgroup.zpowers t) := by
    omega
  change 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup G)
  exact h3.trans (CFSG.SectionRank.pRank_mono (p := 2) (by norm_num) le_top)

end CFSG.OddStandard.SmallF3.L33
