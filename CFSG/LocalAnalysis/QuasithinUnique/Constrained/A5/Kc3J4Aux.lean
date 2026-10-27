
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4ClassBase

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint

theorem five_not_dvd_card_centralizer {Y : Type} [Group Y] [Finite Y]
    (hY : ¬ 5 ^ 2 ∣ Nat.card Y) {V : Subgroup Y} (h : FpfV V) :
    ¬ 5 ∣ Nat.card (Subgroup.centralizer (V : Set Y)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro h5
  obtain ⟨hc, -, -, y, hyN, hy5, hfpf⟩ := h
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.centralizer (V : Set Y))) 5 h5
  have hgC : (g : Y) ∈ Subgroup.centralizer (V : Set Y) := g.2
  have hgN : (g : Y) ∈ Subgroup.normalizer (V : Set Y) := centralizer_le_normalizer_set V hgC
  have hg5 : orderOf (g : Y) = 5 := by
    rw [Subgroup.orderOf_coe]
    exact hg
  have hP : ¬ 5 ^ 2 ∣ Nat.card (Subgroup.normalizer (V : Set Y)) := fun hd =>
    hY (hd.trans (Subgroup.card_subgroup_dvd_card _))
  obtain ⟨m, hm, k, hk⟩ := Kc3J4.exists_conj_of_orderOf_prime (p := 5) hP hgN hyN hg5 hy5
  have hy1 : ∀ v ∈ V, y * v = v * y := by
    intro v hv
    have hv' : m⁻¹ * v * m ∈ V := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hm) v).1 hv
      simpa using this
    have hcomm : Commute (g : Y) (m⁻¹ * v * m) := by
      have := Subgroup.mem_centralizer_iff.1 hgC _ hv'
      exact this.symm
    have hk' : Commute ((g : Y) ^ k) (m⁻¹ * v * m) := hcomm.zpow_left k
    have h1 : (g : Y) ^ k * (m⁻¹ * v * m) = (m⁻¹ * v * m) * (g : Y) ^ k := hk'.eq
    calc y * v = m * (g : Y) ^ k * m⁻¹ * v := by rw [← hk]
      _ = m * ((g : Y) ^ k * (m⁻¹ * v * m)) * m⁻¹ := by group
      _ = m * ((m⁻¹ * v * m) * (g : Y) ^ k) * m⁻¹ := by rw [h1]
      _ = v * (m * (g : Y) ^ k * m⁻¹) := by group
      _ = v * y := by rw [← hk]
  have hV1 : V = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    exact (Subgroup.mem_bot).2 (hfpf v hv (hy1 v hv))
  rw [hV1] at hc
  simp at hc

theorem noNonHBlockAt_of_fpfV_card {Y : Type} [Group Y] [Finite Y] (hY : ¬ 5 ^ 2 ∣ Nat.card Y)
    (Hy : Subgroup Y) {V : Subgroup Y} (h : FpfV V)
    (hlt : Nat.card (Subgroup.normalizer (V : Set Y)) <
      60 * Nat.card (Subgroup.centralizer (V : Set Y))) : NoNonHBlockAt Hy V := by
  refine noNonHBlockAt_of_index Hy (five_not_dvd_card_centralizer hY h) ?_
  intro hd
  have hCN : Subgroup.centralizer (V : Set Y) ≤ Subgroup.normalizer (V : Set Y) :=
    centralizer_le_normalizer_set V
  have hmul : Nat.card (Subgroup.centralizer (V : Set Y)) *
      (Subgroup.centralizer (V : Set Y)).relIndex (Subgroup.normalizer (V : Set Y)) =
      Nat.card (Subgroup.normalizer (V : Set Y)) := by
    have h1 := Subgroup.card_mul_index
      ((Subgroup.centralizer (V : Set Y)).subgroupOf (Subgroup.normalizer (V : Set Y)))
    have h2 : Nat.card ((Subgroup.centralizer (V : Set Y)).subgroupOf
        (Subgroup.normalizer (V : Set Y))) = Nat.card (Subgroup.centralizer (V : Set Y)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv
    rw [h2] at h1
    exact h1
  have hpos : 0 < (Subgroup.centralizer (V : Set Y)).relIndex
      (Subgroup.normalizer (V : Set Y)) := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    rw [h0, mul_zero] at hmul
    exact (Nat.card_pos (α := ↥(Subgroup.normalizer (V : Set Y)))).ne' hmul.symm
  have h60 : 60 ≤ (Subgroup.centralizer (V : Set Y)).relIndex
      (Subgroup.normalizer (V : Set Y)) := Nat.le_of_dvd hpos hd
  have : 60 * Nat.card (Subgroup.centralizer (V : Set Y)) ≤
      Nat.card (Subgroup.normalizer (V : Set Y)) := by
    calc 60 * Nat.card (Subgroup.centralizer (V : Set Y))
        = Nat.card (Subgroup.centralizer (V : Set Y)) * 60 := mul_comm _ _
      _ ≤ Nat.card (Subgroup.centralizer (V : Set Y)) *
          (Subgroup.centralizer (V : Set Y)).relIndex (Subgroup.normalizer (V : Set Y)) :=
        Nat.mul_le_mul_left _ h60
      _ = Nat.card (Subgroup.normalizer (V : Set Y)) := hmul
  omega

end CFSG.QuasithinUnique.A5
