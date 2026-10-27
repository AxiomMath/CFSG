module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7a
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7X0

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7b_L_inf_P {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    L ⊓ (s.fr.B ⊔ zpowers s.t) = s.fr.B := by
  have hdisj : zpowers s.t ⊓ L = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨hyt, hyL⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyt
    have hmod : s.t ^ k = s.t ^ (k % (2 : ℤ)) := by
      rw [← zpow_mod_orderOf, s.t_order]
      rfl
    rw [hmod] at hyL ⊢
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · rw [h]; simp
    · rw [h] at hyL
      exact absurd (by simpa using hyL) (s3_t_not_mem_L s hH.h31)
  have hB_norm : s.fr.B ≤ normalizer (zpowers s.t : Set G) := by
    intro b hbB
    exact mem_normalizer_zpowers (by
      have hbL : b ∈ L := f3_B_le_L s hbB
      have hc : b * s.t = s.t * b := s3_comm_t_of_mem_L s hbL
      calc b * s.t * b⁻¹ = (s.t * b) * b⁻¹ := by rw [hc]
        _ = s.t := by group)
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxL, hxW⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨b, hbB, a, ha, hxba⟩ :=
      (mem_sup_iff_exists_mul_of_le_normalizer (H := s.fr.B) (K := zpowers s.t) hB_norm).mp hxW
    have haL : a ∈ L := by
      have : a = b⁻¹ * x := by rw [hxba]; group
      rw [this]
      exact L.mul_mem (L.inv_mem (f3_B_le_L s hbB)) hxL
    have ha1 : a = 1 := by
      have ha_bot : a ∈ zpowers s.t ⊓ L := Subgroup.mem_inf.mpr ⟨ha, haL⟩
      rw [hdisj] at ha_bot
      simpa using ha_bot
    rw [hxba, ha1, mul_one]
    exact hbB
  · intro x hx
    exact Subgroup.mem_inf.mpr ⟨f3_B_le_L s hx, Subgroup.mem_sup_left hx⟩

private lemma y7b_conj_commute_of_commute {c : Ctx7 G L} {a h : G}
    (ha : Commute a c.s.t) (hh : Commute h c.s.t) :
    Commute (a * h * a⁻¹) c.s.t :=
  (ha.mul_left hh).mul_left ha.inv_left

private lemma y7b_mem_normalizer_B_of_comm_t (c : Ctx7 G L) (hb : B5Std c) {a : G}
    (hat : Commute a c.s.t) (haL : a ∈ normalizer (L : Set G))
    (haW : a ∈ normalizer (y7bW c.s : Set G)) :
    a ∈ normalizer (c.s.fr.B : Set G) := by
  have haH : a ∈ normalizer (c.s.H : Set G) := by
    have hH : c.s.H = Subgroup.centralizer ({c.s.t} : Set G) := rfl
    rw [hH, Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hh
      exact y7b_conj_commute_of_commute hat hh
    · intro hh
      have hconj := y7b_conj_commute_of_commute hat.inv_left hh
      have heq : a⁻¹ * (a * h * a⁻¹) * a⁻¹⁻¹ = h := by group
      rwa [heq] at hconj
  have hB_eq : L ⊓ (c.s.H ⊓ y7bW c.s) = c.s.fr.B := by
    rw [y7b_H_inf_W c hb, y7b_L_inf_P (s := c.s) (e := c.e) hb.hH]
  have hmem : a ∈ normalizer ((L ⊓ (c.s.H ⊓ y7bW c.s) : Subgroup G) : Set G) :=
    mem_normalizer_inf haL (mem_normalizer_inf haH haW)
  rwa [hB_eq] at hmem

theorem y7b_N_le_NM3 (c : Ctx7 G L) (hb : B5Std c) :
    normIn c.s.H c.s.fr.B ≤ normalizer (M3 c.s : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro n hn m hm
  have hnH : n ∈ c.s.H := (Subgroup.mem_inf.mp hn).1
  have hnF : n ∈ normalizer (c.s.fr.F : Set G) := y7b_N_le_NF c.toCtx5 hb.hH hn
  exact y54_N_norm_M3 c.toCtx5 hb.hH n (Subgroup.mem_inf.mpr ⟨hnH, hnF⟩) m hm

theorem y7b_N_le_NC3 (c : Ctx7 G L) (hb : B5Std c) :
    normIn c.s.H c.s.fr.B ≤ normalizer (C3 c.s : Set G) := by
  intro n hn
  rw [y54_C3_eq_M3 c.toCtx5 hb.hH]
  refine mem_normalizer_sup (y7b_N_le_NM3 c hb hn) ?_
  apply mem_normalizer_zpowers
  have hnH : n ∈ c.s.H := (Subgroup.mem_inf.mp hn).1
  have hcomm : n * c.s.t = c.s.t * n := Subgroup.mem_centralizer_singleton_iff.mp hnH
  calc n * c.s.t * n⁻¹ = (c.s.t * n) * n⁻¹ := by rw [hcomm]
    _ = c.s.t := by group

theorem y7b_N_le_X (c : Ctx7 G L) (hb : B5Std c) : normIn c.s.H c.s.fr.B ≤ y7bX c.s := by
  intro n hn
  refine Subgroup.mem_inf.mpr ⟨?_, y7b_N_le_NM3 c hb hn⟩
  exact mem_normalizer_sup (Subgroup.mem_inf.mp hn).2 (y7b_N_le_NC3 c hb hn)

theorem y7b_W_le_X (c : Ctx7 G L) (hb : B5Std c) : y7bW c.s ≤ y7bX c.s := by
  intro x hx
  exact Subgroup.mem_inf.mpr
    ⟨Subgroup.le_normalizer (H := y7bW c.s) hx, y7b_W_le_NM3 c hb hx⟩

theorem y7b_C_le_X (c : Ctx7 G L) (hb : B5Std c) : y7bC c.s ≤ y7bX c.s := by
  have hM3W : M3 c.s ≤ y7bW c.s := by
    rw [y7bW, y54_C3_eq_M3 c.toCtx5 hb.hH]
    exact le_sup_left.trans le_sup_right
  exact sup_le (y7b_N_le_X c hb) (hM3W.trans (y7b_W_le_X c hb))

theorem y7b_mem_C (c : Ctx7 G L) (hb : B5Std c) {x : G} :
    x ∈ y7bC c.s ↔ ∃ n ∈ normIn c.s.H c.s.fr.B, ∃ m ∈ M3 c.s, x = n * m :=
  mem_sup_iff_exists_mul_of_le_normalizer (H := normIn c.s.H c.s.fr.B) (K := M3 c.s)
    (y7b_N_le_NM3 c hb)

theorem y7b_comm_t_of_mem_C (c : Ctx7 G L) (hb : B5Std c) :
    ∀ x ∈ y7bC c.s, ⁅x, c.s.t⁆ ∈ M3 c.s := by
  intro x hx
  obtain ⟨n, hn, m, hm, rfl⟩ := (y7b_mem_C c hb).mp hx
  have hnH : n ∈ c.s.H := (Subgroup.mem_inf.mp hn).1
  have hnM3 : n ∈ normalizer (M3 c.s : Set G) := y7b_N_le_NM3 c hb hn
  have hn_comm : ⁅n, c.s.t⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_singleton_iff.mp hnH)
  have hm_comm : ⁅m, c.s.t⁆ ∈ M3 c.s := by
    have ht : c.s.t * m * c.s.t⁻¹ ∈ M3 c.s :=
      y54_R_norm_M3 c.toCtx5 hb.hH c.s.t (s3_t_mem_R c.s) m hm
    have heq : ⁅m, c.s.t⁆ = m * (c.s.t * m * c.s.t⁻¹)⁻¹ := by
      rw [commutatorElement_def]; group
    rw [heq]
    exact (M3 c.s).mul_mem hm ((M3 c.s).inv_mem ht)
  rw [commutatorElement_mul_left_eq_conj_mul, hn_comm, mul_one]
  exact (Subgroup.mem_normalizer_iff.mp hnM3 ⁅m, c.s.t⁆).mp hm_comm

theorem y7b_cent_tbar (c : Ctx7 G L) (hb : B5Std c) :
    ∀ x ∈ y7bX c.s, ⁅x, c.s.t⁆ ∈ M3 c.s → x ∈ y7bC c.s := by
  intro x hxX hu
  have ht2 : c.s.t * c.s.t = 1 := by
    rw [← pow_two, ← c.s.t_order]
    exact pow_orderOf_eq_one c.s.t
  set u : G := ⁅x, c.s.t⁆ with hu_def
  have hu_mem : u ∈ M3 c.s := by simpa [hu_def] using hu
  have hxt : x * c.s.t * x⁻¹ = u * c.s.t := by
    rw [hu_def, commutatorElement_def]; group
  have hsq : (x * c.s.t * x⁻¹) ^ 2 = 1 := by
    rw [pow_two,
      show (x * c.s.t * x⁻¹) * (x * c.s.t * x⁻¹) = x * (c.s.t * c.s.t) * x⁻¹ by group, ht2]
    group
  have hut : (u * c.s.t) ^ 2 = 1 := by rw [← hxt]; exact hsq
  have hut1 : u * (c.s.t * u * c.s.t) = 1 := by
    rw [show u * (c.s.t * u * c.s.t) = (u * c.s.t) * (u * c.s.t) by group, ← pow_two]
    exact hut
  have htut : c.s.t * u * c.s.t = u⁻¹ := by
    calc c.s.t * u * c.s.t = 1 * (c.s.t * u * c.s.t) := (one_mul _).symm
      _ = (u⁻¹ * u) * (c.s.t * u * c.s.t) := by rw [← inv_mul_cancel]
      _ = u⁻¹ * (u * (c.s.t * u * c.s.t)) := by group
      _ = u⁻¹ * 1 := by rw [hut1]
      _ = u⁻¹ := mul_one _
  have hu_inv : u⁻¹ = u := by
    have hsq_u : u ^ 2 = 1 := (y7b_M3_elem c hb).2 u hu_mem
    rw [pow_two] at hsq_u
    exact inv_eq_of_mul_eq_one_right hsq_u
  rw [hu_inv] at htut
  have hu_comm : u * c.s.t = c.s.t * u := by
    calc u * c.s.t = (c.s.t * u * c.s.t) * c.s.t := by rw [htut]
      _ = c.s.t * u * (c.s.t * c.s.t) := by group
      _ = c.s.t * u := by rw [ht2, mul_one]
  have huH : u ∈ c.s.H := by
    change u ∈ Subgroup.centralizer ({c.s.t} : Set G)
    exact Subgroup.mem_centralizer_singleton_iff.mpr hu_comm
  have huF : u ∈ c.s.fr.F := by
    have : u ∈ c.s.H ⊓ M3 c.s := Subgroup.mem_inf.mpr ⟨huH, hu_mem⟩
    rwa [y54_H_inf_M3 c.toCtx5 hb.hH] at this
  have hxt_mem : x * c.s.t * x⁻¹ ∈ c.s.tCoset c.s.fr.F := ⟨u, huF, hxt⟩
  rw [← y54_conjClass_M3 c.toCtx5 hb.hH] at hxt_mem
  obtain ⟨m, hmM3, hm⟩ := hxt_mem
  have hn_conj : m⁻¹ * x * c.s.t * (m⁻¹ * x)⁻¹ = c.s.t := by
    rw [show m⁻¹ * x * c.s.t * (m⁻¹ * x)⁻¹ = m⁻¹ * (x * c.s.t * x⁻¹) * m by group, hm]
    group
  have hn_comm : (m⁻¹ * x) * c.s.t = c.s.t * (m⁻¹ * x) := by
    calc (m⁻¹ * x) * c.s.t
        = ((m⁻¹ * x) * c.s.t * (m⁻¹ * x)⁻¹) * (m⁻¹ * x) := by group
      _ = c.s.t * (m⁻¹ * x) := by rw [hn_conj]
  have hnH : m⁻¹ * x ∈ c.s.H := by
    change m⁻¹ * x ∈ Subgroup.centralizer ({c.s.t} : Set G)
    exact Subgroup.mem_centralizer_singleton_iff.mpr hn_comm
  have hM3W : M3 c.s ≤ y7bW c.s := by
    rw [y7bW, y54_C3_eq_M3 c.toCtx5 hb.hH]
    exact le_sup_left.trans le_sup_right
  have hxW : x ∈ normalizer (y7bW c.s : Set G) := (Subgroup.mem_inf.mp hxX).1
  have hxN3 : x ∈ normalizer (M3 c.s : Set G) := (Subgroup.mem_inf.mp hxX).2
  have hmNW : m ∈ normalizer (y7bW c.s : Set G) :=
    Subgroup.le_normalizer (H := y7bW c.s) (hM3W hmM3)
  have hmNM3 : m ∈ normalizer (M3 c.s : Set G) :=
    Subgroup.le_normalizer (H := M3 c.s) hmM3
  have hnNW : m⁻¹ * x ∈ normalizer (y7bW c.s : Set G) :=
    (Subgroup.normalizer (y7bW c.s : Set G)).mul_mem
      ((Subgroup.normalizer (y7bW c.s : Set G)).inv_mem hmNW) hxW
  have hnN3 : m⁻¹ * x ∈ normalizer (M3 c.s : Set G) :=
    (Subgroup.normalizer (M3 c.s : Set G)).mul_mem
      ((Subgroup.normalizer (M3 c.s : Set G)).inv_mem hmNM3) hxN3
  have hnNL : m⁻¹ * x ∈ normalizer (L : Set G) := s3_H_le_N c.s hb.hH.hS hnH
  have hnNB : m⁻¹ * x ∈ normalizer (c.s.fr.B : Set G) :=
    y7b_mem_normalizer_B_of_comm_t c hb hn_comm hnNL hnNW
  have hnC : m⁻¹ * x ∈ normIn c.s.H c.s.fr.B := Subgroup.mem_inf.mpr ⟨hnH, hnNB⟩
  rw [y7b_mem_C c hb]
  refine ⟨m⁻¹ * x, hnC, (m⁻¹ * x)⁻¹ * m * (m⁻¹ * x), ?_, ?_⟩
  · have hn_inv : (m⁻¹ * x)⁻¹ ∈ normIn c.s.H c.s.fr.B :=
      (normIn c.s.H c.s.fr.B).inv_mem hnC
    have := (Subgroup.mem_normalizer_iff.mp (y7b_N_le_NM3 c hb hn_inv) m).mp hmM3
    simpa using this
  · group

end CFSG.OddStandard.HigherRank.YamadaG23
