module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7Defs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B5a
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7BAbsF

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y7b_t_sq (c : Ctx7 G L) : c.s.t * c.s.t = 1 := by
  rw [← pow_two, ← c.s.t_order]
  exact pow_orderOf_eq_one c.s.t

private lemma y7b_t_zpowers_eq_one_or_t (c : Ctx7 G L) {a : G}
    (ha : a ∈ zpowers c.s.t) : a = 1 ∨ a = c.s.t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have hmod : c.s.t ^ k = c.s.t ^ (k % (2 : ℤ)) := by
    rw [← zpow_mod_orderOf, c.s.t_order]
    rfl
  rw [hmod]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [h]; simp
  · right; rw [h]; simp

private lemma y7b_t_mem_H (c : Ctx7 G L) : c.s.t ∈ c.s.H := by
  change c.s.t ∈ Subgroup.centralizer ({c.s.t} : Set G)
  exact Subgroup.mem_centralizer_singleton_iff.mpr rfl

private lemma y7b_B_le_H (c : Ctx7 G L) (hb : B5Std c) : c.s.fr.B ≤ c.s.H :=
  (s3_B_le_S c.s).trans ((s3_S_le_L c.s).trans (s3_L_le_H c.s hb.hH.hS))

private lemma y7b_t_mem_f4N (c : Ctx7 G L) : c.s.t ∈ f4N c.s := by
  change c.s.t ∈ c.s.H ⊓ Subgroup.normalizer (c.s.fr.F : Set G)
  refine Subgroup.mem_inf.mpr ⟨y7b_t_mem_H c, ?_⟩
  exact Subgroup.centralizer_le_normalizer (c.s.fr.F : Set G) (by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact y54_t_comm_F c.s f hf)

private lemma y7b_t_mem_NM3 (c : Ctx7 G L) (hb : B5Std c) :
    c.s.t ∈ normalizer (M3 c.s : Set G) := by
  rw [← Subgroup.zpowers_le, Subgroup.le_normalizer_iff]
  intro h hh m hm
  rcases y7b_t_zpowers_eq_one_or_t c hh with rfl | rfl
  · simpa using hm
  · exact y54_N_norm_M3 c.toCtx5 hb.hH c.s.t (y7b_t_mem_f4N c) m hm

theorem y7b_B_inf_M3 (c : Ctx7 G L) (hb : B5Std c) : c.s.fr.B ⊓ M3 c.s = c.s.fr.F := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxB, hxM3⟩ := Subgroup.mem_inf.mp hx
    have hmem : x ∈ c.s.H ⊓ M3 c.s :=
      Subgroup.mem_inf.mpr ⟨y7b_B_le_H c hb hxB, hxM3⟩
    rwa [y54_H_inf_M3 c.toCtx5 hb.hH] at hmem
  · intro x hx
    exact Subgroup.mem_inf.mpr ⟨y54_F_le_B hb.hH hx, Subgroup.mem_sup_right hx⟩

theorem y7b_B_le_NM3 (c : Ctx7 G L) (hb : B5Std c) :
    c.s.fr.B ≤ normalizer (M3 c.s : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro r hr m hm
  exact y54_R_norm_M3 c.toCtx5 hb.hH r (y54_B_le_R c.s hr) m hm

theorem y7b_mem_BM (c : Ctx7 G L) (hb : B5Std c) {x : G} :
    x ∈ y7bBM c.s ↔ ∃ b ∈ c.s.fr.B, ∃ m ∈ M3 c.s, x = b * m :=
  mem_sup_iff_exists_mul_of_le_normalizer (y7b_B_le_NM3 c hb)

theorem y7b_t_norm_BM (c : Ctx7 G L) (hb : B5Std c) :
    c.s.t ∈ normalizer (y7bBM c.s : Set G) := by
  have htB : c.s.t ∈ normalizer (c.s.fr.B : Set G) :=
    Subgroup.centralizer_le_normalizer (c.s.fr.B : Set G) (by
      rw [Subgroup.mem_centralizer_iff]
      intro b hbB
      exact Subgroup.mem_centralizer_singleton_iff.mp (y7b_B_le_H c hb hbB))
  exact inf_normalizer_le_normalizer_sup (c.s.fr.B) (M3 c.s)
    (Subgroup.mem_inf.mpr ⟨htB, y7b_t_mem_NM3 c hb⟩)

theorem y7b_BM_le_W (c : Ctx7 G L) (hb : B5Std c) : y7bBM c.s ≤ y7bW c.s := by
  have hM3C3 : M3 c.s ≤ C3 c.s := by
    rw [y54_C3_eq_M3 c.toCtx5 hb.hH]
    exact le_sup_left
  rw [y7bBM, y7bW]
  exact sup_le le_sup_left (hM3C3.trans le_sup_right)

theorem y7b_t_mem_W (c : Ctx7 G L) (hb : B5Std c) : c.s.t ∈ y7bW c.s := by
  refine Subgroup.mem_sup_right ?_
  rw [y54_C3_eq_M3 c.toCtx5 hb.hH]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c.s.t)

theorem y7b_mem_W (c : Ctx7 G L) (hb : B5Std c) {x : G} :
    x ∈ y7bW c.s ↔ ∃ w ∈ y7bBM c.s, x = w ∨ x = w * c.s.t := by
  have hW : y7bW c.s = y7bBM c.s ⊔ zpowers c.s.t := by
    rw [y7bW, y7bBM, y54_C3_eq_M3 c.toCtx5 hb.hH, sup_assoc]
  rw [hW, sup_comm]
  have hn : zpowers c.s.t ≤ normalizer (y7bBM c.s : Set G) :=
    Subgroup.zpowers_le.mpr (y7b_t_norm_BM c hb)
  constructor
  · intro hx
    obtain ⟨w, hw, a, ha, hxwa⟩ :=
      (mem_sup_iff_exists_mul_of_le_normalizer' (H := zpowers c.s.t) (K := y7bBM c.s)
        hn).mp hx
    rcases y7b_t_zpowers_eq_one_or_t c ha with ha1 | hat
    · exact ⟨w, hw, Or.inl (by rw [hxwa, ha1, mul_one])⟩
    · exact ⟨w, hw, Or.inr (by rw [hxwa, hat])⟩
  · rintro ⟨w, hw, hxw | hxw⟩
    · rw [hxw]; exact Subgroup.mem_sup_right hw
    · rw [hxw]
      exact (zpowers c.s.t ⊔ y7bBM c.s).mul_mem
        (Subgroup.mem_sup_right hw) (Subgroup.mem_sup_left (Subgroup.mem_zpowers c.s.t))

theorem y7b_W_le_NM3 (c : Ctx7 G L) (hb : B5Std c) :
    y7bW c.s ≤ normalizer (M3 c.s : Set G) := by
  have hW : y7bW c.s = y7bBM c.s ⊔ zpowers c.s.t := by
    rw [y7bW, y7bBM, y54_C3_eq_M3 c.toCtx5 hb.hH, sup_assoc]
  rw [hW]
  exact sup_le (sup_le (y7b_B_le_NM3 c hb) (Subgroup.le_normalizer (H := M3 c.s)))
    (Subgroup.zpowers_le.mpr (y7b_t_mem_NM3 c hb))

theorem y7b_relIndex_BM_W (c : Ctx7 G L) (hb : B5Std c) :
    (y7bBM c.s).relIndex (y7bW c.s) = 2 := by
  rw [Subgroup.relIndex_eq_two_iff']
  refine ⟨c.s.t, y7b_t_mem_W c hb, ?_⟩
  intro b hbW
  obtain ⟨w, hw, hbw | hbw⟩ := (y7b_mem_W c hb).mp hbW
  · rw [hbw]
    rw [xor_iff_or_and_not_and]
    have hnot : c.s.t * w ∉ y7bBM c.s := by
      intro hmem
      exact y7b_t_not_mem_BM3 c hb (by
        have : c.s.t = (c.s.t * w) * w⁻¹ := by group
        rw [this]
        exact (y7bBM c.s).mul_mem hmem ((y7bBM c.s).inv_mem hw))
    exact ⟨Or.inr hw, fun h => hnot h.1⟩
  · rw [hbw]
    rw [xor_iff_or_and_not_and]
    have hnot : w * c.s.t ∉ y7bBM c.s := by
      intro hmem
      exact y7b_t_not_mem_BM3 c hb (by
        have : c.s.t = w⁻¹ * (w * c.s.t) := by group
        rw [this]
        exact (y7bBM c.s).mul_mem ((y7bBM c.s).inv_mem hw) hmem)
    refine ⟨Or.inl ?_, fun h => hnot h.2⟩
    have hconj : c.s.t * w * c.s.t⁻¹ ∈ y7bBM c.s :=
      (Subgroup.mem_normalizer_iff.mp (y7b_t_norm_BM c hb) w).mp hw
    rw [inv_eq_of_mul_eq_one_right (y7b_t_sq c)] at hconj
    have ht : c.s.t * (w * c.s.t) = c.s.t * w * c.s.t := by group
    rw [ht]; exact hconj

theorem y7b_H_inf_BM (c : Ctx7 G L) (hb : B5Std c) : c.s.H ⊓ y7bBM c.s = c.s.fr.B := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxH, hxBM⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨b, hbB, m, hmM3, rfl⟩ := (y7b_mem_BM c hb).mp hxBM
    have hbH : b ∈ c.s.H := y7b_B_le_H c hb hbB
    have hmH : m ∈ c.s.H := by
      have : m = b⁻¹ * (b * m) := by group
      rw [this]
      exact c.s.H.mul_mem (c.s.H.inv_mem hbH) hxH
    have hmF : m ∈ c.s.fr.F := by
      have : m ∈ c.s.H ⊓ M3 c.s := Subgroup.mem_inf.mpr ⟨hmH, hmM3⟩
      rwa [y54_H_inf_M3 c.toCtx5 hb.hH] at this
    exact c.s.fr.B.mul_mem hbB (y54_F_le_B hb.hH hmF)
  · intro x hx
    exact Subgroup.mem_inf.mpr ⟨y7b_B_le_H c hb hx, Subgroup.mem_sup_left hx⟩

theorem y7b_H_inf_W (c : Ctx7 G L) (hb : B5Std c) :
    c.s.H ⊓ y7bW c.s = c.s.fr.B ⊔ zpowers c.s.t := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxH, hxW⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨w, hw, hxw | hxw⟩ := (y7b_mem_W c hb).mp hxW
    · have hwB : w ∈ c.s.fr.B := by
        have : w ∈ c.s.H ⊓ y7bBM c.s :=
          Subgroup.mem_inf.mpr ⟨hxw ▸ hxH, hw⟩
        rwa [y7b_H_inf_BM c hb] at this
      rw [hxw]
      exact Subgroup.mem_sup_left hwB
    · have hwH : w ∈ c.s.H := by
        have hxt : w = x * c.s.t := by
          rw [hxw, mul_assoc, y7b_t_sq c, mul_one]
        rw [hxt]
        exact c.s.H.mul_mem hxH (y7b_t_mem_H c)
      have hwB : w ∈ c.s.fr.B := by
        have : w ∈ c.s.H ⊓ y7bBM c.s := Subgroup.mem_inf.mpr ⟨hwH, hw⟩
        rwa [y7b_H_inf_BM c hb] at this
      rw [hxw]
      exact (c.s.fr.B ⊔ zpowers c.s.t).mul_mem (Subgroup.mem_sup_left hwB)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers c.s.t))
  · refine sup_le ?_ ?_
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨y7b_B_le_H c hb hx, Subgroup.mem_sup_left hx⟩
    · exact Subgroup.zpowers_le.mpr
        (Subgroup.mem_inf.mpr ⟨y7b_t_mem_H c, y7b_t_mem_W c hb⟩)

theorem y7b_relIndex_F_B (c : Ctx7 G L) (hb : B5Std c) :
    c.s.fr.F.relIndex c.s.fr.B = 4 :=
  relIndex_eq_of_card_eq_mul (y54_F_le_B hb.hH) (by
    norm_num [y54_card_B hb.hH, y7b_card_F hb.hH])

theorem y7b_card_BM (c : Ctx7 G L) (hb : B5Std c) : Nat.card ↥(y7bBM c.s) = 2 ^ 8 := by
  have h := card_sup_mul_card_inf_of_le_normalizer (H := c.s.fr.B) (K := M3 c.s)
    (y7b_B_le_NM3 c hb)
  rw [y7b_B_inf_M3 c hb, y7b_card_F hb.hH, y54_card_B hb.hH, y7b_card_M3 c hb] at h
  change Nat.card ↥(c.s.fr.B ⊔ M3 c.s) = 2 ^ 8
  norm_num at h ⊢
  omega

theorem y7b_card_W (c : Ctx7 G L) (hb : B5Std c) : Nat.card ↥(y7bW c.s) = 2 ^ 9 := by
  have h := Subgroup.relIndex_mul_card (H := y7bBM c.s) (K := y7bW c.s)
  rw [inf_of_le_left (y7b_BM_le_W c hb), y7b_relIndex_BM_W c hb, y7b_card_BM c hb] at h
  rw [← h]
  norm_num

theorem y7b_relIndex_M3_BM (c : Ctx7 G L) (hb : B5Std c) :
    (M3 c.s).relIndex (y7bBM c.s) = 4 :=
  relIndex_eq_of_card_eq_mul le_sup_right (by
    norm_num [y7b_card_BM c hb, y7b_card_M3 c hb])

theorem y7b_relIndex_M3_W (c : Ctx7 G L) (hb : B5Std c) :
    (M3 c.s).relIndex (y7bW c.s) = 8 := by
  have hM3le : M3 c.s ≤ y7bW c.s := by
    rw [y7bW, y54_C3_eq_M3 c.toCtx5 hb.hH]
    exact le_sup_left.trans le_sup_right
  exact relIndex_eq_of_card_eq_mul hM3le (by
    norm_num [y7b_card_W c hb, y7b_card_M3 c hb])

end CFSG.OddStandard.HigherRank.YamadaG23
