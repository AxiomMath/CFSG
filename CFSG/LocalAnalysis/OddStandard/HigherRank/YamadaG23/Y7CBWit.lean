module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CBP1

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

theorem y7c_comm_cent_t {Γ : Type} [Group Γ] {W : Subgroup Γ} (hW : IsElemAbelian 2 W) {t : Γ}
    (ht2 : t ^ 2 = 1) (htW : ∀ m ∈ W, t * m * t⁻¹ ∈ W) {m : Γ} (hm : m ∈ W) :
    ⁅m, t⁆ ∈ W ∧ ⁅m, t⁆ * t = t * ⁅m, t⁆ := by
  obtain ⟨hcomm, hexp⟩ := hW
  have hu : t * m * t⁻¹ ∈ W := htW m hm
  have hm' : m⁻¹ = m := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hexp m hm)
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact ht2)
  have hmu : m * (t * m * t⁻¹) = (t * m * t⁻¹) * m :=
    congrArg Subtype.val (hcomm.is_comm.comm ⟨m, hm⟩ ⟨_, hu⟩)
  rw [ht'] at hmu hu
  refine ⟨?_, ?_⟩
  · have : ⁅m, t⁆ = m * (t * m * t)⁻¹ := by
      simp only [commutatorElement_def, hm', ht', mul_inv_rev, mul_assoc]
    rw [this]
    exact W.mul_mem hm (W.inv_mem hu)
  · have hmu' : m * t * m * t = t * m * t * m := by simpa only [mul_assoc] using hmu
    have htt : t * t = 1 := by rw [← pow_two]; exact ht2
    simp only [commutatorElement_def, hm', ht']
    calc m * t * m * t * t = m * t * m * (t * t) := by simp only [mul_assoc]
      _ = m * t * m := by rw [htt, mul_one]
      _ = t * (m * t * m * t) := by
        have h1 : t * (m * t * m * t) = t * (t * m * t * m) := by rw [hmu']
        rw [h1]
        simp only [← mul_assoc, htt, one_mul]

private theorem y7c_isElemAbelian_of_isE {Γ : Type} [Group Γ] {W : Subgroup Γ} {n : ℕ}
    (h : IsE n ↥W) : IsElemAbelian 2 W := by
  obtain ⟨⟨hc, hsq⟩, -⟩ := h
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · exact congrArg Subtype.val (hc.is_comm.comm ⟨a, Subgroup.mem_top a⟩ ⟨b, Subgroup.mem_top b⟩)
  · exact congrArg Subtype.val (hsq ⟨x, hx⟩ (Subgroup.mem_top _))

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7c_B_comm_wit (c : Ctx7 G L) (hb : B7Std c) :
    ∃ m : y7cGam c.s, ⁅m, y7cTC c hb⁆ ∈ y7cJC c ∧ ⁅m, y7cTC c hb⁆ ≠ 1 := by
  obtain ⟨k, hk6, hk5⟩ := y7b_exists_M6_comm_not_mem_M5 c hb.toB6Std
  have hkX : k ∈ y7cX c.s := y7c_M6_le_X c hb hk6
  have htX : c.s.t ∈ y7cX c.s := y7c_t_mem_X c hb
  have htM6 : c.s.t ∈ normalizer (M6 c.e : Set G) := y7b_R_le_NM6 c hb.toB5Std (s3_t_mem_R c.s)
  refine ⟨y7cPi c.s ⟨k, hkX⟩, ?_, ?_⟩
  · have hmM6 : y7cPi c.s ⟨k, hkX⟩ ∈ y7cM6C c := (mem_y7cImg c.s).mpr ⟨⟨k, hkX⟩, hk6, rfl⟩
    have htn : ∀ x ∈ y7cM6C c, y7cTC c hb * x * (y7cTC c hb)⁻¹ ∈ y7cM6C c := by
      intro x hx
      obtain ⟨y, hyM6, rfl⟩ := (mem_y7cImg c.s).mp hx
      have hconj : c.s.t * (y : G) * c.s.t⁻¹ ∈ M6 c.e :=
        (Subgroup.mem_normalizer_iff.mp htM6 _).mp hyM6
      refine (mem_y7cImg c.s).mpr ⟨⟨c.s.t, htX⟩ * y * ⟨c.s.t, htX⟩⁻¹, hconj, ?_⟩
      simp only [map_mul, map_inv]
    obtain ⟨hmem, hcomm⟩ := y7c_comm_cent_t (y7c_isElemAbelian_of_isE (y7c_B_M6_E c hb))
      (y7c_B_t_sq c hb) htn hmM6
    have hle : y7cM6C c ≤ y7cPC c := by
      rw [y7c_B_P_sup c hb]
      exact le_sup_left
    exact y7c_B_P_cent_t c hb _ (hle hmem) hcomm
  · intro h1
    have h2 : y7cPi c.s ⁅(⟨k, hkX⟩ : ↥(y7cX c.s)), ⟨c.s.t, htX⟩⁆ = 1 := by
      rw [map_commutatorElement]
      exact h1
    rw [y7cPi_eq_one_iff] at h2
    exact hk5 ((show M3 c.s ≤ M5 c.e from le_sup_left) h2)

end CFSG.OddStandard.HigherRank.YamadaG23
